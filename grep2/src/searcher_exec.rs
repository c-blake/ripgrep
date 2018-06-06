use std::cmp;
use std::fmt;
use std::io;

use memchr::memchr;

use lines::{self, LineStep};
use line_buffer::{
    self, LineBufferReader,
    DEFAULT_BUFFER_CAPACITY,
};
use matcher::{LineMatchKind, Match, Matcher};
use searcher_builder::{Config, Searcher};
use sink::{Sink, SinkFinish, SinkMatch};

/// A trait to abstract over different sources of bytes to search.
///
/// This trait is used by the Searcher to construct a source to search over.
/// Principally, it copies the API of a LineBufferReader. The actual search
/// routines then use this Reader as if it were a LineBufferReader.
///
/// The trick is that we also implement this trait with a SliceReader, that
/// behaves like a LineBufferReader that reads the entire contents of its
/// source into memory in the first read.
pub trait Reader {
    fn absolute_byte_offset(&self) -> u64;
    fn binary_byte_offset(&self) -> Option<u64>;
    fn fill(&mut self) -> Result<bool, io::Error>;
    fn buffer(&self) -> &[u8];
    fn consume(&mut self, amt: usize);
    fn consume_all(&mut self);
    fn has_binary(&mut self, binary_byte: u8, range: &Match) -> bool;
}

impl<'b, R: io::Read> Reader for LineBufferReader<'b, R> {
    fn absolute_byte_offset(&self) -> u64 {
        LineBufferReader::absolute_byte_offset(self)
    }

    fn binary_byte_offset(&self) -> Option<u64> {
        LineBufferReader::binary_byte_offset(self)
    }

    fn fill(&mut self) -> Result<bool, io::Error> {
        LineBufferReader::fill(self)
    }

    fn buffer(&self) -> &[u8] {
        LineBufferReader::buffer(self)
    }

    fn consume(&mut self, amt: usize) {
        LineBufferReader::consume(self, amt)
    }

    fn consume_all(&mut self) {
        LineBufferReader::consume_all(self)
    }

    fn has_binary(&mut self, _binary_byte: u8, _range: &Match) -> bool {
        // The InputBuffer does its own binary detection logic.
        false
    }
}

/// SliceReader is a way of making a slice behave as a LineBuffer. Initially,
/// it starts empty, like a LineBuffer. The first call to `fill` causes the
/// entire slice to be available. Subsequent calls to `fill` return `true`
/// until the entire buffer is consumed.
pub struct SliceReader<'b> {
    slice: &'b [u8],
    absolute_byte_offset: u64,
    binary_byte_offset: Option<u64>,
    filled: bool,
}

impl<'b> SliceReader<'b> {
    pub fn new(slice: &'b [u8]) -> SliceReader<'b> {
        SliceReader {
            slice,
            absolute_byte_offset: 0,
            binary_byte_offset: None,
            filled: false,
        }
    }
}

impl<'b> Reader for SliceReader<'b> {
    fn absolute_byte_offset(&self) -> u64 {
        self.absolute_byte_offset
    }

    fn binary_byte_offset(&self) -> Option<u64> {
        self.binary_byte_offset
    }

    fn fill(&mut self) -> Result<bool, io::Error> {
        if !self.filled {
            self.filled = true;
        }
        Ok(!self.slice.is_empty())
    }

    fn buffer(&self) -> &[u8] {
        if !self.filled {
            &[]
        } else {
            self.slice
        }
    }

    fn consume(&mut self, amt: usize) {
        if !self.filled {
            return;
        }
        self.slice = &self.slice[amt..];
        self.absolute_byte_offset += amt as u64;
    }

    fn consume_all(&mut self) {
        let amt = self.slice.len();
        self.consume(amt);
    }

    fn has_binary(&mut self, binary_byte: u8, range: &Match) -> bool {
        if !self.filled {
            return false;
        }
        if self.binary_byte_offset.is_some() {
            return true;
        }
        self.binary_byte_offset = memchr(binary_byte, &self.slice[*range])
            .map(|o| (range.start() + o) as u64);
        self.binary_byte_offset.is_some()
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
struct LineMatch {
    line: Match,
    line_number: Option<u64>,
}

#[derive(Debug)]
pub struct SearcherByLine<'s, M: 's, R, S> {
    searcher: &'s Searcher<M>,
    config: &'s Config,
    matcher: &'s M,
    sink: S,
    rdr: R,
    search_pos: usize,
    line_number: Option<u64>,
    last_line_counted: usize,
}

impl<'s, M, R, S> SearcherByLine<'s, M, R, S>
where M: Matcher,
      M::Error: fmt::Display,
      R: Reader,
      S: Sink
{
    pub fn new(
        searcher: &'s Searcher<M>,
        read_from: R,
        write_to: S,
    ) -> SearcherByLine<'s, M, R, S> {
        assert!(!searcher.config.multi_line);

        let line_number =
            if searcher.config.line_number {
                Some(1)
            } else {
                None
            };
        SearcherByLine {
            searcher: searcher,
            config: &searcher.config,
            matcher: &searcher.matcher,
            sink: write_to,
            rdr: read_from,
            search_pos: 0,
            line_number: line_number,
            last_line_counted: 0,
        }
    }

    pub fn run(mut self) -> Result<(), S::Error> {
        assert!(!self.config.multi_line);

    'LOOP:
        loop {
            if !self.fill()? {
                break;
            }
            let binary_upto = cmp::min(
                self.search_buffer().len(),
                DEFAULT_BUFFER_CAPACITY,
            );
            if self.has_binary(&Match::new(0, binary_upto)) {
                break 'LOOP;
            }
            while !self.search_buffer().is_empty() {
                if !self.sink()? {
                    break 'LOOP;
                }
            }
        }
        self.sink.finish(&SinkFinish {
            byte_count: self.rdr.absolute_byte_offset(),
            binary_byte_offset: self.rdr.binary_byte_offset(),
        })
    }

    fn buffer(&self) -> &[u8] {
        self.rdr.buffer()
    }

    fn search_buffer(&self) -> &[u8] {
        &self.rdr.buffer()[self.search_pos..]
    }

    fn fill(&mut self) -> Result<bool, S::Error> {
        assert!(self.search_buffer().is_empty());

        self.count_remaining_lines();
        self.rdr.consume_all();
        self.search_pos = 0;
        self.last_line_counted = 0;
        let didread = match self.rdr.fill() {
            Err(err) => return Err(S::error_io(err)),
            Ok(didread) => didread,
        };
        if !didread || self.rdr.binary_byte_offset().is_some() {
            return Ok(false);
        }
        Ok(true)
    }

    fn sink(&mut self) -> Result<bool, S::Error> {
        if self.config.invert_match {
            self.sink_inverted_matches()
        } else if let Some(line) = self.find()? {
            self.count_lines(line.start());
            let keepgoing = self.sink_matched(&line)?;
            self.search_pos = line.end();
            Ok(keepgoing)
        } else {
            self.search_pos = self.buffer().len();
            Ok(true)
        }
    }

    fn sink_inverted_matches(&mut self) -> Result<bool, S::Error> {
        assert!(self.config.invert_match);

        let invert_match = match self.find()? {
            None => {
                let m = Match::new(self.search_pos, self.buffer().len());
                self.search_pos = m.end();
                m
            }
            Some(line) => {
                let m = Match::new(self.search_pos, line.start());
                self.search_pos = line.end();
                m
            }
        };
        self.count_lines(invert_match.start());
        let mut stepper = LineStep::new(self.config.line_term, invert_match);
        while let Some(line) = stepper.next(self.buffer()) {
            if !self.sink_matched(&line)? {
                return Ok(false);
            }
            self.add_one_line(line.end());
        }
        Ok(true)
    }

    fn sink_matched(&mut self, line: &Match) -> Result<bool, S::Error> {
        if line.is_empty() {
            // The only way we can produce an empty line for a match is if
            // we match the position immediately following the last byte in
            // a buffer, and where that last byte is also the line terminator.
            // We never want to report a match beyond the end of a line, so
            // skip it.
            return Ok(true);
        }
        if self.has_binary(line) {
            self.rdr.consume(line.start());
            return Ok(false);
        }
        let offset = self.rdr.absolute_byte_offset() + line.start() as u64;
        self.sink.matched(
            self.searcher,
            &SinkMatch {
                line_term: self.config.line_term,
                bytes: &self.rdr.buffer()[*line],
                absolute_byte_offset: offset,
                line_number: self.line_number,
            },
        )
    }

    fn find(&mut self) -> Result<Option<Match>, S::Error> {
        if let Some(line_term) = self.matcher.line_terminator() {
            // This is checked by the search builder.
            assert_eq!(line_term, self.config.line_term);
            self.find_fast()
        } else {
            self.find_by_line()
        }
    }

    fn find_fast(&mut self) -> Result<Option<Match>, S::Error> {
        let buf = &self.rdr.buffer();
        let mut pos = self.search_pos;
        while !buf[pos..].is_empty() {
            match self.matcher.find_candidate_line(&buf[pos..]) {
                Err(err) => return Err(S::error_message(err)),
                Ok(None) => return Ok(None),
                Ok(Some(LineMatchKind::Confirmed(i))) => {
                    return Ok(Some(lines::locate(
                        self.buffer(),
                        self.config.line_term,
                        Match::zero(i).offset(pos),
                    )));
                }
                Ok(Some(LineMatchKind::Candidate(i))) => {
                    let line = lines::locate(
                        self.rdr.buffer(),
                        self.config.line_term,
                        Match::zero(i).offset(pos),
                    );
                    let slice = lines::without_terminator(
                        &buf[line],
                        self.config.line_term,
                    );
                    match self.matcher.shortest_match(slice) {
                        Err(err) => return Err(S::error_message(err)),
                        Ok(Some(_)) => return Ok(Some(line)),
                        Ok(None) => {
                            pos = line.end();
                            continue;
                        }
                    }
                }
            }
        }
        Ok(None)
    }

    fn find_by_line(&mut self) -> Result<Option<Match>, S::Error> {
        let range = Match::new(0, self.search_buffer().len());
        let mut stepper = LineStep::new(self.config.line_term, range);
        while let Some(line) = stepper.next(self.search_buffer()) {
            let slice = lines::without_terminator(
                &self.search_buffer()[line], self.config.line_term);
            match self.matcher.shortest_match(slice) {
                Err(err) => return Err(S::error_message(err)),
                Ok(Some(_)) => return Ok(Some(line.offset(self.search_pos))),
                Ok(None) => continue,
            }
        }
        Ok(None)
    }

    fn count_remaining_lines(&mut self) {
        let upto = self.buffer().len();
        self.count_lines(upto);
    }

    fn count_lines(&mut self, upto: usize) {
        if let Some(ref mut line_number) = self.line_number {
            let slice = &self.rdr.buffer()[self.last_line_counted..upto];
            *line_number += lines::count(slice, self.config.line_term);
            self.last_line_counted = upto;
        }
    }

    fn add_one_line(&mut self, line_end: usize) {
        if let Some(ref mut line_number) = self.line_number {
            *line_number += 1;
            self.last_line_counted = line_end;
        }
    }

    fn has_binary(&mut self, range: &Match) -> bool {
        let binary_byte = match self.config.binary.0 {
            line_buffer::BinaryDetection::Quit(b) => b,
            _ => return false,
        };
        self.rdr.has_binary(binary_byte, range)
    }
}

#[derive(Debug)]
pub struct SearcherMultiLine<'s, M: 's, S> {
    searcher: &'s Searcher<M>,
    config: &'s Config,
    matcher: &'s M,
    sink: S,
    slice: &'s [u8],
    search_pos: usize,
    binary_byte_offset: Option<u64>,
    last_match: Option<LineMatch>,
    line_number: Option<u64>,
    last_line_counted: usize,
}

impl<'s, M, S> SearcherMultiLine<'s, M, S>
where M: Matcher,
      M::Error: fmt::Display,
      S: Sink
{
    pub fn new(
        searcher: &'s Searcher<M>,
        slice: &'s [u8],
        write_to: S,
    ) -> SearcherMultiLine<'s, M, S> {
        assert!(searcher.config.multi_line);

        let line_number =
            if searcher.config.line_number {
                Some(1)
            } else {
                None
            };
        SearcherMultiLine {
            searcher: searcher,
            config: &searcher.config,
            matcher: &searcher.matcher,
            sink: write_to,
            slice: slice,
            search_pos: 0,
            binary_byte_offset: None,
            last_match: None,
            line_number: line_number,
            last_line_counted: 0,
        }
    }

    pub fn run(mut self) -> Result<(), S::Error> {
        assert!(self.config.multi_line);

        let binary_upto = cmp::min(self.slice.len(), DEFAULT_BUFFER_CAPACITY);
        if !self.has_binary(&Match::new(0, binary_upto)) {
            while !self.search_buffer().is_empty() {
                if !self.sink()? {
                    break;
                }
            }
        }
        if let Some(last_match) = self.last_match.take() {
            self.sink_matched(&last_match)?;
        }
        self.sink.finish(&SinkFinish {
            byte_count: self.slice.len() as u64,
            binary_byte_offset: self.binary_byte_offset,
        })
    }

    fn search_buffer(&self) -> &[u8] {
        &self.slice[self.search_pos..]
    }

    fn sink(&mut self) -> Result<bool, S::Error> {
        if self.config.invert_match {
            return self.sink_inverted_matches();
        }
        let mat = match self.find()? {
            Some(range) => range,
            None => {
                self.search_pos = self.slice.len();
                return Ok(true);
            }
        };
        let line = lines::locate(self.slice, self.config.line_term, mat);
        // We delay sinking the match to make sure we group adjacent matches
        // together in a single sink. Adjacent matches are distinct matches
        // that start and end on the same line, respectively. This guarantees
        // that a single line is never sinked more than once.
        let keepgoing = match self.last_match.take() {
            None => true,
            Some(last_match) => {
                // If the lines in the previous match overlap with the lines
                // in this match, then simply grow the match and move on.
                // This happens when the next match begins on the same line
                // that the last match ends on.
                if last_match.line.end() > line.start() {
                    self.last_match = Some(LineMatch {
                        line: last_match.line.with_end(line.end()),
                        line_number: last_match.line_number,
                    });
                    self.advance(&mat);
                    return Ok(true);
                } else {
                    self.sink_matched(&last_match)?
                }
            }
        };
        self.count_lines(line.start());
        self.last_match = Some(LineMatch {
            line: line,
            line_number: self.line_number,
        });
        self.advance(&mat);
        Ok(keepgoing)
    }

    fn sink_inverted_matches(&mut self) -> Result<bool, S::Error> {
        assert!(self.config.invert_match);

        let invert_match = match self.find()? {
            None => {
                let m = Match::new(self.search_pos, self.slice.len());
                self.search_pos = m.end();
                m
            }
            Some(mat) => {
                let line = lines::locate(
                    self.slice, self.config.line_term, mat);
                let m = Match::new(self.search_pos, line.start());
                self.search_pos = line.end();
                m
            }
        };
        let mut stepper = LineStep::new(self.config.line_term, invert_match);
        while let Some(line) = stepper.next(self.slice) {
            self.count_lines(line.start());
            let m = LineMatch {
                line: line,
                line_number: self.line_number,
            };
            if !self.sink_matched(&m)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn sink_matched(&mut self, m: &LineMatch) -> Result<bool, S::Error> {
        if m.line.is_empty() {
            // The only way we can produce an empty line for a match is if we
            // match the position immediately following the last byte that we
            // search, and where that last byte is also the line terminator. We
            // never want to report that match, and we know we're done at that
            // point anyway.
            return Ok(false);
        }
        if self.has_binary(&m.line) {
            return Ok(false);
        }
        self.sink.matched(
            self.searcher,
            &SinkMatch {
                line_term: self.config.line_term,
                bytes: &self.slice[m.line],
                absolute_byte_offset: m.line.start() as u64,
                line_number: m.line_number,
            },
        )
    }

    fn find(&mut self) -> Result<Option<Match>, S::Error> {
        match self.matcher.find(self.search_buffer()) {
            Err(err) => Err(S::error_message(err)),
            Ok(None) => Ok(None),
            Ok(Some(m)) => Ok(Some(m.offset(self.search_pos))),
        }
    }

    fn count_lines(&mut self, upto: usize) {
        if let Some(ref mut line_number) = self.line_number {
            let slice = &self.slice[self.last_line_counted..upto];
            *line_number += lines::count(slice, self.config.line_term);
            self.last_line_counted = upto;
        }
    }

    /// Advance the search position based on the previous match.
    ///
    /// If the previous match is zero width, then this advances the search
    /// position one byte past the end of the match.
    fn advance(&mut self, m: &Match) {
        self.search_pos = m.end();
        if m.is_empty() && self.search_pos < self.slice.len() {
            self.search_pos += 1;
        }
    }

    /// Return true if and only if binary detection is enabled and the given
    /// range contains binary data. When this returns true, the binary offset
    /// is updated.
    fn has_binary(&mut self, range: &Match) -> bool {
        if self.binary_byte_offset.is_some() {
            return true;
        }
        let binary_byte = match self.config.binary.0 {
            line_buffer::BinaryDetection::Quit(b) => b,
            _ => return false,
        };
        if let Some(i) = memchr(binary_byte, &self.slice[*range]) {
            let offset = range.start() + i;
            self.binary_byte_offset = Some(offset as u64);
            // If this is the beginning, then we haven't searched anything,
            // so null out the slice.
            if range.start() == 0 {
                self.slice = &[];
            } else {
                self.slice = &self.slice[..offset];
            }
            return true;
        }
        false
    }
}

// BREADCRUMBS:
//
// Where to go next? Some thoughts:
//
//   1. Do context handling last. (Famous last words.)
//   2. The find_by_line implementation is a little weird. We might want a
//      completely different searcher for that case.
//      2. The find_by_line implementation is a little weird. We might want a
//         completely different searcher for that case.
//   3. Fill out the logic for opening a reader in Searcher.
//
// Massive cleanup. Get things working and then search for simplications.
// Index heavy code is gross. Context handling will make it much worse.

#[cfg(test)]
mod tests {
    use std::fmt;

    use searcher_builder::*;
    use testutil::{EmptyLineMatcher, KitchenSink, SubstringMatcher};

    use super::*;

    const SHERLOCK: &'static str = "\
For the Doctor Watsons of this world, as opposed to the Sherlock
Holmeses, success in the province of detective work must always
be, to a very large extent, the result of luck. Sherlock Holmes
can extract a clew from a wisp of straw or a flake of cigar ash;
but Doctor Watson has to have it taken out for him and dusted,
and exhibited clearly, with a label attached.\
";

    /// Executes the given search on all available searchers, and asserts that
    /// the result of every search is equivalent to the expected result.
    ///
    /// This creates a substring matcher from the given pattern.
    fn search_assert_all<F>(
        expected: &str,
        haystack: &str,
        pattern: &str,
        mut build: F,
    )
    where F: FnMut(&mut SearcherBuilder) -> &mut SearcherBuilder
    {
        let mut matcher = SubstringMatcher::new(pattern);
        search_assert_all_matcher(expected, haystack, &matcher, &mut build);

        // If we're testing single line search, then set the line terminator
        // to force the searcher to use the fast path. This doesn't matter for
        // multi line search (and multi line search tests usually include the
        // line terminator in the pattern).
        if !build(&mut SearcherBuilder::new()).config.multi_line {
            matcher.set_line_term(Some(b'\n'));
            search_assert_all_matcher(
                expected, haystack, &matcher, &mut build);

            // Also, exercise the line oriented optimization by forcing the
            // matcher to report every single line as a candidate match.
            matcher.every_line_is_candidate(true);
            search_assert_all_matcher(
                expected, haystack, &matcher, &mut build);
        }
    }

    /// Executes the given search on all available searchers, and asserts that
    /// the result of every search is equivalent to the expected result.
    ///
    /// This uses the matcher provided.
    fn search_assert_all_matcher<M, F>(
        expected: &str,
        haystack: &str,
        matcher: M,
        mut build: F,
    )
    where M: Matcher,
          M::Error: fmt::Display,
          F: FnMut(&mut SearcherBuilder) -> &mut SearcherBuilder
    {
        let got = search_reader(haystack, &matcher, &mut build);
        assert_eq!(expected, got, "\nsearch_reader mismatch");

        let got = search_slice(haystack, &matcher, &mut build);
        assert_eq!(expected, got, "\nsearch_slice mismatch");

        // If we are executing a multi_line search, then test a heap limit that
        // is equal to the haystack (plus 1), since multi-line search needs to
        // read the entire buffer at once. The plus 1 is necessary since we
        // need space for 1 remaining byte to detect EOF.
        //
        // For line oriented search, test with a heap limit equivalent to the
        // longest line.
        let got =
            if build(&mut SearcherBuilder::new()).config.multi_line {
                search_reader(haystack, &matcher, |b| {
                    build(b).heap_limit(Some(haystack.len() + 1))
                })
            } else {
                let lim = haystack.lines().map(|s| s.len()).max().unwrap_or(0);
                search_reader(haystack, &matcher, |b| {
                    // str::lines doesn't return the line terminator, so add 1.
                    build(b).heap_limit(Some(lim + 1))
                })
            };
        assert_eq!(expected, got, "\nsearch_reader with small limit mismatch");
    }

    fn search_reader<M, F>(
        haystack: &str,
        matcher: M,
        mut build: F,
    ) -> String
    where M: Matcher,
          M::Error: fmt::Display,
          F: FnMut(&mut SearcherBuilder) -> &mut SearcherBuilder
    {
        let mut sink = KitchenSink::new();
        let mut builder = SearcherBuilder::new();
        build(&mut builder);
        let mut searcher = builder.build(matcher).unwrap();
        searcher.search_reader(haystack.as_bytes(), &mut sink).unwrap();
        String::from_utf8(sink.as_bytes().to_vec()).unwrap()
    }

    fn search_slice<M, F>(
        haystack: &str,
        matcher: M,
        mut build: F,
    ) -> String
    where M: Matcher,
          M::Error: fmt::Display,
          F: FnMut(&mut SearcherBuilder) -> &mut SearcherBuilder
    {
        let mut sink = KitchenSink::new();
        let mut builder = SearcherBuilder::new();
        build(&mut builder);
        let mut searcher = builder.build(matcher).unwrap();
        searcher.search_slice(haystack.as_bytes(), &mut sink).unwrap();
        String::from_utf8(sink.as_bytes().to_vec()).unwrap()
    }

    #[test]
    fn basic1() {
        let exp = "\
0:For the Doctor Watsons of this world, as opposed to the Sherlock
129:be, to a very large extent, the result of luck. Sherlock Holmes

byte count:366
";
        search_assert_all(exp, SHERLOCK, "Sherlock", |b| b);
        search_assert_all(exp, SHERLOCK, "Sherlock", |b| b.multi_line(true));
    }

    #[test]
    fn basic2() {
        let exp = "\nbyte count:366\n";
        search_assert_all(exp, SHERLOCK, "NADA", |b| b);
        search_assert_all(exp, SHERLOCK, "NADA", |b| b.multi_line(true));
    }

    #[test]
    fn basic3() {
        let exp = "\
0:For the Doctor Watsons of this world, as opposed to the Sherlock
65:Holmeses, success in the province of detective work must always
129:be, to a very large extent, the result of luck. Sherlock Holmes
193:can extract a clew from a wisp of straw or a flake of cigar ash;
258:but Doctor Watson has to have it taken out for him and dusted,
321:and exhibited clearly, with a label attached.
byte count:366
";
        search_assert_all(exp, SHERLOCK, "a", |b| b);
        search_assert_all(exp, SHERLOCK, "a", |b| b.multi_line(true));
    }

    #[test]
    fn invert1() {
        let pattern = "Sherlock";
        let exp = "\
65:Holmeses, success in the province of detective work must always
193:can extract a clew from a wisp of straw or a flake of cigar ash;
258:but Doctor Watson has to have it taken out for him and dusted,
321:and exhibited clearly, with a label attached.
byte count:366
";

        search_assert_all(exp, SHERLOCK, pattern, |b| {
            b.invert_match(true)
        });
        search_assert_all(exp, SHERLOCK, pattern, |b| {
            b.invert_match(true).multi_line(true)
        });
    }

    #[test]
    fn line_number1() {
        let exp = "\
1:0:For the Doctor Watsons of this world, as opposed to the Sherlock
3:129:be, to a very large extent, the result of luck. Sherlock Holmes

byte count:366
";
        search_assert_all(exp, SHERLOCK, "Sherlock", |b| {
            b.line_number(true)
        });
        search_assert_all(exp, SHERLOCK, "Sherlock", |b| {
            b.line_number(true).multi_line(true)
        });
    }

    #[test]
    fn line_number_invert1() {
        let exp = "\
2:65:Holmeses, success in the province of detective work must always
4:193:can extract a clew from a wisp of straw or a flake of cigar ash;
5:258:but Doctor Watson has to have it taken out for him and dusted,
6:321:and exhibited clearly, with a label attached.
byte count:366
";
        search_assert_all(exp, SHERLOCK, "Sherlock", |b| {
            b.line_number(true).invert_match(true)
        });
        search_assert_all(exp, SHERLOCK, "Sherlock", |b| {
            b.line_number(true).multi_line(true).invert_match(true)
        });
    }

    #[test]
    fn multi_line_overlap1() {
        let haystack = "xxx\nabc\ndefxxxabc\ndefxxx\nxxx";
        let byte_count = haystack.len();
        let pattern = "abc\ndef";
        let exp = format!(
            "4:abc\n8:defxxxabc\n18:defxxx\n\nbyte count:{}\n",
            byte_count);

        search_assert_all(&exp, haystack, pattern, |b| b.multi_line(true));
    }

    #[test]
    fn multi_line_overlap2() {
        let haystack = "xxx\nabc\ndefabc\ndefxxx\nxxx";
        let byte_count = haystack.len();
        let pattern = "abc\ndef";
        let exp = format!(
            "4:abc\n8:defabc\n15:defxxx\n\nbyte count:{}\n",
            byte_count);

        search_assert_all(&exp, haystack, pattern, |b| b.multi_line(true));
    }

    #[test]
    fn empty_line1() {
        let haystack = "";
        let matcher = EmptyLineMatcher::new(b'\n');
        let exp = "\nbyte count:0\n";

        search_assert_all_matcher(exp, haystack, &matcher, |b| b);
        search_assert_all_matcher(exp, haystack, &matcher, |b| {
            b.line_number(true)
        });
        search_assert_all_matcher(exp, haystack, &matcher, |b| {
            b.multi_line(true)
        });
        search_assert_all_matcher(exp, haystack, &matcher, |b| {
            b.multi_line(true).line_number(true)
        });
    }

    #[test]
    fn empty_line2() {
        let haystack = "\n";
        let matcher = EmptyLineMatcher::new(b'\n');
        let exp = "0:\n\nbyte count:1\n";
        let exp_line = "1:0:\n\nbyte count:1\n";

        search_assert_all_matcher(exp, haystack, &matcher, |b| b);
        search_assert_all_matcher(exp_line, haystack, &matcher, |b| {
            b.line_number(true)
        });
        search_assert_all_matcher(exp, haystack, &matcher, |b| {
            b.multi_line(true)
        });
        search_assert_all_matcher(exp_line, haystack, &matcher, |b| {
            b.multi_line(true).line_number(true)
        });
    }

    #[test]
    fn empty_line3() {
        let haystack = "\n\n";
        let matcher = EmptyLineMatcher::new(b'\n');
        let exp = "0:\n1:\n\nbyte count:2\n";
        let exp_line = "1:0:\n2:1:\n\nbyte count:2\n";

        search_assert_all_matcher(exp, haystack, &matcher, |b| b);
        search_assert_all_matcher(exp_line, haystack, &matcher, |b| {
            b.line_number(true)
        });
        search_assert_all_matcher(exp, haystack, &matcher, |b| {
            b.multi_line(true)
        });
        search_assert_all_matcher(exp_line, haystack, &matcher, |b| {
            b.multi_line(true).line_number(true)
        });
    }

    #[test]
    fn empty_line4() {
        // See: https://github.com/BurntSushi/ripgrep/issues/441
        let haystack = "\
a
b

c


d
";
        let byte_count = haystack.len();
        let matcher = EmptyLineMatcher::new(b'\n');
        let exp = format!("4:\n7:\n8:\n\nbyte count:{}\n", byte_count);
        let exp_line = format!(
            "3:4:\n5:7:\n6:8:\n\nbyte count:{}\n",
            byte_count);

        search_assert_all_matcher(&exp, haystack, &matcher, |b| b);
        search_assert_all_matcher(&exp_line, haystack, &matcher, |b| {
            b.line_number(true)
        });
        search_assert_all_matcher(&exp, haystack, &matcher, |b| {
            b.multi_line(true)
        });
        search_assert_all_matcher(&exp_line, haystack, &matcher, |b| {
            b.multi_line(true).line_number(true)
        });
    }

    #[test]
    fn empty_line5() {
        // See: https://github.com/BurntSushi/ripgrep/issues/441
        // This is like empty_line4, but lacks the trailing line terminator.
        let haystack = "\
a
b

c


d";
        let byte_count = haystack.len();
        let matcher = EmptyLineMatcher::new(b'\n');
        let exp = format!("4:\n7:\n8:\n\nbyte count:{}\n", byte_count);
        let exp_line = format!(
            "3:4:\n5:7:\n6:8:\n\nbyte count:{}\n",
            byte_count);

        search_assert_all_matcher(&exp, haystack, &matcher, |b| b);
        search_assert_all_matcher(&exp_line, haystack, &matcher, |b| {
            b.line_number(true)
        });
        search_assert_all_matcher(&exp, haystack, &matcher, |b| {
            b.multi_line(true)
        });
        search_assert_all_matcher(&exp_line, haystack, &matcher, |b| {
            b.multi_line(true).line_number(true)
        });
    }

    #[test]
    fn empty_line6() {
        // See: https://github.com/BurntSushi/ripgrep/issues/441
        // This is like empty_line4, but includes an empty line at the end.
        let haystack = "\
a
b

c


d

";
        let byte_count = haystack.len();
        let matcher = EmptyLineMatcher::new(b'\n');
        let exp = format!(
            "4:\n7:\n8:\n11:\n\nbyte count:{}\n",
            byte_count);
        let exp_line = format!(
            "3:4:\n5:7:\n6:8:\n8:11:\n\nbyte count:{}\n",
            byte_count);

        search_assert_all_matcher(&exp, haystack, &matcher, |b| b);
        search_assert_all_matcher(&exp_line, haystack, &matcher, |b| {
            b.line_number(true)
        });
        search_assert_all_matcher(&exp, haystack, &matcher, |b| {
            b.multi_line(true)
        });
        search_assert_all_matcher(&exp_line, haystack, &matcher, |b| {
            b.multi_line(true).line_number(true)
        });
    }

    #[test]
    fn big1() {
        let mut haystack = String::new();
        haystack.push_str("a\n");
        // Pick an arbitrary number above the capacity.
        for _ in 0..(4 * (DEFAULT_BUFFER_CAPACITY + 7)) {
            haystack.push_str("zzz\n");
        }
        haystack.push_str("a\n");

        let byte_count = haystack.len();
        let exp = format!("0:a\n131186:a\n\nbyte count:{}\n", byte_count);
        let got = search_reader(&haystack, SubstringMatcher::new("a"), |b| {
            b.heap_limit(Some(4))
        });
        assert_eq!(exp, got, "\nsearch_reader mismatch");

        let exp = format!("0:a\n131186:a\n\nbyte count:{}\n", byte_count);
        let got = search_reader(&haystack, SubstringMatcher::new("a"), |b| {
            b.multi_line(true).heap_limit(Some(haystack.len() + 1))
        });
        assert_eq!(exp, got, "\nsearch_reader mismatch");
    }

    #[test]
    fn big_error_one_line() {
        let mut haystack = String::new();
        haystack.push_str("a\n");
        // Pick an arbitrary number above the capacity.
        for _ in 0..(4 * (DEFAULT_BUFFER_CAPACITY + 7)) {
            haystack.push_str("zzz\n");
        }
        haystack.push_str("a\n");

        let mut sink = KitchenSink::new();
        let mut searcher = SearcherBuilder::new()
            .heap_limit(Some(3)) // max line length is 4, one byte short
            .build(SubstringMatcher::new("a"))
            .unwrap();
        let result = searcher.search_reader(haystack.as_bytes(), &mut sink);
        assert!(result.is_err());
    }

    #[test]
    fn big_error_multi_line() {
        let mut haystack = String::new();
        haystack.push_str("a\n");
        // Pick an arbitrary number above the capacity.
        for _ in 0..(4 * (DEFAULT_BUFFER_CAPACITY + 7)) {
            haystack.push_str("zzz\n");
        }
        haystack.push_str("a\n");

        let mut sink = KitchenSink::new();
        let mut searcher = SearcherBuilder::new()
            .multi_line(true)
            .heap_limit(Some(haystack.len())) // actually need one more byte
            .build(SubstringMatcher::new("a"))
            .unwrap();
        let result = searcher.search_reader(haystack.as_bytes(), &mut sink);
        assert!(result.is_err());
    }

    #[test]
    fn binary1() {
        let haystack = "\x00a";
        let exp = "\nbyte count:0\nbinary offset:0\n";
        search_assert_all(exp, haystack, "a", |b| {
            b.binary_detection(BinaryDetection::quit(0))
        });
        search_assert_all(exp, haystack, "a", |b| {
            b.multi_line(true).binary_detection(BinaryDetection::quit(0))
        });
    }

    #[test]
    fn binary2() {
        let haystack = "a\x00";

        let exp = "\nbyte count:0\nbinary offset:1\n";
        search_assert_all(exp, haystack, "a", |b| {
            b.binary_detection(BinaryDetection::quit(0))
        });
        search_assert_all(exp, haystack, "a", |b| {
            b.multi_line(true).binary_detection(BinaryDetection::quit(0))
        });
    }

    #[test]
    fn binary3() {
        let mut haystack = String::new();
        haystack.push_str("a\n");
        for _ in 0..DEFAULT_BUFFER_CAPACITY {
            haystack.push_str("zzz\n");
        }
        haystack.push_str("a\n");
        haystack.push_str("a\x00a\n");
        haystack.push_str("a\n");

        // The line buffered searcher has slightly different semantics here.
        // Namely, it will *always* detect binary data in the current buffer
        // before searching it.
        let exp = "0:a\n\nbyte count:32766\nbinary offset:32773\n";
        let got = search_reader(&haystack, SubstringMatcher::new("a"), |b| {
            b.binary_detection(BinaryDetection::quit(0))
        });
        assert_eq!(exp, got, "\nsearch_reader mismatch");

        // In contrast, the slice readers (for multi line as well) will only
        // look for binary data in the initial chunk of bytes. After that
        // point, it only looks for binary data in matches. This is also why
        // the total byte count is slightly different.
        let exp = "0:a\n32770:a\n\nbyte count:32772\nbinary offset:32773\n";
        let got = search_slice(&haystack, SubstringMatcher::new("a"), |b| {
            b.binary_detection(BinaryDetection::quit(0))
        });
        assert_eq!(exp, got, "\nsearch_slice mismatch");

        let exp = "0:a\n32770:a\n\nbyte count:32773\nbinary offset:32773\n";
        search_assert_all(&exp, &haystack, "a", |b| {
            b.multi_line(true).binary_detection(BinaryDetection::quit(0))
        });
    }
}
