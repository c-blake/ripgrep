use std::cell::Cell;
use std::cmp;
use std::fmt;
use std::io;
use std::marker::PhantomData;

use memchr::memchr;

use lines::{self, LineStep};
use line_buffer::{
    self, LineBufferReader,
    DEFAULT_BUFFER_CAPACITY,
};
use matcher::{LineMatchKind, Match, Matcher};
use searcher_builder::{Config, Searcher};
use sink::{Sink, SinkFinish, SinkMatch};

#[derive(Debug)]
pub struct ReadByLine<'s, M: 's, R, S> {
    config: &'s Config,
    core: Core<'s, M, S>,
    sink: S,
    rdr: LineBufferReader<'s, R>,
}

impl<'s, M, R, S> ReadByLine<'s, M, R, S>
where M: Matcher,
      M::Error: fmt::Display,
      R: io::Read,
      S: Sink
{
    pub fn new(
        searcher: &'s Searcher<M>,
        read_from: LineBufferReader<'s, R>,
        write_to: S,
    ) -> ReadByLine<'s, M, R, S> {
        assert!(!searcher.config.multi_line);

        ReadByLine {
            config: &searcher.config,
            core: Core::new(searcher),
            sink: write_to,
            rdr: read_from,
        }
    }

    pub fn run(mut self) -> Result<(), S::Error> {
        assert!(!self.config.multi_line);

        while self.fill()? && self.sink()? {}
        self.sink.finish(&SinkFinish {
            byte_count: self.rdr.absolute_byte_offset(),
            binary_byte_offset: self.rdr.binary_byte_offset(),
        })
    }

    fn fill(&mut self) -> Result<bool, S::Error> {
        assert!(self.rdr.buffer()[self.core.pos()..].is_empty());

        self.core.roll(self.rdr.buffer());
        self.rdr.consume_all();
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
        let absolute_byte_offset = self.rdr.absolute_byte_offset();
        let buf = self.rdr.buffer();
        let sink = &mut self.sink;
        self.core.match_by_line(buf, |core, line| {
            let offset = absolute_byte_offset + line.start() as u64;
            sink.matched(
                &core.searcher,
                &SinkMatch {
                    line_term: core.config().line_term,
                    bytes: &buf[*line],
                    absolute_byte_offset: offset,
                    line_number: core.line_number(),
                },
            )
        })
    }
}

#[derive(Debug)]
pub struct SliceByLine<'s, M: 's, S> {
    config: &'s Config,
    core: Core<'s, M, S>,
    sink: S,
    slice: &'s [u8],
}

impl<'s, M, S> SliceByLine<'s, M, S>
where M: Matcher,
      M::Error: fmt::Display,
      S: Sink
{
    pub fn new(
        searcher: &'s Searcher<M>,
        slice: &'s [u8],
        write_to: S,
    ) -> SliceByLine<'s, M, S> {
        assert!(!searcher.config.multi_line);

        SliceByLine {
            config: &searcher.config,
            core: Core::new(searcher),
            sink: write_to,
            slice: slice,
        }
    }

    pub fn run(mut self) -> Result<(), S::Error> {
        assert!(!self.config.multi_line);

        let binary_upto = cmp::min(self.slice.len(), DEFAULT_BUFFER_CAPACITY);
        if !self.core.detect_binary(self.slice, &Match::new(0, binary_upto)) {
            while !self.slice[self.core.pos()..].is_empty() {
                if !self.sink()? {
                    break;
                }
            }
        }
        let byte_count = self.byte_count();
        self.sink.finish(&SinkFinish {
            byte_count: byte_count,
            binary_byte_offset: self.core.binary_byte_offset(),
        })
    }

    fn sink(&mut self) -> Result<bool, S::Error> {
        let buf = self.slice;
        let sink = &mut self.sink;
        self.core.match_by_line(buf, |core, line| {
            if core.detect_binary(buf, line) {
                return Ok(false);
            }
            sink.matched(
                &core.searcher,
                &SinkMatch {
                    line_term: core.config().line_term,
                    bytes: &buf[*line],
                    absolute_byte_offset: line.start() as u64,
                    line_number: core.line_number(),
                },
            )
        })
    }

    fn byte_count(&self) -> u64 {
        match self.core.binary_byte_offset() {
            Some(offset) if offset < self.core.pos() as u64 => offset,
            _ => self.core.pos() as u64,
        }
    }
}

#[derive(Debug)]
pub struct MultiLine<'s, M: 's, S> {
    config: &'s Config,
    core: Core<'s, M, S>,
    matcher: &'s M,
    sink: S,
    slice: &'s [u8],
    last_match: Option<LineMatch>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
struct LineMatch {
    line: Match,
    line_number: Option<u64>,
}

impl<'s, M, S> MultiLine<'s, M, S>
where M: Matcher,
      M::Error: fmt::Display,
      S: Sink
{
    pub fn new(
        searcher: &'s Searcher<M>,
        slice: &'s [u8],
        write_to: S,
    ) -> MultiLine<'s, M, S> {
        assert!(searcher.config.multi_line);

        MultiLine {
            config: &searcher.config,
            core: Core::new(searcher),
            matcher: &searcher.matcher,
            sink: write_to,
            slice: slice,
            last_match: None,
        }
    }

    pub fn run(mut self) -> Result<(), S::Error> {
        assert!(self.config.multi_line);

        let binary_upto = cmp::min(self.slice.len(), DEFAULT_BUFFER_CAPACITY);
        if !self.core.detect_binary(self.slice, &Match::new(0, binary_upto)) {
            while !self.slice[self.core.pos()..].is_empty() {
                if !self.sink()? {
                    break;
                }
            }
            if let Some(last_match) = self.last_match.take() {
                self.sink_matched(&last_match)?;
            }
        }
        let byte_count = self.byte_count();
        self.sink.finish(&SinkFinish {
            byte_count: byte_count,
            binary_byte_offset: self.core.binary_byte_offset(),
        })
    }

    fn sink(&mut self) -> Result<bool, S::Error> {
        if self.config.invert_match {
            return self.sink_matched_inverted();
        }
        let mat = match self.find()? {
            Some(range) => range,
            None => {
                self.core.set_pos(self.slice.len());
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
        self.core.count_lines(self.slice, line.start());
        self.last_match = Some(LineMatch {
            line: line,
            line_number: self.core.line_number(),
        });
        self.advance(&mat);
        Ok(keepgoing)
    }

    fn sink_matched_inverted(&mut self) -> Result<bool, S::Error> {
        assert!(self.config.invert_match);

        let invert_match = match self.find()? {
            None => {
                let m = Match::new(self.core.pos(), self.slice.len());
                self.core.set_pos(m.end());
                m
            }
            Some(mat) => {
                let line = lines::locate(
                    self.slice, self.config.line_term, mat);
                let m = Match::new(self.core.pos(), line.start());
                self.advance(&line);
                m
            }
        };
        let mut stepper = LineStep::new(self.config.line_term, invert_match);
        while let Some(line) = stepper.next(self.slice) {
            self.core.count_lines(self.slice, line.start());
            let m = LineMatch {
                line: line,
                line_number: self.core.line_number(),
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
            return Ok(true);
        }
        if self.core.detect_binary(self.slice, &m.line) {
            return Ok(false);
        }
        self.sink.matched(
            self.core.searcher,
            &SinkMatch {
                line_term: self.config.line_term,
                bytes: &self.slice[m.line],
                absolute_byte_offset: m.line.start() as u64,
                line_number: m.line_number,
            },
        )
    }

    fn find(&self) -> Result<Option<Match>, S::Error> {
        match self.matcher.find(&self.slice[self.core.pos()..]) {
            Err(err) => Err(S::error_message(err)),
            Ok(None) => Ok(None),
            Ok(Some(m)) => Ok(Some(m.offset(self.core.pos()))),
        }
    }

    /// Advance the search position based on the previous match.
    ///
    /// If the previous match is zero width, then this advances the search
    /// position one byte past the end of the match.
    fn advance(&self, m: &Match) {
        self.core.set_pos(m.end());
        if m.is_empty() && self.core.pos() < self.slice.len() {
            self.core.set_pos(self.core.pos() + 1);
        }
    }

    fn byte_count(&self) -> u64 {
        match self.core.binary_byte_offset() {
            Some(offset) if offset < self.core.pos() as u64 => offset,
            _ => self.core.pos() as u64,
        }
    }
}

#[derive(Debug)]
struct Core<'s, M: 's, S> {
    _sink_type: PhantomData<S>,
    config: &'s Config,
    matcher: &'s M,
    searcher: &'s Searcher<M>,
    pos: Cell<usize>,
    line_number: Option<Cell<u64>>,
    last_line_counted: Cell<usize>,
    binary_byte_offset: Cell<Option<usize>>,
}

impl<'s, M, S> Core<'s, M, S>
where M: Matcher,
      M::Error: fmt::Display,
      S: Sink
{
    fn new(searcher: &'s Searcher<M>) -> Core<'s, M, S> {
        let line_number =
            if searcher.config.line_number {
                Some(Cell::new(1))
            } else {
                None
            };
        Core {
            _sink_type: PhantomData,
            config: &searcher.config,
            matcher: &searcher.matcher,
            searcher: searcher,
            pos: Cell::new(0),
            line_number: line_number,
            last_line_counted: Cell::new(0),
            binary_byte_offset: Cell::new(None),
        }
    }

    fn roll(&self, buf: &[u8]) {
        self.count_remaining_lines(buf);
        self.pos.set(0);
        self.last_line_counted.set(0);
    }

    fn config(&self) -> &Config {
        &self.config
    }

    fn is_line_by_line_fast(&self) -> bool {
        assert!(!self.config.multi_line);

        match self.matcher.line_terminator() {
            None => false,
            Some(line_term) => line_term == self.config.line_term,
        }
    }

    fn pos(&self) -> usize {
        self.pos.get()
    }

    fn set_pos(&self, pos: usize) {
        self.pos.set(pos);
    }

    fn line_number(&self) -> Option<u64> {
        self.line_number.as_ref().map(|cell| cell.get())
    }

    fn count_remaining_lines(&self, buf: &[u8]) {
        self.count_lines(buf, buf.len());
    }

    fn count_lines(&self, buf: &[u8], upto: usize) {
        if let Some(ref line_number) = self.line_number {
            let slice = &buf[self.last_line_counted.get()..upto];
            let count = lines::count(slice, self.config.line_term);
            line_number.set(line_number.get() + count);
            self.last_line_counted.set(upto);
        }
    }

    fn add_one_line(&self, line_end: usize) {
        if let Some(ref line_number) = self.line_number {
            line_number.set(line_number.get() + 1);
            self.last_line_counted.set(line_end);
        }
    }

    fn binary_byte_offset(&self) -> Option<u64> {
        self.binary_byte_offset.get().map(|offset| offset as u64)
    }

    fn detect_binary(&self, buf: &[u8], range: &Match) -> bool {
        if self.binary_byte_offset.get().is_some() {
            return true;
        }
        let binary_byte = match self.config.binary.0 {
            line_buffer::BinaryDetection::Quit(b) => b,
            _ => return false,
        };
        if let Some(i) = memchr(binary_byte, &buf[*range]) {
            let offset = Some(range.start() + i);
            self.binary_byte_offset.set(offset);
            true
        } else {
            false
        }
    }

    fn match_by_line<F>(
        &self,
        buf: &[u8],
        on_match: F,
    ) -> Result<bool, S::Error>
    where F: FnMut(&Self, &Match) -> Result<bool, S::Error>
    {
        if self.is_line_by_line_fast() {
            self.match_by_line_fast(buf, on_match)
        } else {
            self.match_by_line_slow(buf, on_match)
        }
    }

    fn match_by_line_slow<F>(
        &self,
        buf: &[u8],
        mut on_match: F,
    ) -> Result<bool, S::Error>
    where F: FnMut(&Self, &Match) -> Result<bool, S::Error>
    {
        assert!(!self.config.multi_line);

        let range = Match::new(self.pos(), buf.len());
        let mut stepper = LineStep::new(self.config.line_term, range);
        while let Some(line) = stepper.next(buf) {
            let matched = {
                // Stripping the line terminator is necessary to prevent some
                // classes of regexes from matching the empty position *after*
                // the end of the line. For example, `(?m)^$` will match at
                // position (2, 2) in the string `a\n`.
                let slice = lines::without_terminator(
                    &buf[line],
                    self.config.line_term,
                );
                match self.matcher.shortest_match(slice) {
                    Err(err) => return Err(S::error_message(err)),
                    Ok(result) => result.is_some(),
                }
            };
            self.set_pos(line.end());
            if matched != self.config.invert_match {
                if !on_match(self, &line)? {
                    return Ok(false);
                }
            }
            self.add_one_line(line.end());
        }
        Ok(true)
    }

    fn match_by_line_fast<F>(
        &self,
        buf: &[u8],
        mut on_match: F,
    ) -> Result<bool, S::Error>
    where F: FnMut(&Self, &Match) -> Result<bool, S::Error> {
        while !buf[self.pos()..].is_empty() {
            if self.config.invert_match {
                if !self.match_by_line_fast_invert(buf, &mut on_match)? {
                    return Ok(false);
                }
            } else if let Some(line) = self.find_by_line_fast(buf)? {
                self.count_lines(buf, line.start());
                self.set_pos(line.end());
                if !on_match(self, &line)? {
                    return Ok(false);
                }
            } else {
                self.set_pos(buf.len());
            }
        }
        Ok(true)
    }

    fn match_by_line_fast_invert<F>(
        &self,
        buf: &[u8],
        mut on_match: F,
    ) -> Result<bool, S::Error>
    where F: FnMut(&Self, &Match) -> Result<bool, S::Error> {
        assert!(self.config.invert_match);

        let invert_match = match self.find_by_line_fast(buf)? {
            None => {
                let m = Match::new(self.pos(), buf.len());
                self.set_pos(m.end());
                m
            }
            Some(line) => {
                let m = Match::new(self.pos(), line.start());
                self.set_pos(line.end());
                m
            }
        };
        self.count_lines(buf, invert_match.start());
        let mut stepper = LineStep::new(self.config.line_term, invert_match);
        while let Some(line) = stepper.next(buf) {
            if !on_match(self, &line)? {
                return Ok(false);
            }
            self.add_one_line(line.end());
        }
        Ok(true)
    }

    fn find_by_line_fast(
        &self,
        buf: &[u8],
    ) -> Result<Option<Match>, S::Error> {
        assert!(!self.config.multi_line);
        assert_eq!(
            self.matcher.line_terminator().unwrap(),
            self.config.line_term,
            "requires a matcher's line terminator to match config",
        );

        let mut pos = self.pos.get();
        while !buf[pos..].is_empty() {
            match self.matcher.find_candidate_line(&buf[pos..]) {
                Err(err) => return Err(S::error_message(err)),
                Ok(None) => return Ok(None),
                Ok(Some(LineMatchKind::Confirmed(i))) => {
                    let line = lines::locate(
                        buf,
                        self.config.line_term,
                        Match::zero(i).offset(pos),
                    );
                    // If we matched beyond the end of the buffer, then we
                    // don't report this as a match.
                    if line.start() == buf.len() {
                        pos = buf.len();
                        continue;
                    }
                    return Ok(Some(line));
                }
                Ok(Some(LineMatchKind::Candidate(i))) => {
                    let line = lines::locate(
                        buf,
                        self.config.line_term,
                        Match::zero(i).offset(pos),
                    );
                    // We need to strip the line terminator here to match the
                    // semantics of line-by-line searching. Namely, regexes
                    // like `(?m)^$` can match at the final position beyond a
                    // line terminator, which is non-sensical in line oriented
                    // matching.
                    let slice = lines::without_terminator(
                        &buf[line],
                        self.config.line_term,
                    );
                    match self.matcher.is_match(slice) {
                        Err(err) => return Err(S::error_message(err)),
                        Ok(true) => return Ok(Some(line)),
                        Ok(false) => {
                            pos = line.end();
                            continue;
                        }
                    }
                }
            }
        }
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use searcher_builder::*;
    use testutil::{KitchenSink, RegexMatcher, SearcherTester};

    use super::*;

    const SHERLOCK: &'static str = "\
For the Doctor Watsons of this world, as opposed to the Sherlock
Holmeses, success in the province of detective work must always
be, to a very large extent, the result of luck. Sherlock Holmes
can extract a clew from a wisp of straw or a flake of cigar ash;
but Doctor Watson has to have it taken out for him and dusted,
and exhibited clearly, with a label attached.\
";

    #[test]
    fn basic1() {
        let exp = "\
0:For the Doctor Watsons of this world, as opposed to the Sherlock
129:be, to a very large extent, the result of luck. Sherlock Holmes

byte count:366
";
        SearcherTester::new(SHERLOCK, "Sherlock")
            .line_number(false)
            .expected_no_line_number(exp)
            .test();
    }

    #[test]
    fn basic2() {
        let exp = "\nbyte count:366\n";
        SearcherTester::new(SHERLOCK, "NADA")
            .line_number(false)
            .expected_no_line_number(exp)
            .test();
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
        SearcherTester::new(SHERLOCK, "a")
            .line_number(false)
            .expected_no_line_number(exp)
            .test();
    }

    #[test]
    fn basic4() {
        let haystack = "\
a
b

c


d
";
        let byte_count = haystack.len();
        let exp = format!("0:a\n\nbyte count:{}\n", byte_count);
        SearcherTester::new(haystack, "a")
            .line_number(false)
            .expected_no_line_number(&exp)
            .test();
    }

    #[test]
    fn invert1() {
        let exp = "\
65:Holmeses, success in the province of detective work must always
193:can extract a clew from a wisp of straw or a flake of cigar ash;
258:but Doctor Watson has to have it taken out for him and dusted,
321:and exhibited clearly, with a label attached.
byte count:366
";
        SearcherTester::new(SHERLOCK, "Sherlock")
            .line_number(false)
            .invert_match(true)
            .expected_no_line_number(exp)
            .test();
    }

    #[test]
    fn line_number1() {
        let exp = "\
0:For the Doctor Watsons of this world, as opposed to the Sherlock
129:be, to a very large extent, the result of luck. Sherlock Holmes

byte count:366
";
        let exp_line = "\
1:0:For the Doctor Watsons of this world, as opposed to the Sherlock
3:129:be, to a very large extent, the result of luck. Sherlock Holmes

byte count:366
";
        SearcherTester::new(SHERLOCK, "Sherlock")
            .expected_no_line_number(exp)
            .expected_with_line_number(exp_line)
            .test();
    }

    #[test]
    fn line_number_invert1() {
        let exp = "\
65:Holmeses, success in the province of detective work must always
193:can extract a clew from a wisp of straw or a flake of cigar ash;
258:but Doctor Watson has to have it taken out for him and dusted,
321:and exhibited clearly, with a label attached.
byte count:366
";
        let exp_line = "\
2:65:Holmeses, success in the province of detective work must always
4:193:can extract a clew from a wisp of straw or a flake of cigar ash;
5:258:but Doctor Watson has to have it taken out for him and dusted,
6:321:and exhibited clearly, with a label attached.
byte count:366
";
        SearcherTester::new(SHERLOCK, "Sherlock")
            .invert_match(true)
            .expected_no_line_number(exp)
            .expected_with_line_number(exp_line)
            .test();
    }

    #[test]
    fn multi_line_overlap1() {
        let haystack = "xxx\nabc\ndefxxxabc\ndefxxx\nxxx";
        let byte_count = haystack.len();
        let exp = format!(
            "4:abc\n8:defxxxabc\n18:defxxx\n\nbyte count:{}\n",
            byte_count);

        SearcherTester::new(haystack, "abc\ndef")
            .by_line(false)
            .line_number(false)
            .expected_no_line_number(&exp)
            .test();
    }

    #[test]
    fn multi_line_overlap2() {
        let haystack = "xxx\nabc\ndefabc\ndefxxx\nxxx";
        let byte_count = haystack.len();
        let exp = format!(
            "4:abc\n8:defabc\n15:defxxx\n\nbyte count:{}\n",
            byte_count);

        SearcherTester::new(haystack, "abc\ndef")
            .by_line(false)
            .line_number(false)
            .expected_no_line_number(&exp)
            .test();
    }

    #[test]
    fn empty_line1() {
        let exp = "\nbyte count:0\n";
        SearcherTester::new("", r"^$")
            .expected_no_line_number(exp)
            .expected_with_line_number(exp)
            .test();
    }

    #[test]
    fn empty_line2() {
        let exp = "0:\n\nbyte count:1\n";
        let exp_line = "1:0:\n\nbyte count:1\n";

        SearcherTester::new("\n", r"^$")
            .expected_no_line_number(exp)
            .expected_with_line_number(exp_line)
            .test();
    }

    #[test]
    fn empty_line3() {
        let exp = "0:\n1:\n\nbyte count:2\n";
        let exp_line = "1:0:\n2:1:\n\nbyte count:2\n";

        SearcherTester::new("\n\n", r"^$")
            .expected_no_line_number(exp)
            .expected_with_line_number(exp_line)
            .test();
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
        let exp = format!("4:\n7:\n8:\n\nbyte count:{}\n", byte_count);
        let exp_line = format!(
            "3:4:\n5:7:\n6:8:\n\nbyte count:{}\n",
            byte_count);

        SearcherTester::new(haystack, r"^$")
            .expected_no_line_number(&exp)
            .expected_with_line_number(&exp_line)
            .test();
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
        let exp = format!("4:\n7:\n8:\n\nbyte count:{}\n", byte_count);
        let exp_line = format!(
            "3:4:\n5:7:\n6:8:\n\nbyte count:{}\n",
            byte_count);

        SearcherTester::new(haystack, r"^$")
            .expected_no_line_number(&exp)
            .expected_with_line_number(&exp_line)
            .test();
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
        let exp = format!(
            "4:\n7:\n8:\n11:\n\nbyte count:{}\n",
            byte_count);
        let exp_line = format!(
            "3:4:\n5:7:\n6:8:\n8:11:\n\nbyte count:{}\n",
            byte_count);

        SearcherTester::new(haystack, r"^$")
            .expected_no_line_number(&exp)
            .expected_with_line_number(&exp_line)
            .test();
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

        SearcherTester::new(&haystack, "a")
            .line_number(false)
            .expected_no_line_number(&exp)
            .test();
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
            .build(RegexMatcher::new("a"))
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
            .build(RegexMatcher::new("a"))
            .unwrap();
        let result = searcher.search_reader(haystack.as_bytes(), &mut sink);
        assert!(result.is_err());
    }

    #[test]
    fn binary1() {
        let haystack = "\x00a";
        let exp = "\nbyte count:0\nbinary offset:0\n";

        SearcherTester::new(haystack, "a")
            .binary_detection(BinaryDetection::quit(0))
            .line_number(false)
            .expected_no_line_number(exp)
            .test();
    }

    #[test]
    fn binary2() {
        let haystack = "a\x00";
        let exp = "\nbyte count:0\nbinary offset:1\n";

        SearcherTester::new(haystack, "a")
            .binary_detection(BinaryDetection::quit(0))
            .line_number(false)
            .expected_no_line_number(exp)
            .test();
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
        // before searching it. Thus, the total number of bytes searched is
        // smaller than below.
        let exp = "0:a\n\nbyte count:32766\nbinary offset:32773\n";
        // In contrast, the slice readers (for multi line as well) will only
        // look for binary data in the initial chunk of bytes. After that
        // point, it only looks for binary data in matches. Note though that
        // the binary offset remains the same. (See the binary4 test for a case
        // where the offset is explicitly different.)
        let exp_slice =
            "0:a\n32770:a\n\nbyte count:32773\nbinary offset:32773\n";

        SearcherTester::new(&haystack, "a")
            .binary_detection(BinaryDetection::quit(0))
            .line_number(false)
            .auto_heap_limit(false)
            .expected_no_line_number(exp)
            .expected_slice_no_line_number(exp_slice)
            .test();
    }

    #[test]
    fn binary4() {
        let mut haystack = String::new();
        haystack.push_str("a\n");
        for _ in 0..DEFAULT_BUFFER_CAPACITY {
            haystack.push_str("zzz\n");
        }
        haystack.push_str("a\n");
        // The Read searcher will detect binary data here, but since this is
        // beyond the initial buffer size and doesn't otherwise contain a
        // match, the Slice reader won't detect the binary data until the next
        // line (which is a match).
        haystack.push_str("b\x00b\n");
        haystack.push_str("a\x00a\n");
        haystack.push_str("a\n");

        let exp = "0:a\n\nbyte count:32766\nbinary offset:32773\n";
        // The binary offset for the Slice readers corresponds to the binary
        // data in `a\x00a\n` since the first line with binary data
        // (`b\x00b\n`) isn't part of a match, and is therefore undetected.
        let exp_slice =
            "0:a\n32770:a\n\nbyte count:32777\nbinary offset:32777\n";

        SearcherTester::new(&haystack, "a")
            .binary_detection(BinaryDetection::quit(0))
            .line_number(false)
            .auto_heap_limit(false)
            .expected_no_line_number(exp)
            .expected_slice_no_line_number(exp_slice)
            .test();
    }
}
