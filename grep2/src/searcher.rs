use std::cell::RefCell;
use std::fmt;
use std::io;
use std::ops::Range;

use lines::{self, LineStep};
use line_buffer::{
    self, BufferAllocation, LineBuffer, LineBufferBuilder, LineBufferReader,
    DEFAULT_BUFFER_CAPACITY,
};
use matcher::Matcher;
use sink::{Sink, SinkMatch};

/// The behavior of binary detection while searching.
///
/// Binary detection is the process of _heuristically_ identifying whether a
/// given chunk of data is binary or not, and then taking an action based on
/// the result of that heuristic. The motivation behind detecting binary data
/// is that binary data often indicates data that is undesirable to search
/// using textual patterns. Of course, there are many cases in which this isn't
/// true, which is why binary detection is disabled by default.
///
/// Unfortunately, binary detection works differently depending on the type of
/// search being executed:
///
/// 1. When performing a search using a fixed size buffer, binary detection is
///    applied to the buffer's contents as it is filled. Binary detection must
///    be applied to the buffer directly because binary files may not contain
///    line terminators, which could result in exorbitant memory usage.
/// 2. When performing a search using memory maps or by reading data off the
///    heap, then binary detection is only guaranteed to be applied to the
///    parts corresponding to a match. When `Quit` is enabled, then the first
///    few KB of the data are searched for binary data.
#[derive(Clone, Debug, Default)]
pub struct BinaryDetection(line_buffer::BinaryDetection);

impl BinaryDetection {
    /// No binary detection is performed. Data reported by the line buffer may
    /// contain arbitrary bytes.
    ///
    /// This is the default.
    pub fn none() -> BinaryDetection {
        BinaryDetection(line_buffer::BinaryDetection::None)
    }

    /// The given byte is searched in all contents read by the line buffer. If
    /// it occurs, then the data is considered binary and the line buffer acts
    /// as if it reached EOF. The line buffer guarantees that this byte will
    /// never be observable by callers.
    pub fn quit(binary_byte: u8) -> BinaryDetection {
        BinaryDetection(line_buffer::BinaryDetection::Quit(binary_byte))
    }

    /// The given byte is searched in all contents read by the line buffer. If
    /// it occurs, then it is replaced by the line terminator. The line buffer
    /// guarantees that this byte will never be observable by callers.
    fn convert(binary_byte: u8) -> BinaryDetection {
        BinaryDetection(line_buffer::BinaryDetection::Convert(binary_byte))
    }
}

/// Controls the strategy used for determining when to use memory maps.
///
/// If a searcher is called in circumstances where it is possible to use memory
/// maps, then it will attempt to do so if it believes it will be advantageous.
#[derive(Clone, Debug)]
pub struct MmapChoice(MmapChoiceImpl);

#[derive(Clone, Debug)]
enum MmapChoiceImpl {
    Auto,
    Never,
}

impl Default for MmapChoice {
    fn default() -> MmapChoice {
        MmapChoice(MmapChoiceImpl::Auto)
    }
}

impl MmapChoice {
    /// Use memory maps when they are believed to be advantageous.
    ///
    /// The heuristics used to determine whether to use a memory map or not
    /// may depend on many things, including but not limited to, file size
    /// and operating system.
    ///
    /// If memory maps are unavailable or cannot be used for a specific input,
    /// then normal OS read calls are used instead.
    pub fn auto() -> MmapChoice {
        MmapChoice(MmapChoiceImpl::Auto)
    }

    /// Never use memory maps, no matter what.
    pub fn never() -> MmapChoice {
        MmapChoice(MmapChoiceImpl::Never)
    }

    /// Whether this strategy may employ memory maps or not.
    fn is_enabled(&self) -> bool {
        match self.0 {
            MmapChoiceImpl::Auto => true,
            MmapChoiceImpl::Never => false,
        }
    }
}

/// The internal configuration of a searcher. This is shared among several
/// search related types, but is only ever written to by the SearcherBuilder.
#[derive(Clone, Debug)]
struct Config {
    /// The line terminator to use.
    line_term: u8,
    /// Whether to invert matching.
    invert_match: bool,
    /// Whether to quit searching after a match is found.
    stop_after_first_match: bool,
    /// The number of lines after a match to include.
    after_context: usize,
    /// The number of lines before a match to include.
    before_context: usize,
    /// Whether to count line numbers.
    line_number: bool,
    /// The maximum amount of heap memory to use.
    ///
    /// When not given, no explicit limit is enforced. When set to `0`, then
    /// only the memory map search strategy is available.
    heap_limit: Option<usize>,
    /// The memory map strategy.
    mmap: MmapChoice,
    /// The binary data detection strategy.
    binary: BinaryDetection,
    /// Whether to enable matching across multiple lines.
    multi_line: bool,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            line_term: b'\n',
            invert_match: false,
            stop_after_first_match: false,
            after_context: 0,
            before_context: 0,
            line_number: false,
            heap_limit: None,
            mmap: MmapChoice::default(),
            binary: BinaryDetection::default(),
            multi_line: false,
        }
    }
}

impl Config {
    /// Build a line buffer from this configuration.
    fn line_buffer(&self) -> LineBuffer {
        let mut builder = LineBufferBuilder::new();
        builder
            .line_terminator(self.line_term)
            .binary_detection(self.binary.0);

        if let Some(limit) = self.heap_limit {
            let (capacity, additional) =
                if limit <= DEFAULT_BUFFER_CAPACITY {
                    (limit, 0)
                } else {
                    (DEFAULT_BUFFER_CAPACITY, limit - DEFAULT_BUFFER_CAPACITY)
                };
            builder
                .capacity(capacity)
                .buffer_alloc(BufferAllocation::Error(additional));
        }
        builder.build()
    }
}

/// An error that can occur when building a searcher.
///
/// This error occurs when a non-sensical configuration is present when trying
/// to construct a `Searcher` from a `SearcherBuilder`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConfigError {
    /// Indicates that the heap limit configuration prevents all possible
    /// search strategies from being used. For example, if the heap limit is
    /// set to 0 and memory map searching is disabled or unavailable.
    SearchUnavailable,
    /// Occurs when a matcher reports a line terminator that is different than
    /// the one configured in the searcher.
    MismatchedLineTerminators {
        /// The matcher's line terminator.
        matcher: u8,
        /// The searcher's line terminator.
        searcher: u8,
    },
    /// Hints that destructuring should not be exhaustive.
    ///
    /// This enum may grow additional variants, so this makes sure clients
    /// don't count on exhaustive matching. (Otherwise, adding a new variant
    /// could break existing code.)
    #[doc(hidden)]
    __Nonexhaustive,
}

impl ::std::error::Error for ConfigError {}

impl fmt::Display for ConfigError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ConfigError::SearchUnavailable => {
                write!(f, "grep config error: no available searchers")
            }
            ConfigError::MismatchedLineTerminators { matcher, searcher } => {
                write!(
                    f,
                    "grep config error: mismatched line terminators, \
                     matcher has 0x{:02X} but searcher has 0x{:02X}",
                    matcher,
                    searcher
                )
            }
            _ => panic!("BUG: unexpected variant found"),
        }
    }
}

#[derive(Debug)]
pub struct SearcherBuilder {
    config: Config,
}

impl Default for SearcherBuilder {
    fn default() -> SearcherBuilder {
        SearcherBuilder::new()
    }
}

impl SearcherBuilder {
    pub fn new() -> SearcherBuilder {
        SearcherBuilder {
            config: Config::default(),
        }
    }

    pub fn build<M>(&self, matcher: M) -> Result<Searcher<M>, ConfigError>
    where M: Matcher,
          M::Error: fmt::Display
    {
        if self.config.heap_limit == Some(0)
            && !self.config.mmap.is_enabled()
        {
            return Err(ConfigError::SearchUnavailable);
        } else if let Some(matcher_line_term) = matcher.line_terminator() {
            if matcher_line_term != self.config.line_term {
                return Err(ConfigError::MismatchedLineTerminators {
                    matcher: matcher_line_term,
                    searcher: self.config.line_term,
                });
            }
        }
        Ok(Searcher {
            config: self.config.clone(),
            matcher: matcher,
            line_buffer: RefCell::new(self.config.line_buffer()),
        })
    }

    pub fn line_terminator(&mut self, line_term: u8) -> &mut SearcherBuilder {
        self.config.line_term = line_term;
        self
    }

    pub fn invert_match(&mut self, yes: bool) -> &mut SearcherBuilder {
        self.config.invert_match = yes;
        self
    }

    pub fn stop_after_first_match(
        &mut self,
        yes: bool,
    ) -> &mut SearcherBuilder {
        self.config.stop_after_first_match = yes;
        self
    }

    pub fn after_context(
        &mut self,
        line_count: usize,
    ) -> &mut SearcherBuilder {
        self.config.after_context = line_count;
        self
    }

    pub fn before_context(
        &mut self,
        line_count: usize,
    ) -> &mut SearcherBuilder {
        self.config.before_context = line_count;
        self
    }

    pub fn line_number(&mut self, yes: bool) -> &mut SearcherBuilder {
        self.config.line_number = yes;
        self
    }

    pub fn heap_limit(
        &mut self,
        bytes: Option<usize>,
    ) -> &mut SearcherBuilder {
        self.config.heap_limit = bytes;
        self
    }

    pub fn memory_map(
        &mut self,
        strategy: MmapChoice,
    ) -> &mut SearcherBuilder {
        self.config.mmap = strategy;
        self
    }

    pub fn binary_detection(
        &mut self,
        detection: BinaryDetection,
    ) -> &mut SearcherBuilder {
        self.config.binary = detection;
        self
    }

    pub fn multi_line(&mut self, yes: bool) -> &mut SearcherBuilder {
        self.config.multi_line = yes;
        self
    }
}

#[derive(Debug)]
pub struct Searcher<M> {
    config: Config,
    matcher: M,
    /// A line buffer for use in line oriented searching.
    ///
    /// We wrap it in a RefCell to permit lending out borrows of `Searcher`
    /// to sinks. We still require a mutable borrow to execute a search, so
    /// we statically prevent callers from causing RefCell to panic at runtime
    /// due to a borrowing violation.
    line_buffer: RefCell<LineBuffer>,
}

impl<M> Searcher<M>
where M: Matcher,
      M::Error: fmt::Display
{
    pub fn search_reader<R: io::Read, S: Sink>(
        &mut self,
        mut read_from: R,
        write_to: S,
    ) -> Result<(), S::Error> {
        if self.config.multi_line {
            let mut bytes = vec![];
            if let Err(err) = read_from.read_to_end(&mut bytes) {
                return Err(S::error_io(err));
            }
            return self.search_slice(&bytes, write_to);
        }
        let mut line_buffer = self.line_buffer.borrow_mut();
        let rdr = LineBufferReader::new(read_from, &mut *line_buffer);
        self.search(rdr, write_to)
    }

    pub fn search_slice<S: Sink>(
        &mut self,
        slice: &[u8],
        write_to: S,
    ) -> Result<(), S::Error> {
        if self.config.multi_line {
            SearcherMultiLine {
                searcher: self,
                config: &self.config,
                matcher: &self.matcher,
                sink: write_to,
                slice: slice,
                search_pos: 0,
                last_match: None,
                line_number:
                    if self.config.line_number { Some(1) } else { None },
                last_line_counted: 0,
            }.run()
        } else {
            self.search(SliceReader::new(slice), write_to)
        }
    }

    fn search<R: Reader, S: Sink>(
        &self,
        read_from: R,
        write_to: S,
    ) -> Result<(), S::Error> {
        SearcherByLine {
            searcher: self,
            config: &self.config,
            matcher: &self.matcher,
            sink: write_to,
            rdr: read_from,
            search_pos: 0,
            line_number: if self.config.line_number { Some(1) } else { None },
            last_line_counted: 0,
        }.run()
    }
}

/// A trait to abstract over different sources of bytes to search.
///
/// This trait is used by the Searcher to construct a source to search over.
/// Principally, it copies the API of a LineBufferReader. The actual search
/// routines then use this Reader as if it were a LineBufferReader.
///
/// The trick is that we also implement this trait with a SliceReader, that
/// behaves like a LineBufferReader that reads the entire contents of its
/// source into memory in the first read.
trait Reader {
    fn absolute_byte_offset(&self) -> u64;
    fn binary_byte_offset(&self) -> Option<u64>;
    fn fill(&mut self) -> Result<bool, io::Error>;
    fn buffer(&self) -> &[u8];
    fn consume(&mut self, amt: usize);
    fn consume_all(&mut self);
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
}

/// SliceReader is a way of making a slice behave as a LineBuffer. Initially,
/// it starts empty, like a LineBuffer. The first call to `fill` causes the
/// entire slice to be available. Subsequent calls to `fill` return `true`
/// until the entire buffer is consumed.
struct SliceReader<'b> {
    slice: &'b [u8],
    filled: bool,
}

impl<'b> SliceReader<'b> {
    fn new(slice: &'b [u8]) -> SliceReader<'b> {
        SliceReader { slice, filled: false }
    }
}

impl<'b> Reader for SliceReader<'b> {
    fn absolute_byte_offset(&self) -> u64 {
        0
    }

    fn binary_byte_offset(&self) -> Option<u64> {
        None
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
    }

    fn consume_all(&mut self) {
        let amt = self.slice.len();
        self.consume(amt);
    }
}

#[derive(Debug)]
struct SearcherByLine<'s, M: 's, R, S> {
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
    fn run(mut self) -> Result<(), S::Error> {
        assert!(!self.config.multi_line);
    'LOOP:
        loop {
            if !self.fill()? {
                break;
            }
            while !self.search_buffer().is_empty() {
                if !self.sink()? {
                    break 'LOOP;
                }
            }
        }
        Ok(())
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
        if !didread {
            return Ok(false);
        }
        Ok(true)
    }

    fn sink(&mut self) -> Result<bool, S::Error> {
        if self.config.invert_match {
            self.sink_inverted_matches()
        } else if let Some((line_start, line_end)) = self.find()? {
            self.count_lines(line_start);
            let keepgoing = self.sink_matched(line_start, line_end)?;
            self.search_pos = line_end;
            Ok(keepgoing)
        } else {
            self.search_pos = self.buffer().len();
            Ok(true)
        }
    }

    fn sink_inverted_matches(&mut self) -> Result<bool, S::Error> {
        assert!(self.config.invert_match);

        let (invert_start, invert_end) = match self.find()? {
            None => {
                let start = self.search_pos;
                self.search_pos = self.buffer().len();
                (start, self.buffer().len())
            }
            Some((mat_start, mat_end)) => {
                let start = self.search_pos;
                self.search_pos = mat_end;
                (start, mat_start)
            }
        };
        self.count_lines(invert_start);
        let mut stepper = LineStep::new(
            self.config.line_term, invert_start, invert_end);
        while let Some((s, e)) = stepper.next(self.buffer()) {
            if !self.sink_matched(s, e)? {
                return Ok(false);
            }
            self.add_one_line(e);
        }
        Ok(true)
    }

    fn sink_matched(
        &mut self,
        line_start: usize,
        line_end: usize,
    ) -> Result<bool, S::Error> {
        if line_start == line_end {
            // The only way we can produce an empty line for a match is if
            // we match the position immediately following the last byte that
            // we search, and where that last byte is also the line terminator.
            // We never want to report a match, and we know we're done at that
            // point anyway.
            return Ok(false);
        }
        let offset = self.rdr.absolute_byte_offset() + line_start as u64;
        self.sink.matched(
            self.searcher,
            &SinkMatch {
                line_term: self.config.line_term,
                bytes: &self.rdr.buffer()[line_start..line_end],
                absolute_byte_offset: offset,
                line_number: self.line_number,
            },
        )
    }

    fn find(&mut self) -> Result<Option<(usize, usize)>, S::Error> {
        match self.matcher.find(self.search_buffer()) {
            Err(err) => return Err(S::error_message(err)),
            Ok(None) => return Ok(None),
            Ok(Some((start, end))) => {
                let (line_start, line_end) = lines::locate(
                    self.buffer(),
                    self.config.line_term,
                    self.search_pos + start,
                    self.search_pos + end,
                );
                Ok(Some((line_start, line_end)))
            }
        }
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
}

#[derive(Debug)]
struct SearcherMultiLine<'s, M: 's, S> {
    searcher: &'s Searcher<M>,
    config: &'s Config,
    matcher: &'s M,
    sink: S,
    slice: &'s [u8],
    search_pos: usize,
    last_match: Option<MultiLineMatch>,
    line_number: Option<u64>,
    last_line_counted: usize,
}

impl<'s, M, S> SearcherMultiLine<'s, M, S>
where M: Matcher,
      M::Error: fmt::Display,
      S: Sink
{
    fn run(mut self) -> Result<(), S::Error> {
        assert!(self.config.multi_line);
        while !self.search_buffer().is_empty() {
            if !self.sink()? {
                break;
            }
        }
        if let Some(last_match) = self.last_match.take() {
            self.sink_matched(&last_match)?;
        }
        Ok(())
    }

    fn search_buffer(&self) -> &[u8] {
        &self.slice[self.search_pos..]
    }

    fn sink(&mut self) -> Result<bool, S::Error> {
        if self.config.invert_match {
            return self.sink_inverted_matches();
        }
        let (mat_start, mat_end) = match self.find()? {
            Some(range) => range,
            None => {
                self.search_pos = self.slice.len();
                return Ok(true);
            }
        };
        let (line_start, line_end) = lines::locate(
            self.slice,
            self.config.line_term,
            mat_start,
            mat_end,
        );
        let keepgoing = match self.last_match.take() {
            None => true,
            Some(last_match) => {
                // If the lines in the previous match overlap with the lines
                // in this match, then simply grow the match and move on.
                // This happens when the next match begins on the same line
                // that the last match ends on.
                if last_match.line.end >= line_start {
                    self.last_match = Some(MultiLineMatch {
                        line: last_match.line.start..line_end,
                        line_number: last_match.line_number,
                    });
                    self.advance(mat_start, mat_end);
                    return Ok(true);
                } else {
                    self.sink_matched(&last_match)?
                }
            }
        };
        self.count_lines(line_start);
        self.last_match = Some(MultiLineMatch {
            line: line_start..line_end,
            line_number: self.line_number,
        });
        self.advance(mat_start, mat_end);
        Ok(keepgoing)
    }

    fn sink_inverted_matches(&mut self) -> Result<bool, S::Error> {
        assert!(self.config.invert_match);

        let (invert_start, invert_end) = match self.find()? {
            None => {
                let start = self.search_pos;
                self.search_pos = self.slice.len();
                (start, self.slice.len())
            }
            Some((mat_start, mat_end)) => {
                let (line_start, line_end) = lines::locate(
                    self.slice,
                    self.config.line_term,
                    mat_start,
                    mat_end,
                );
                let start = self.search_pos;
                self.search_pos = line_end;
                (start, line_start)
            }
        };
        let mut stepper = LineStep::new(
            self.config.line_term, invert_start, invert_end);
        while let Some((s, e)) = stepper.next(self.slice) {
            self.count_lines(s);
            let m = MultiLineMatch {
                line: s..e,
                line_number: self.line_number,
            };
            if !self.sink_matched(&m)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn sink_matched(&mut self, m: &MultiLineMatch) -> Result<bool, S::Error> {
        if m.is_empty() {
            // The only way we can produce an empty line for a match is if
            // we match the position immediately following the last byte that
            // we search, and where that last byte is also the line terminator.
            // We never want to report a match, and we know we're done at that
            // point anyway.
            return Ok(false);
        }
        self.sink.matched(
            self.searcher,
            &SinkMatch {
                line_term: self.config.line_term,
                bytes: &self.slice[m.line.clone()],
                absolute_byte_offset: m.line.start as u64,
                line_number: m.line_number,
            },
        )
    }

    fn find(&mut self) -> Result<Option<(usize, usize)>, S::Error> {
        match self.matcher.find(self.search_buffer()) {
            Err(err) => return Err(S::error_message(err)),
            Ok(None) => return Ok(None),
            Ok(Some((start, end))) => {
                Ok(Some((self.search_pos + start, self.search_pos + end)))
            }
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
    fn advance(&mut self, mat_start: usize, mat_end: usize) {
        self.search_pos = mat_end;
        if mat_start == mat_end && self.search_pos < self.slice.len() {
            self.search_pos += 1;
        }
    }
}

#[derive(Clone, Debug)]
struct MultiLineMatch {
    line: Range<usize>,
    line_number: Option<u64>,
}

impl MultiLineMatch {
    /// Returns the length of this match, in bytes.
    fn len(&self) -> usize {
        self.line.end.checked_sub(self.line.start).unwrap()
    }

    /// Returns true if and only if this match is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

// BREADCRUMBS:
//
// Where to go next? Some thoughts:
//
//   1a. Switch to using ops::Range instead of (usize, usize).
//   1b. Do context handling last. (Famous last words.)
//   2. Binary detectiong for SliceReader. Maybe punt on Convert.
//   3. Fill out the single-line searcher. Use optimizations. Line-by-line too.
//   4. Fill out the logic for opening a reader in Searcher.
//   5. Stop after first match.
//
// Massive cleanup. Get things working and then search for simplications.
// Index heavy code is gross. Context handling will make it much worse.

#[cfg(test)]
mod tests {
    use std::fmt;

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
        build: F,
    )
    where F: FnMut(&mut SearcherBuilder) -> &mut SearcherBuilder
    {
        let matcher = SubstringMatcher::new(pattern);
        search_assert_all_matcher(expected, haystack, matcher, build)
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
        assert_eq!(expected, got, "search_reader mismatch");

        let got = search_slice(haystack, &matcher, &mut build);
        assert_eq!(expected, got, "search_slice mismatch");

        let got = search_reader(haystack, &matcher, |b| {
            build(b).heap_limit(Some(80))
        });
        assert_eq!(expected, got, "search_reader with small limit mismatch");
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
";
        search_assert_all(exp, SHERLOCK, "Sherlock", |b| b);
        search_assert_all(exp, SHERLOCK, "Sherlock", |b| b.multi_line(true));
    }

    #[test]
    fn basic2() {
        let exp = "";
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
321:and exhibited clearly, with a label attached.\
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
321:and exhibited clearly, with a label attached.\
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
6:321:and exhibited clearly, with a label attached.\
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
        let pattern = "abc\ndef";
        let exp = "4:abc\n8:defxxxabc\n18:defxxx\n";

        search_assert_all(exp, haystack, pattern, |b| b.multi_line(true));
    }

    #[test]
    fn multi_line_overlap2() {
        let haystack = "xxx\nabc\ndefabc\ndefxxx\nxxx";
        let pattern = "abc\ndef";
        let exp = "4:abc\n8:defabc\n15:defxxx\n";

        search_assert_all(exp, haystack, pattern, |b| b.multi_line(true));
    }

    #[test]
    fn empty_line1() {
        let haystack = "";
        let matcher = EmptyLineMatcher::new(b'\n');
        let exp = "";

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
        let exp = "0:\n";
        let exp_line = "1:0:\n";

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
        let exp = "0:\n1:\n";
        let exp_line = "1:0:\n2:1:\n";

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
        let matcher = EmptyLineMatcher::new(b'\n');
        let exp = "4:\n7:\n8:\n";
        let exp_line = "3:4:\n5:7:\n6:8:\n";

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
    fn empty_line5() {
        // See: https://github.com/BurntSushi/ripgrep/issues/441
        // This is like empty_line4, but lacks the trailing line terminator.
        let haystack = "\
a
b

c


d";
        let matcher = EmptyLineMatcher::new(b'\n');
        let exp = "4:\n7:\n8:\n";
        let exp_line = "3:4:\n5:7:\n6:8:\n";

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
    fn empty_line6() {
        // See: https://github.com/BurntSushi/ripgrep/issues/441
        // This is like empty_line4, but includes an empty line at the end.
        let haystack = "\
a
b

c


d

";
        let matcher = EmptyLineMatcher::new(b'\n');
        let exp = "4:\n7:\n8:\n11:\n";
        let exp_line = "3:4:\n5:7:\n6:8:\n8:11:\n";

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
}
