use std::cell::RefCell;
use std::cmp;
use std::fmt;
use std::fs::File;
use std::io::{self, Read};
use std::ops::Range;

use memchr::memchr;

use lines::{self, LineStep};
use line_buffer::{
    self, BufferAllocation, LineBuffer, LineBufferBuilder, LineBufferReader,
    DEFAULT_BUFFER_CAPACITY, alloc_error,
};
use matcher::{Match, Matcher};
use sink::{Sink, SinkFinish, SinkMatch};

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
            multi_line_buffer: vec![],
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
    /// A buffer in which to store the contents of a reader when performing a
    /// multi line search. In particular, multi line searches cannot be
    /// performed incrementally, and need the entire haystack in memory at
    /// once.
    ///
    /// This is a RefCell for the same reason that line_buffer is a RefCell.
    multi_line_buffer: Vec<u8>,
}

impl<M> Searcher<M>
where M: Matcher,
      M::Error: fmt::Display
{
    pub fn search_reader<R: io::Read, S: Sink>(
        &mut self,
        read_from: R,
        write_to: S,
    ) -> Result<(), S::Error> {
        if self.config.multi_line {
            self.fill_multi_line_buffer_from_reader::<R, S>(read_from)?;
            self.search_multi_line(&self.multi_line_buffer, write_to)
        } else {
            let mut line_buffer = self.line_buffer.borrow_mut();
            let rdr = LineBufferReader::new(read_from, &mut *line_buffer);
            self.search_by_line(rdr, write_to)
        }
    }

    pub fn search_slice<S: Sink>(
        &mut self,
        slice: &[u8],
        write_to: S,
    ) -> Result<(), S::Error> {
        if self.config.multi_line {
            self.search_multi_line(slice, write_to)
        } else {
            self.search_by_line(SliceReader::new(slice), write_to)
        }
    }

    fn search_by_line<R: Reader, S: Sink>(
        &self,
        read_from: R,
        write_to: S,
    ) -> Result<(), S::Error> {
        assert!(!self.config.multi_line);

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

    fn search_multi_line<S: Sink>(
        &self,
        slice: &[u8],
        write_to: S,
    ) -> Result<(), S::Error> {
        assert!(self.config.multi_line);

        SearcherMultiLine {
            searcher: self,
            config: &self.config,
            matcher: &self.matcher,
            sink: write_to,
            slice: slice,
            search_pos: 0,
            binary_byte_offset: None,
            last_match: None,
            line_number: if self.config.line_number { Some(1) } else { None },
            last_line_counted: 0,
        }.run()
    }

    /// Fill the buffer for use with multi-line searching from the given file.
    /// This reads from the file until EOF or until an error occurs. If the
    /// contents exceed the configured heap limit, then an error is returned.
    fn fill_multi_line_buffer_from_file<S: Sink>(
        &mut self,
        mut read_from: &File,
    ) -> Result<(), S::Error> {
        assert!(self.config.multi_line);

        if self.config.heap_limit.is_none() {
            let buf = &mut self.multi_line_buffer;
            buf.clear();
            let cap = read_from
                .metadata()
                .map(|m| m.len() as usize + 1)
                .unwrap_or(0);
            buf.reserve(cap);
            read_from.read_to_end(buf).map_err(S::error_io)?;
        }
        self.fill_multi_line_buffer_from_reader::<&File, S>(read_from)
    }

    /// Fill the buffer for use with multi-line searching from the given
    /// reader. This reads from the reader until EOF or until an error occurs.
    /// If the contents exceed the configured heap limit, then an error is
    /// returned.
    fn fill_multi_line_buffer_from_reader<R: io::Read, S: Sink>(
        &mut self,
        mut read_from: R,
    ) -> Result<(), S::Error> {
        assert!(self.config.multi_line);

        let buf = &mut self.multi_line_buffer;
        buf.clear();

        // If we don't have a heap limit, then we can defer to std's
        // read_to_end implementation...
        let heap_limit = match self.config.heap_limit {
            Some(heap_limit) => heap_limit,
            None => {
                read_from.read_to_end(buf).map_err(S::error_io)?;
                return Ok(());
            }
        };
        if heap_limit == 0 {
            return Err(S::error_io(alloc_error(heap_limit)));
        }

        // ... otherwise we need to roll our own. This is likely quite a bit
        // slower than what is optimal, but we avoid `unsafe` until there's a
        // compelling reason to speed this up.
        buf.resize(cmp::min(DEFAULT_BUFFER_CAPACITY, heap_limit), 0);
        let mut pos = 0;
        loop {
            let nread = match read_from.read(&mut buf[pos..]) {
                Ok(nread) => nread,
                Err(ref err) if err.kind() == io::ErrorKind::Interrupted => {
                    continue;
                }
                Err(err) => return Err(S::error_io(err)),
            };
            if nread == 0 {
                buf.resize(pos, 0);
                return Ok(());
            }

            pos += nread;
            if buf[pos..].is_empty() {
                let additional = heap_limit - buf.len();
                if additional == 0 {
                    return Err(S::error_io(alloc_error(heap_limit)));
                }
                let limit = buf.len() + additional;
                let doubled = 2 * buf.len();
                buf.resize(cmp::min(doubled, limit), 0);
            }
        }
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
struct SliceReader<'b> {
    slice: &'b [u8],
    binary_byte_offset: Option<u64>,
    filled: bool,
}

impl<'b> SliceReader<'b> {
    fn new(slice: &'b [u8]) -> SliceReader<'b> {
        SliceReader { slice, binary_byte_offset: None, filled: false }
    }
}

impl<'b> Reader for SliceReader<'b> {
    fn absolute_byte_offset(&self) -> u64 {
        0
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
        match self.matcher.find(self.search_buffer()) {
            Err(err) => Err(S::error_message(err)),
            Ok(None) => Ok(None),
            Ok(Some(m)) => {
                Ok(Some(lines::locate(
                    self.buffer(),
                    self.config.line_term,
                    m.offset(self.search_pos),
                )))
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

    fn has_binary(&mut self, range: &Match) -> bool {
        let binary_byte = match self.config.binary.0 {
            line_buffer::BinaryDetection::Quit(b) => b,
            _ => return false,
        };
        self.rdr.has_binary(binary_byte, range)
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
    fn run(mut self) -> Result<(), S::Error> {
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
            self.binary_byte_offset = Some((range.start() + i) as u64);
            return true;
        }
        false
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
//   1. Do context handling last. (Famous last words.)
//   2. Fill out the single-line searcher. Use optimizations. Line-by-line too.
//   3. Fill out the logic for opening a reader in Searcher.
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

    #[test]
    fn big1() {
        let mut haystack = String::new();
        haystack.push_str("a\n");
        // Pick an arbitrary number above the capacity.
        for _ in 0..(4 * (DEFAULT_BUFFER_CAPACITY + 7)) {
            haystack.push_str("zzz\n");
        }
        haystack.push_str("a\n");

        let exp = "0:a\n131186:a\n";
        let got = search_reader(&haystack, SubstringMatcher::new("a"), |b| {
            b.heap_limit(Some(4))
        });
        assert_eq!(exp, got, "\nsearch_reader mismatch");

        let exp = "0:a\n131186:a\n";
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
        let exp = "\nbinary offset:0\n";
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
        let exp = "\nbinary offset:1\n";
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
        let exp = "0:a\n\nbinary offset:32773\n";
        let got = search_reader(&haystack, SubstringMatcher::new("a"), |b| {
            b.binary_detection(BinaryDetection::quit(0))
        });
        assert_eq!(exp, got, "\nsearch_reader mismatch");

        // In contrast, the slice readers (for multi line as well) will only
        // look for binary data in the initial chunk of bytes. After that
        // point, it only looks for binary data in matches.
        let exp = "0:a\n32770:a\n\nbinary offset:32773\n";
        let got = search_slice(&haystack, SubstringMatcher::new("a"), |b| {
            b.binary_detection(BinaryDetection::quit(0))
        });
        assert_eq!(exp, got, "\nsearch_slice mismatch");

        let exp = "0:a\n32770:a\n\nbinary offset:32773\n";
        search_assert_all(exp, &haystack, "a", |b| {
            b.multi_line(true).binary_detection(BinaryDetection::quit(0))
        });
    }
}
