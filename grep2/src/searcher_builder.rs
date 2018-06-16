use std::cell::RefCell;
use std::cmp;
use std::fmt;
use std::fs::File;
use std::io::{self, Read};

use line_buffer::{
    self, BufferAllocation, LineBuffer, LineBufferBuilder, LineBufferReader,
    DEFAULT_BUFFER_CAPACITY, alloc_error,
};
use matcher::Matcher;
use searcher_exec::{
    Reader, SliceReader,
    SearcherByLine,
    SearcherReadByLineFast, SearcherMultiLine,
};
use sink::Sink;

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
pub struct BinaryDetection(pub(crate) line_buffer::BinaryDetection);

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
pub struct Config {
    /// The line terminator to use.
    pub line_term: u8,
    /// Whether to invert matching.
    pub invert_match: bool,
    /// The number of lines after a match to include.
    pub after_context: usize,
    /// The number of lines before a match to include.
    pub before_context: usize,
    /// Whether to count line numbers.
    pub line_number: bool,
    /// The maximum amount of heap memory to use.
    ///
    /// When not given, no explicit limit is enforced. When set to `0`, then
    /// only the memory map search strategy is available.
    pub heap_limit: Option<usize>,
    /// The memory map strategy.
    pub mmap: MmapChoice,
    /// The binary data detection strategy.
    pub binary: BinaryDetection,
    /// Whether to enable matching across multiple lines.
    pub multi_line: bool,
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
    pub(crate) config: Config,
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
    pub(crate) config: Config,
    pub(crate) matcher: M,
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
            if self.is_line_by_line_fast() {
                SearcherReadByLineFast::new(self, rdr, write_to).run()
            } else {
                self.search_by_line(rdr, write_to)
            }
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
        SearcherByLine::new(self, read_from, write_to).run()
    }

    fn search_multi_line<S: Sink>(
        &self,
        slice: &[u8],
        write_to: S,
    ) -> Result<(), S::Error> {
        SearcherMultiLine::new(self, slice, write_to).run()
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

    fn is_line_by_line_fast(&self) -> bool {
        match self.matcher.line_terminator() {
            None => false,
            Some(line_term) => line_term == self.config.line_term,
        }
    }
}
