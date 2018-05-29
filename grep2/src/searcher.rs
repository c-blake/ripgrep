use std::fmt;
use std::io;

use lines;
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
            line_buffer: self.config.line_buffer(),
        })
    }
}

#[derive(Debug)]
pub struct Searcher<M> {
    config: Config,
    matcher: M,
    line_buffer: LineBuffer,
}

impl<M> Searcher<M>
where M: Matcher,
      M::Error: fmt::Display
{
    fn search_reader<R: io::Read, S: Sink>(
        &mut self,
        read_from: R,
        write_to: S,
    ) -> Result<(), S::Error> {
        let rdr = LineBufferReader::new(read_from, &mut self.line_buffer);
        SearcherExec {
            config: &self.config,
            matcher: &self.matcher,
            rdr: rdr,
            sink: write_to,
            search_pos: 0,
        }.run()
    }

    fn search_slice<S: Sink>(
        &mut self,
        slice: &[u8],
        write_to: S,
    ) -> Result<(), S::Error> {
        SearcherExec {
            config: &self.config,
            matcher: &self.matcher,
            rdr: SliceReader::new(slice),
            sink: write_to,
            search_pos: 0,
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
///
/// This is a bit of a sneaky trick, but it lets multi-line search work because
/// the entire contents of the source will be searched before consuming
/// anything.
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
struct SearcherExec<'s, M: 's, R, S> {
    config: &'s Config,
    matcher: &'s M,
    rdr: R,
    sink: S,
    search_pos: usize,
}

impl<'s, M, R, S> SearcherExec<'s, M, R, S>
where M: Matcher,
      M::Error: fmt::Display,
      R: Reader,
      S: Sink
{
    fn run(mut self) -> Result<(), S::Error> {
    'LOOP:
        loop {
            if !self.fill()? {
                break;
            }
            while !self.search_buffer().is_empty() {
                if !self.process_next_match()? {
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
        self.rdr.consume_all();
        self.search_pos = 0;
        let didread = match self.rdr.fill() {
            Err(err) => return Err(S::error_io(err)),
            Ok(didread) => didread,
        };
        if !didread {
            return Ok(false);
        }
        Ok(true)
    }

    fn process_next_match(&mut self) -> Result<bool, S::Error> {
        let (line_start, line_end) = match self.find()? {
            Some(range) => range,
            None => {
                self.search_pos = self.buffer().len();
                return Ok(true);
            }
        };
        let keepgoing = self.sink.matched(
            &self.matcher,
            &SinkMatch {
                bytes: &self.rdr.buffer()[line_start..line_end],
                absolute_byte_offset: 0,
                line_number: None,
            },
        )?;
        self.search_pos = line_end;
        Ok(keepgoing)
    }

    fn find(&mut self) -> Result<Option<(usize, usize)>, S::Error> {
        if self.config.multi_line {
            return self.find_multi_line();
        }
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

    fn find_multi_line(&mut self) -> Result<Option<(usize, usize)>, S::Error> {
        assert!(self.config.multi_line);
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
}

#[cfg(test)]
mod tests {
    use testutil::{KitchenSink, SubstringMatcher};

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
    fn scratch() {
        // let pattern = "\
// For the Doctor Watsons of this world, as opposed to the Sherlock
// Holmeses, success in the province of detective work must always
// ";
        // let pattern = "\n";
        let pattern = "For the Doctor Watsons of this world, as opposed to the Sherlock\nH";
        let mut sink = KitchenSink::new();
        let matcher = SubstringMatcher::new(pattern);
        let mut searcher = SearcherBuilder::new()
            // .binary_detection(BinaryDetection::quit(b'u'))
            .multi_line(true)
            .build(matcher)
            .unwrap();
        searcher.search_slice(SHERLOCK.as_bytes(), &mut sink).unwrap();
        println!("{}", String::from_utf8(sink.as_bytes().to_vec()).unwrap());
    }
}
