use std::io;

use memchr::memchr;

/// The behavior of a searcher in the face of long lines and big contexts.
///
/// When searching data incrementally using a fixed size buffer, this controls
/// the amount of *additional* memory to allocate beyond the size of the buffer
/// to accommodate lines (which may include the lines in a context window, when
/// enabled) that do not fit in the buffer.
#[derive(Clone, Copy, Debug)]
pub enum BufferAllocation {
    /// Attempt to expand the size of the buffer until either at least the next
    /// line fits into memory or until all available memory is exhausted.
    ///
    /// This is the default.
    Eager,
    /// Limit the amount of additional memory allocated to the given size. If
    /// a line is found that requires more memory than is allowed here, then
    /// stop reading and return an error.
    Error(usize),
}

impl Default for BufferAllocation {
    fn default() -> BufferAllocation {
        BufferAllocation::Eager
    }
}

/// The behavior of binary detection in the line buffer.
///
/// Binary detection is the process of _heuristically_ identifying whether a
/// given chunk of data is binary or not, and then taking an action based on
/// the result of that heuristic. The motivation behind detecting binary data
/// is that binary data often indicates data that is undesirable to search
/// using textual patterns. Of course, there are many cases in which this isn't
/// true, which is why binary detection is disabled by default.
#[derive(Clone, Copy, Debug)]
pub enum BinaryDetection {
    /// No binary detection is performed. Data reported by the line buffer may
    /// contain arbitrary bytes.
    None,
    /// The given byte is searched in all contents read by the line buffer. If
    /// it occurs, then the data is considered binary and the line buffer acts
    /// as if it reached EOF. The line buffer guarantees that this byte will
    /// never be observable by callers.
    Quit(u8),
    /// The given byte is searched in all contents read by the line buffer. If
    /// it occurs, then it is replaced by the line terminator. The line buffer
    /// guarantees that this byte will never be observable by callers.
    Convert(u8),
}

impl Default for BinaryDetection {
    fn default() -> BinaryDetection {
        BinaryDetection::None
    }
}

/// The configuration of a buffer. This contains options that are fixed once
/// a buffer has been constructed.
#[derive(Clone, Copy, Debug)]
struct Config {
    /// The number of bytes to attempt to read at a time.
    capacity: usize,
    /// The line terminator.
    lineterm: u8,
    /// The behavior for handling long lines.
    buffer_alloc: BufferAllocation,
    /// When set, the presence of the given byte indicates binary content.
    binary_detection: BinaryDetection,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            capacity: 8 * (1<<10), // 8 KB
            lineterm: b'\n',
            buffer_alloc: BufferAllocation::default(),
            binary_detection: BinaryDetection::default(),
        }
    }
}

/// A builder for constructing line buffers.
#[derive(Clone, Debug, Default)]
pub struct LineBufferBuilder {
    config: Config,
}

impl LineBufferBuilder {
    /// Create a new builder for a buffer.
    pub fn new() -> LineBufferBuilder {
        LineBufferBuilder { config: Config::default() }
    }

    /// Create a new line buffer from this builder's configuration.
    pub fn build(&self) -> LineBuffer {
        LineBuffer {
            config: self.config,
            buf: vec![0; self.config.capacity],
            start: 0,
            last_lineterm: 0,
            end: 0,
            absolute_byte_offset: 0,
            binary_byte_offset: None,
        }
    }

    /// Set the default capacity to use for a buffer.
    ///
    /// In general, the capacity of a buffer corresponds to the amount of data
    /// to hold in memory, and the size of the reads to make to the underlying
    /// reader.
    ///
    /// This is set to a reasonable default and probably shouldn't be changed
    /// unless there's a specific reason to do so.
    pub fn capacity(&mut self, capacity: usize) -> &mut LineBufferBuilder {
        self.config.capacity = capacity;
        self
    }

    /// Set the line terminator for the buffer.
    ///
    /// Every buffer has a line terminator, and this line terminator is used
    /// to determine how to roll the buffer forward. For example, when a read
    /// to the buffer's underlying reader occurs, the end of the data that is
    /// read is likely to correspond to an incomplete line. As a line buffer,
    /// callers should not access this data since it is incomplete. The line
    /// terminator is how the line buffer determines the part of the read that
    /// is incomplete.
    ///
    /// By default, this is set to `b'\n'`.
    pub fn line_terminator(&mut self, lineterm: u8) -> &mut LineBufferBuilder {
        self.config.lineterm = lineterm;
        self
    }

    /// Set the maximum amount of additional memory to allocate for long lines.
    ///
    /// In order to enable line oriented search, a fundamental requirement is
    /// that, at a minimum, each line must be able to fit into memory. This
    /// setting controls how big that line is allowed to be. By default, this
    /// is set to `BufferAllocation::Eager`, which means a line buffer will
    /// attempt to allocate as much memory as possible to fit a line, and will
    /// only be limited by available memory.
    ///
    /// Note that this setting only applies to the amount of *additional*
    /// memory to allocate, beyond the capacity of the buffer. That means that
    /// a value of `0` is sensible, and in particular, will guarantee that a
    /// line buffer will never allocate additional memory beyond its initial
    /// capacity.
    pub fn buffer_alloc(
        &mut self,
        behavior: BufferAllocation,
    ) -> &mut LineBufferBuilder {
        self.config.buffer_alloc = behavior;
        self
    }

    /// Whether to enable binary detection or not. Depending on the setting,
    /// this can either cause the line buffer to report EOF early or it can
    /// cause the line buffer to clean the data.
    ///
    /// By default, this is disabled. In general, binary detection should be
    /// viewed as an imperfect heuristic.
    pub fn binary_detection(
        &mut self,
        detection: BinaryDetection,
    ) -> &mut LineBufferBuilder {
        self.config.binary_detection = detection;
        self
    }
}

/// A line buffer reader efficiently reads a line oriented buffer from an
/// arbitrary reader.
#[derive(Debug)]
pub struct LineBufferReader<'b, R> {
    rdr: R,
    line_buffer: &'b mut LineBuffer,
}

impl<'b, R: io::Read> LineBufferReader<'b, R> {
    /// Create a new buffered reader that reads from `rdr` and uses the given
    /// `line_buffer` as an intermediate buffer.
    ///
    /// This does not change the binary detection behavior of the given line
    /// buffer.
    pub fn new(
        rdr: R,
        line_buffer: &'b mut LineBuffer,
    ) -> LineBufferReader<'b, R> {
        line_buffer.clear();
        LineBufferReader { rdr, line_buffer }
    }

    /// Like `new`, but sets the binary detection behavior of the line buffer
    /// to the behavior specified.
    pub fn with_binary_detection(
        rdr: R,
        line_buffer: &'b mut LineBuffer,
        detection: BinaryDetection,
    ) -> LineBufferReader<'b, R> {
        line_buffer.clear();
        line_buffer.binary_detection(detection);
        LineBufferReader { rdr, line_buffer }
    }

    /// If binary data was detected, then this returns the absolute byte offset
    /// at which binary data was initially found.
    pub fn binary_byte_offset(&self) -> Option<u64> {
        self.line_buffer.binary_byte_offset()
    }
}

/// A line buffer manages a (typically fixed) buffer for holding lines.
#[derive(Clone, Debug)]
pub struct LineBuffer {
    /// The configuration of this buffer.
    config: Config,
    /// The primary buffer with which to hold data.
    buf: Vec<u8>,
    /// The current position of this buffer. This is always a valid sliceable
    /// index into `buf`, and its maximum value is the length of `buf`.
    start: usize,
    /// The end position of searchable content in this buffer. This is either
    /// set to the final line terminator in the buffer, or to last byte emitted
    /// by the reader when it has been exhausted.
    last_lineterm: usize,
    /// The end position of the buffer. This is always greater than or equal to
    /// lastnl. The bytes between lastnl and end, if any, always correspond to
    /// a partial line.
    end: usize,
    /// The absolute byte offset corresponding to `pos`. This is most typically
    /// not a valid index into addressable memory, but rather, an offset that
    /// is relative to all data that passes through a line buffer (since
    /// construction or since the last time `clear` was called).
    absolute_byte_offset: u64,
    /// If binary data was found, this records the absolute byte offset at
    /// which it was first detected.
    binary_byte_offset: Option<u64>,
}

impl LineBuffer {
    /// Reset this buffer, such that it can be used with a new reader.
    fn clear(&mut self) {
        self.start = 0;
        self.last_lineterm = 0;
        self.end = 0;
        self.absolute_byte_offset = 0;
        self.binary_byte_offset = None;
    }

    /// The absolute byte offset which corresponds to the starting offsets
    /// of the data returned by `buffer` relative to the beginning of the
    /// reader's contents. As such, this offset does not generally correspond
    /// to an offset in memory. It is typically used for reporting purposes,
    /// particularly in error messages.
    ///
    /// This is reset to `0` when `clear` is called.
    fn absolute_byte_offset(&self) -> u64 {
        self.absolute_byte_offset
    }

    /// If binary data was detected, then this returns the absolute byte offset
    /// at which binary data was initially found.
    fn binary_byte_offset(&self) -> Option<u64> {
        self.binary_byte_offset
    }

    /// Set the binary detection behavior of this input buffer. The behavior
    /// of this input buffer is not specified if this is called after `fill`
    /// and before `clear`.
    fn binary_detection(
        &mut self,
        detection: BinaryDetection,
    ) -> &mut LineBuffer {
        self.config.binary_detection = detection;
        self
    }

    /// Return the contents of this buffer.
    fn buffer(&self) -> &[u8] {
        &self.buf[self.start..self.last_lineterm]
    }

    /// Consume the number of bytes provided. This must be less than or equal
    /// to the number of bytes returned by `buffer`.
    fn consume(&mut self, amt: usize) {
        assert!(amt <= self.buffer().len());
        self.start += amt;
        self.absolute_byte_offset += amt as u64;
    }

    /// Consumes the remainder of the buffer. Subsequent calls to `buffer` are
    /// guaranteed to return an empty slice until the buffer is refilled.
    ///
    /// This is a convenience function for `consume(buffer.len())`.
    fn consume_all(&mut self) {
        let amt = self.buffer().len();
        self.consume(amt);
    }

    /// Fill the contents of this buffer by discarding the part of the buffer
    /// that has been consumed. The free space created by discarding the
    /// consumed part of the buffer is then filled with new data from the given
    /// reader.
    ///
    /// Callers should provide the same reader to this line buffer in
    /// subsequent calls to fill. A different reader can only be used
    /// immediately following a call to `clear`.
    ///
    /// If EOF is reached, then `false` is returned. Otherwise, `true` is
    /// returned. (Note that if this line buffer's binary detection is set to
    /// `Quit`, then the presence of binary data will cause this buffer to
    /// behave as if it had seen EOF.)
    ///
    /// This forwards any errors returned by `rdr`, and will also return an
    /// error if the buffer must be expanded past its allocation limit, as
    /// governed by the buffer allocation strategy.
    #[allow(unused_variables)]
    fn fill<R: io::Read>(&mut self, rdr: R) -> Result<bool, io::Error> {
        Ok(false)
    }
}

fn is_binary(buf: &[u8], b: u8) -> bool {
    memchr(b, buf).is_some()
}
