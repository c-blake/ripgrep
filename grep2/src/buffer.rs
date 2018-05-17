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
    binary_detection: Option<u8>,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            capacity: 8 * (1<<10), // 8 KB
            lineterm: b'\n',
            buffer_alloc: BufferAllocation::default(),
            binary_detection: None,
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
            tmp: vec![0; self.config.capacity],
            pos: 0,
            end: 0,
            is_binary: false,
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

    /// Whether to enable binary detection or not. When enabled, if the given
    /// byte occurs anywhere within the input buffer, then the buffer's binary
    /// flag is set to `true`.
    ///
    /// By default, this is disabled.
    pub fn binary_detection(
        &mut self,
        byte: Option<u8>,
    ) -> &mut LineBufferBuilder {
        self.config.binary_detection = byte;
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
    pub fn new(
        rdr: R,
        line_buffer: &'b mut LineBuffer,
    ) -> LineBufferReader<'b, R> {
        line_buffer.clear();
        LineBufferReader { rdr, line_buffer }
    }

    /// Returns true if and only if this buffer currently contains binary
    /// data. This is recomputed each time new data is added to the buffer.
    fn is_binary(&self) -> bool {
        self.line_buffer.is_binary()
    }
}

/// A line buffer manages a (typically fixed) buffer for holding lines.
#[derive(Clone, Debug)]
pub struct LineBuffer {
    /// The configuration of this buffer.
    config: Config,
    /// The primary buffer with which to hold data.
    buf: Vec<u8>,
    /// A scratch buffer for use when rolling buffer contents.
    tmp: Vec<u8>,
    /// The current position of this buffer. This is always a valid sliceable
    /// index into `buf`, and its maximum value is the length of `buf`.
    pos: usize,
    /// The end position of searchable content in this buffer. This is either
    /// set to the final line terminator in the buffer, or to the end of the
    /// buffer when the underlying reader has been exhausted.
    end: usize,
    /// Set to true if and only if binary detection is enabled and if the
    /// contents of `buf` contain binary data.
    is_binary: bool,
}

impl LineBuffer {
    /// Reset this buffer, such that it can be used with a new reader.
    fn clear(&mut self) {
        self.pos = 0;
        self.end = 0;
        self.is_binary = false;
    }

    /// Returns true if and only if this buffer currently contains binary
    /// data. This is recomputed each time new data is added to the buffer.
    fn is_binary(&self) -> bool {
        self.is_binary
    }

    fn fill<R: io::Read>(&mut self, rdr: R) -> Result<bool, io::Error> {
        Ok(false)
    }
}

fn is_binary(buf: &[u8], b: u8) -> bool {
    memchr(b, buf).is_some()
}
