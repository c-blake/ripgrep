use std::fmt;
use std::io;

use lines::LineIter;
use matcher::Matcher;
use searcher_builder::{ConfigError, Searcher};

pub trait Sink {
    type Error;

    fn error_message<T: fmt::Display>(message: T) -> Self::Error;

    fn error_io(err: io::Error) -> Self::Error {
        Self::error_message(err)
    }

    fn error_config(err: ConfigError) -> Self::Error {
        Self::error_message(err)
    }

    fn matched<M>(
        &mut self,
        _searcher: &Searcher<M>,
        _mat: &SinkMatch,
    ) -> Result<bool, Self::Error>
    where M: Matcher,
          M::Error: fmt::Display
    {
        Ok(false)
    }

    fn context<M>(
        &mut self,
        _searcher: &Searcher<M>,
        _context: &SinkContext,
    ) -> Result<bool, Self::Error>
    where M: Matcher,
          M::Error: fmt::Display
    {
        Ok(true)
    }

    fn context_break<M>(
        &mut self,
        _searcher: &Searcher<M>,
    ) -> Result<bool, Self::Error>
    where M: Matcher,
          M::Error: fmt::Display
    {
        Ok(true)
    }

    fn finish<M>(
        &mut self,
        _searcher: &Searcher<M>,
        _: &SinkFinish,
    ) -> Result<(), Self::Error>
    where M: Matcher,
          M::Error: fmt::Display
    {
        Ok(())
    }
}

impl<'a, S: Sink> Sink for &'a mut S {
    type Error = S::Error;

    fn error_message<T: fmt::Display>(message: T) -> S::Error {
        S::error_message(message)
    }

    fn error_io(err: io::Error) -> S::Error {
        S::error_io(err)
    }

    fn matched<M>(
        &mut self,
        searcher: &Searcher<M>,
        mat: &SinkMatch,
    ) -> Result<bool, S::Error>
    where M: Matcher,
          M::Error: fmt::Display
    {
        (**self).matched(searcher, mat)
    }

    fn context<M>(
        &mut self,
        searcher: &Searcher<M>,
        context: &SinkContext,
    ) -> Result<bool, S::Error>
    where M: Matcher,
          M::Error: fmt::Display
    {
        (**self).context(searcher, context)
    }

    fn context_break<M>(
        &mut self,
        searcher: &Searcher<M>,
    ) -> Result<bool, S::Error>
    where M: Matcher,
          M::Error: fmt::Display
    {
        (**self).context_break(searcher)
    }

    fn finish<M>(
        &mut self,
        searcher: &Searcher<M>,
        sink_finish: &SinkFinish,
    ) -> Result<(), S::Error>
    where M: Matcher,
          M::Error: fmt::Display
    {
        (**self).finish(searcher, sink_finish)
    }
}

#[derive(Clone, Debug)]
pub struct SinkFinish {
    pub(crate) byte_count: u64,
    pub(crate) binary_byte_offset: Option<u64>,
}

impl SinkFinish {
    /// Return the total number of bytes searched.
    pub fn byte_count(&self) -> u64 {
        self.byte_count
    }

    /// If binary detection is enabled and if binary data was found, then this
    /// returns the absolute byte offset of the first detected byte of binary
    /// data.
    ///
    /// Note that since this is an absolute byte offset, it cannot be relied
    /// upon to index into any addressable memory.
    pub fn binary_byte_offset(&self) -> Option<u64> {
        self.binary_byte_offset
    }
}

#[derive(Clone, Debug)]
pub struct SinkMatch<'b> {
    pub(crate) line_term: u8,
    pub(crate) bytes: &'b [u8],
    pub(crate) absolute_byte_offset: u64,
    pub(crate) line_number: Option<u64>,
}

impl<'b> SinkMatch<'b> {
    /// Returns the bytes for all matching lines, including the line
    /// terminators, if they exist.
    pub fn bytes(&self) -> &'b [u8] {
        self.bytes
    }

    /// Return an iterator over the lines in this match.
    pub fn lines(&self) -> LineIter<'b> {
        LineIter::new(self.line_term, self.bytes)
    }

    /// Returns the absolute byte offset of the start of this match. This
    /// offset is absolute in that it is relative to the very beginning of the
    /// input in a search, and can never be relied upon to be a valid index
    /// into an in-memory slice.
    pub fn absolute_byte_offset(&self) -> u64 {
        self.absolute_byte_offset
    }

    /// Returns the line number of the first line in this match, if available.
    ///
    /// Line numbers are only available when the search builder is instructed
    /// to compute them.
    pub fn line_number(&self) -> Option<u64> {
        self.line_number
    }
}

#[derive(Clone, Debug)]
pub enum SinkContextKind {
    Before,
    After,
}

#[derive(Clone, Debug)]
pub struct SinkContext<'a> {
    pub(crate) bytes: &'a [u8],
    pub(crate) kind: SinkContextKind,
    pub(crate) absolute_byte_offset: u64,
    pub(crate) line_number: Option<u64>,
}

impl<'a> SinkContext<'a> {
    /// Returns the context bytes, including line terminators.
    pub fn bytes(&self) -> &[u8] {
        self.bytes
    }

    /// Returns the type of context.
    pub fn kind(&self) -> &SinkContextKind {
        &self.kind
    }

    /// Returns the absolute byte offset of the start of this context. This
    /// offset is absolute in that it is relative to the very beginning of the
    /// input in a search, and can never be relied upon to be a valid index
    /// into an in-memory slice.
    pub fn absolute_byte_offset(&self) -> u64 {
        self.absolute_byte_offset
    }

    /// Returns the line number of the first line in this context, if
    /// available.
    ///
    /// Line numbers are only available when the search builder is instructed
    /// to compute them.
    pub fn line_number(&self) -> Option<u64> {
        self.line_number
    }
}

#[derive(Clone, Debug)]
pub struct StandardSink<W> {
    wtr: W,
}

impl<W: io::Write> StandardSink<W> {
    pub fn new(wtr: W) -> StandardSink<W> {
        StandardSink { wtr }
    }

    pub fn into_inner(self) -> W {
        self.wtr
    }
}

impl<W: io::Write> Sink for StandardSink<W> {
    type Error = io::Error;

    fn error_message<T: fmt::Display>(message: T) -> io::Error {
        io::Error::new(io::ErrorKind::Other, message.to_string())
    }

    fn error_io(err: io::Error) -> io::Error {
        err
    }

    fn matched<M>(
        &mut self,
        _searcher: &Searcher<M>,
        mat: &SinkMatch,
    ) -> Result<bool, io::Error>
    where M: Matcher,
          M::Error: fmt::Display
    {
        self.wtr.write_all(mat.bytes())?;
        Ok(true)
    }
}
