use std::fmt;
use std::io;

use matcher::Matcher;

pub trait Sink {
    type Error;

    fn error_message<T: fmt::Display>(message: T) -> Self::Error;

    fn error_io(err: io::Error) -> Self::Error {
        Self::error_message(err)
    }

    fn matched<M: Matcher>(
        &mut self,
        _matcher: M,
        _mat: &SinkMatch,
    ) -> Result<bool, Self::Error> {
        Ok(false)
    }

    fn context(
        &mut self,
        _context: &SinkContext,
    ) -> Result<bool, Self::Error> {
        Ok(true)
    }

    fn context_break(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn finish(&mut self, _: &SinkFinish) -> Result<(), Self::Error> {
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

    fn matched<M: Matcher>(
        &mut self,
        matcher: M,
        mat: &SinkMatch,
    ) -> Result<bool, S::Error> {
        (**self).matched(matcher, mat)
    }

    fn context(
        &mut self,
        context: &SinkContext,
    ) -> Result<bool, S::Error> {
        (**self).context(context)
    }

    fn context_break(&mut self) -> Result<(), S::Error> {
        (**self).context_break()
    }

    fn finish(&mut self, sink_finish: &SinkFinish) -> Result<(), S::Error> {
        (**self).finish(sink_finish)
    }
}

#[derive(Clone, Debug)]
pub struct SinkFinish {
    pub(crate) lines_matched: u64,
}

impl SinkFinish {
    /// Returns the total number of lines matched.
    pub fn lines_matched(&self) -> u64 {
        self.lines_matched
    }
}

#[derive(Clone, Debug)]
pub struct SinkMatch<'a> {
    pub(crate) bytes: &'a [u8],
    pub(crate) absolute_byte_offset: u64,
    pub(crate) line_number: Option<u64>,
}

impl<'a> SinkMatch<'a> {
    /// Returns the bytes for all matching lines, including the line
    /// terminators, if they exist.
    pub fn bytes(&self) -> &[u8] {
        self.bytes
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

    fn matched<M: Matcher>(
        &mut self,
        _matcher: M,
        mat: &SinkMatch,
    ) -> Result<bool, io::Error> {
        self.wtr.write_all(mat.bytes())?;
        Ok(true)
    }
}
