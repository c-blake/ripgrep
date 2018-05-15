use memchr::{memchr, memrchr};

use matcher::Matcher;

pub trait Sink {
    type Error;

    fn matched_line<M: Matcher>(
        &mut self,
        _matcher: M,
        _line_match: &LineMatch,
    ) -> Result<bool, Self::Error> {
        Ok(false)
    }

    fn matched_multiline<M: Matcher>(
        &mut self,
        _matcher: M,
        _line_match: &MultiLineMatch,
    ) -> Result<bool, Self::Error> {
        Ok(false)
    }

    fn context_line(
        &mut self,
        _line_context: &LineContext,
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
pub enum ContextKind {
    Before,
    After,
}

#[derive(Clone, Debug)]
pub struct LineContext<'a> {
    pub(crate) line: &'a [u8],
    pub(crate) kind: ContextKind,
    pub(crate) line_number: Option<u64>,
    pub(crate) absolute_byte_offset: Option<u64>,
}

impl<'a> LineContext<'a> {
    /// Returns the context line, including the line terminator.
    pub fn line(&self) -> &[u8] {
        self.line
    }

    /// Returns the type of context.
    pub fn kind(&self) -> &ContextKind {
        &self.kind
    }

    /// Returns the line number of this context line, if available.
    ///
    /// Line numbers are only available when the search builder is instructed
    /// to compute them.
    pub fn line_number(&self) -> Option<u64> {
        self.line_number
    }

    /// Returns the absolute byte offset of the start of this context line.
    /// This offset is absolute in that it is relative to the very beginning of
    /// the input in a search, and can never be relied upon to be a valid index
    /// into an in-memory slice.
    ///
    /// Byte offsets are only available when the search builder is instructed
    /// to compute them.
    pub fn absolute_byte_offset(&self) -> Option<u64> {
        self.absolute_byte_offset
    }
}

#[derive(Clone, Debug)]
pub struct LineMatch<'a> {
    pub(crate) line: &'a [u8],
    pub(crate) line_number: Option<u64>,
    pub(crate) absolute_byte_offset: Option<u64>,
}

impl<'a> LineMatch<'a> {
    pub(crate) fn from_line_match(
        lineterm: u8,
        buf: &'a [u8],
        pos: usize,
    ) -> LineMatch<'a> {
        let line_start = memrchr(lineterm, &buf[0..pos])
            .map_or(0, |i| i + 1);
        let line_end = memchr(lineterm, &buf[pos..])
            .map_or(buf.len(), |i| pos + i + 1);
        LineMatch  {
            line: &buf[line_start..line_end],
            line_number: None,
            absolute_byte_offset: None,
        }
    }

    /// Returns the matching line, including the line terminator, if it exists.
    pub fn line(&self) -> &[u8] {
        self.line
    }

    /// Returns the line number of this match, if available.
    ///
    /// Line numbers are only available when the search builder is instructed
    /// to compute them.
    pub fn line_number(&self) -> Option<u64> {
        self.line_number
    }

    /// Returns the absolute byte offset of the start of the line that matched.
    /// This offset is absolute in that it is relative to the very beginning of
    /// the input in a search, and can never be relied upon to be a valid index
    /// into an in-memory slice.
    ///
    /// Byte offsets are only available when the search builder is instructed
    /// to compute them.
    pub fn absolute_byte_offset(&self) -> Option<u64> {
        self.absolute_byte_offset
    }
}

#[derive(Clone, Debug)]
pub struct MultiLineMatch<'a> {
    pub(crate) line: &'a [u8],
    pub(crate) matched: &'a [u8],
    pub(crate) line_number_start: Option<u64>,
    pub(crate) line_number_end: Option<u64>,
    pub(crate) absolute_byte_offset: Option<u64>,
}

impl<'a> MultiLineMatch<'a> {
    /// Returns the matching lines, including the final line terminators, if
    /// it exists.
    pub fn line(&self) -> &[u8] {
        self.line
    }

    /// Returns the matched part of the lines. This slice is guaranteed to be
    /// contained within the slice returned by `line`.
    pub fn matched(&self) -> &[u8] {
        self.matched
    }

    /// Returns the line number of the first line containing this match, if
    /// available.
    ///
    /// Line numbers are only available when the search builder is instructed
    /// to compute them.
    pub fn line_number_start(&self) -> Option<u64> {
        self.line_number_start
    }

    /// Returns the line number of the last line containing this match, if
    /// available.
    ///
    /// Line numbers are only available when the search builder is instructed
    /// to compute them.
    pub fn line_number_end(&self) -> Option<u64> {
        self.line_number_end
    }

    /// Returns the absolute byte offset of the start of the first line
    /// containing this match. This offset is absolute in that it is relative
    /// to the very beginning of the input in a search, and can never be relied
    /// upon to be a valid index into an in-memory slice.
    ///
    /// Byte offsets are only available when the search builder is instructed
    /// to compute them.
    pub fn absolute_byte_offset(&self) -> Option<u64> {
        self.absolute_byte_offset
    }
}
