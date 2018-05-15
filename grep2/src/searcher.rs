use memchr::{memchr, memrchr};

#[derive(Clone, Debug)]
pub struct LineMatch<'a> {
    pub(crate) line: &'a [u8],
    pub(crate) line_number: Option<u64>,
    pub(crate) byte_offset: Option<u64>,
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

    /// Returns the matching line, including the line terminator.
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
    /// into an in-memory slice. (That is what the `start` and `end` methods
    /// are for.)
    ///
    /// Byte offsets are only available when the search builder is instructed
    /// to compute them.
    pub fn absolute_byte_offset(&self) -> Option<u64> {
        self.absolute_byte_offset
    }
}

#[derive(Clone, Debug)]
pub struct MultiLineMatch {
    pub(crate) line_start: usize,
    pub(crate) line_end: usize,
    pub(crate) match_start: usize,
    pub(crate) match_end: usize,
    pub(crate) line_number_start: Option<u64>,
    pub(crate) line_number_end: Option<u64>,
    pub(crate) byte_offset_start: Option<u64>,
    pub(crate) byte_offset_end: Option<u64>,
}

impl MultiLineMatch {
    /// Returns the starting byte offset of the first line in this match.
    pub fn line_start(&self) -> usize {
        self.line_start
    }

    /// Returns the ending byte offset of the last line line in this match.
    /// This includes the line terminator, if one exists (otherwise, this
    /// offset corresponds to the end of the input).
    pub fn line_end(&self) -> usize {
        self.line_end
    }

    /// Returns the starting byte offset of this match. This is guaranteed to
    /// be greater than or equal to the starting offset of the first line
    /// containing this match.
    pub fn match_start(&self) -> usize {
        self.match_start
    }

    /// Returns the ending byte offset of this match. This is guaranteed to be
    /// less than or equal to the ending offset of the last line containing
    /// this match.
    pub fn match_end(&self) -> usize {
        self.match_end
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
    /// upon to be a valid index into an in-memory slice. (That is what the
    /// `start` and `end` methods are for.)
    ///
    /// Byte offsets are only available when the search builder is instructed
    /// to compute them.
    pub fn byte_offset_start(&self) -> Option<u64> {
        self.byte_offset_start
    }
}

#[derive(Debug)]
struct Options {
    /// The number of lines after a match to include.
    after_context: usize,
    /// The number of lines before a match to include.
    before_context: usize,
    /// Whether to report absolute byte offsets or not.
    absolute_byte_offset: bool,
    /// Whether to count matching lines.
    count: bool,
    /// Whether to count each individual match, including multiple matches on
    /// a single line.
    count_matches: bool,
    /// The line terminator to use.
    lineterm: u8,
    /// Whether to invert matching.
    invert_match: bool,
    /// Whether to count line numbers.
    line_number: bool,
    /// Whether to enable binary data detection.
    /// TODO: This should probably be an enum.
    binary: bool,
}
