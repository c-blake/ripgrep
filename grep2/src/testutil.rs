use std::fmt;
use std::io::{self, Write};
use std::str;

use memchr::memchr;

use lines;
use matcher::{LineMatchKind, Match, Matcher, NoCaptures, NoError};
use searcher::Searcher;
use sink::{Sink, SinkContext, SinkFinish, SinkMatch};

/// A simple substring matcher that requires UTF-8.
///
/// This supports setting the matcher's line terminator configuration directly,
/// which we use for testing purposes.
#[derive(Clone, Debug)]
pub struct SubstringMatcher {
    pattern: String,
    line_term: Option<u8>,
    every_line_is_candidate: bool,
}

impl SubstringMatcher {
    /// Create a new substring matcher.
    pub fn new(pattern: &str) -> SubstringMatcher {
        SubstringMatcher {
            pattern: pattern.to_string(),
            line_term: None,
            every_line_is_candidate: false,
        }
    }

    /// Forcefully set the line terminator of this matcher.
    ///
    /// By default, this matcher has no line terminator set.
    ///
    /// This panics if the pattern string contains the given line terminator.
    pub fn set_line_term(
        &mut self,
        line_term: Option<u8>,
    ) -> &mut SubstringMatcher {
        if let Some(b) = line_term {
            let bytes = self.pattern.as_bytes();
            assert!(bytes.iter().position(|&x| x == b).is_none());
        }
        self.line_term = line_term;
        self
    }

    /// Whether to return every line as a candidate or not.
    ///
    /// This forces searchers to handle the case of reporting a false positive.
    pub fn every_line_is_candidate(
        &mut self,
        yes: bool,
    ) -> &mut SubstringMatcher {
        self.every_line_is_candidate = yes;
        self
    }
}

impl Matcher for SubstringMatcher {
    type Captures = NoCaptures;
    type Error = str::Utf8Error;

    fn find_at(
        &self,
        haystack: &[u8],
        at: usize,
    ) -> Result<Option<Match>, str::Utf8Error> {
        let slice = str::from_utf8(haystack)?;
        Ok(slice[at..].find(&self.pattern).map(|i| {
            Match::new(at + i, at + i + self.pattern.len())
        }))
    }

    fn new_captures(&self) -> Result<NoCaptures, str::Utf8Error> {
        Ok(NoCaptures::new())
    }

    fn line_terminator(&self) -> Option<u8> {
        self.line_term
    }

    fn find_candidate_line(
        &self,
        haystack: &[u8],
    ) -> Result<Option<LineMatchKind>, str::Utf8Error> {
        if self.every_line_is_candidate {
            assert!(self.line_term.is_some());
            if haystack.is_empty() {
                return Ok(None);
            }
            // Make it interesting and return the last byte in the current
            // line.
            let i = memchr(self.line_term.unwrap(), haystack)
                .map(|i| i)
                .unwrap_or(haystack.len() - 1);
            Ok(Some(LineMatchKind::Candidate(i)))
        } else {
            Ok(self.shortest_match(haystack)?.map(LineMatchKind::Confirmed))
        }
    }
}

/// A matcher that matches only the empty line and nothing else. An empty line
/// is defined as a line with at most one byte, where that byte is the line
/// terminator.
#[derive(Clone, Debug)]
pub struct EmptyLineMatcher {
    line_term: u8,
}

impl EmptyLineMatcher {
    /// Create a new empty line matcher.
    pub fn new(line_term: u8) -> EmptyLineMatcher {
        EmptyLineMatcher { line_term }
    }

    fn next_line(&self, haystack: &[u8], at: usize) -> Match {
        let end = haystack[at..]
            .iter()
            .position(|&b| b == self.line_term)
            .map(|i| at + i + 1);
        match end {
            None => {
                lines::locate(
                    haystack,
                    self.line_term,
                    Match::zero(haystack.len()),
                )
            }
            Some(end) => {
                let start = lines::preceding(
                    &haystack[..end], self.line_term, 0);
                Match::new(start, end)
            }
        }
    }

    fn line_len(&self, line: &[u8]) -> usize {
        if let Some(&last) = line.last() {
            if last == self.line_term {
                line.len() - 1
            } else {
                line.len()
            }
        } else {
            0
        }
    }
}

impl Matcher for EmptyLineMatcher {
    type Captures = NoCaptures;
    type Error = NoError;

    fn find_at(
        &self,
        haystack: &[u8],
        mut at: usize,
    ) -> Result<Option<Match>, NoError> {
        loop {
            let line = self.next_line(haystack, at);
            if line.start() >= at {
                if self.line_len(&haystack[line]) == 0 {
                    return Ok(Some(Match::zero(line.start())));
                }
            }
            if at == haystack.len() {
                return Ok(None);
            }
            at = line.end();
        }
    }

    fn new_captures(&self) -> Result<NoCaptures, NoError> {
        Ok(NoCaptures::new())
    }
}

/// An implementation of Sink that prints all available information.
///
/// This is useful for tests because it lets us easily confirm whether data
/// is being passed to Sink correctly.
#[derive(Clone, Debug)]
pub struct KitchenSink(Vec<u8>);

impl KitchenSink {
    /// Create a new implementation of Sink that includes everything in the
    /// kitchen.
    pub fn new() -> KitchenSink {
        KitchenSink(vec![])
    }

    /// Return the data written to this sink.
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

impl Sink for KitchenSink {
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
        let mut line_number = mat.line_number();
        let mut byte_offset = mat.absolute_byte_offset();
        for line in mat.lines() {
            if let Some(ref mut n) = line_number {
                write!(self.0, "{}:", n)?;
                *n += 1;
            }

            write!(self.0, "{}:", byte_offset)?;
            byte_offset += line.len() as u64;
            self.0.write_all(line)?;
        }
        Ok(true)
    }

    fn context(
        &mut self,
        context: &SinkContext,
    ) -> Result<bool, io::Error> {
        write!(self.0, "{}-", context.absolute_byte_offset)?;
        if let Some(line_number) = context.line_number() {
            write!(self.0, "{}-", line_number)?;
        }
        self.0.write_all(context.bytes())?;
        Ok(true)
    }

    fn context_break(&mut self) -> Result<(), io::Error> {
        self.0.write_all(b"--\n")?;
        Ok(())
    }

    fn finish(&mut self, sink_finish: &SinkFinish) -> Result<(), io::Error> {
        writeln!(self.0, "")?;
        writeln!(self.0, "byte count:{}", sink_finish.byte_count())?;
        if let Some(offset) = sink_finish.binary_byte_offset() {
            writeln!(self.0, "binary offset:{}", offset)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use matcher::{Match, Matcher};

    use super::*;

    fn m(start: usize, end: usize) -> Match {
        Match::new(start, end)
    }

    #[test]
    fn empty_line1() {
        let haystack = b"";
        let matcher = EmptyLineMatcher::new(b'\n');

        assert_eq!(matcher.find_at(haystack, 0), Ok(Some(m(0, 0))));
    }

    #[test]
    fn empty_line2() {
        let haystack = b"\n";
        let matcher = EmptyLineMatcher::new(b'\n');

        assert_eq!(matcher.find_at(haystack, 0), Ok(Some(m(0, 0))));
        assert_eq!(matcher.find_at(haystack, 1), Ok(Some(m(1, 1))));
    }

    #[test]
    fn empty_line3() {
        let haystack = b"\n\n";
        let matcher = EmptyLineMatcher::new(b'\n');

        assert_eq!(matcher.find_at(haystack, 0), Ok(Some(m(0, 0))));
        assert_eq!(matcher.find_at(haystack, 1), Ok(Some(m(1, 1))));
        assert_eq!(matcher.find_at(haystack, 2), Ok(Some(m(2, 2))));
    }

    #[test]
    fn empty_line4() {
        let haystack = b"a\n\nb\n";
        let matcher = EmptyLineMatcher::new(b'\n');

        assert_eq!(matcher.find_at(haystack, 0), Ok(Some(m(2, 2))));
        assert_eq!(matcher.find_at(haystack, 1), Ok(Some(m(2, 2))));
        assert_eq!(matcher.find_at(haystack, 2), Ok(Some(m(2, 2))));
        assert_eq!(matcher.find_at(haystack, 3), Ok(Some(m(5, 5))));
        assert_eq!(matcher.find_at(haystack, 4), Ok(Some(m(5, 5))));
        assert_eq!(matcher.find_at(haystack, 5), Ok(Some(m(5, 5))));
    }

    #[test]
    fn empty_line5() {
        let haystack = b"a\n\nb\nc";
        let matcher = EmptyLineMatcher::new(b'\n');

        assert_eq!(matcher.find_at(haystack, 0), Ok(Some(m(2, 2))));
        assert_eq!(matcher.find_at(haystack, 1), Ok(Some(m(2, 2))));
        assert_eq!(matcher.find_at(haystack, 2), Ok(Some(m(2, 2))));
        assert_eq!(matcher.find_at(haystack, 3), Ok(None));
        assert_eq!(matcher.find_at(haystack, 4), Ok(None));
        assert_eq!(matcher.find_at(haystack, 5), Ok(None));
        assert_eq!(matcher.find_at(haystack, 6), Ok(None));
    }
}
