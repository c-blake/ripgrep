use std::fmt;
use std::io::{self, Write};
use std::str;

use matcher::{Matcher, NoCaptures};
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
}

impl SubstringMatcher {
    /// Create a new substring matcher.
    pub fn new(pattern: &str) -> SubstringMatcher {
        SubstringMatcher {
            pattern: pattern.to_string(),
            line_term: if pattern.contains('\n') { Some(b'\n') } else { None },
        }
    }
}

impl Matcher for SubstringMatcher {
    type Captures = NoCaptures;
    type Error = str::Utf8Error;

    fn find_at(
        &self,
        haystack: &[u8],
        at: usize,
    ) -> Result<Option<(usize, usize)>, str::Utf8Error> {
        let slice = str::from_utf8(haystack)?;
        Ok(slice[at..].find(&self.pattern).map(|i| {
            (at + i, at + i + self.pattern.len())
        }))
    }

    fn new_captures(&self) -> Result<NoCaptures, str::Utf8Error> {
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
        writeln!(self.0, "lines matched:{}", sink_finish.lines_matched)?;
        Ok(())
    }
}
