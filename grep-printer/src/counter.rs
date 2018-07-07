use std::io::{self, Write};

use termcolor::{ColorSpec, WriteColor};

/// A writer that counts the number of bytes that have been successfully
/// written.
#[derive(Clone, Debug)]
pub struct CounterWriter<W> {
    wtr: W,
    count: u64,
}

impl<W: Write> CounterWriter<W> {
    pub fn new(wtr: W) -> CounterWriter<W> {
        CounterWriter { wtr: wtr, count: 0 }
    }

    pub fn count(&self) -> u64 {
        self.count
    }

    pub fn get_ref(&self) -> &W {
        &self.wtr
    }

    pub fn get_mut(&mut self) -> &mut W {
        &mut self.wtr
    }

    pub fn into_inner(self) -> W {
        self.wtr
    }
}

impl<W: Write> Write for CounterWriter<W> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, io::Error> {
        let n = self.wtr.write(buf)?;
        self.count += n as u64;
        Ok(n)
    }

    fn flush(&mut self) -> Result<(), io::Error> {
        self.wtr.flush()
    }
}

impl<W: WriteColor> WriteColor for CounterWriter<W> {
    fn supports_color(&self) -> bool {
        self.wtr.supports_color()
    }

    fn set_color(&mut self, spec: &ColorSpec) -> io::Result<()> {
        self.wtr.set_color(spec)
    }

    fn reset(&mut self) -> io::Result<()> {
        self.wtr.reset()
    }

    fn is_synchronous(&self) -> bool {
        self.wtr.is_synchronous()
    }
}
