use std::borrow::Cow;
use std::cell::RefCell;
use std::fmt;
use std::io::{self, Write};
use std::path::Path;
use std::sync::Arc;
use std::time::Instant;

use grep2::{Searcher, Sink, SinkContext, SinkFinish, SinkMatch};
use grep_matcher::Matcher;
use termcolor::{ColorSpec, WriteColor};

use color::ColorSpecs;
use counter::CounterWriter;
use stats::Stats;

#[derive(Debug, Clone)]
struct Config {
    colors: ColorSpecs,
    separator_file: Arc<Option<Vec<u8>>>,
    separator_context: Arc<Option<Vec<u8>>>,
    separator_field_match: u8,
    separator_field_context: u8,
    separator_path: Option<u8>,
    path_terminator: Option<u8>,
    replacement: Arc<Option<Vec<u8>>>,
    max_columns: Option<u64>,
    max_matches: Option<u64>,
    column: bool,
    byte_offset: bool,
    heading: bool,
    line_per_match: bool,
    only_matching: bool,
    quiet: bool,
    stats: bool,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            colors: ColorSpecs::default(),
            separator_file: Arc::new(None),
            separator_context: Arc::new(Some(b"--".to_vec())),
            separator_field_match: b':',
            separator_field_context: b'-',
            separator_path: None,
            path_terminator: None,
            replacement: Arc::new(None),
            max_columns: None,
            max_matches: None,
            column: false,
            byte_offset: false,
            heading: false,
            line_per_match: false,
            only_matching: false,
            quiet: false,
            stats: false,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StandardBuilder {
    config: Config,
}

impl StandardBuilder {
    pub fn new() -> StandardBuilder {
        StandardBuilder { config: Config::default() }
    }

    pub fn build<'a, W: WriteColor>(
        &self,
        path: Option<&'a Path>,
        wtr: W,
    ) -> Standard<'a, W> {
        let stats =
            if self.config.stats {
                Some(Stats::new())
            } else {
                None
            };
        Standard {
            config: self.config.clone(),
            wtr: RefCell::new(CounterWriter::new(wtr)),
            start_time: Instant::now(),
            matched: false,
            binary_byte_offset: None,
            path: path.map(|p| {
                PrinterPath::with_separator(p, self.config.separator_path)
            }),
            stats: stats,
        }
    }

    /// Set the separator used between discontiguous runs of search context.
    ///
    /// The separator is always printed on its own line.
    ///
    /// If no separator is set, then nothing is printed when a context break
    /// occurs.
    pub fn separator_context(
        &mut self,
        sep: Option<Vec<u8>>,
    ) -> &mut StandardBuilder {
        self.config.separator_context = Arc::new(sep);
        self
    }

    /// Enable the gathering of various aggregate statistics.
    ///
    /// When this is enabled (it's disabled by default), statistics will be
    /// gathered on the subsequent search, including but not limited to, the
    /// total number of matches, the total number of bytes searched and the
    /// total number of bytes printed.
    ///
    /// When this is enabled, this printer may need to do extra work in order
    /// to compute certain statistics, which could cause the search to take
    /// long.
    ///
    /// For a complete description of available statistics, see
    /// [`Stats`](struct.Stats.html).
    pub fn stats(&mut self, yes: bool) -> &mut StandardBuilder {
        self.config.stats = yes;
        self
    }
}

#[derive(Debug)]
pub struct Standard<'a, W> {
    config: Config,
    wtr: RefCell<CounterWriter<W>>,
    start_time: Instant,
    matched: bool,
    binary_byte_offset: Option<u64>,
    path: Option<PrinterPath<'a>>,
    stats: Option<Stats>,
}

impl<'a, W: WriteColor> Standard<'a, W> {
    /// Returns true if and only if this printer received a match.
    pub fn matched(&self) -> bool {
        self.matched
    }

    /// If binary data was detected, this returns the offset at which the
    /// binary data was first detected.
    ///
    /// The offset returned is an absolute offset relative to the entire
    /// set of bytes searched.
    pub fn binary_byte_offset(&self) -> Option<u64> {
        self.binary_byte_offset
    }

    /// Return a mutable reference to the underlying writer.
    pub fn get_mut(&mut self) -> &mut W {
        self.wtr.get_mut().get_mut()
    }

    /// Return a reference to the stats produced by the printer, if they
    /// exist.
    pub fn stats(&self) -> Option<&Stats> {
        self.stats.as_ref()
    }
}

impl<'a, W: WriteColor> Sink for Standard<'a, W> {
    type Error = io::Error;

    fn matched<M>(
        &mut self,
        searcher: &Searcher<M>,
        mat: &SinkMatch,
    ) -> Result<bool, io::Error>
    where M: Matcher,
          M::Error: fmt::Display
    {
        self.matched = true;
        StandardImpl::new(searcher, self).matched(mat)
    }

    fn context<M>(
        &mut self,
        searcher: &Searcher<M>,
        context: &SinkContext,
    ) -> Result<bool, io::Error>
    where M: Matcher,
          M::Error: fmt::Display
    {
        StandardImpl::new(searcher, self).context(context)
    }

    fn context_break<M>(
        &mut self,
        searcher: &Searcher<M>,
    ) -> Result<bool, io::Error>
    where M: Matcher,
          M::Error: fmt::Display
    {
        StandardImpl::new(searcher, self).context_break()
    }

    fn finish<M>(
        &mut self,
        _searcher: &Searcher<M>,
        finish: &SinkFinish,
    ) -> Result<(), io::Error>
    where M: Matcher,
          M::Error: fmt::Display
    {
        self.binary_byte_offset = finish.binary_byte_offset();
        if let Some(stats) = self.stats.as_mut() {
            stats.add_elapsed(self.start_time.elapsed());
            stats.add_searches(1);
            if self.matched {
                stats.add_searches_with_match(1);
            }
            stats.add_bytes_searched(finish.byte_count());
            stats.add_bytes_printed(self.wtr.borrow().count());
        }
        Ok(())
    }
}

/// The actual implementation of the standard printer. This couples together
/// the configuration, the writer, the file path (if present) and the searcher.
/// Everything's in one convenient place.
#[derive(Debug)]
pub struct StandardImpl<'a, M: 'a, W: 'a> {
    searcher: &'a Searcher<M>,
    config: &'a Config,
    wtr: &'a RefCell<CounterWriter<W>>,
    path: Option<&'a PrinterPath<'a>>,
}

impl<'a, M, W> StandardImpl<'a, M, W>
where M: Matcher,
      M::Error: fmt::Display,
      W: WriteColor
{
    fn new<'unused>(
        searcher: &'a Searcher<M>,
        // The borrow checker can't seem to figure out what to do with
        // `Standard`'s lifetime here. It seems like it _should_ be OK in that
        // the lifetime should just shrink, but this is beyond my paygrade.
        // Interestingly, switching to a superfluous lifetime appeases the
        // compiler, but it's not clear why. Perhaps invariance is the culprit.
        printer: &'a mut Standard<'unused, W>,
    ) -> StandardImpl<'a, M, W> {
        StandardImpl {
            searcher: searcher,
            config: &printer.config,
            wtr: &printer.wtr,
            path: printer.path.as_ref(),
        }
    }

    fn matched(&self, mat: &SinkMatch) -> io::Result<bool> {
        if !self.needs_match_granularity() {
            self.matched_fast(mat)
        } else {
            Ok(true)
        }
    }

    /// Print matched lines quickly by avoiding the detection of each
    /// individual match in the lines reported in the given `SinkMatch`.
    ///
    /// This should only be used when the configuration does not demand match
    /// granularity.
    fn matched_fast(&self, mat: &SinkMatch) -> io::Result<bool> {
        debug_assert!(!self.needs_match_granularity());

        if self.path.is_some() {
            if self.config.heading {
                self.write_file_separator()?;
                self.write_path_line()?;
            } else {
                self.write_path_field(self.config.separator_field_match)?;
            }
        }
        if let Some(n) = mat.line_number() {
            self.write_line_number(n, self.config.separator_field_match)?;
        }
        if self.config.byte_offset {
            self.write_byte_offset(
                mat.absolute_byte_offset(),
                self.config.separator_field_match,
            )?;
        }
        if self.exceeds_max_columns(mat.bytes()) {
            self.write(b"[Omitted long matching line]")?;
            self.write_line_term()?;
        }
        self.write(mat.bytes())?;
        if !self.has_line_terminator(mat.bytes()) {
            self.write_line_term()?;
        }
        Ok(true)
    }

    fn context(&self, context: &SinkContext) -> io::Result<bool> {
        if self.path.is_some() {
            if self.config.heading {
                self.write_file_separator()?;
                self.write_path_line()?;
            } else {
                self.write_path_field(self.config.separator_field_context)?;
            }
        }
        if let Some(n) = context.line_number() {
            self.write_line_number(n, self.config.separator_field_context)?;
        }
        if self.config.byte_offset {
            self.write_byte_offset(
                context.absolute_byte_offset(),
                self.config.separator_field_context,
            )?;
        }
        if self.exceeds_max_columns(context.bytes()) {
            self.write(b"[Omitted long context line]")?;
            self.write_line_term()?;
        }
        self.write(context.bytes())?;
        if !self.has_line_terminator(context.bytes()) {
            self.write_line_term()?;
        }
        // TODO: Highlight matches if search is inverted and colors are
        // enabled.
        Ok(true)
    }

    fn context_break(&self) -> io::Result<bool> {
        if let Some(ref sep) = *self.config.separator_context {
            self.write(sep)?;
            self.write_line_term()?;
        }
        Ok(true)
    }

    /// If this printer has a file path associated with it, then this will
    /// write that path to the underlying writer followed by a line terminator.
    /// (If a path terminator is set, then that is used instead of the line
    /// terminator.)
    fn write_path_line(&self) -> io::Result<()> {
        if let Some(path) = self.path {
            self.write_spec(self.config.colors.path(), path.as_bytes())?;
            if let Some(term) = self.config.path_terminator {
                self.write(&[term])?;
            } else {
                self.write_line_term()?;
            }
        }
        Ok(())
    }

    /// If this printer has a file path associated with it, then this will
    /// write that path to the underlying writer followed by the given field
    /// separator. (If a path terminator is set, then that is used instead of
    /// the field separator.)
    fn write_path_field(&self, field_separator: u8) -> io::Result<()> {
        if let Some(path) = self.path {
            self.write_spec(self.config.colors.path(), path.as_bytes())?;
            if let Some(term) = self.config.path_terminator {
                self.write(&[term])?;
            } else {
                self.write(&[field_separator])?;
            }
        }
        Ok(())
    }

    fn write_file_separator(&self) -> io::Result<()> {
        if !self.has_written() {
            if let Some(ref sep) = *self.config.separator_file {
                self.write(sep)?;
                self.write_line_term()?;
            }
        }
        Ok(())
    }

    fn write_line_number(
        &self,
        line_number: u64,
        field_separator: u8,
    ) -> io::Result<()> {
        let n = line_number.to_string();
        self.write_spec(self.config.colors.line(), n.as_bytes())?;
        self.write(&[field_separator])?;
        Ok(())
    }

    fn write_column_number(
        &self,
        column_number: u64,
        field_separator: u8,
    ) -> io::Result<()> {
        let n = column_number.to_string();
        self.write_spec(self.config.colors.column(), n.as_bytes())?;
        self.write(&[field_separator])?;
        Ok(())
    }

    fn write_byte_offset(
        &self,
        offset: u64,
        field_separator: u8,
    ) -> io::Result<()> {
        let n = offset.to_string();
        self.write_spec(self.config.colors.column(), n.as_bytes())?;
        self.write(&[field_separator])?;
        Ok(())
    }

    fn write_line_term(&self) -> io::Result<()> {
        self.write(&[self.searcher.line_terminator()])
    }

    fn write_spec(&self, spec: &ColorSpec, buf: &[u8]) -> io::Result<()> {
        let mut wtr = self.wtr.borrow_mut();
        wtr.set_color(spec)?;
        wtr.write_all(buf)?;
        wtr.reset()?;
        Ok(())
    }

    fn write(&self, buf: &[u8]) -> io::Result<()> {
        self.wtr.borrow_mut().write_all(buf)
    }

    fn has_written(&self) -> bool {
        self.wtr.borrow().count() > 0
    }

    fn has_line_terminator(&self, buf: &[u8]) -> bool {
        buf.last() == Some(&self.searcher.line_terminator())
    }

    /// Returns true if and only if the configuration of the printer requires
    /// us to find each individual match in the lines reported by the searcher.
    ///
    /// We care about this distinction because finding each individual match
    /// costs more.
    fn needs_match_granularity(&self) -> bool {
        !self.config.colors.matched.is_none()
        || self.config.column
        || self.config.replacement.is_some()
        || self.config.line_per_match
        || self.config.only_matching
        || self.config.stats
    }

    /// Returns true if and only if the given line exceeds the maximum number
    /// of columns set. If no maximum is set, then this always returns false.
    fn exceeds_max_columns(&self, line: &[u8]) -> bool {
        self.config.max_columns.map_or(false, |m| line.len() as u64 > m)
    }
}

/// A simple encapsulation of a file path used by the printer.
///
/// This represents any transforms that we might want to perform on the path,
/// such as converting it to valid UTF-8 and/or replacing its separator with
/// something else. This allows us to amortize work if we are printing the
/// file path for every match.
///
/// In the common case, no transformation is needed, which lets us avoid the
/// allocation. Typically, only Windows requires a transform, since we can't
/// access the raw bytes of a path directly and first need to lossily convert
/// to UTF-8. Windows is also typically where the path separator replacement
/// is used, e.g., in cygwin environments to use `/` instead of `\`.
#[derive(Clone, Debug)]
struct PrinterPath<'a>(Cow<'a, [u8]>);

impl<'a> PrinterPath<'a> {
    /// Create a new printer path from the given path which can be efficiently
    /// written to a writer without allocation.
    ///
    /// If the given separator is present, then any separators in `path` are
    /// replaced with it.
    fn with_separator(path: &'a Path, sep: Option<u8>) -> PrinterPath<'a> {
        let mut ppath = PrinterPath::new(path);
        if let Some(sep) = sep {
            ppath.replace_separator(sep);
        }
        ppath
    }

    #[cfg(unix)]
    fn new(path: &'a Path) -> PrinterPath<'a> {
        use std::os::unix::ffi::OsStrExt;
        PrinterPath(Cow::Borrowed(path.as_os_str().as_bytes()))
    }

    #[cfg(not(unix))]
    fn new(path: &'a Path) -> PrinterPath<'a> {
        let path = path.to_string_lossy();
        PrinterPath(Cow::Owned(path.into_bytes()))
    }

    /// Replace the path separator in this path with the given separator
    /// and do it in place. On Windows, both `/` and `\` are treated as
    /// path separators that are both replaced by `new_sep`. In all other
    /// environments, only `/` is treated as a path separator.
    fn replace_separator(&mut self, new_sep: u8) {
        let transformed_path: Vec<_> = self.as_bytes().iter().map(|&b| {
            if b == b'/' || (cfg!(windows) && b == b'\\') {
                new_sep
            } else {
                b
            }
        }).collect();
        self.0 = Cow::Owned(transformed_path);
    }

    fn as_bytes(&self) -> &[u8] {
        &*self.0
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use grep2::SearcherBuilder;
    use grep_regex::RegexMatcher;
    use termcolor::{NoColor, WriteColor};

    use stats::Stats;
    use super::{Standard, StandardBuilder};

    const SHERLOCK: &'static str = "\
For the Doctor Watsons of this world, as opposed to the Sherlock
Holmeses, success in the province of detective work must always
be, to a very large extent, the result of luck. Sherlock Holmes
can extract a clew from a wisp of straw or a flake of cigar ash;
but Doctor Watson has to have it taken out for him and dusted,
and exhibited clearly, with a label attached.\
";

    fn search<'a>(
        mut printer: &mut Standard<'a, NoColor<Vec<u8>>>,
        pattern: &str,
        haystack: &str,
    ) -> String {
        let matcher = RegexMatcher::new(pattern).unwrap();
        SearcherBuilder::new()
            .build(&matcher)
            .unwrap()
            .search_reader(haystack.as_bytes(), &mut printer)
            .unwrap();
        printer_contents(printer)
    }

    fn printer_contents<'a>(
        printer: &mut Standard<'a, NoColor<Vec<u8>>>,
    ) -> String {
        String::from_utf8(printer.get_mut().get_ref().to_owned()).unwrap()
    }

    #[test]
    fn scratch() {
        let mut printer = StandardBuilder::new()
            .build(Some(Path::new("sherlock")), NoColor::new(vec![]));
        SearcherBuilder::new()
            .after_context(1)
            .line_number(true)
            .build(RegexMatcher::new("Sherlock").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();
        let got = printer_contents(&mut printer);

        println!("{}", got);
    }

    #[test]
    fn reports_match() {
        let mut printer = StandardBuilder::new()
            .build(None, NoColor::new(vec![]));
        search(&mut printer, "Sherlock", SHERLOCK);
        assert!(printer.matched());

        let mut printer = StandardBuilder::new()
            .build(None, NoColor::new(vec![]));
        search(&mut printer, "zzzz", SHERLOCK);
        assert!(!printer.matched());
    }

    #[test]
    fn reports_binary() {
        use grep2::BinaryDetection;

        let mut printer = StandardBuilder::new()
            .build(None, NoColor::new(vec![]));
        search(&mut printer, "Sherlock", SHERLOCK);
        assert!(printer.binary_byte_offset().is_none());

        let mut printer = StandardBuilder::new()
            .build(None, NoColor::new(vec![]));
        SearcherBuilder::new()
            .binary_detection(BinaryDetection::quit(b'\x00'))
            .build(RegexMatcher::new(".+").unwrap())
            .unwrap()
            .search_reader(&b"abc\x00"[..], &mut printer)
            .unwrap();
        assert_eq!(printer.binary_byte_offset(), Some(3));
    }

    #[test]
    fn reports_stats() {
        use std::time::Duration;

        let mut printer = StandardBuilder::new()
            .stats(true)
            .build(None, NoColor::new(vec![]));
        let buf = search(&mut printer, "Sherlock|opposed", SHERLOCK);

        let stats = printer.stats().unwrap();
        assert!(stats.elapsed() > Duration::default());
        assert_eq!(stats.searches(), 1);
        assert_eq!(stats.searches_with_match(), 1);
        assert_eq!(stats.bytes_searched(), SHERLOCK.len() as u64);
        assert_eq!(stats.bytes_printed(), buf.len() as u64);
        // TODO:
        // assert_eq!(stats.matched_lines(), 2);
        // assert_eq!(stats.matches(), 3);
    }

    #[test]
    fn context_break() {
        let mut printer = StandardBuilder::new()
            .separator_context(Some(b"--abc--".to_vec()))
            .build(None, NoColor::new(vec![]));
        SearcherBuilder::new()
            .before_context(1)
            .after_context(1)
            .build(RegexMatcher::new("Watson").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
For the Doctor Watsons of this world, as opposed to the Sherlock
Holmeses, success in the province of detective work must always
--abc--
can extract a clew from a wisp of straw or a flake of cigar ash;
but Doctor Watson has to have it taken out for him and dusted,
and exhibited clearly, with a label attached.
";
        assert_eq!(expected, got);
    }
}
