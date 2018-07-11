use std::borrow::Cow;
use std::cell::RefCell;
use std::fmt;
use std::io::{self, Write};
use std::path::Path;
use std::sync::Arc;
use std::time::Instant;

use grep2::{
    Searcher,
    Sink, SinkContext, SinkContextKind, SinkFinish, SinkMatch,
};
use grep_matcher::Matcher;
use termcolor::{ColorSpec, WriteColor};

use color::{ColorSpecs, UserColorSpec};
use counter::CounterWriter;
use stats::Stats;

#[derive(Debug, Clone)]
struct Config {
    colors: ColorSpecs,
    stats: bool,
    heading: bool,
    only_matching: bool,
    line_per_match: bool,
    replacement: Arc<Option<Vec<u8>>>,
    max_columns: Option<u64>,
    max_matches: Option<u64>,
    column: bool,
    byte_offset: bool,
    separator_context: Arc<Option<Vec<u8>>>,
    separator_field_match: Arc<Vec<u8>>,
    separator_field_context: Arc<Vec<u8>>,
    separator_path: Option<u8>,
    path_terminator: Option<u8>,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            colors: ColorSpecs::default(),
            stats: false,
            heading: false,
            only_matching: false,
            line_per_match: false,
            replacement: Arc::new(None),
            max_columns: None,
            max_matches: None,
            column: false,
            byte_offset: false,
            separator_context: Arc::new(Some(b"--".to_vec())),
            separator_field_match: Arc::new(b":".to_vec()),
            separator_field_context: Arc::new(b"-".to_vec()),
            separator_path: None,
            path_terminator: None,
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
            match_count: 0,
            after_context_remaining: 0,
            binary_byte_offset: None,
            path: path.map(|p| {
                PrinterPath::with_separator(p, self.config.separator_path)
            }),
            stats: stats,
        }
    }

    /// Set the user color specifications to use for coloring in this printer.
    ///
    /// A [`UserColorSpec`](struct.UserColorSpec.html) can be constructed from
    /// a string in accordance with the color specification format. See the
    /// `UserColorSpec` type documentation for more details on the format.
    ///
    /// Regardless of the color specifications provided here, whether color
    /// is actually used or not is determined by the implementation of
    /// `WriteColor` provided to `build`. For example, if `termcolor::NoColor`
    /// is provided to `build`, then no color will ever be printed regardless
    /// of the color specifications provided here.
    ///
    /// This completely overrides any previous color specifications. This does
    /// not add to any previously provided color specifications on this
    /// builder.
    pub fn user_color_specs(
        &mut self,
        specs: &[UserColorSpec],
    ) -> &mut StandardBuilder {
        self.config.colors = ColorSpecs::new(specs);
        self
    }

    /// Enable the gathering of various aggregate statistics.
    ///
    /// When this is enabled (it's disabled by default), statistics will be
    /// gathered on the subsequent search, including but not limited to, the
    /// total number of matches, the total number of bytes searched and the
    /// total number of bytes printed.
    ///
    /// Aggregate statistics can be accessed via the printer's
    /// [`Standard::build`](struct.Standard.html#method.stats)
    /// method.
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

    /// Enable the use of "headings" in the printer.
    ///
    /// When this is enabled, and if a file path has been given to the printer,
    /// then the file path will be printed once on its own line before showing
    /// any matches. If the heading is not the first thing emitted by the
    /// printer, then a line terminator is printed before the heading.
    ///
    /// By default, this option is disabled. When disabled, the printer will
    /// not show any heading and will instead print the file path (if one is
    /// given) on the same line as each matching (or context) line.
    pub fn heading(&mut self, yes: bool) -> &mut StandardBuilder {
        self.config.heading = yes;
        self
    }

    /// Only print the specific matches instead of the entire line containing
    /// each match. Each match is printed on its own line. When multi line
    /// search is enabled, then matches spanning multiple lines are printed
    /// such that only the matching portions of each line are shown.
    pub fn only_matching(&mut self, yes: bool) -> &mut StandardBuilder {
        self.config.only_matching = yes;
        self
    }

    /// Print a line for every match shown.
    ///
    /// This is similar to the `only_matching` option, except the entire line
    /// is printed for each match. This is typically useful in conjunction with
    /// the `column` option, which will show the starting column number for
    /// every match on every line.
    ///
    /// This option has no effect when multi line search is enabled, even if
    /// the searcher only reports matches that span at most one line.
    pub fn line_per_match(&mut self, yes: bool) -> &mut StandardBuilder {
        self.config.line_per_match = yes;
        self
    }

    /// Set the bytes that will be used to replace each occurrence of a match
    /// found.
    ///
    /// The replacement bytes given may include references to capturing groups,
    /// which may either be in index form (e.g., `$2`) or can reference named
    /// capturing groups if present in the original pattern (e.g., `$foo`).
    ///
    /// For documentation on the full format, please see the `Matcher` trait's
    /// `interpolate` method.
    pub fn replacement(
        &mut self,
        replacement: Option<Vec<u8>>,
    ) -> &mut StandardBuilder {
        self.config.replacement = Arc::new(replacement);
        self
    }

    /// Set the maximum number of columns allowed for each line printed. A
    /// single column is heuristically defined as a single byte.
    ///
    /// If a line is found which exceeds this maximum, then it is replaced
    /// with a message indicating that the line has been omitted.
    ///
    /// The default is to not specify a limit, in which each matching or
    /// contextual line is printed regardless of how long it is.
    pub fn max_columns(&mut self, limit: Option<u64>) -> &mut StandardBuilder {
        self.config.max_columns = limit;
        self
    }

    /// Set the maximum amount of matching lines that are printed.
    ///
    /// If multi line search is enabled and a match spans multiple lines, then
    /// that match is counted exactly one for the purposes of enforcing this
    /// limit, regardless of how many lines it spans.
    pub fn max_matches(&mut self, limit: Option<u64>) -> &mut StandardBuilder {
        self.config.max_matches = limit;
        self
    }

    /// Print the column number of the first match in a line.
    ///
    /// This option is convenient for use with `line_per_match` which will
    /// print a line for every match along with the starting offset for that
    /// match.
    ///
    /// Column numbers are computed in terms of bytes from the start of the
    /// line being printed.
    ///
    /// When multi line search is enabled, this option has no effect.
    ///
    /// This is disabled by default.
    pub fn column(&mut self, yes: bool) -> &mut StandardBuilder {
        self.config.column = yes;
        self
    }

    /// Print the absolute byte offset of the beginning of each line printed.
    ///
    /// The absolute byte offset starts from the beginning of each search and
    /// is zero based.
    ///
    /// If the `only_matching` option is set, then this will print the absolute
    /// byte offset of the beginning of each match.
    pub fn byte_offset(&mut self, yes: bool) -> &mut StandardBuilder {
        self.config.byte_offset = yes;
        self
    }

    /// Set the separator used between discontiguous runs of search context
    /// and between matches from different files, but only when the searcher
    /// is configured to report contextual lines.
    ///
    /// The separator is always printed on its own line.
    ///
    /// If no separator is set, then nothing is printed when a context break
    /// occurs.
    ///
    /// By default, this is set to `--`.
    pub fn separator_context(
        &mut self,
        sep: Option<Vec<u8>>,
    ) -> &mut StandardBuilder {
        self.config.separator_context = Arc::new(sep);
        self
    }

    /// Set the separator used between fields emitted for matching lines.
    ///
    /// For example, when the searcher has line numbers enabled, this printer
    /// will print the line number before each matching line. The bytes given
    /// here will be written after the line number but before the matching
    /// line.
    ///
    /// By default, this is set to `:`.
    pub fn separator_field_match(
        &mut self,
        sep: Vec<u8>,
    ) -> &mut StandardBuilder {
        self.config.separator_field_match = Arc::new(sep);
        self
    }

    /// Set the separator used between fields emitted for context lines.
    ///
    /// For example, when the searcher has line numbers enabled, this printer
    /// will print the line number before each context line. The bytes given
    /// here will be written after the line number but before the context
    /// line.
    ///
    /// By default, this is set to `-`.
    pub fn separator_field_context(
        &mut self,
        sep: Vec<u8>,
    ) -> &mut StandardBuilder {
        self.config.separator_field_context = Arc::new(sep);
        self
    }

    /// Set the path separator used when printing file paths.
    ///
    /// When a printer is configured with a file path, and when a match is
    /// found, that file path will be printed (either as a heading or as a
    /// prefix to each matching or contextual line, depending on other
    /// configuration settings). Typically, printing is done by emitting the
    /// file path as is. However, this setting provides the ability to use a
    /// different path separator from what the current environment has
    /// configured.
    ///
    /// A typical use for this option is to permit cygwin users on Windows to
    /// set the path separator to `/` instead of using the system default of
    /// `\`.
    pub fn separator_path(
        &mut self,
        sep: Option<u8>,
    ) -> &mut StandardBuilder {
        self.config.separator_path = sep;
        self
    }

    /// Set the path terminator used.
    ///
    /// The path terminator is a byte that is printed after every file path
    /// emitted by this printer.
    ///
    /// If no path terminator is set (the default), then paths are terminated
    /// by either new lines (for when `heading` is enabled) or the match or
    /// context field separators (e.g., `:` or `-`).
    pub fn path_terminator(
        &mut self,
        terminator: Option<u8>,
    ) -> &mut StandardBuilder {
        self.config.path_terminator = terminator;
        self
    }
}

#[derive(Debug)]
pub struct Standard<'a, W> {
    config: Config,
    wtr: RefCell<CounterWriter<W>>,
    start_time: Instant,
    match_count: u64,
    after_context_remaining: u64,
    binary_byte_offset: Option<u64>,
    path: Option<PrinterPath<'a>>,
    stats: Option<Stats>,
}

impl<'a, W: WriteColor> Standard<'a, W> {
    /// Set the path on this printer to the path provided.
    ///
    /// When a printer is associated with a path, then it may, depending on
    /// its configuration, print the path along with the matches found.
    ///
    /// While this will not reset the state of aggregate statistics (if
    /// enabled), this will reset other search oriented state such as whether
    /// the printer matched and the first offset at which binary data has been
    /// detected.
    pub fn with_path<'p>(
        self,
        path: &'p Path,
    ) -> Standard<'p, W> {
        Standard {
            path: Some(PrinterPath::with_separator(
                path, self.config.separator_path)),
            ..self.without_path()
        }
    }

    /// Disassociate this printer with any path.
    ///
    /// Since this disassociates a file path from the printer it is impossible
    /// for the printer to emit a file path.
    pub fn without_path(self) -> Standard<'static, W> {
        Standard {
            config: self.config,
            wtr: self.wtr,
            start_time: self.start_time,
            match_count: self.match_count,
            after_context_remaining: self.after_context_remaining,
            binary_byte_offset: self.binary_byte_offset,
            path: None,
            stats: self.stats,
        }
    }

    /// Returns true if and only if this printer received a match in the
    /// previous search.
    ///
    /// This is unaffected by the result of searches before the previous
    /// search.
    pub fn has_match(&self) -> bool {
        self.match_count > 0
    }

    /// If binary data was found in the previous search, this returns the
    /// offset at which the binary data was first detected.
    ///
    /// The offset returned is an absolute offset relative to the entire
    /// set of bytes searched.
    ///
    /// This is unaffected by the result of searches before the previous
    /// search. e.g., If the search prior to the previous search found binary
    /// data but the previous search found no binary data, then this will
    /// return `None`.
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
        self.match_count += 1;
        self.after_context_remaining = searcher.after_context() as u64;

        let imp = StandardImpl::new(searcher, self);
        if !imp.matched(mat)? || imp.should_quit() {
            return Ok(false);
        }
        Ok(true)
    }

    fn context<M>(
        &mut self,
        searcher: &Searcher<M>,
        context: &SinkContext,
    ) -> Result<bool, io::Error>
    where M: Matcher,
          M::Error: fmt::Display
    {
        if context.kind() == &SinkContextKind::After {
            self.after_context_remaining =
                self.after_context_remaining.saturating_sub(1);
        }
        let imp = StandardImpl::new(searcher, self);
        if !imp.context(context)? || imp.should_quit() {
            return Ok(false);
        }
        Ok(true)
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

    fn begin<M>(
        &mut self,
        searcher: &Searcher<M>,
    ) -> Result<bool, io::Error>
    where M: Matcher,
          M::Error: fmt::Display
    {
        self.wtr.borrow_mut().reset_count();
        self.start_time = Instant::now();
        self.match_count = 0;
        self.after_context_remaining = 0;
        self.binary_byte_offset = None;
        if self.config.max_matches == Some(0) {
            return Ok(false);
        }

        StandardImpl::new(searcher, self).begin()?;
        Ok(true)
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
            if self.match_count > 0 {
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
    match_count: u64,
    after_context_remaining: u64,
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
            match_count: printer.match_count,
            after_context_remaining: printer.after_context_remaining,
            path: printer.path.as_ref(),
        }
    }

    fn matched(&self, mat: &SinkMatch) -> io::Result<bool> {
        if !self.needs_match_granularity() {
            if self.searcher.multi_line() {
                self.matched_fast_multi_line(mat)
            } else {
                self.matched_fast(mat)
            }
        } else {
            Ok(true)
        }
    }

    /// Print matches (limited to one line) quickly by avoiding the detection
    /// of each individual match in the lines reported in the given
    /// `SinkMatch`.
    ///
    /// This should only be used when the configuration does not demand match
    /// granularity and the searcher is not in multi line mode.
    fn matched_fast(&self, mat: &SinkMatch) -> io::Result<bool> {
        debug_assert!(!self.needs_match_granularity());
        debug_assert!(!self.searcher.multi_line());

        if !self.config.heading {
            self.write_path_field(&self.config.separator_field_match)?;
        }
        if let Some(n) = mat.line_number() {
            self.write_line_number(n, &self.config.separator_field_match)?;
        }
        if self.config.byte_offset {
            self.write_byte_offset(
                mat.absolute_byte_offset(),
                &self.config.separator_field_match,
            )?;
        }
        if self.exceeds_max_columns(mat.bytes()) {
            self.write(b"[Omitted long matching line]")?;
            self.write_line_term()?;
            return Ok(true);
        }
        self.write(mat.bytes())?;
        if !self.has_line_terminator(mat.bytes()) {
            self.write_line_term()?;
        }
        Ok(true)
    }

    /// Print matches (possibly spanning more than one line) quickly by
    /// avoiding the detection of each individual match in the lines reported
    /// in the given `SinkMatch`.
    ///
    /// This should only be used when the configuration does not demand match
    /// granularity. This may be used when the searcher is in multi line mode.
    fn matched_fast_multi_line(&self, mat: &SinkMatch) -> io::Result<bool> {
        debug_assert!(!self.needs_match_granularity());
        // This isn't actually a required invariant for using this method,
        // but if we wind up here and multi line mode is disabled, then we
        // should still treat it as a bug since we should be using matched_fast
        // instead.
        debug_assert!(self.searcher.multi_line());

        let mut absolute_byte_offset = mat.absolute_byte_offset();
        for (i, line) in mat.lines().enumerate() {
            if !self.config.heading {
                self.write_path_field(&self.config.separator_field_match)?;
            }
            if let Some(n) = mat.line_number() {
                self.write_line_number(
                    n + i as u64,
                    &self.config.separator_field_match,
                )?;
            }
            if self.config.byte_offset {
                self.write_byte_offset(
                    absolute_byte_offset,
                    &self.config.separator_field_match,
                )?;
            }
            if self.exceeds_max_columns(line) {
                self.write(b"[Omitted long matching line]")?;
                self.write_line_term()?;
            } else {
                self.write(line)?;
            }
            absolute_byte_offset += line.len() as u64;
        }
        if !self.has_line_terminator(mat.bytes()) {
            self.write_line_term()?;
        }
        Ok(true)
    }

    fn context(&self, context: &SinkContext) -> io::Result<bool> {
        if !self.config.heading {
            self.write_path_field(&self.config.separator_field_context)?;
        }
        if let Some(n) = context.line_number() {
            self.write_line_number(n, &self.config.separator_field_context)?;
        }
        if self.config.byte_offset {
            self.write_byte_offset(
                context.absolute_byte_offset(),
                &self.config.separator_field_context,
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
        self.write_context_separator()?;
        Ok(true)
    }

    fn begin(&self) -> io::Result<()> {
        self.write_file_separator()?;
        if self.config.heading {
            self.write_path_line()?;
        }
        Ok(())
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
    fn write_path_field(&self, field_separator: &[u8]) -> io::Result<()> {
        if let Some(path) = self.path {
            self.write_spec(self.config.colors.path(), path.as_bytes())?;
            if let Some(term) = self.config.path_terminator {
                self.write(&[term])?;
            } else {
                self.write(field_separator)?;
            }
        }
        Ok(())
    }

    fn write_file_separator(&self) -> io::Result<()> {
        if !self.has_written() {
            return Ok(());
        }
        if self.config.heading {
            self.write_line_term()
        } else if self.has_context() {
            self.write_context_separator()
        } else {
            Ok(())
        }
    }

    fn write_context_separator(&self) -> io::Result<()> {
        if let Some(ref sep) = *self.config.separator_context {
            self.write(sep)?;
            self.write_line_term()?;
        }
        Ok(())
    }

    fn write_line_number(
        &self,
        line_number: u64,
        field_separator: &[u8],
    ) -> io::Result<()> {
        let n = line_number.to_string();
        self.write_spec(self.config.colors.line(), n.as_bytes())?;
        self.write(field_separator)?;
        Ok(())
    }

    fn write_column_number(
        &self,
        column_number: u64,
        field_separator: &[u8],
    ) -> io::Result<()> {
        let n = column_number.to_string();
        self.write_spec(self.config.colors.column(), n.as_bytes())?;
        self.write(field_separator)?;
        Ok(())
    }

    fn write_byte_offset(
        &self,
        offset: u64,
        field_separator: &[u8],
    ) -> io::Result<()> {
        let n = offset.to_string();
        self.write_spec(self.config.colors.column(), n.as_bytes())?;
        self.write(field_separator)?;
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
        self.wtr.borrow().total_count() > 0
    }

    fn has_line_terminator(&self, buf: &[u8]) -> bool {
        buf.last() == Some(&self.searcher.line_terminator())
    }

    fn has_context(&self) -> bool {
        self.searcher.before_context() > 0 || self.searcher.after_context() > 0
    }

    /// Returns true if and only if the configuration of the printer requires
    /// us to find each individual match in the lines reported by the searcher.
    ///
    /// We care about this distinction because finding each individual match
    /// costs more.
    fn needs_match_granularity(&self) -> bool {
        let multi_line = self.searcher.multi_line();
        let supports_color = self.wtr.borrow().supports_color();
        let match_colored = !self.config.colors.matched.is_none();

        // Coloring requires identifying each individual match.
        (supports_color && match_colored)
        // The column feature requires finding the position of the first match.
        || (!multi_line && self.config.column)
        // Requires finding each match for performing replacement.
        || self.config.replacement.is_some()
        // Emitting a line for each match requires finding each match.
        || (!multi_line && self.config.line_per_match)
        // Emitting only the match requires finding each match.
        || self.config.only_matching
        // Computing certain statistics requires finding each match.
        || self.config.stats
        // Imposing a limit on matched lines generally doesn't require finding
        // each individual match, but when multi line mode is enabled, we
        // can't assume that each match is one line, nor can we assume that
        // each `SinkMatch` contains exactly one match, so we must go out and
        // find each individual match.
        || (multi_line && self.config.max_matches.is_some())
    }

    /// Returns true if and only if the given line exceeds the maximum number
    /// of columns set. If no maximum is set, then this always returns false.
    fn exceeds_max_columns(&self, line: &[u8]) -> bool {
        self.config.max_columns.map_or(false, |m| line.len() as u64 > m)
    }

    /// Returns true if this printer should quit.
    ///
    /// This implements the logic for handling quitting after seeing a certain
    /// amount of matches. In most cases, the logic is simple, but we must
    /// permits all "after" contextual lines to print after reaching the limit.
    fn should_quit(&self) -> bool {
        let limit = match self.config.max_matches {
            None => return false,
            Some(limit) => limit,
        };
        if self.match_count < limit {
            return false;
        }
        self.after_context_remaining == 0
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
        SearcherBuilder::new()
            .build(RegexMatcher::new("Sherlock").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();
        assert!(printer.has_match());

        let mut printer = StandardBuilder::new()
            .build(None, NoColor::new(vec![]));
        SearcherBuilder::new()
            .build(RegexMatcher::new("zzzzz").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();
        assert!(!printer.has_match());
    }

    #[test]
    fn reports_binary() {
        use grep2::BinaryDetection;

        let mut printer = StandardBuilder::new()
            .build(None, NoColor::new(vec![]));
        SearcherBuilder::new()
            .build(RegexMatcher::new("Sherlock").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();
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
        SearcherBuilder::new()
            .build(RegexMatcher::new("Sherlock|opposed").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();
        let buf = printer_contents(&mut printer);

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
    fn reports_stats_multiple() {
        use std::time::Duration;

        let mut printer = StandardBuilder::new()
            .stats(true)
            .build(None, NoColor::new(vec![]));
        SearcherBuilder::new()
            .build(RegexMatcher::new("Sherlock|opposed").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();
        SearcherBuilder::new()
            .build(RegexMatcher::new("zzzzzzzzz").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();
        SearcherBuilder::new()
            .build(RegexMatcher::new("Sherlock|opposed").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();
        let buf = printer_contents(&mut printer);

        let stats = printer.stats().unwrap();
        assert!(stats.elapsed() > Duration::default());
        assert_eq!(stats.searches(), 3);
        assert_eq!(stats.searches_with_match(), 2);
        assert_eq!(stats.bytes_searched(), 3 * SHERLOCK.len() as u64);
        assert_eq!(stats.bytes_printed(), 2 * buf.len() as u64);
        // TODO:
        // assert_eq!(stats.matched_lines(), 4);
        // assert_eq!(stats.matches(), 6);
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
        assert_eq_printed!(expected, got);
    }

    #[test]
    fn context_break_multiple_no_heading() {
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
        SearcherBuilder::new()
            .before_context(1)
            .after_context(1)
            .build(RegexMatcher::new("Sherlock").unwrap())
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
--abc--
For the Doctor Watsons of this world, as opposed to the Sherlock
Holmeses, success in the province of detective work must always
be, to a very large extent, the result of luck. Sherlock Holmes
can extract a clew from a wisp of straw or a flake of cigar ash;
";
        assert_eq_printed!(expected, got);
    }

    #[test]
    fn context_break_multiple_heading() {
        let mut printer = StandardBuilder::new()
            .heading(true)
            .separator_context(Some(b"--abc--".to_vec()))
            .build(None, NoColor::new(vec![]));

        SearcherBuilder::new()
            .before_context(1)
            .after_context(1)
            .build(RegexMatcher::new("Watson").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();
        SearcherBuilder::new()
            .before_context(1)
            .after_context(1)
            .build(RegexMatcher::new("Sherlock").unwrap())
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

For the Doctor Watsons of this world, as opposed to the Sherlock
Holmeses, success in the province of detective work must always
be, to a very large extent, the result of luck. Sherlock Holmes
can extract a clew from a wisp of straw or a flake of cigar ash;
";
        assert_eq_printed!(expected, got);
    }

    #[test]
    fn separator_field() {
        let mut printer = StandardBuilder::new()
            .separator_field_match(b"!!".to_vec())
            .separator_field_context(b"^^".to_vec())
            .build(Some(Path::new("sherlock")), NoColor::new(vec![]));
        SearcherBuilder::new()
            .before_context(1)
            .after_context(1)
            .build(RegexMatcher::new("Watson").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
sherlock!!For the Doctor Watsons of this world, as opposed to the Sherlock
sherlock^^Holmeses, success in the province of detective work must always
--
sherlock^^can extract a clew from a wisp of straw or a flake of cigar ash;
sherlock!!but Doctor Watson has to have it taken out for him and dusted,
sherlock^^and exhibited clearly, with a label attached.
";
        assert_eq_printed!(expected, got);
    }

    #[test]
    fn heading() {
        let mut printer = StandardBuilder::new()
            .heading(true)
            .build(Some(Path::new("sherlock")), NoColor::new(vec![]));
        SearcherBuilder::new()
            .build(RegexMatcher::new("Watson").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
sherlock
For the Doctor Watsons of this world, as opposed to the Sherlock
but Doctor Watson has to have it taken out for him and dusted,
";
        assert_eq_printed!(expected, got);
    }

    #[test]
    fn no_heading() {
        let mut printer = StandardBuilder::new()
            .heading(false)
            .build(Some(Path::new("sherlock")), NoColor::new(vec![]));
        SearcherBuilder::new()
            .build(RegexMatcher::new("Watson").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
sherlock:For the Doctor Watsons of this world, as opposed to the Sherlock
sherlock:but Doctor Watson has to have it taken out for him and dusted,
";
        assert_eq_printed!(expected, got);
    }

    #[test]
    fn no_heading_multiple() {
        let mut printer = StandardBuilder::new()
            .heading(false)
            .build(Some(Path::new("sherlock")), NoColor::new(vec![]));
        SearcherBuilder::new()
            .build(RegexMatcher::new("Watson").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();
        SearcherBuilder::new()
            .build(RegexMatcher::new("Sherlock").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
sherlock:For the Doctor Watsons of this world, as opposed to the Sherlock
sherlock:but Doctor Watson has to have it taken out for him and dusted,
sherlock:For the Doctor Watsons of this world, as opposed to the Sherlock
sherlock:be, to a very large extent, the result of luck. Sherlock Holmes
";
        assert_eq_printed!(expected, got);
    }

    #[test]
    fn heading_multiple() {
        let mut printer = StandardBuilder::new()
            .heading(true)
            .build(Some(Path::new("sherlock")), NoColor::new(vec![]));
        SearcherBuilder::new()
            .build(RegexMatcher::new("Watson").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();
        SearcherBuilder::new()
            .build(RegexMatcher::new("Sherlock").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
sherlock
For the Doctor Watsons of this world, as opposed to the Sherlock
but Doctor Watson has to have it taken out for him and dusted,

sherlock
For the Doctor Watsons of this world, as opposed to the Sherlock
be, to a very large extent, the result of luck. Sherlock Holmes
";
        assert_eq_printed!(expected, got);
    }

    #[test]
    fn line_number() {
        let mut printer = StandardBuilder::new()
            .build(None, NoColor::new(vec![]));
        SearcherBuilder::new()
            .line_number(true)
            .build(RegexMatcher::new("Watson").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
1:For the Doctor Watsons of this world, as opposed to the Sherlock
5:but Doctor Watson has to have it taken out for him and dusted,
";
        assert_eq_printed!(expected, got);
    }

    #[test]
    fn line_number_multi_line() {
        let mut printer = StandardBuilder::new()
            .build(None, NoColor::new(vec![]));
        SearcherBuilder::new()
            .line_number(true)
            .multi_line(true)
            .build(RegexMatcher::new("(?s)Watson.+Watson").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
1:For the Doctor Watsons of this world, as opposed to the Sherlock
2:Holmeses, success in the province of detective work must always
3:be, to a very large extent, the result of luck. Sherlock Holmes
4:can extract a clew from a wisp of straw or a flake of cigar ash;
5:but Doctor Watson has to have it taken out for him and dusted,
";
        assert_eq_printed!(expected, got);
    }

    #[test]
    fn byte_offset() {
        let mut printer = StandardBuilder::new()
            .byte_offset(true)
            .build(None, NoColor::new(vec![]));
        SearcherBuilder::new()
            .build(RegexMatcher::new("Watson").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
0:For the Doctor Watsons of this world, as opposed to the Sherlock
258:but Doctor Watson has to have it taken out for him and dusted,
";
        assert_eq_printed!(expected, got);
    }

    #[test]
    fn byte_offset_multi_line() {
        let mut printer = StandardBuilder::new()
            .byte_offset(true)
            .build(None, NoColor::new(vec![]));
        SearcherBuilder::new()
            .multi_line(true)
            .build(RegexMatcher::new("(?s)Watson.+Watson").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
0:For the Doctor Watsons of this world, as opposed to the Sherlock
65:Holmeses, success in the province of detective work must always
129:be, to a very large extent, the result of luck. Sherlock Holmes
193:can extract a clew from a wisp of straw or a flake of cigar ash;
258:but Doctor Watson has to have it taken out for him and dusted,
";
        assert_eq_printed!(expected, got);
    }

    #[test]
    fn max_columns() {
        let mut printer = StandardBuilder::new()
            .max_columns(Some(63))
            .build(None, NoColor::new(vec![]));
        SearcherBuilder::new()
            .build(RegexMatcher::new("ash|dusted").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
[Omitted long matching line]
but Doctor Watson has to have it taken out for him and dusted,
";
        assert_eq_printed!(expected, got);
    }

    #[test]
    fn max_columns_multi_line() {
        let mut printer = StandardBuilder::new()
            .max_columns(Some(63))
            .build(None, NoColor::new(vec![]));
        SearcherBuilder::new()
            .multi_line(true)
            .build(RegexMatcher::new("(?s)ash.+dusted").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
[Omitted long matching line]
but Doctor Watson has to have it taken out for him and dusted,
";
        assert_eq_printed!(expected, got);
    }

    #[test]
    fn max_matches() {
        let mut printer = StandardBuilder::new()
            .max_matches(Some(1))
            .build(None, NoColor::new(vec![]));
        SearcherBuilder::new()
            .build(RegexMatcher::new("Sherlock").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
For the Doctor Watsons of this world, as opposed to the Sherlock
";
        assert_eq_printed!(expected, got);
    }

    #[test]
    fn max_matches_context() {
        // after context: 1
        let mut printer = StandardBuilder::new()
            .max_matches(Some(1))
            .build(None, NoColor::new(vec![]));
        SearcherBuilder::new()
            .after_context(1)
            .build(RegexMatcher::new("Doctor Watsons").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
For the Doctor Watsons of this world, as opposed to the Sherlock
Holmeses, success in the province of detective work must always
";
        assert_eq_printed!(expected, got);

        // after context: 4
        let mut printer = StandardBuilder::new()
            .max_matches(Some(1))
            .build(None, NoColor::new(vec![]));
        SearcherBuilder::new()
            .after_context(4)
            .build(RegexMatcher::new("Doctor Watsons").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
For the Doctor Watsons of this world, as opposed to the Sherlock
Holmeses, success in the province of detective work must always
be, to a very large extent, the result of luck. Sherlock Holmes
can extract a clew from a wisp of straw or a flake of cigar ash;
but Doctor Watson has to have it taken out for him and dusted,
";
        assert_eq_printed!(expected, got);

        // after context: 1, max matches: 2
        let mut printer = StandardBuilder::new()
            .max_matches(Some(2))
            .build(None, NoColor::new(vec![]));
        SearcherBuilder::new()
            .after_context(1)
            .build(RegexMatcher::new("Doctor Watsons|but Doctor").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
For the Doctor Watsons of this world, as opposed to the Sherlock
Holmeses, success in the province of detective work must always
--
but Doctor Watson has to have it taken out for him and dusted,
and exhibited clearly, with a label attached.
";
        assert_eq_printed!(expected, got);

        // after context: 4, max matches: 2
        let mut printer = StandardBuilder::new()
            .max_matches(Some(2))
            .build(None, NoColor::new(vec![]));
        SearcherBuilder::new()
            .after_context(4)
            .build(RegexMatcher::new("Doctor Watsons|but Doctor").unwrap())
            .unwrap()
            .search_reader(SHERLOCK.as_bytes(), &mut printer)
            .unwrap();

        let got = printer_contents(&mut printer);
        let expected = "\
For the Doctor Watsons of this world, as opposed to the Sherlock
Holmeses, success in the province of detective work must always
be, to a very large extent, the result of luck. Sherlock Holmes
can extract a clew from a wisp of straw or a flake of cigar ash;
but Doctor Watson has to have it taken out for him and dusted,
and exhibited clearly, with a label attached.
";
        assert_eq_printed!(expected, got);
    }
}
