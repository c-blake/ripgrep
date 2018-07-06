use std::io;
use std::path::Path;
use std::sync::Arc;

use grep2::{Searcher, Sink, SinkMatch};
use grep_matcher::Matcher;
use termcolor::WriteColor;

use color::ColorSpecs;

#[derive(Debug, Clone)]
struct Config {
    line_term: u8,
    separator_file: Arc<Option<Vec<u8>>>,
    separator_context: Arc<Option<Vec<u8>>>,
    separator_field: u8,
    separator_path: Option<u8>,
    column: bool,
    heading: bool,
    line_per_match: bool,
    only_matching: bool,
    replacement: Arc<Option<Vec<u8>>>,
    with_filename: bool,
    max_columns: Option<usize>,
    colors: ColorSpecs,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            line_term: b'\n',
            separator_file: Arc::new(None),
            separator_context: Arc::new(Some(b"--".to_vec())),
            separator_field: b':',
            separator_path: None,
            column: false,
            heading: false,
            line_per_match: false,
            only_matching: false,
            replacement: Arc::new(None),
            with_filename: false,
            max_columns: None,
            colors: ColorSpecs::default(),
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

    pub fn build<'p, W: WriteColor>(
        &self,
        path: Option<&'p Path>,
        wtr: W,
    ) -> Standard<'p, W> {
        Standard {
            config: self.config.clone(),
            wtr: wtr,
            path: path,
            bytes_printed: 0,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Standard<'p, W> {
    config: Config,
    wtr: W,
    path: Option<&'p Path>,
    bytes_printed: u64,
}

impl<'p, W: WriteColor> Standard<'p, W> {
    pub fn into_writer(self) -> W {
        self.wtr
    }
}

impl<'p, W: WriteColor> Sink for Standard<'p, W> {
    type Error = io::Error;

    fn matched<M: Matcher>(
        &mut self,
        _searcher: &Searcher<M>,
        mat: &SinkMatch,
    ) -> Result<bool, io::Error> {
        let mut line_number = mat.line_number();
        let mut byte_offset = mat.absolute_byte_offset();
        for line in mat.lines() {
            if let Some(ref mut n) = line_number {
                write!(self.wtr, "{}:", n)?;
                *n += 1;
            }

            write!(self.wtr, "{}:", byte_offset)?;
            byte_offset += line.len() as u64;
            self.wtr.write_all(line)?;
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use grep2::SearcherBuilder;
    use grep_regex::RegexMatcher;
    use termcolor::NoColor;

    use super::StandardBuilder;

    const SHERLOCK: &'static str = "\
For the Doctor Watsons of this world, as opposed to the Sherlock
Holmeses, success in the province of detective work must always
be, to a very large extent, the result of luck. Sherlock Holmes
can extract a clew from a wisp of straw or a flake of cigar ash;
but Doctor Watson has to have it taken out for him and dusted,
and exhibited clearly, with a label attached.\
";

    #[test]
    fn scratch() {
        let wtr = NoColor::new(vec![]);
        let mut printer = StandardBuilder::new().build(None, wtr);
        let matcher = RegexMatcher::new("Sherlock").unwrap();
        let mut searcher = SearcherBuilder::new()
            .build(&matcher)
            .unwrap();
        searcher.search_reader(SHERLOCK.as_bytes(), &mut printer).unwrap();

        let buf = printer.into_writer().into_inner();
        println!("{}", String::from_utf8(buf).unwrap());
    }
}
