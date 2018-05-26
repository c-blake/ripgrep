use std::io;

use line_buffer::{LineBuffer, LineBufferBuilder, LineBufferReader};
use matcher::Matcher;
use sink::Sink;

#[derive(Debug)]
struct Config {
    /// The line terminator to use.
    lineterm: u8,
    /// Whether to invert matching.
    invert_match: bool,
    /// Whether to quit searching after a match is found.
    stop_after_first_match: bool,
    /// The number of lines after a match to include.
    after_context: usize,
    /// The number of lines before a match to include.
    before_context: usize,
    /// Whether to count line numbers.
    line_number: bool,
    /// Whether to enable binary data detection.
    /// TODO: This should probably be an enum.
    binary: bool,
}

#[derive(Debug)]
pub struct Searcher<M> {
    config: Config,
    matcher: M,
    line_buffer: LineBuffer,
}

impl<M: Matcher> Searcher<M> {
    fn new(config: Config, matcher: M) -> Searcher<M> {
        // TODO: This should be constructed by a builder.
        Searcher {
            config,
            matcher,
            line_buffer: LineBufferBuilder::new().build(),
        }
    }
}

#[derive(Debug)]
struct SearcherExec<'s, M: 's, R, S> {
    config: &'s Config,
    matcher: &'s M,
    line_reader: LineBufferReader<'s, R>,
    sink: S,
}

// BREADCRUMB: Consider using interior mutability. Maybe try without it though.

impl<'s, M: Matcher, R: io::Read, S: Sink> SearcherExec<'s, M, R, S> {
    fn run(self) {}
}
