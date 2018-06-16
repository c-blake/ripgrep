#![allow(dead_code)]

extern crate bytecount;
extern crate memchr;
#[cfg(test)]
extern crate regex;

pub use lines::LineIter;
pub use matcher::{
    Captures, LineMatchKind, Match, Matcher, NoCaptures, NoError,
};
pub use searcher_builder::{
    BinaryDetection, ConfigError, MmapChoice,
    Searcher, SearcherBuilder,
};
pub use sink::{Sink, SinkContext, SinkContextKind, SinkFinish, SinkMatch};

mod interpolate;
mod line_buffer;
mod lines;
mod matcher;
mod searcher_builder;
mod searcher_exec;
mod sink;
#[cfg(test)]
mod testutil;
