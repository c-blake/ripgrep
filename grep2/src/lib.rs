#![allow(dead_code)]

extern crate bytecount;
extern crate memchr;

pub use lines::LineIter;
pub use matcher::{
    Captures, LineMatchKind, Match, Matcher, NoCaptures, NoError,
};
pub use searcher::{
    BinaryDetection, ConfigError, MmapChoice,
    Searcher, SearcherBuilder,
};
pub use sink::{Sink, SinkContext, SinkContextKind, SinkFinish, SinkMatch};

mod interpolate;
mod line_buffer;
mod lines;
mod matcher;
mod searcher;
mod sink;
#[cfg(test)]
mod testutil;
