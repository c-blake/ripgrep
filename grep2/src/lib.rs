#![allow(dead_code)]

extern crate bytecount;
extern crate failure;
extern crate memchr;

pub use matcher::{
    Captures, LineMatchKind, Matcher, NoCaptures,
};
pub use sink::{SinkMatch, Sink};

mod interpolate;
mod line_buffer;
mod lines;
mod matcher;
mod searcher;
mod sink;
#[cfg(test)]
mod testutil;
