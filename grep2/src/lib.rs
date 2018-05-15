#![allow(dead_code)]

extern crate failure;
extern crate memchr;

pub use matcher::{
    Captures, LineMatchKind, Matcher, NoCaptures,
};
pub use sink::{LineMatch, Sink};

mod interpolate;
mod matcher;
mod searcher;
mod sink;
