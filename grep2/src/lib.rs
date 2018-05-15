#![allow(dead_code)]

extern crate failure;
extern crate memchr;

pub use matcher::{
    Captures, LineMatchKind, Matcher, NoCaptures,
};
pub use searcher::LineMatch;

mod interpolate;
mod matcher;
mod searcher;
