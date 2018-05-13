#![allow(dead_code)]

extern crate failure;
extern crate memchr;

pub use matcher::{
    CaptureMatch, CaptureMatches, LineMatch, LineMatcher, Matcher,
};

mod interpolate;
mod matcher;
