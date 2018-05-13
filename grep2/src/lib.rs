#![allow(dead_code)]

extern crate failure;
extern crate memchr;

pub use matcher::{
    Captures, LineMatch, Matcher, NoCaptures,
};

mod interpolate;
mod matcher;
