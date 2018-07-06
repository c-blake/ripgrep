#![allow(dead_code, unused_imports)]

extern crate grep2;
extern crate grep_matcher;
#[cfg(test)]
extern crate grep_regex;
#[macro_use]
extern crate log;
#[cfg(feature = "serde1")]
extern crate serde;
#[cfg(feature = "serde1")]
#[macro_use]
extern crate serde_derive;
extern crate termcolor;

pub use color::UserColorSpec;

mod ackmate;
mod color;
#[cfg(feature = "serde1")]
mod json;
mod standard;
