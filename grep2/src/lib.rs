/*!
grep, as a library.
*/

#![deny(missing_docs)]

extern crate bytecount;
extern crate memchr;
#[cfg(test)]
extern crate regex;

pub use lines::LineIter;
pub use matcher::{
    Captures, LineMatchKind, Match, Matcher, NoCaptures, NoError,
};
pub use searcher::{
    BinaryDetection, ConfigError, MmapChoice,
    Searcher, SearcherBuilder,
};
pub use sink::{
    Sink, SinkError,
    SinkContext, SinkContextKind, SinkFinish, SinkMatch,
};
pub use sink::sinks;

mod interpolate;
mod line_buffer;
mod lines;
mod matcher;
mod searcher;
mod sink;
#[cfg(test)]
mod testutil;
