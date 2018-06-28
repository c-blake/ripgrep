use std::sync::{Arc, Mutex};

use regex::bytes::{CaptureLocations, Regex, RegexBuilder};

use config::ConfiguredHIR;
use error::Error;

/// A matcher for implementing "word match" semantics.
#[derive(Clone, Debug)]
pub struct WordMatcher {
    /// The regex which is roughly `(?:^|\W)(<original pattern>)(?:$|\W)`.
    regex: Regex,
    /// A reusable buffer for finding the match location of the inner group.
    /// We may consider using the `thread_local` crate if the mutex turns out
    /// to be too slow, but let's start simple.
    locs: Arc<Mutex<CaptureLocations>>,
}

impl WordMatcher {
    /// Create a new matcher from the given pattern that only produces matches
    /// that are considered "words."
    ///
    /// The given options are used to construct the regular expression
    /// internally.
    pub fn new(expr: &ConfiguredHIR) -> Result<WordMatcher, Error> {
        let word_expr = expr.with_pattern(|pat| {
            format!(r"(?:(?m:^)|\W)({})(?:(?m:$)|\W)", pat)
        })?;
        let regex = word_expr.regex()?;
        let locs = Arc::new(Mutex::new(regex.capture_locations()));
        Ok(WordMatcher { regex, locs })
    }
}
