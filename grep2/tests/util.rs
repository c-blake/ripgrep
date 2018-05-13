use std::collections::HashMap;

use regex::bytes::Regex;

use grep2::{CaptureMatches, LineMatcher, Matcher};

#[derive(Debug)]
pub struct RegexMatcher {
    pub re: Regex,
    pub names: HashMap<String, usize>,
}

impl RegexMatcher {
    pub fn new(re: Regex) -> RegexMatcher {
        let mut names = HashMap::new();
        for (i, optional_name) in re.capture_names().enumerate() {
            if let Some(name) = optional_name {
                names.insert(name.to_string(), i);
            }
        }
        RegexMatcher {
            re: re,
            names: names,
        }
    }
}

impl Matcher for RegexMatcher {
    type LineMatcher = Self;

    fn find_at(&self, haystack: &[u8], at: usize) -> Option<(usize, usize)> {
        // TODO: This relies on an undocumented part of the regex API.
        // It is simple enough that we should probably just expose it.
        self.re.find_at(haystack, at).map(|m| (m.start(), m.end()))
    }

    fn captures_at(
        &self,
        haystack: &[u8],
        at: usize,
        matches: &mut CaptureMatches,
    ) -> bool {
        // TODO: This relies on an undocumented part of the regex API.
        // This needs a little thought. The simplest solution is to push
        // the burden of satisfying the API contract on to the caller, which
        // is tempting, and potentially justifiable by virtue of it being a low
        // level API.
        //
        // See: https://github.com/rust-lang/regex/issues/219
        matches.resize(0);
        let mut locs = self.re.locations();
        if self.re.read_captures_at(&mut locs, haystack, at).is_none() {
            return false;
        }

        matches.resize(locs.len());
        for (i, m) in locs.iter().enumerate() {
            matches.set(i, m);
        }
        true
    }

    fn capture_count(&self) -> usize {
        self.re.captures_len()
    }

    fn capture_index(&self, name: &str) -> Option<usize> {
        self.names.get(name).map(|i| *i)
    }

    // We purposely don't implement any other methods, so that we test the
    // default impls. The "real" Regex impl for Matcher provides a few more
    // impls. e.g., Its `find_iter` impl is faster than what we can do here,
    // since the regex crate avoids synchronization overhead.
}

impl LineMatcher for RegexMatcher {}

#[derive(Debug)]
pub struct RegexMatcherNoCaps(pub Regex);

impl Matcher for RegexMatcherNoCaps {
    type LineMatcher = Self;

    fn find_at(&self, haystack: &[u8], at: usize) -> Option<(usize, usize)> {
        self.0.find_at(haystack, at).map(|m| (m.start(), m.end()))
    }
}

impl LineMatcher for RegexMatcherNoCaps {}
