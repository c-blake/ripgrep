use std::collections::HashMap;
use std::fmt;
use std::result;

use failure::Fail;
use regex::bytes::{Locations, Regex};

use grep2::{Captures, Matcher, NoCaptures};

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

type Result<T> = result::Result<T, NoError>;

impl Matcher for RegexMatcher {
    type Captures = RegexCaptures;
    type Error = NoError;

    fn find_at(
        &self,
        haystack: &[u8],
        at: usize,
    ) -> Result<Option<(usize, usize)>> {
        // TODO: This relies on an undocumented part of the regex API.
        // It is simple enough that we should probably just expose it.
        Ok(self.re.find_at(haystack, at).map(|m| (m.start(), m.end())))
    }

    fn new_captures(&self) -> Result<RegexCaptures> {
        Ok(RegexCaptures(self.re.locations()))
    }

    fn captures_at(
        &self,
        haystack: &[u8],
        at: usize,
        caps: &mut RegexCaptures,
    ) -> Result<bool> {
        // TODO: This relies on an undocumented part of the regex API.
        // This needs a little thought. The simplest solution is to push
        // the burden of satisfying the API contract on to the caller, which
        // is tempting, and potentially justifiable by virtue of it being a low
        // level API.
        //
        // See: https://github.com/rust-lang/regex/issues/219
        Ok(self.re.read_captures_at(&mut caps.0, haystack, at).is_some())
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

#[derive(Debug)]
pub struct RegexMatcherNoCaps(pub Regex);

impl Matcher for RegexMatcherNoCaps {
    type Captures = NoCaptures;
    type Error = NoError;

    fn find_at(
        &self,
        haystack: &[u8],
        at: usize,
    ) -> Result<Option<(usize, usize)>> {
        Ok(self.0.find_at(haystack, at).map(|m| (m.start(), m.end())))
    }

    fn new_captures(&self) -> Result<NoCaptures> {
        Ok(NoCaptures::new())
    }
}

#[derive(Debug)]
pub struct NoError(());

impl Fail for NoError {}

impl fmt::Display for NoError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BUG for NoError: an impossible error occurred")
    }
}

pub struct RegexCaptures(Locations);

impl Captures for RegexCaptures {
    fn len(&self) -> usize {
        self.0.len()
    }

    fn get(&self, i: usize) -> Option<(usize, usize)> {
        self.0.pos(i)
    }
}

impl fmt::Debug for RegexCaptures {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut list = f.debug_list();
        for x in self.0.iter() {
            list.entry(&x);
        }
        list.finish()
    }
}
