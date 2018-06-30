#![allow(dead_code, unused_imports, unused_variables)]

extern crate grep_matcher;
#[macro_use]
extern crate log;
extern crate regex;
extern crate regex_syntax;
extern crate thread_local;

use std::collections::HashMap;
use std::result;

use grep_matcher::{Captures, Match, Matcher, NoError};
use regex::bytes::{CaptureLocations, Regex};

pub use ast::AstAnalysis;
pub use error::{Error, ErrorKind};

// BREADCRUMBS:
//
// Still have a lot of work to do:
//
// * Add RegexMatcherBuilder, which probably needs to re-export most of
//   RegexBuilder in addition to grep-regex specific options. e.g., Setting
//   a line terminator.
// * Figure out how to handle multi-line search and also the `m` and `s`
//   flags. It's likely that we always want to enable `m` by default in every
//   case. The `s` flag is trickier. In multi line mode, we could defensibly
//   make it match line terminators, but this could be surprising. The reverse
//   behavior could be surprising as well though. (N.B. I posed this question
//   to GitHub.)
// * Arrange the RegexMatcher such that it can implement `find_candidate_line`
//   efficiently.
//
// I think most of the guts are done. What's needed now is to tie everything
// together. Write out the builder and the construction logic. The matcher
// itself will need to contain a sub-matcher enum that combines the standard
// matcher with the word matcher.
//
// Figure out how to arrange the config module. Lots of attributes, but it
// would be nice to not just expose everything...

mod ast;
mod config;
mod crlf;
mod error;
mod literal;
mod strip;
mod util;
mod word;

type Result<T> = result::Result<T, NoError>;

#[derive(Debug)]
pub struct RegexMatcher {
    re: Regex,
    names: HashMap<String, usize>,
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
    type Captures = RegexCaptures;
    type Error = NoError;

    fn find_at(
        &self,
        haystack: &[u8],
        at: usize,
    ) -> Result<Option<Match>> {
        Ok(self.re
            .find_at(haystack, at)
            .map(|m| Match::new(m.start(), m.end())))
    }

    fn new_captures(&self) -> Result<RegexCaptures> {
        Ok(RegexCaptures::new(self.re.capture_locations()))
    }

    fn capture_count(&self) -> usize {
        self.re.captures_len()
    }

    fn capture_index(&self, name: &str) -> Option<usize> {
        self.names.get(name).map(|i| *i)
    }

    fn find_iter<F>(
        &self,
        haystack: &[u8],
        mut matched: F,
    ) -> Result<()>
    where F: FnMut(Match) -> bool
    {
        for m in self.re.find_iter(haystack) {
            if !matched(Match::new(m.start(), m.end())) {
                return Ok(());
            }
        }
        Ok(())
    }

    fn captures_at(
        &self,
        haystack: &[u8],
        at: usize,
        caps: &mut RegexCaptures,
    ) -> Result<bool> {
        Ok(self.re.captures_read_at(&mut caps.locs, haystack, at).is_some())
    }

    fn shortest_match_at(
        &self,
        haystack: &[u8],
        at: usize,
    ) -> Result<Option<usize>> {
        Ok(self.re.shortest_match_at(haystack, at))
    }
}

/// Represents the match offsets of each capturing group in a match.
///
/// The first, or `0`th capture group, always corresponds to the entire match
/// and is guaranteed to be present. The next capture group, at index `1`,
/// corresponds to the first capturing group in the regex, ordered by the
/// position at which the left opening parenthesis occurs.
///
/// Note that not all capturing groups are guaranteed to be present in a match.
/// For example, in the regex, `(?P<foo>\w)|(?P<bar>\W)`, only one of `foo`
/// or `bar` will ever be set in any given match..
///
/// In order to access a capture group by name, you'll need to first find the
/// index of the group using the corresponding matcher's `capture_index`
/// method, and then use that index with `RegexCaptures::get`.
#[derive(Clone, Debug)]
pub struct RegexCaptures {
    /// Where the locations are stored.
    locs: CaptureLocations,
    /// These captures behave as if the capturing groups begin at the given
    /// offset. When set to `0`, this has no affect and capture groups are
    /// indexed like normal.
    ///
    /// This is useful when building matchers that wrap arbitrary regular
    /// expressions. For example, `WordMatcher` takes an existing regex `re`
    /// and creates `(?:^|\W)(re)(?:$|\W)`, but hides the fact that the regex
    /// has been wrapped from the caller. In order to do this, the matcher
    /// and the capturing groups must behave as if `(re)` is the `0`th capture
    /// group.
    offset: usize,
}

impl Captures for RegexCaptures {
    fn len(&self) -> usize {
        self.locs.len().checked_sub(self.offset).unwrap()
    }

    fn get(&self, i: usize) -> Option<Match> {
        let actual = i.checked_add(self.offset).unwrap();
        self.locs.pos(actual).map(|(s, e)| Match::new(s, e))
    }
}

impl RegexCaptures {
    fn new(locs: CaptureLocations) -> RegexCaptures {
        RegexCaptures::with_offset(locs, 0)
    }

    fn with_offset(locs: CaptureLocations, offset: usize) -> RegexCaptures {
        RegexCaptures { locs, offset }
    }
}
