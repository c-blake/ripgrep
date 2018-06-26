#![allow(dead_code)]

extern crate grep_matcher;
#[macro_use]
extern crate log;
extern crate regex;
extern crate regex_syntax;

use std::collections::HashMap;
use std::result;

use grep_matcher::{Captures, Match, Matcher, NoError};
use regex::bytes::{CaptureLocations, Regex};

pub use ast::AstAnalysis;

// BREADCRUMBS:
//
// Still have a lot of work to do:
//
// * Add routines for stripping/erroring if line terminators are in the
//   pattern. Make sure to leave room for stripping CRLF.
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
// * Figure out CRLF handling. Idea: replace occurrences of `$` with
//   `(?:\r?$)` and then trim matches if they end with `\r`.
// * Figure out word boundaries. We want `(?:^|\W)(...)(?:$|\W)`. The trick is
//   in behaving as if the outer capture groups aren't visible. It will need
//   some careful work in the `Matcher` implementation, but it seems possible.
//   Alternatively, we could figure out how to trim the match after the fact,
//   but this seems potentially tricky. It would be nice if we could figure
//   out how to encapsulate the inevitable case analysis sprawl this is going
//   to introduce...

mod ast;
mod literal;

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
        Ok(RegexCaptures(self.re.capture_locations()))
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
        Ok(self.re.captures_read_at(&mut caps.0, haystack, at).is_some())
    }

    fn shortest_match_at(
        &self,
        haystack: &[u8],
        at: usize,
    ) -> Result<Option<usize>> {
        Ok(self.re.shortest_match_at(haystack, at))
    }
}

#[derive(Clone, Debug)]
pub struct RegexCaptures(CaptureLocations);

impl Captures for RegexCaptures {
    fn len(&self) -> usize {
        self.0.len()
    }

    fn get(&self, i: usize) -> Option<Match> {
        self.0.pos(i).map(|(s, e)| Match::new(s, e))
    }
}
