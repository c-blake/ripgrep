use std::collections::HashMap;

use grep_matcher::{Captures, LineMatchKind, Match, Matcher, NoError};
use regex::bytes::{CaptureLocations, Regex};

use config::{Config, ConfiguredHIR};
use error::Error;
use strip::LineTerminator;
use word::WordMatcher;

/// A builder for constructing a `Matcher` using regular expressions.
#[derive(Clone, Debug)]
pub struct RegexMatcherBuilder {
    config: Config,
}

impl Default for RegexMatcherBuilder {
    fn default() -> RegexMatcherBuilder {
        RegexMatcherBuilder::new()
    }
}

impl RegexMatcherBuilder {
    pub fn new() -> RegexMatcherBuilder {
        RegexMatcherBuilder {
            config: Config::default(),
        }
    }

    pub fn build(&self, pattern: &str) -> Result<RegexMatcher, Error> {
        let chir = self.config.hir(pattern)?;
        let fast_line_regex = chir.fast_line_regex()?;
        Ok(RegexMatcher {
            config: self.config.clone(),
            matcher: RegexMatcherImpl::new(&chir)?,
            fast_line_regex: fast_line_regex,
        })
    }

    pub fn case_insensitive(&mut self, yes: bool) -> &mut RegexMatcherBuilder {
        self.config.case_insensitive = yes;
        self
    }

    pub fn case_smart(&mut self, yes: bool) -> &mut RegexMatcherBuilder {
        self.config.case_smart = yes;
        self
    }

    pub fn multi_line(&mut self, yes: bool) -> &mut RegexMatcherBuilder {
        self.config.multi_line = yes;
        self
    }

    pub fn dot_matches_new_line(
        &mut self,
        yes: bool,
    ) -> &mut RegexMatcherBuilder {
        self.config.dot_matches_new_line = yes;
        self
    }

    pub fn swap_greed(&mut self, yes: bool) -> &mut RegexMatcherBuilder {
        self.config.swap_greed = yes;
        self
    }

    pub fn ignore_whitespace(
        &mut self,
        yes: bool,
    ) -> &mut RegexMatcherBuilder {
        self.config.ignore_whitespace = yes;
        self
    }

    pub fn unicode(&mut self, yes: bool) -> &mut RegexMatcherBuilder {
        self.config.unicode = yes;
        self
    }

    pub fn octal(&mut self, yes: bool) -> &mut RegexMatcherBuilder {
        self.config.octal = yes;
        self
    }

    pub fn size_limit(&mut self, bytes: usize) -> &mut RegexMatcherBuilder {
        self.config.size_limit = bytes;
        self
    }

    pub fn dfa_size_limit(
        &mut self,
        bytes: usize,
    ) -> &mut RegexMatcherBuilder {
        self.config.dfa_size_limit = bytes;
        self
    }

    pub fn nest_limit(&mut self, limit: u32) -> &mut RegexMatcherBuilder {
        self.config.nest_limit = limit;
        self
    }

    pub fn line_terminator(
        &mut self,
        line_term: Option<u8>,
    ) -> &mut RegexMatcherBuilder {
        self.config.line_terminator = line_term.map(LineTerminator::Byte);
        self
    }

    pub fn crlf(&mut self, yes: bool) -> &mut RegexMatcherBuilder {
        if yes {
            self.config.line_terminator = Some(LineTerminator::CRLF);
        } else {
            self.config.line_terminator = None;
        }
        self.config.crlf = yes;
        self
    }

    pub fn word(&mut self, yes: bool) -> &mut RegexMatcherBuilder {
        self.config.word = yes;
        self
    }
}

/// An implementation of the `Matcher` trait using Rust's standard regex
/// library.
#[derive(Clone, Debug)]
pub struct RegexMatcher {
    /// The configuration specified by the caller.
    config: Config,
    /// The underlying matcher implementation.
    matcher: RegexMatcherImpl,
    /// A regex that never reports false negatives but may report false
    /// positives that is believed to be capable of being matched more quickly
    /// than `regex`. Typically, this is a single literal or an alternation
    /// of literals.
    fast_line_regex: Option<Regex>,
}

impl RegexMatcher {
    /// Create a new matcher from the given pattern using the default
    /// configuration.
    pub fn new(pattern: &str) -> Result<RegexMatcher, Error> {
        RegexMatcherBuilder::new().build(pattern)
    }

    /// Create a new matcher from the given pattern using the default
    /// configuration, but matches lines terminated by `\n`.
    ///
    /// This returns an error if the given pattern contains a literal `\n`.
    /// Other uses of `\n` (such as in `\s`) are removed transparently.
    pub fn new_line_matcher(pattern: &str) -> Result<RegexMatcher, Error> {
        RegexMatcherBuilder::new()
            .line_terminator(Some(b'\n'))
            .build(pattern)
    }
}

/// An encapsulation of the type of matcher we use in `RegexMatcher`.
#[derive(Clone, Debug)]
enum RegexMatcherImpl {
    /// The standard matcher used for all regular expressions.
    Standard(StandardMatcher),
    /// A matcher that only matches at word boundaries. This transforms the
    /// regex to `(^|\W)(...)($|\W)` instead of the more intuitive `\b(...)\b`.
    /// Because of this, the WordMatcher provides its own implementation of
    /// `Matcher` to encapsulate its use of capture groups to make them
    /// invisible to the caller.
    Word(WordMatcher),
}

impl RegexMatcherImpl {
    /// Based on the configuration, create a new implementation of the
    /// `Matcher` trait.
    fn new(expr: &ConfiguredHIR) -> Result<RegexMatcherImpl, Error> {
        if expr.config().word {
            Ok(RegexMatcherImpl::Word(WordMatcher::new(expr)?))
        } else {
            Ok(RegexMatcherImpl::Standard(StandardMatcher::new(expr)?))
        }
    }
}

// This implementation just dispatches on the internal matcher impl except
// for the line terminator optimization, which is possibly executed via
// `fast_line_regex`.
impl Matcher for RegexMatcher {
    type Captures = RegexCaptures;
    type Error = NoError;

    fn find_at(
        &self,
        haystack: &[u8],
        at: usize,
    ) -> Result<Option<Match>, NoError> {
        use self::RegexMatcherImpl::*;
        match self.matcher {
            Standard(ref m) => m.find_at(haystack, at),
            Word(ref m) => m.find_at(haystack, at),
        }
    }

    fn new_captures(&self) -> Result<RegexCaptures, NoError> {
        use self::RegexMatcherImpl::*;
        match self.matcher {
            Standard(ref m) => m.new_captures(),
            Word(ref m) => m.new_captures(),
        }
    }

    fn capture_count(&self) -> usize {
        use self::RegexMatcherImpl::*;
        match self.matcher {
            Standard(ref m) => m.capture_count(),
            Word(ref m) => m.capture_count(),
        }
    }

    fn capture_index(&self, name: &str) -> Option<usize> {
        use self::RegexMatcherImpl::*;
        match self.matcher {
            Standard(ref m) => m.capture_index(name),
            Word(ref m) => m.capture_index(name),
        }
    }

    fn find(&self, haystack: &[u8]) -> Result<Option<Match>, NoError> {
        use self::RegexMatcherImpl::*;
        match self.matcher {
            Standard(ref m) => m.find(haystack),
            Word(ref m) => m.find(haystack),
        }
    }

    fn find_iter<F>(
        &self,
        haystack: &[u8],
        matched: F,
    ) -> Result<(), NoError>
    where F: FnMut(Match) -> bool
    {
        use self::RegexMatcherImpl::*;
        match self.matcher {
            Standard(ref m) => m.find_iter(haystack, matched),
            Word(ref m) => m.find_iter(haystack, matched),
        }
    }

    fn captures(
        &self,
        haystack: &[u8],
        caps: &mut RegexCaptures,
    ) -> Result<bool, NoError> {
        use self::RegexMatcherImpl::*;
        match self.matcher {
            Standard(ref m) => m.captures(haystack, caps),
            Word(ref m) => m.captures(haystack, caps),
        }
    }

    fn captures_iter<F>(
        &self,
        haystack: &[u8],
        caps: &mut RegexCaptures,
        matched: F,
    ) -> Result<(), NoError>
    where F: FnMut(&RegexCaptures) -> bool
    {
        use self::RegexMatcherImpl::*;
        match self.matcher {
            Standard(ref m) => m.captures_iter(haystack, caps, matched),
            Word(ref m) => m.captures_iter(haystack, caps, matched),
        }
    }

    fn captures_at(
        &self,
        haystack: &[u8],
        at: usize,
        caps: &mut RegexCaptures,
    ) -> Result<bool, NoError> {
        use self::RegexMatcherImpl::*;
        match self.matcher {
            Standard(ref m) => m.captures_at(haystack, at, caps),
            Word(ref m) => m.captures_at(haystack, at, caps),
        }
    }

    fn replace<F>(
        &self,
        haystack: &[u8],
        dst: &mut Vec<u8>,
        append: F,
    ) -> Result<(), NoError>
    where F: FnMut(Match, &mut Vec<u8>) -> bool
    {
        use self::RegexMatcherImpl::*;
        match self.matcher {
            Standard(ref m) => m.replace(haystack, dst, append),
            Word(ref m) => m.replace(haystack, dst, append),
        }
    }

    fn replace_with_captures<F>(
        &self,
        haystack: &[u8],
        caps: &mut RegexCaptures,
        dst: &mut Vec<u8>,
        append: F,
    ) -> Result<(), NoError>
    where F: FnMut(&Self::Captures, &mut Vec<u8>) -> bool
    {
        use self::RegexMatcherImpl::*;
        match self.matcher {
            Standard(ref m) => {
                m.replace_with_captures(haystack, caps, dst, append)
            }
            Word(ref m) => {
                m.replace_with_captures(haystack, caps, dst, append)
            }
        }
    }

    fn is_match(&self, haystack: &[u8]) -> Result<bool, NoError> {
        use self::RegexMatcherImpl::*;
        match self.matcher {
            Standard(ref m) => m.is_match(haystack),
            Word(ref m) => m.is_match(haystack),
        }
    }

    fn is_match_at(
        &self,
        haystack: &[u8],
        at: usize,
    ) -> Result<bool, NoError> {
        use self::RegexMatcherImpl::*;
        match self.matcher {
            Standard(ref m) => m.is_match_at(haystack, at),
            Word(ref m) => m.is_match_at(haystack, at),
        }
    }

    fn shortest_match(
        &self,
        haystack: &[u8],
    ) -> Result<Option<usize>, NoError> {
        use self::RegexMatcherImpl::*;
        match self.matcher {
            Standard(ref m) => m.shortest_match(haystack),
            Word(ref m) => m.shortest_match(haystack),
        }
    }

    fn shortest_match_at(
        &self,
        haystack: &[u8],
        at: usize,
    ) -> Result<Option<usize>, NoError> {
        use self::RegexMatcherImpl::*;
        match self.matcher {
            Standard(ref m) => m.shortest_match_at(haystack, at),
            Word(ref m) => m.shortest_match_at(haystack, at),
        }
    }

    fn line_terminator(&self) -> Option<u8> {
        match self.config.line_terminator {
            None => None,
            Some(LineTerminator::CRLF) => Some(b'\n'),
            Some(LineTerminator::Byte(b)) => Some(b),
        }
    }

    fn find_candidate_line(
        &self,
        haystack: &[u8],
    ) -> Result<Option<LineMatchKind>, NoError> {
        Ok(match self.fast_line_regex {
            Some(ref regex) => {
                regex.shortest_match(haystack).map(LineMatchKind::Candidate)
            }
            None if self.config.line_terminator.is_some() => {
                self.shortest_match(haystack)?.map(LineMatchKind::Confirmed)
            }
            None => panic!("misuse of find_candidate_line; no line term set"),
        })
    }
}

/// The implementation of the standard regex matcher.
#[derive(Clone, Debug)]
struct StandardMatcher {
    /// The regular expression compiled from the pattern provided by the
    /// caller.
    regex: Regex,
    /// A map from capture group name to its corresponding index.
    names: HashMap<String, usize>,
}

impl StandardMatcher {
    fn new(expr: &ConfiguredHIR) -> Result<StandardMatcher, Error> {
        let regex = expr.regex()?;
        let mut names = HashMap::new();
        for (i, optional_name) in regex.capture_names().enumerate() {
            if let Some(name) = optional_name {
                names.insert(name.to_string(), i);
            }
        }
        Ok(StandardMatcher { regex, names })
    }
}

impl Matcher for StandardMatcher {
    type Captures = RegexCaptures;
    type Error = NoError;

    fn find_at(
        &self,
        haystack: &[u8],
        at: usize,
    ) -> Result<Option<Match>, NoError> {
        Ok(self.regex
            .find_at(haystack, at)
            .map(|m| Match::new(m.start(), m.end())))
    }

    fn new_captures(&self) -> Result<RegexCaptures, NoError> {
        Ok(RegexCaptures::new(self.regex.capture_locations()))
    }

    fn capture_count(&self) -> usize {
        self.regex.captures_len()
    }

    fn capture_index(&self, name: &str) -> Option<usize> {
        self.names.get(name).map(|i| *i)
    }

    fn find_iter<F>(
        &self,
        haystack: &[u8],
        mut matched: F,
    ) -> Result<(), NoError>
    where F: FnMut(Match) -> bool
    {
        for m in self.regex.find_iter(haystack) {
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
    ) -> Result<bool, NoError> {
        Ok(self.regex.captures_read_at(&mut caps.locs, haystack, at).is_some())
    }

    fn shortest_match_at(
        &self,
        haystack: &[u8],
        at: usize,
    ) -> Result<Option<usize>, NoError> {
        Ok(self.regex.shortest_match_at(haystack, at))
    }
}

/// Represents the match offsets of each capturing group in a match.
///
/// The first, or `0`th capture group, always corresponds to the entire match
/// and is guaranteed to be present when a match occurs. The next capture
/// group, at index `1`, corresponds to the first capturing group in the regex,
/// ordered by the position at which the left opening parenthesis occurs.
///
/// Note that not all capturing groups are guaranteed to be present in a match.
/// For example, in the regex, `(?P<foo>\w)|(?P<bar>\W)`, only one of `foo`
/// or `bar` will ever be set in any given match.
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
    pub(crate) fn new(locs: CaptureLocations) -> RegexCaptures {
        RegexCaptures::with_offset(locs, 0)
    }

    pub(crate) fn with_offset(
        locs: CaptureLocations,
        offset: usize,
    ) -> RegexCaptures {
        RegexCaptures { locs, offset }
    }

    pub(crate) fn locations(&mut self) -> &mut CaptureLocations {
        &mut self.locs
    }
}
