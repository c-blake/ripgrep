use failure;

use interpolate::interpolate;

/// The type of match for a line oriented matcher.
pub enum LineMatch {
    /// A position inside a line that is known to contain a match.
    ///
    /// This position can be anywhere in the line. It does not need to point
    /// at the location of the match.
    Confirmed(usize),
    /// A position inside a line that may contain a match, and must be searched
    /// for verification.
    ///
    /// This position can be anywhere in the line. It does not need to point
    /// at the location of the match.
    Candidate(usize),
}

/// A matcher optimized for searching line-by-line.
///
/// A line matcher is, fundamentally, a normal matcher with the addition of
/// one optional method: finding a line. By default, this routine is
/// implemented via the matcher's `shortest_match` method, which always yields
/// either no match or a `LineMatch::Match`. However, implementors may provide
/// a routine for this that can return candidate lines that need subsequent
/// verification to be confirmed as a match. This can be useful in cases where
/// it may be quicker to find candidate lines via some other means instead of
/// relying on the more general implementations for `find` and
/// `shortest_match`.
///
/// For example, consider the regex `\w+foo\s+`. Both `find` and
/// `shortest_match` must consider the entire regex, including the `\w+` and
/// `\s+`, while searching. However, a `LineMatcher`'s `find_line` method
/// could look for lines containing `foo` and return them as candidates.
/// Finding `foo` might be a implemented as a highly optimized substring search
/// routine (like `memmem`), which is likely to be faster than whatever more
/// generalized routine is required for resolving `\w+foo\s+`.
///
/// Note that while a line matcher may report false positives, a line matcher
/// must never report false negatives. That is, it can never skip over lines
/// that contain a match.
pub trait LineMatcher: Matcher {
    /// Return one of the following: a confirmed line match, a candidate line
    /// match (which may be a false positive) or no match at all (which **must
    /// not** be a false negative). When reporting a confirmed or candidate
    /// match, the position returned can be any position in the line.
    ///
    /// By default, this never returns a candidate match, and always either
    /// returns a confirmed match or no match at all.
    fn find_line(&self, haystack: &[u8]) -> Option<LineMatch> {
        self.shortest_match(haystack).map(LineMatch::Confirmed)
    }
}

/// CaptureMatch is a match for a single capturing group, if one exists.
pub type CaptureMatch = Option<(usize, usize)>;

/// CaptureMatches represents the match locations for each capturing group in a
/// matcher.
///
/// After receiving matches, if a matcher supports capturing groups, then this
/// value always has length equivalent to the number of capturing groups in the
/// matcher. Each capturing group may or may not have a match, but the first
/// capturing group always corresponds to the overall match.
///
/// If a matcher does not support capturing groups, then this value always has
/// length zero after attempting a match.
pub struct CaptureMatches(Vec<CaptureMatch>);

impl CaptureMatches {
    /// Create an empty set of capture matches. The value returned here may
    /// be passed to a matcher to retrieve capture locations.
    pub fn new() -> CaptureMatches {
        CaptureMatches(vec![])
    }

    /// Returns the number of possible capture matches. Note that this includes
    /// unmatched capturing groups.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns true if and only if this group of matches is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Resize this container to hold `n` capture matches. If `n` is less
    /// than the current length, then this truncates. If `n` is more than the
    /// current length, then this adds new empty matches.
    pub fn resize(&mut self, n: usize) {
        self.0.resize(n, None);
    }

    /// Returns the capture match at the given index.
    ///
    /// If no match occurred at the given capturing group, or if the given
    /// index is out of bounds, then this returns `None`.
    ///
    /// The capture match at index `0` is guaranteed to exist whenever a
    /// matcher reports a successful overall match.
    pub fn get(&self, i: usize) -> CaptureMatch {
        self.0.get(i).and_then(|m| *m)
    }

    /// Sets the given match to the given position.
    ///
    /// This panics if `i` is greater than this container's length.
    pub fn set(&mut self, i: usize, m: CaptureMatch) {
        self.0[i] = m;
    }

    /// Expands all instances of `$name` in `replacement` to the corresponding
    /// capture group `name`, and writes them to the `dst` buffer given.
    ///
    /// `name` may be an integer corresponding to the index of the
    /// capture group (counted by order of opening parenthesis where `0` is the
    /// entire match) or it can be a name (consisting of letters, digits or
    /// underscores) corresponding to a named capture group.
    ///
    /// A `name` is translated to a capture group index via the given
    /// `name_to_index` function. If `name` isn't a valid capture group
    /// (whether the name doesn't exist or isn't a valid index), then it is
    /// replaced with the empty string.
    ///
    /// The longest possible name is used. e.g., `$1a` looks up the capture
    /// group named `1a` and not the capture group at index `1`. To exert
    /// more precise control over the name, use braces, e.g., `${1}a`. In all
    /// cases, capture group names are limited to ASCII letters, numbers and
    /// underscores.
    ///
    /// To write a literal `$` use `$$`.
    ///
    /// Note that the capture group match indices are resolved by slicing
    /// the given `haystack`. Generally, this means that `haystack` should be
    /// the same slice that was searched to get the current capture group
    /// matches.
    pub fn interpolate<F>(
        &self,
        name_to_index: F,
        haystack: &[u8],
        replacement: &[u8],
        dst: &mut Vec<u8>,
    ) where F: FnMut(&str) -> Option<usize>
    {
        interpolate(
            replacement,
            |i, dst| {
                if let Some((s, e)) = self.get(i) {
                    dst.extend(&haystack[s..e]);
                }
            },
            name_to_index,
            dst,
        )
    }
}

pub trait Matcher {
    type LineMatcher: LineMatcher;

    /// Returns the start and end byte range of the first match in `haystack`
    /// after `at`, where the byte offsets are relative to that start of
    /// `haystack` (and not `at`). If no match exists, then `None` is returned.
    ///
    /// The text encoding of `haystack` is not strictly specified. Matchers are
    /// advised to assume UTF-8, or at worst, some ASCII compatible encoding.
    ///
    /// The significance of the starting point is that it takes the surrounding
    /// context into consideration. For example, the `\A` anchor can only
    /// match when `start == 0`.
    fn find_at(&self, haystack: &[u8], at: usize) -> Option<(usize, usize)>;

    /// Populates the first set of capture group matches from `haystack` into
    /// `matches` after `at`, where the byte offsets in each capturing group
    /// are relative to the start of `haystack` (and not `at`). If no match
    /// exists, then `false` is returned and the length of the given matches
    /// is set to `0`.
    ///
    /// The text encoding of `haystack` is not strictly specified. Matchers are
    /// advised to assume UTF-8, or at worst, some ASCII compatible encoding.
    ///
    /// The significance of the starting point is that it takes the surrounding
    /// context into consideration. For example, the `\A` anchor can only
    /// match when `start == 0`.
    ///
    /// By default, capturing groups aren't supported, and this implementation
    /// will always behave as if a match were impossible.
    ///
    /// Implementors that provide support for capturing groups must guarantee
    /// that when a match occurs, the first capture match (at index `0`) is
    /// always set to the overall match offsets.
    #[allow(unused_variables)]
    fn captures_at(
        &self,
        haystack: &[u8],
        at: usize,
        matches: &mut CaptureMatches,
    ) -> bool {
        matches.0.clear();
        false
    }

    /// Returns the total number of capturing groups in this matcher.
    ///
    /// If a matcher supports capturing groups, then this value must always
    /// be 1, where the first capturing group always corresponds to the overall
    /// match.
    ///
    /// If a matcher does not support capturing groups, then this should
    /// always return 0.
    ///
    /// By default, capturing groups are not supported, so this always
    /// returns 0.
    fn capture_count(&self) -> usize {
        0
    }

    /// Maps the given capture group name to its corresponding capture group
    /// index, if one exists. If one does not exist, then `None` is returned.
    ///
    /// If the given capture group name maps to multiple indices, then it is
    /// not specified which one is returned. However, it is guaranteed that
    /// one of them is returned.
    ///
    /// By default, capturing groups are not supported, so this always returns
    /// `None`.
    #[allow(unused_variables)]
    fn capture_index(&self, name: &str) -> Option<usize> {
        None
    }

    /// Returns the start and end byte range of the first match in `haystack`.
    /// If no match exists, then `None` is returned.
    ///
    /// The text encoding of `haystack` is not strictly specified. Matchers are
    /// advised to assume UTF-8, or at worst, some ASCII compatible encoding.
    fn find(&self, haystack: &[u8]) -> Option<(usize, usize)> {
        self.find_at(haystack, 0)
    }

    /// Executes the given function over successive non-overlapping matches
    /// in `haystack`. If no match exists, then the given function is never
    /// called. If the function returns `false`, then iteration stops.
    fn find_iter<F>(&self, haystack: &[u8], mut matched: F)
    where F: FnMut(usize, usize) -> bool
    {
        let mut last_end = 0;
        let mut last_match = None;

        loop {
            if last_end > haystack.len() {
                return;
            }
            let (s, e) = match self.find_at(haystack, last_end) {
                None => return,
                Some((s, e)) => (s, e),
            };
            if s == e {
                // This is an empty match. To ensure we make progress, start
                // the next search at the smallest possible starting position
                // of the next match following this one.
                last_end = e + 1;
                // Don't accept empty matches immediately following a match.
                // Just move on to the next match.
                if Some(e) == last_match {
                    continue;
                }
            } else {
                last_end = e;
            }
            last_match = Some(e);
            if !matched(s, e) {
                return;
            }
        }
    }

    /// Populates the first set of capture group matches from `haystack` into
    /// `matches`. If no match exists, then `false` is returned.
    ///
    /// The text encoding of `haystack` is not strictly specified. Matchers are
    /// advised to assume UTF-8, or at worst, some ASCII compatible encoding.
    fn captures(&self, haystack: &[u8], matches: &mut CaptureMatches) -> bool {
        self.captures_at(haystack, 0, matches)
    }

    /// Executes the given function over successive non-overlapping matches
    /// in `haystack` with capture groups extracted from each match. If no
    /// match exists, then the given function is never called. If the function
    /// returns `false`, then iteration stops.
    fn captures_iter<F>(
        &self,
        haystack: &[u8],
        matches: &mut CaptureMatches,
        mut matched: F,
    )
    where F: FnMut(&mut CaptureMatches) -> bool
    {
        let mut last_end = 0;
        let mut last_match = None;

        loop {
            if last_end > haystack.len() {
                return;
            }
            if !self.captures_at(haystack, last_end, matches) {
                return;
            }
            let (s, e) = matches.get(0).unwrap();
            if s == e {
                // This is an empty match. To ensure we make progress, start
                // the next search at the smallest possible starting position
                // of the next match following this one.
                last_end = e + 1;
                // Don't accept empty matches immediately following a match.
                // Just move on to the next match.
                if Some(e) == last_match {
                    continue;
                }
            } else {
                last_end = e;
            }
            last_match = Some(e);
            if !matched(matches) {
                return;
            }
        }
    }

    /// Replaces every match in the given haystack with the result of calling
    /// `append`.
    ///
    /// If the given `append` function returns `false`, then replacement stops.
    fn replace<F>(
        &self,
        haystack: &[u8],
        dst: &mut Vec<u8>,
        mut append: F,
    )
    where F: FnMut(usize, usize, &mut Vec<u8>) -> bool
    {
        let mut last_match = 0;
        self.find_iter(haystack, |start, end| {
            dst.extend(&haystack[last_match..start]);
            last_match = end;
            append(start, end, dst)
        });
        dst.extend(&haystack[last_match..]);
    }

    /// Replaces every match in the given haystack with the result of calling
    /// `append` with the matching capture groups.
    ///
    /// If the given `append` function returns `false`, then replacement stops.
    fn replace_with_captures<F>(
        &self,
        haystack: &[u8],
        matches: &mut CaptureMatches,
        dst: &mut Vec<u8>,
        mut append: F,
    )
    where F: FnMut(&CaptureMatches, &mut Vec<u8>) -> bool
    {
        let mut last_match = 0;
        self.captures_iter(haystack, matches, |matches| {
            let (start, end) = matches.get(0).unwrap();
            dst.extend(&haystack[last_match..start]);
            last_match = end;
            append(matches, dst)
        });
        dst.extend(&haystack[last_match..]);
    }

    /// Returns an end location of the first match in `haystack`. If no match
    /// exists, then `None` is returned.
    ///
    /// Note that the end location reported by this method may be less than the
    /// same end location reported by `find`. For example, running `find` with
    /// the pattern `a+` on the haystack `aaa` should report a range of `[0,
    /// 3)`, but `shortest_match` may report `1` as the ending location since
    /// that is the place at which a match is guaranteed to occur.
    ///
    /// This method should never report false positives or false negatives. The
    /// point of this method is that some implementors may be able to provide
    /// a faster implementation of this than what `find` does.
    ///
    /// By default, this method is implemented by calling `find`.
    fn shortest_match(&self, haystack: &[u8]) -> Option<usize> {
        self.find(haystack).map(|(_, end)| end)
    }

    /// Returns a new matcher, if possible, that is optimized for matching
    /// lines.
    ///
    /// The `line_terminator` given is a single arbitrary byte that is used to
    /// terminate lines. Typically, this is `b'\n'`. The line matcher returned
    /// **must never** match the line terminator. That is, in the set of all
    /// possible strings matched, the line terminator must not appear in any of
    /// them. If an implementor cannot uphold this contract, then `None` **must
    /// be** returned. Violating this contract will result in unspecified
    /// behavior, which may include program crashes, loops or incorrect results
    /// (but never memory unsafety).
    ///
    /// The purpose of this method is to allow implementors to provide a
    /// routine for finding matching lines more quickly than what `find` or
    /// `shortest_match` can achieve.
    ///
    /// Implementors may choose to return an error if failing to build a line
    /// matcher would be undesirable or if some other unexpected problem
    /// occurred.
    #[allow(unused_variables)]
    fn line_matcher(
        &self,
        line_terminator: u8,
    ) -> Result<Option<Self::LineMatcher>, failure::Error> {
        Ok(None)
    }
}

impl<'a, M: Matcher> Matcher for &'a M {
    type LineMatcher = M::LineMatcher;

    fn find_at(&self, haystack: &[u8], at: usize) -> Option<(usize, usize)> {
        (*self).find_at(haystack, at)
    }

    fn captures_at(
        &self,
        haystack: &[u8],
        at: usize,
        matches: &mut CaptureMatches,
    ) -> bool {
        (*self).captures_at(haystack, at, matches)
    }

    fn capture_index(&self, name: &str) -> Option<usize> {
        (*self).capture_index(name)
    }

    fn capture_count(&self) -> usize {
        (*self).capture_count()
    }

    fn find(&self, haystack: &[u8]) -> Option<(usize, usize)> {
        (*self).find(haystack)
    }

    fn find_iter<F>(&self, haystack: &[u8], matched: F)
    where F: FnMut(usize, usize) -> bool
    {
        (*self).find_iter(haystack, matched)
    }

    fn captures(&self, haystack: &[u8], matches: &mut CaptureMatches) -> bool {
        (*self).captures(haystack, matches)
    }

    fn captures_iter<F>(
        &self,
        haystack: &[u8],
        matches: &mut CaptureMatches,
        matched: F,
    )
    where F: FnMut(&mut CaptureMatches) -> bool
    {
        (*self).captures_iter(haystack, matches, matched)
    }

    fn replace<F>(
        &self,
        haystack: &[u8],
        dst: &mut Vec<u8>,
        append: F,
    )
    where F: FnMut(usize, usize, &mut Vec<u8>) -> bool
    {
        (*self).replace(haystack, dst, append)
    }

    fn replace_with_captures<F>(
        &self,
        haystack: &[u8],
        matches: &mut CaptureMatches,
        dst: &mut Vec<u8>,
        append: F,
    )
    where F: FnMut(&CaptureMatches, &mut Vec<u8>) -> bool
    {
        (*self).replace_with_captures(haystack, matches, dst, append)
    }

    fn shortest_match(&self, haystack: &[u8]) -> Option<usize> {
        (*self).shortest_match(haystack)
    }

    fn line_matcher(
        &self,
        line_terminator: u8,
    ) -> Result<Option<Self::LineMatcher>, failure::Error> {
        (*self).line_matcher(line_terminator)
    }
}

impl<'a, L: LineMatcher> LineMatcher for &'a L {
    fn find_line(&self, haystack: &[u8]) -> Option<LineMatch> {
        (*self).find_line(haystack)
    }
}
