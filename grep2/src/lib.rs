#![allow(dead_code)]

extern crate failure;

/// Indicates whether search is by line or across lines.
pub enum MatchMode {
    /// A "by line" search means that every match is guaranteed to correspond
    /// to exactly one line, and will never span multiple lines.
    ByLine,
    /// A "multi line" search means that matches are permitted to span across
    /// multiple lines.
    MultiLine,
}

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

// BREADCRUMBS: The matcher below needs to be filled out. e.g., find_iter
// and replace, I think. This in turn implies putting captures into the trait.
// Yuck. Make sure to scrutinize the replacer in ripgrep's printer, which does
// some fancy things for coloring... We might need to replicate the Replacer
// trait from Regex.

pub trait Matcher {
    type LineMatcher: LineMatcher;

    /// Returns the start and end byte range of the first match in `haystack`
    /// after `at`, where the byte offsets are relative to that start of
    /// `haystack` (and not `at`). If no match exists, then `None` is returned.
    ///
    /// The text encoding of `haystack` is not strictly specified. Matchers are
    /// advised to assume UTF-8, or at worst, some ASCII compatible encoding.
    fn find_at(&self, haystack: &[u8], at: usize) -> Option<(usize, usize)>;

    /// Returns the start and end byte range of the first match in `haystack`.
    /// If no match exists, then `None` is returned.
    ///
    /// The text encoding of `haystack` is not strictly specified. Matchers are
    /// advised to assume UTF-8, or at worst, some ASCII compatible encoding.
    fn find(&self, haystack: &[u8]) -> Option<(usize, usize)> {
        self.find_at(haystack, 0)
    }

    /// Returns an iterator over successive non-overlapping matches in
    /// `haystack`. If no match exists, then the iterator yields no matches.
    fn find_iter<'h, 'm>(
        &'m self,
        haystack: &'h [u8],
    ) -> FindMatches<'h, 'm, Self>
    where Self: Sized
    {
        FindMatches {
            matcher: self,
            haystack: haystack,
            last_end: 0,
            last_match: None,
        }
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

    fn find(&self, haystack: &[u8]) -> Option<(usize, usize)> {
        (*self).find(haystack)
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

#[derive(Debug)]
pub struct FindMatches<'h, 'm, M: 'm> {
    matcher: &'m M,
    haystack: &'h [u8],
    last_end: usize,
    last_match: Option<usize>,
}

impl<'h, 'm, M: Matcher> Iterator for FindMatches<'h, 'm, M> {
    type Item = (usize, usize);

    fn next(&mut self) -> Option<(usize, usize)> {
        if self.last_end > self.haystack.len() {
            return None;
        }
        let (s, e) = match self.matcher.find_at(self.haystack, self.last_end) {
            None => return None,
            Some((s, e)) => (s, e),
        };
        if s == e {
            // This is an empty match. To ensure we make progress, start
            // the next search at the smallest possible starting position
            // of the next match following this one.
            self.last_end = e + 1;
            // Don't accept empty matches immediately following a match.
            // Just move on to the next match.
            if Some(e) == self.last_match {
                return self.next();
            }
        } else {
            self.last_end = e;
        }
        self.last_match = Some(e);
        Some((s, e))
    }
}
