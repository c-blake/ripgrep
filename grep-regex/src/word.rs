use std::collections::HashMap;
use std::cell::RefCell;
use std::sync::Arc;

use grep_matcher::{Match, Matcher, NoError};
use regex::bytes::{CaptureLocations, Regex, RegexBuilder};
use thread_local::CachedThreadLocal;

use config::ConfiguredHIR;
use error::Error;
use RegexCaptures;

/// A matcher for implementing "word match" semantics.
#[derive(Debug)]
pub struct WordMatcher {
    /// The regex which is roughly `(?:^|\W)(<original pattern>)(?:$|\W)`.
    regex: Regex,
    /// A map from capture group name to capture group index.
    names: HashMap<String, usize>,
    /// A reusable buffer for finding the match location of the inner group.
    locs: Arc<CachedThreadLocal<RefCell<CaptureLocations>>>,
}

impl Clone for WordMatcher {
    fn clone(&self) -> WordMatcher {
        // We implement Clone manually so that we get a fresh CachedThreadLocal
        // such that it can set its own thread owner. This permits each thread
        // usings `locs` to hit the fast path.
        WordMatcher {
            regex: self.regex.clone(),
            names: self.names.clone(),
            locs: Arc::new(CachedThreadLocal::new()),
        }
    }
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
        let locs = Arc::new(CachedThreadLocal::new());

        let mut names = HashMap::new();
        for (i, optional_name) in regex.capture_names().enumerate() {
            if let Some(name) = optional_name {
                names.insert(name.to_string(), i);
            }
        }
        Ok(WordMatcher { regex, names, locs })
    }
}

type MResult<T> = Result<T, NoError>;

impl Matcher for WordMatcher {
    type Captures = RegexCaptures;
    type Error = NoError;

    fn find_at(
        &self,
        haystack: &[u8],
        at: usize,
    ) -> MResult<Option<Match>> {
        let cell = self.locs.get_or(|| {
            Box::new(RefCell::new(self.regex.capture_locations()))
        });
        let mut caps = cell.borrow_mut();
        self.regex.captures_read_at(&mut caps, haystack, at);
        Ok(caps.get(1).map(|m| Match::new(m.0, m.1)))
    }

    fn new_captures(&self) -> MResult<RegexCaptures> {
        Ok(RegexCaptures(self.regex.capture_locations()))
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
    ) -> MResult<()>
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
    ) -> MResult<bool> {
        Ok(self.regex.captures_read_at(&mut caps.0, haystack, at).is_some())
    }

    fn shortest_match_at(
        &self,
        haystack: &[u8],
        at: usize,
    ) -> MResult<Option<usize>> {
        Ok(self.regex.shortest_match_at(haystack, at))
    }
}

#[cfg(test)]
mod tests {
    use grep_matcher::Matcher;
    use config::{Config, ConfiguredHIR};
    use super::WordMatcher;

    #[test]
    fn scratch() {
        let chir = Config::default().hir(r"foo").unwrap();
        let wmatcher = WordMatcher::new(&chir).unwrap();

        let r = wmatcher.find(b"a^!foo@#");
        println!("{:?}", r);
    }
}
