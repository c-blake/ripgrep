use regex::bytes::{Regex, RegexBuilder};
use regex_syntax::ast::{self, Ast};
use regex_syntax::hir::Hir;

use ast::AstAnalysis;
use error::Error;
use literal::LiteralSets;
use strip::{LineTerminator, strip_from_match};

#[derive(Clone, Debug)]
pub struct Config {
    case_insensitive: bool,
    multi_line: bool,
    dot_matches_new_line: bool,
    swap_greed: bool,
    ignore_whitespace: bool,
    unicode: bool,
    octal: bool,
    size_limit: usize,
    dfa_size_limit: usize,
    nest_limit: u32,
    line_terminator: Option<LineTerminator>,
    case_smart: bool,
    crlf: bool,
    word: bool,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            case_insensitive: false,
            multi_line: false,
            dot_matches_new_line: false,
            swap_greed: false,
            ignore_whitespace: false,
            unicode: true,
            octal: false,
            size_limit: 100 * (1<<20),
            dfa_size_limit: 100 * (1<<20),
            nest_limit: 250,
            line_terminator: None,
            case_smart: false,
            crlf: false,
            word: false,
        }
    }
}

impl Config {
    pub fn hir(&self, pattern: &str) -> Result<ConfiguredHIR, Error> {
        let analysis = self.analysis(pattern)?;
        let expr = ::regex_syntax::ParserBuilder::new()
            .nest_limit(self.nest_limit)
            .octal(self.octal)
            .allow_invalid_utf8(true)
            .ignore_whitespace(self.ignore_whitespace)
            .case_insensitive(self.is_case_insensitive(&analysis)?)
            .multi_line(self.multi_line)
            .dot_matches_new_line(self.dot_matches_new_line)
            .swap_greed(self.swap_greed)
            .unicode(self.unicode)
            .build()
            .parse(pattern)
            .map_err(Error::regex)?;
        let expr = match self.line_terminator {
            None => expr,
            Some(line_term) => strip_from_match(expr, line_term)?,
        };
        Ok(ConfiguredHIR {
            original: pattern.to_string(),
            config: self.clone(),
            analysis: analysis,
            expr: expr,
        })
    }

    fn is_case_insensitive(
        &self,
        analysis: &AstAnalysis,
    ) -> Result<bool, Error> {
        if self.case_insensitive {
            return Ok(true);
        }
        if !self.case_smart {
            return Ok(false);
        }
        Ok(analysis.any_literal() && !analysis.any_uppercase())
    }

    fn analysis(&self, pattern: &str) -> Result<AstAnalysis, Error> {
        Ok(AstAnalysis::from_ast(&self.ast(pattern)?))
    }

    fn ast(&self, pattern: &str) -> Result<Ast, Error> {
        ast::parse::ParserBuilder::new()
            .nest_limit(self.nest_limit)
            .octal(self.octal)
            .ignore_whitespace(self.ignore_whitespace)
            .build()
            .parse(pattern)
            .map_err(Error::regex)
    }
}

#[derive(Clone, Debug)]
pub struct ConfiguredHIR {
    original: String,
    config: Config,
    analysis: AstAnalysis,
    expr: Hir,
}

impl ConfiguredHIR {
    pub fn regex(&self) -> Result<Regex, Error> {
        self.pattern_to_regex(&self.expr.to_string())
    }

    pub fn fast_line_regex(&self) -> Result<Option<Regex>, Error> {
        let line_term = match self.config.line_terminator {
            None => return Ok(None),
            Some(b) => b,
        };
        match LiteralSets::new(&self.expr).one_regex() {
            None => Ok(None),
            Some(pattern) => self.pattern_to_regex(&pattern).map(Some),
        }
    }

    pub fn with_pattern<F: FnMut(&str) -> String>(
        &self,
        mut f: F,
    ) -> Result<ConfiguredHIR, Error>
    {
        self.pattern_to_hir(&f(&self.expr.to_string()))
    }

    fn pattern_to_regex(&self, pattern: &str) -> Result<Regex, Error> {
        // The settings we explicitly set here are intentionally a subset
        // of the settings we have. The key point here is that our HIR
        // expression is computed with the settings in mind, such that setting
        // them here could actually lead to unintended behavior. For example,
        // consider the pattern `(?U)a+`. This will get folded into the HIR
        // as a non-greedy repetition operator which will in turn get printed
        // to the concrete syntax as `a+?`, which is correct. But if we
        // set the `swap_greed` option again, then we'll wind up with `(?U)a+?`
        // which is equal to `a+` which is not the same as what we were given.
        //
        // We also don't need to apply `case_insensitive` since this gets
        // folded into the HIR and would just cause us to do redundant work.
        //
        // Finally, we don't need to set `ignore_whitespace` since the concrete
        // syntax emitted by the HIR printer never needs it.
        //
        // We set the rest of the options. Some of them are important, such as
        // the size limit, and some of them are necessary to preserve the
        // intention of the original pattern. For example, the Unicode flag
        // will impact how the WordMatcher functions, namely, whether its
        // word boundaries are Unicode aware or not.
        RegexBuilder::new(&pattern)
            .nest_limit(self.config.nest_limit)
            .octal(self.config.octal)
            .multi_line(self.config.multi_line)
            .dot_matches_new_line(self.config.dot_matches_new_line)
            .unicode(self.config.unicode)
            .size_limit(self.config.size_limit)
            .dfa_size_limit(self.config.dfa_size_limit)
            .build()
            .map_err(Error::regex)
    }

    fn pattern_to_hir(&self, pattern: &str) -> Result<ConfiguredHIR, Error> {
        // See `pattern_to_regex` comment for explanation of why we only set
        // a subset of knobs here. e.g., `swap_greed` is explicitly left out.
        let expr = ::regex_syntax::ParserBuilder::new()
            .nest_limit(self.config.nest_limit)
            .octal(self.config.octal)
            .allow_invalid_utf8(true)
            .multi_line(self.config.multi_line)
            .dot_matches_new_line(self.config.dot_matches_new_line)
            .unicode(self.config.unicode)
            .build()
            .parse(pattern)
            .map_err(Error::regex)?;
        Ok(ConfiguredHIR {
            original: self.original.clone(),
            config: self.config.clone(),
            analysis: self.analysis.clone(),
            expr: expr,
        })
    }
}
