use regex_syntax::hir::Hir;

use error::{Error, ErrorKind};

/// Represents the type of line terminator to strip from a regex.
#[derive(Clone, Copy, Debug)]
pub enum LineTerminator {
    /// A special value that will prevent a regex from matching either a `\r`
    /// or a `\n`.
    CRLF,
    /// Prevent a regex from matching a substring that contains the given byte.
    Byte(u8),
}

impl Default for  LineTerminator {
    fn default() -> LineTerminator {
        LineTerminator::Byte(b'\n')
    }
}

/// Return an HIR that is guaranteed to never match the given line terminator,
/// if possible.
///
/// If the transformation isn't possible, then an error is returned.
///
/// In general, if a literal line terminator occurs anywhere in the HIR, then
/// this will return an error. However, if the line terminator occurs within
/// a character class with at least one other character (that isn't also a line
/// terminator), then the line terminator is simply stripped from that class.
///
/// If the given line terminator is not ASCII, then this function returns an
/// error.
pub fn strip_from_match(
    expr: Hir,
    line_term: LineTerminator,
) -> Result<Hir, Error> {
    if let LineTerminator::Byte(b) = line_term {
        if b > 0x7F {
            return Err(Error::new(ErrorKind::InvalidLineTerminator(b)));
        }
    }
    Ok(expr)
}
