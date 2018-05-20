use bytecount;
use memchr::{memchr, memrchr};

/// Count the number of occurrences of `line_term` in `bytes`.
pub fn count(bytes: &[u8], line_term: u8) -> u64 {
    bytecount::count(bytes, line_term) as u64
}

/// An iterator over lines in a particular slice of bytes.
///
/// This iterator avoids borrowing the bytes themselves, and instead requires
/// callers to explicitly provide the bytes when moving through the iterator.
/// While not idiomatic, this provides a simple way of iterating over lines
/// that doesn't require borrowing the slice itself, which can be convenient.
#[derive(Debug)]
pub struct LineIter {
    line_term: u8,
    pos: usize,
    end: usize,
}

impl LineIter {
    /// Create a new line iterator over the given range of bytes using the
    /// given line terminator.
    ///
    /// Callers should provide the actual bytes for each call to `next`. The
    /// same slice must be provided to each call.
    ///
    /// This panics if `start` is not less than or equal to `end`.
    pub fn new(line_term: u8, start: usize, end: usize) -> LineIter {
        assert!(start <= end);
        LineIter { line_term, pos: start, end }
    }

    /// Return the start and end position of the next line in the given bytes.
    ///
    /// The caller must past exactly the same slice of bytes for each call to
    /// `next`.
    ///
    /// The range returned includes the line terminator.
    pub fn next(&mut self, bytes: &[u8]) -> Option<(usize, usize)> {
        match memchr(self.line_term, &bytes[self.pos..self.end]) {
            None => {
                if self.pos < bytes.len() {
                    let start = self.pos;
                    self.pos = bytes.len();
                    Some((start, bytes.len()))
                } else {
                    None
                }
            }
            Some(line_end) => {
                let (start, end) = (self.pos, self.pos + line_end + 1);
                self.pos = end;
                Some((start, end))
            }
        }
    }
}

// Returns the starting index of the Nth line preceding `end`.
//
// If `buf` is empty, then `0` is returned. If `count` is `0`, then `end` is
// returned.
//
// If `end` points at a new line in `buf`, then searching starts as if `end`
// pointed immediately before the new line.
//
// The position returned corresponds to the first byte in the given line.

/// Returns a slice starting with the line that occurs `count` lines before the
/// last line in `bytes`. Lines are terminated by `line_term`. If `count` is
/// zero, then this returns the starting offset of the last line in `bytes`.
///
/// If `bytes` ends with a line terminator, then the terminator itself is
/// considered part of the last line.
pub fn preceding(bytes: &[u8], line_term: u8, count: usize) -> &[u8] {
    &bytes[preceding_by_pos(bytes, bytes.len(), line_term, count)..]
}

/// Returns the minimal starting offset of the line that occurs `count` lines
/// before the line containing `pos`. Lines are terminated by `line_term`.
/// If `count` is zero, then this returns the starting offset of the line
/// containing `pos`.
///
/// If `pos` points just past a line terminator, then it is considered part of
/// the line that it terminates. For example, given `bytes = b"abc\nxyz\n"`
/// and `pos = 7`, `preceding(bytes, pos, b'\n', 0)` returns `4` (as does `pos
/// = 8`) and `preceding(bytes, pos, `b'\n', 1)` returns `0`.
fn preceding_by_pos(
    bytes: &[u8],
    mut pos: usize,
    line_term: u8,
    mut count: usize,
) -> usize {
    if pos == 0 {
        return 0;
    } else if bytes[pos - 1] == b'\n' {
        pos -= 1;
    }
    loop {
        match memrchr(line_term, &bytes[..pos]) {
            None => {
                return 0;
            }
            Some(i) => {
                if count == 0 {
                    return i + 1;
                } else if i == 0 {
                    return 0;
                }
                count -= 1;
                pos = i;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Range;
    use super::*;

    const SHERLOCK: &'static str = "\
For the Doctor Watsons of this world, as opposed to the Sherlock
Holmeses, success in the province of detective work must always
be, to a very large extent, the result of luck. Sherlock Holmes
can extract a clew from a wisp of straw or a flake of cigar ash;
but Doctor Watson has to have it taken out for him and dusted,
and exhibited clearly, with a label attached.\
";

    fn lines(text: &str) -> Vec<&str> {
        let mut results = vec![];
        let mut it = LineIter::new(b'\n', 0, text.len());
        while let Some((s, e)) = it.next(text.as_bytes()) {
            results.push(&text[s..e]);
        }
        results
    }

    fn line_ranges(text: &str) -> Vec<Range<usize>> {
        let mut results = vec![];
        let mut it = LineIter::new(b'\n', 0, text.len());
        while let Some((start, end)) = it.next(text.as_bytes()) {
            results.push(Range { start, end });
        }
        results
    }

    fn prev(text: &str, pos: usize, count: usize) -> usize {
        preceding_by_pos(text.as_bytes(), pos, b'\n', count)
    }

    #[test]
    fn line_count() {
        assert_eq!(0, count(b"", b'\n'));
        assert_eq!(1, count(b"\n", b'\n'));
        assert_eq!(2, count(b"\n\n", b'\n'));
        assert_eq!(2, count(b"a\nb\nc", b'\n'));
    }

    #[test]
    fn line_iter() {
        assert_eq!(lines("abc"), vec!["abc"]);

        assert_eq!(lines("abc\n"), vec!["abc\n"]);
        assert_eq!(lines("abc\nxyz"), vec!["abc\n", "xyz"]);
        assert_eq!(lines("abc\nxyz\n"), vec!["abc\n", "xyz\n"]);

        assert_eq!(lines("abc\n\n"), vec!["abc\n", "\n"]);
        assert_eq!(lines("abc\n\n\n"), vec!["abc\n", "\n", "\n"]);
        assert_eq!(lines("abc\n\nxyz"), vec!["abc\n", "\n", "xyz"]);
        assert_eq!(lines("abc\n\nxyz\n"), vec!["abc\n", "\n", "xyz\n"]);
        assert_eq!(lines("abc\nxyz\n\n"), vec!["abc\n", "xyz\n", "\n"]);

        assert_eq!(lines("\n"), vec!["\n"]);
        assert_eq!(lines(""), Vec::<&str>::new());
    }

    #[test]
    fn preceding_lines_doc() {
        // These are the examples mentions in the documentation of `preceding`.
        let bytes = b"abc\nxyz\n";
        assert_eq!(4, preceding_by_pos(bytes, 7, b'\n', 0));
        assert_eq!(4, preceding_by_pos(bytes, 8, b'\n', 0));
        assert_eq!(0, preceding_by_pos(bytes, 7, b'\n', 1));
        assert_eq!(0, preceding_by_pos(bytes, 8, b'\n', 1));
    }

    #[test]
    fn preceding_lines_sherlock() {
        let t = SHERLOCK;
        let lines = line_ranges(t);

        // The following tests check the count == 0 case, i.e., finding the
        // beginning of the line containing the given position.
        assert_eq!(0, prev(t, 0, 0));
        assert_eq!(0, prev(t, 1, 0));
        // The line terminator is addressed by `end-1` and terminates the line
        // it is part of.
        assert_eq!(0, prev(t, lines[0].end - 1, 0));
        assert_eq!(lines[0].start, prev(t, lines[0].end, 0));
        // The end position of line addresses the byte immediately following a
        // line terminator, which puts it on the following line.
        assert_eq!(lines[1].start, prev(t, lines[0].end + 1, 0));

        // Now tests for count > 0.
        assert_eq!(0, prev(t, 0, 1));
        assert_eq!(0, prev(t, 0, 2));
        assert_eq!(0, prev(t, 1, 1));
        assert_eq!(0, prev(t, 1, 2));
        assert_eq!(0, prev(t, lines[0].end - 1, 1));
        assert_eq!(0, prev(t, lines[0].end - 1, 2));
        assert_eq!(0, prev(t, lines[0].end, 1));
        assert_eq!(0, prev(t, lines[0].end, 2));
        assert_eq!(lines[3].start, prev(t, lines[4].end - 1, 1));
        assert_eq!(lines[3].start, prev(t, lines[4].end, 1));
        assert_eq!(lines[4].start, prev(t, lines[4].end + 1, 1));

        // The last line has no line terminator.
        assert_eq!(lines[5].start, prev(t, lines[5].end, 0));
        assert_eq!(lines[5].start, prev(t, lines[5].end - 1, 0));
        assert_eq!(lines[4].start, prev(t, lines[5].end, 1));
        assert_eq!(lines[0].start, prev(t, lines[5].end, 5));
    }

    #[test]
    fn preceding_lines_short() {
        let t = "a\nb\nc\nd\ne\nf\n";
        let lines = line_ranges(t);
        assert_eq!(12, t.len());

        assert_eq!(lines[5].start, prev(t, lines[5].end, 0));
        assert_eq!(lines[4].start, prev(t, lines[5].end, 1));
        assert_eq!(lines[3].start, prev(t, lines[5].end, 2));
        assert_eq!(lines[2].start, prev(t, lines[5].end, 3));
        assert_eq!(lines[1].start, prev(t, lines[5].end, 4));
        assert_eq!(lines[0].start, prev(t, lines[5].end, 5));
        assert_eq!(lines[0].start, prev(t, lines[5].end, 6));

        assert_eq!(lines[5].start, prev(t, lines[5].end - 1, 0));
        assert_eq!(lines[4].start, prev(t, lines[5].end - 1, 1));
        assert_eq!(lines[3].start, prev(t, lines[5].end - 1, 2));
        assert_eq!(lines[2].start, prev(t, lines[5].end - 1, 3));
        assert_eq!(lines[1].start, prev(t, lines[5].end - 1, 4));
        assert_eq!(lines[0].start, prev(t, lines[5].end - 1, 5));
        assert_eq!(lines[0].start, prev(t, lines[5].end - 1, 6));

        assert_eq!(lines[4].start, prev(t, lines[5].start, 0));
        assert_eq!(lines[3].start, prev(t, lines[5].start, 1));
        assert_eq!(lines[2].start, prev(t, lines[5].start, 2));
        assert_eq!(lines[1].start, prev(t, lines[5].start, 3));
        assert_eq!(lines[0].start, prev(t, lines[5].start, 4));
        assert_eq!(lines[0].start, prev(t, lines[5].start, 5));

        assert_eq!(lines[3].start, prev(t, lines[4].end - 1, 1));
        assert_eq!(lines[2].start, prev(t, lines[4].start, 1));

        assert_eq!(lines[2].start, prev(t, lines[3].end - 1, 1));
        assert_eq!(lines[1].start, prev(t, lines[3].start, 1));

        assert_eq!(lines[1].start, prev(t, lines[2].end - 1, 1));
        assert_eq!(lines[0].start, prev(t, lines[2].start, 1));

        assert_eq!(lines[0].start, prev(t, lines[1].end - 1, 1));
        assert_eq!(lines[0].start, prev(t, lines[1].start, 1));

        assert_eq!(lines[0].start, prev(t, lines[0].end - 1, 1));
        assert_eq!(lines[0].start, prev(t, lines[0].start, 1));
    }

    #[test]
    fn preceding_lines_empty1() {
        let t = "\n\n\nd\ne\nf\n";
        let lines = line_ranges(t);
        assert_eq!(9, t.len());

        assert_eq!(lines[0].start, prev(t, lines[0].end, 0));
        assert_eq!(lines[0].start, prev(t, lines[0].end, 1));
        assert_eq!(lines[1].start, prev(t, lines[1].end, 0));
        assert_eq!(lines[0].start, prev(t, lines[1].end, 1));

        assert_eq!(lines[5].start, prev(t, lines[5].end, 0));
        assert_eq!(lines[4].start, prev(t, lines[5].end, 1));
        assert_eq!(lines[3].start, prev(t, lines[5].end, 2));
        assert_eq!(lines[2].start, prev(t, lines[5].end, 3));
        assert_eq!(lines[1].start, prev(t, lines[5].end, 4));
        assert_eq!(lines[0].start, prev(t, lines[5].end, 5));
        assert_eq!(lines[0].start, prev(t, lines[5].end, 6));
    }

    #[test]
    fn preceding_lines_empty2() {
        let t = "a\n\n\nd\ne\nf\n";
        let lines = line_ranges(t);
        assert_eq!(10, t.len());

        assert_eq!(lines[0].start, prev(t, lines[0].end, 0));
        assert_eq!(lines[0].start, prev(t, lines[0].end, 1));
        assert_eq!(lines[1].start, prev(t, lines[1].end, 0));
        assert_eq!(lines[0].start, prev(t, lines[1].end, 1));

        assert_eq!(lines[5].start, prev(t, lines[5].end, 0));
        assert_eq!(lines[4].start, prev(t, lines[5].end, 1));
        assert_eq!(lines[3].start, prev(t, lines[5].end, 2));
        assert_eq!(lines[2].start, prev(t, lines[5].end, 3));
        assert_eq!(lines[1].start, prev(t, lines[5].end, 4));
        assert_eq!(lines[0].start, prev(t, lines[5].end, 5));
        assert_eq!(lines[0].start, prev(t, lines[5].end, 6));
    }
}
