use std::cell::{Cell, RefCell};
use std::cmp;
use std::fmt;

use memchr::memchr;

use lines::{self, LineStep};
use line_buffer::BinaryDetection;
use matcher::{LineMatchKind, Match, Matcher};
use searcher::{Config, Searcher};
use sink::{Sink, SinkFinish, SinkContext, SinkContextKind, SinkMatch};

#[derive(Debug)]
pub struct Core<'s, M: 's, S> {
    config: &'s Config,
    matcher: &'s M,
    searcher: &'s Searcher<M>,
    sink: RefCell<S>,
    binary: bool,
    pos: Cell<usize>,
    absolute_byte_offset: Cell<u64>,
    binary_byte_offset: Cell<Option<usize>>,
    line_number: Option<Cell<u64>>,
    last_line_counted: Cell<usize>,
    last_line_visited: Cell<usize>,
    after_context_left: Cell<usize>,
    has_sunk: Cell<bool>,
}

impl<'s, M, S> Core<'s, M, S>
where M: Matcher,
      M::Error: fmt::Display,
      S: Sink
{
    pub fn new(
        searcher: &'s Searcher<M>,
        sink: S,
        binary: bool,
    ) -> Core<'s, M, S> {
        let line_number =
            if searcher.config.line_number {
                Some(Cell::new(1))
            } else {
                None
            };
        Core {
            config: &searcher.config,
            matcher: &searcher.matcher,
            searcher: searcher,
            sink: RefCell::new(sink),
            binary: binary,
            pos: Cell::new(0),
            absolute_byte_offset: Cell::new(0),
            binary_byte_offset: Cell::new(None),
            line_number: line_number,
            last_line_counted: Cell::new(0),
            last_line_visited: Cell::new(0),
            after_context_left: Cell::new(0),
            has_sunk: Cell::new(false),
        }
    }

    pub fn roll(&self, absolute_byte_offset: u64, buf: &[u8]) -> usize {
        let consumed =
            if self.config.max_context() == 0 {
                buf.len()
            } else {
                // It might seem like all we need to care about here is just
                // the "before context," but in order to sink the context
                // separator (when before_context==0 and after_context>0), we
                // need to know something about the position of the previous
                // line visited, even if we're at the beginning of the buffer.
                let context_start = lines::preceding(
                    buf,
                    self.config.line_term,
                    self.config.max_context(),
                );
                let consumed = cmp::max(
                    context_start,
                    self.last_line_visited.get(),
                );
                consumed
            };
        self.count_lines(buf, consumed);
        self.absolute_byte_offset.set(absolute_byte_offset + consumed as u64);
        self.last_line_counted.set(0);
        self.last_line_visited.set(0);
        self.set_pos(buf.len() - consumed);
        consumed
    }

    fn config(&self) -> &Config {
        &self.config
    }

    pub fn finish(
        &self,
        byte_count: u64,
        binary_byte_offset: Option<u64>,
    ) -> Result<(), S::Error> {
        self.sink.borrow_mut().finish(
            &self.searcher,
            &SinkFinish {
                byte_count,
                binary_byte_offset,
            })
    }

    fn is_line_by_line_fast(&self) -> bool {
        assert!(!self.config.multi_line);

        match self.matcher.line_terminator() {
            None => false,
            Some(line_term) => line_term == self.config.line_term,
        }
    }

    pub fn pos(&self) -> usize {
        self.pos.get()
    }

    pub fn set_pos(&self, pos: usize) {
        self.pos.set(pos);
    }

    fn line_number(&self) -> Option<u64> {
        self.line_number.as_ref().map(|cell| cell.get())
    }

    fn count_lines(&self, buf: &[u8], upto: usize) {
        if let Some(ref line_number) = self.line_number {
            if self.last_line_counted.get() >= upto {
                return;
            }
            let slice = &buf[self.last_line_counted.get()..upto];
            let count = lines::count(slice, self.config.line_term);
            line_number.set(line_number.get() + count);
            self.last_line_counted.set(upto);
        }
    }

    pub fn binary_byte_offset(&self) -> Option<u64> {
        self.binary_byte_offset.get().map(|offset| offset as u64)
    }

    pub fn detect_binary(&self, buf: &[u8], range: &Match) -> bool {
        if self.binary_byte_offset.get().is_some() {
            return true;
        }
        let binary_byte = match self.config.binary.0 {
            BinaryDetection::Quit(b) => b,
            _ => return false,
        };
        if let Some(i) = memchr(binary_byte, &buf[*range]) {
            let offset = Some(range.start() + i);
            self.binary_byte_offset.set(offset);
            true
        } else {
            false
        }
    }

    pub fn sink_matched(
        &self,
        buf: &[u8],
        range: &Match,
    ) -> Result<bool, S::Error> {
        if self.binary && self.detect_binary(buf, range) {
            return Ok(false);
        }
        if !self.sink_break_context(range.start())? {
            return Ok(false);
        }
        self.count_lines(buf, range.start());
        let offset = self.absolute_byte_offset.get() + range.start() as u64;
        let keepgoing = self.sink.borrow_mut().matched(
            &self.searcher,
            &SinkMatch {
                line_term: self.config.line_term,
                bytes: &buf[*range],
                absolute_byte_offset: offset,
                line_number: self.line_number(),
            },
        )?;
        if !keepgoing {
            return Ok(false);
        }
        self.last_line_visited.set(range.end());
        self.after_context_left.set(self.config.after_context);
        self.has_sunk.set(true);
        Ok(true)
    }

    pub fn match_by_line(&self, buf: &[u8]) -> Result<bool, S::Error> {
        if self.is_line_by_line_fast() {
            self.match_by_line_fast(buf)
        } else {
            self.match_by_line_slow(buf)
        }
    }

    fn match_by_line_slow(&self, buf: &[u8]) -> Result<bool, S::Error> {
        assert!(!self.config.multi_line);

        let range = Match::new(self.pos(), buf.len());
        let mut stepper = LineStep::new(self.config.line_term, range);
        while let Some(line) = stepper.next(buf) {
            let matched = {
                // Stripping the line terminator is necessary to prevent some
                // classes of regexes from matching the empty position *after*
                // the end of the line. For example, `(?m)^$` will match at
                // position (2, 2) in the string `a\n`.
                let slice = lines::without_terminator(
                    &buf[line],
                    self.config.line_term,
                );
                match self.matcher.shortest_match(slice) {
                    Err(err) => return Err(S::error_message(err)),
                    Ok(result) => result.is_some(),
                }
            };
            self.set_pos(line.end());
            if matched != self.config.invert_match {
                if !self.before_context_by_line(buf, line.start())? {
                    return Ok(false);
                }
                if !self.sink_matched(buf, &line)? {
                    return Ok(false);
                }
            } else if self.after_context_left.get() >= 1 {
                if !self.sink_after_context(buf, &line)? {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }

    fn match_by_line_fast(&self, buf: &[u8]) -> Result<bool, S::Error> {
        while !buf[self.pos()..].is_empty() {
            if self.config.invert_match {
                if !self.match_by_line_fast_invert(buf)? {
                    return Ok(false);
                }
            } else if let Some(line) = self.find_by_line_fast(buf)? {
                if !self.after_context_by_line(buf, line.start())? {
                    return Ok(false);
                }
                if !self.before_context_by_line(buf, line.start())? {
                    return Ok(false);
                }
                self.set_pos(line.end());
                if !self.sink_matched(buf, &line)? {
                    return Ok(false);
                }
            } else {
                break;
            }
        }
        if !self.after_context_by_line(buf, buf.len())? {
            return Ok(false);
        }
        self.set_pos(buf.len());
        Ok(true)
    }

    fn match_by_line_fast_invert(&self, buf: &[u8]) -> Result<bool, S::Error> {
        assert!(self.config.invert_match);

        let invert_match = match self.find_by_line_fast(buf)? {
            None => {
                let m = Match::new(self.pos(), buf.len());
                self.set_pos(m.end());
                m
            }
            Some(line) => {
                let m = Match::new(self.pos(), line.start());
                self.set_pos(line.end());
                m
            }
        };
        if invert_match.is_empty() {
            return Ok(true);
        }
        if !self.after_context_by_line(buf, invert_match.start())? {
            return Ok(false);
        }
        if !self.before_context_by_line(buf, invert_match.start())? {
            return Ok(false);
        }
        self.count_lines(buf, invert_match.start());
        let mut stepper = LineStep::new(self.config.line_term, invert_match);
        while let Some(line) = stepper.next(buf) {
            if !self.sink_matched(buf, &line)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn find_by_line_fast(
        &self,
        buf: &[u8],
    ) -> Result<Option<Match>, S::Error> {
        assert!(!self.config.multi_line);
        assert_eq!(
            self.matcher.line_terminator().unwrap(),
            self.config.line_term,
            "requires a matcher's line terminator to match config",
        );

        let mut pos = self.pos.get();
        while !buf[pos..].is_empty() {
            match self.matcher.find_candidate_line(&buf[pos..]) {
                Err(err) => return Err(S::error_message(err)),
                Ok(None) => return Ok(None),
                Ok(Some(LineMatchKind::Confirmed(i))) => {
                    let line = lines::locate(
                        buf,
                        self.config.line_term,
                        Match::zero(i).offset(pos),
                    );
                    // If we matched beyond the end of the buffer, then we
                    // don't report this as a match.
                    if line.start() == buf.len() {
                        pos = buf.len();
                        continue;
                    }
                    return Ok(Some(line));
                }
                Ok(Some(LineMatchKind::Candidate(i))) => {
                    let line = lines::locate(
                        buf,
                        self.config.line_term,
                        Match::zero(i).offset(pos),
                    );
                    // We need to strip the line terminator here to match the
                    // semantics of line-by-line searching. Namely, regexes
                    // like `(?m)^$` can match at the final position beyond a
                    // line terminator, which is non-sensical in line oriented
                    // matching.
                    let slice = lines::without_terminator(
                        &buf[line],
                        self.config.line_term,
                    );
                    match self.matcher.is_match(slice) {
                        Err(err) => return Err(S::error_message(err)),
                        Ok(true) => return Ok(Some(line)),
                        Ok(false) => {
                            pos = line.end();
                            continue;
                        }
                    }
                }
            }
        }
        Ok(None)
    }

    fn sink_after_context(
        &self,
        buf: &[u8],
        range: &Match,
    ) -> Result<bool, S::Error> {
        assert!(self.after_context_left.get() >= 1);

        if self.binary && self.detect_binary(buf, range) {
            return Ok(false);
        }
        self.count_lines(buf, range.start());
        let offset = self.absolute_byte_offset.get() + range.start() as u64;
        let keepgoing = self.sink.borrow_mut().context(
            &self.searcher,
            &SinkContext {
                bytes: &buf[*range],
                kind: SinkContextKind::After,
                absolute_byte_offset: offset,
                line_number: self.line_number(),
            },
        )?;
        if !keepgoing {
            return Ok(false);
        }
        self.last_line_visited.set(range.end());
        self.after_context_left.set(self.after_context_left.get() - 1);
        self.has_sunk.set(true);
        Ok(true)
    }

    pub fn after_context_by_line(
        &self,
        buf: &[u8],
        upto: usize,
    ) -> Result<bool, S::Error> {
        if self.after_context_left.get() == 0 {
            return Ok(true);
        }
        let range = Match::new(self.last_line_visited.get(), upto);
        let mut stepper = LineStep::new(self.config.line_term, range);
        while let Some(line) = stepper.next(buf) {
            if !self.sink_after_context(buf, &line)? {
                return Ok(false);
            }
            if self.after_context_left.get() == 0 {
                break;
            }
        }
        Ok(true)
    }

    fn sink_before_context(
        &self,
        buf: &[u8],
        range: &Match,
    ) -> Result<bool, S::Error> {
        if self.binary && self.detect_binary(buf, range) {
            return Ok(false);
        }
        self.count_lines(buf, range.start());
        let offset = self.absolute_byte_offset.get() + range.start() as u64;
        let keepgoing = self.sink.borrow_mut().context(
            &self.searcher,
            &SinkContext {
                bytes: &buf[*range],
                kind: SinkContextKind::Before,
                absolute_byte_offset: offset,
                line_number: self.line_number(),
            },
        )?;
        if !keepgoing {
            return Ok(false);
        }
        self.last_line_visited.set(range.end());
        self.has_sunk.set(true);
        Ok(true)
    }

    pub fn before_context_by_line(
        &self,
        buf: &[u8],
        upto: usize,
    ) -> Result<bool, S::Error> {
        if self.config.before_context == 0 {
            return Ok(true);
        }
        let range = Match::new(self.last_line_visited.get(), upto);
        if range.is_empty() {
            return Ok(true);
        }
        let before_context_start = range.start() + lines::preceding(
            &buf[range],
            self.config.line_term,
            self.config.before_context - 1,
        );

        let range = Match::new(before_context_start, range.end());
        let mut stepper = LineStep::new(self.config.line_term, range);
        while let Some(line) = stepper.next(buf) {
            if !self.sink_break_context(line.start())? {
                return Ok(false);
            }
            if !self.sink_before_context(buf, &line)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn sink_break_context(
        &self,
        start_of_line: usize,
    ) -> Result<bool, S::Error> {
        let any_context =
            self.config.before_context > 0
            || self.config.after_context > 0;
        let is_gap =
            self.last_line_visited.get() < start_of_line;

        if !any_context || !self.has_sunk.get() || !is_gap {
            Ok(true)
        } else {
            self.sink.borrow_mut().context_break(&self.searcher)
        }
    }
}
