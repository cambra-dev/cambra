//! Conversion between byte offsets into a source text and line/column
//! positions, the form editors and the Language Server Protocol use.
//!
//! A line ends at `\n`, at `\r\n`, or at a `\r` not followed by `\n`, the line
//! terminators the protocol defines. A column counts bytes from the line's
//! start.

/// A line and a byte column, both counted from 0.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LineCol {
    pub line: usize,
    pub col: usize,
}

/// The start of every line in one text, and where its content ends before the
/// line's terminator. It holds no copy of the text, so the methods that need
/// character boundaries take the text the index was built from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LineIndex {
    /// The byte offset each line starts at. The first is 0.
    starts: Vec<usize>,
    /// The byte offset each line's content ends at, before its terminator.
    ends: Vec<usize>,
}

impl LineIndex {
    pub fn new(text: &str) -> LineIndex {
        let bytes = text.as_bytes();
        let mut starts = vec![0];
        let mut ends = Vec::new();
        let mut i = 0;
        while i < bytes.len() {
            match bytes[i] {
                b'\n' => {
                    ends.push(i);
                    starts.push(i + 1);
                }
                b'\r' if bytes.get(i + 1) == Some(&b'\n') => {
                    ends.push(i);
                    starts.push(i + 2);
                    i += 1;
                }
                b'\r' => {
                    ends.push(i);
                    starts.push(i + 1);
                }
                _ => {}
            }
            i += 1;
        }
        ends.push(text.len());
        LineIndex { starts, ends }
    }

    /// The number of lines. A text ending in a line terminator has an empty
    /// last line after it.
    pub fn line_count(&self) -> usize {
        self.starts.len()
    }

    /// The byte range of `line`'s content, without its terminator, or `None`
    /// past the last line.
    pub fn line_range(&self, line: usize) -> Option<std::ops::Range<usize>> {
        Some(*self.starts.get(line)?..self.ends[line])
    }

    /// The line and column of `offset`. An offset inside a line terminator,
    /// between `\r` and `\n`, maps to the end of its line's content.
    ///
    /// # Panics
    ///
    /// When `offset` is past the end of the text.
    pub fn line_col(&self, offset: usize) -> LineCol {
        let last = *self.ends.last().expect("a text has at least one line");
        assert!(offset <= last, "offset {offset} is past the end ({last})");
        let line = self.starts.partition_point(|&start| start <= offset) - 1;
        LineCol {
            line,
            col: offset.min(self.ends[line]) - self.starts[line],
        }
    }

    /// The byte offset of `pos` in `text`, which this index was built from.
    /// Every position names an offset:
    ///
    /// - A line past the last one is the end of the text.
    /// - A column past the end of its line's content is the end of the
    ///   content, before the line's terminator.
    /// - A column inside a multi-byte character is the start of that
    ///   character.
    pub fn offset(&self, text: &str, pos: LineCol) -> usize {
        debug_assert_eq!(
            self.ends.last().copied(),
            Some(text.len()),
            "the index was built from another text"
        );
        let Some(&start) = self.starts.get(pos.line) else {
            return text.len();
        };
        let mut offset = start + pos.col.min(self.ends[pos.line] - start);
        while !text.is_char_boundary(offset) {
            offset -= 1;
        }
        offset
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lc(line: usize, col: usize) -> LineCol {
        LineCol { line, col }
    }

    #[test]
    fn every_line_terminator_ends_a_line() {
        let text = "a\nb\r\nc\rd";
        let index = LineIndex::new(text);
        assert_eq!(index.line_count(), 4);
        for (offset, expected) in [(0, lc(0, 0)), (2, lc(1, 0)), (5, lc(2, 0)), (7, lc(3, 0))] {
            assert_eq!(index.line_col(offset), expected, "offset {offset}");
            assert_eq!(index.offset(text, expected), offset);
        }
    }

    #[test]
    fn a_line_range_excludes_its_terminator() {
        let index = LineIndex::new("ab\r\ncd");
        assert_eq!(index.line_range(0), Some(0..2));
        assert_eq!(index.line_range(1), Some(4..6));
        assert_eq!(index.line_range(2), None);
    }

    #[test]
    fn a_trailing_terminator_leaves_an_empty_last_line() {
        let index = LineIndex::new("a\n");
        assert_eq!(index.line_count(), 2);
        assert_eq!(index.line_col(2), lc(1, 0));
    }

    #[test]
    fn an_offset_inside_crlf_is_the_end_of_its_line() {
        let index = LineIndex::new("ab\r\nc");
        assert_eq!(index.line_col(3), lc(0, 2));
    }

    #[test]
    fn positions_past_the_text_clamp() {
        let text = "ab\r\ncd";
        let index = LineIndex::new(text);
        assert_eq!(index.offset(text, lc(0, 99)), 2, "before the terminator");
        assert_eq!(index.offset(text, lc(5, 0)), text.len());
    }

    #[test]
    fn a_column_inside_a_character_is_its_start() {
        let text = "aé";
        let index = LineIndex::new(text);
        assert_eq!(index.offset(text, lc(0, 2)), 1);
        assert_eq!(index.offset(text, lc(0, 3)), 3);
    }
}
