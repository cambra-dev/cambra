//! An open document: its text as the editor holds it, and the parse of that
//! text (`cambra-lsp/design-cambra-lsp.md`, "Documents").

use chl_parser::ast::{Module, Span};
use chl_parser::line_index::{Encoding, LineCol, LineIndex};
use chl_parser::parser::ParseResult;
use chl_parser::{FileId, parse_module};
use lsp_types::{Position, Range, TextDocumentContentChangeEvent};
use std::cell::OnceCell;

pub(crate) struct Document {
    text: String,
    version: i32,
    index: LineIndex,
    /// What the protocol positions' columns count, chosen for the session at
    /// `initialize`.
    encoding: Encoding,
    /// The parse of `text`, made the first time it is asked for and
    /// discarded when `text` changes.
    parsed: OnceCell<ParseResult<Module>>,
}

impl Document {
    pub(crate) fn new(text: String, version: i32, encoding: Encoding) -> Document {
        Document {
            index: LineIndex::new(&text),
            text,
            version,
            encoding,
            parsed: OnceCell::new(),
        }
    }

    pub(crate) fn text(&self) -> &str {
        &self.text
    }

    pub(crate) fn version(&self) -> i32 {
        self.version
    }

    pub(crate) fn index(&self) -> &LineIndex {
        &self.index
    }

    /// The parse of the current text, parsing it if it has changed.
    pub(crate) fn parsed(&self) -> &ParseResult<Module> {
        self.parsed
            .get_or_init(|| parse_module(FileId::ROOT, &self.text))
    }

    /// Applies one edit from a `didChange`. A range whose start lies after its
    /// end is refused and leaves the text unchanged.
    pub(crate) fn apply(&mut self, change: TextDocumentContentChangeEvent) -> Result<(), String> {
        match change {
            TextDocumentContentChangeEvent::TextDocumentContentChangeWholeDocument(whole) => {
                self.text = whole.text;
            }
            TextDocumentContentChangeEvent::TextDocumentContentChangePartial(partial) => {
                let start = self.offset(partial.range.start);
                let end = self.offset(partial.range.end);
                if start > end {
                    return Err(format!("the edit's range {:?} is reversed", partial.range));
                }
                self.text.replace_range(start..end, &partial.text);
            }
        }
        self.index = LineIndex::new(&self.text);
        self.parsed = OnceCell::new();
        Ok(())
    }

    /// Records the version a `didChange` brings the document to.
    pub(crate) fn set_version(&mut self, version: i32) {
        self.version = version;
    }

    /// The byte offset of `pos`, clamped into the text
    /// ([`LineIndex::offset_in`]).
    fn offset(&self, pos: Position) -> usize {
        self.index.offset_in(
            &self.text,
            LineCol {
                line: pos.line as usize,
                col: pos.character as usize,
            },
            self.encoding,
        )
    }

    /// The protocol range of `span`, with columns in the session's encoding.
    pub(crate) fn range(&self, span: Span) -> Range {
        Range {
            start: self.position(span.start),
            end: self.position(span.end),
        }
    }

    pub(crate) fn position(&self, offset: usize) -> Position {
        let LineCol { line, col } = self.index.line_col_in(&self.text, offset, self.encoding);
        Position {
            line: to_u32(line),
            character: to_u32(col),
        }
    }

    /// The 0-based line `offset` is on.
    pub(crate) fn line(&self, offset: usize) -> u32 {
        to_u32(self.index.line_col(offset).line)
    }
}

/// Protocol positions are `u32`s; a document of 4 GiB or more is out of the
/// protocol's range anyway.
fn to_u32(n: usize) -> u32 {
    u32::try_from(n).unwrap_or(u32::MAX)
}

#[cfg(test)]
mod tests {
    use super::*;
    use lsp_types::TextDocumentContentChangePartial;

    // `range_length` is deprecated in the protocol, but the struct literal
    // must name it.
    #[allow(deprecated)]
    fn edit(start: (u32, u32), end: (u32, u32), text: &str) -> TextDocumentContentChangeEvent {
        let pos = |(line, character)| Position { line, character };
        TextDocumentContentChangeEvent::TextDocumentContentChangePartial(
            TextDocumentContentChangePartial {
                range: Range {
                    start: pos(start),
                    end: pos(end),
                },
                range_length: None,
                text: text.to_owned(),
            },
        )
    }

    #[test]
    fn edits_apply_in_order() {
        let mut doc = Document::new("x = 1\ny = 2\n".to_owned(), 1, Encoding::Utf8);
        doc.apply(edit((0, 4), (0, 5), "10")).unwrap();
        doc.apply(edit((1, 0), (1, 1), "z")).unwrap();
        assert_eq!(doc.text(), "x = 10\nz = 2\n");
    }

    #[test]
    fn positions_past_the_end_clamp() {
        let mut doc = Document::new("ab\ncd".to_owned(), 1, Encoding::Utf8);
        doc.apply(edit((0, 9), (9, 0), "!")).unwrap();
        assert_eq!(doc.text(), "ab!");
    }

    #[test]
    fn a_reversed_range_is_refused() {
        let mut doc = Document::new("abc".to_owned(), 1, Encoding::Utf8);
        assert!(doc.apply(edit((0, 2), (0, 1), "x")).is_err());
        assert_eq!(doc.text(), "abc");
    }

    #[test]
    fn a_column_inside_a_character_edits_from_its_start() {
        let mut doc = Document::new("é".to_owned(), 1, Encoding::Utf8);
        doc.apply(edit((0, 1), (0, 2), "e")).unwrap();
        assert_eq!(doc.text(), "e");
    }

    /// In UTF-16, `😀` is two columns and `é` one.
    #[test]
    fn utf16_edits_count_code_units() {
        let mut doc = Document::new("s = \"😀é\" $".to_owned(), 1, Encoding::Utf16);
        doc.apply(edit((0, 9), (0, 11), "")).unwrap();
        assert_eq!(doc.text(), "s = \"😀é\"");
        assert_eq!(
            doc.position(doc.text().len()),
            Position {
                line: 0,
                character: 9
            }
        );
    }

    /// splitmix64, as in `chl-parser/tests/lexer_recovery.rs`: deterministic
    /// and dependency-free, so a failure replays.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// Text built from ASCII, multi-byte characters and every line break.
    fn text(rng: &mut Rng) -> String {
        const PIECES: &[&str] = &["a", "x = 1", " ", "é", "€", "𝑥", "\n", "\r\n", "\r"];
        (0..rng.below(12))
            .map(|_| PIECES[rng.below(PIECES.len() as u64) as usize])
            .collect()
    }

    /// For random texts and edits, in each encoding: no edit panics, reversed
    /// and out-of-range ones included; every character boundary survives a
    /// trip through a position; a column agrees with the UTF-16 length of the
    /// line up to it; and every column on a line, including one inside a
    /// surrogate pair, names a character boundary at or before it.
    /// `CAMBRA_FUZZ_SEED` and `CAMBRA_FUZZ_N` pick the seed and the number of
    /// cases.
    #[test]
    fn random_edits_keep_positions_consistent() {
        let env = |key: &str, default: u64| {
            std::env::var(key)
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or(default)
        };
        let (seed, n) = (env("CAMBRA_FUZZ_SEED", 0x5EED), env("CAMBRA_FUZZ_N", 2000));
        let mut rng = Rng(seed);
        for case in 0..n {
            let encoding = [Encoding::Utf8, Encoding::Utf16][(case % 2) as usize];
            let at = format!("case {case} (CAMBRA_FUZZ_SEED={seed}, {encoding:?})");
            let mut doc = Document::new(text(&mut rng), 1, encoding);
            for _ in 0..rng.below(4) {
                let mut pos = || (rng.below(6) as u32, rng.below(8) as u32);
                let (start, end) = (pos(), pos());
                let replacement = text(&mut rng);
                let _ = doc.apply(edit(start, end, &replacement));
                assert_eq!(
                    *doc.index(),
                    LineIndex::new(doc.text()),
                    "{at}: the index follows the text"
                );
            }
            let text = doc.text();
            let width = |s: &str| match encoding {
                Encoding::Utf8 => s.len(),
                Encoding::Utf16 => s.encode_utf16().count(),
            };
            for offset in (0..=text.len()).filter(|&o| text.is_char_boundary(o)) {
                // An offset between `\r` and `\n` names the end of its line.
                let expected = if text[..offset].ends_with('\r') && text[offset..].starts_with('\n')
                {
                    offset - 1
                } else {
                    offset
                };
                let position = doc.position(offset);
                let line_start = doc
                    .index()
                    .line_range(position.line as usize)
                    .expect("the position's line exists")
                    .start;
                assert_eq!(
                    position.character as usize,
                    width(&text[line_start..expected]),
                    "{at}: the column of {offset} in {text:?}"
                );
                assert_eq!(doc.offset(position), expected, "{at}: {text:?} at {offset}");
            }
            for line in 0..doc.index().line_count() {
                let content = doc.index().line_range(line).expect("the line exists");
                for col in 0..=width(&text[content.clone()]) + 1 {
                    let offset = doc.offset(Position {
                        line: line as u32,
                        character: col as u32,
                    });
                    assert!(
                        text.is_char_boundary(offset)
                            && (content.start..=content.end).contains(&offset)
                            && width(&text[content.start..offset]) <= col,
                        "{at}: column {col} of line {line} in {text:?} gave {offset}"
                    );
                }
            }
        }
    }
}
