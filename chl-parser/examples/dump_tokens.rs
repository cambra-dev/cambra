//! Prints the highlight spans of CHL source files as JSON lines, one span per
//! line, for the editor highlight check (`editors/README.md`, "Editor
//! highlight check").
//!
//! ```text
//! cargo run -q -p chl-parser --example dump_tokens -- FILE...
//! ```
//!
//! Each line is `{"file", "start", "end", "line", "col", "class"}`. `start` and
//! `end` are byte offsets, `end` exclusive. `line` and `col` locate `start`,
//! both 1-based, with `col` counted in bytes as Vim's `col()` counts it.
//! `class` is a [`HighlightClass::name`]. A file that lexes with errors also
//! prints them to stderr, and makes the exit status 1.

use chl_parser::FileId;
use chl_parser::lexer::{HighlightClass, Highlighted, highlight};
use chl_parser::line_index::{LineCol, LineIndex};
use std::fmt::Write as _;
use std::io::Write as _;
use std::process::ExitCode;

fn main() -> ExitCode {
    let mut out = String::new();
    let mut failed = false;
    for path in std::env::args().skip(1) {
        let source = match std::fs::read_to_string(&path) {
            Ok(source) => source,
            Err(e) => {
                eprintln!("{path}: {e}");
                failed = true;
                continue;
            }
        };
        let Highlighted { spans, errors } = highlight(FileId::ROOT, &source);
        let index = LineIndex::new(&source);
        let line_col = |offset| {
            let LineCol { line, col } = index.line_col(offset);
            (line + 1, col + 1)
        };
        for e in &errors {
            let (line, col) = line_col(e.span().start);
            eprintln!("{path}:{line}:{col}: {e}");
            failed = true;
        }
        let file = json_string(&path);
        for (class, span) in spans {
            let (line, col) = line_col(span.start);
            writeln!(
                out,
                r#"{{"file":{file},"start":{},"end":{},"line":{line},"col":{col},"class":"{}"}}"#,
                span.start,
                span.end,
                HighlightClass::name(class),
            )
            .expect("writing to a String does not fail");
        }
    }
    std::io::stdout()
        .write_all(out.as_bytes())
        .expect("stdout is writable");
    if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

/// The 1-based line and 1-based byte column of byte `offset` in `source`.
/// `s` as a JSON string literal.
fn json_string(s: &str) -> String {
    let mut quoted = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => quoted.push_str("\\\""),
            '\\' => quoted.push_str("\\\\"),
            c if c.is_control() => {
                write!(quoted, "\\u{:04x}", u32::from(c))
                    .expect("writing to a String does not fail");
            }
            c => quoted.push(c),
        }
    }
    quoted.push('"');
    quoted
}
