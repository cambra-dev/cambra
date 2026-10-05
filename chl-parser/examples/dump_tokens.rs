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
//! `class` is a [`HighlightClass::name`]. A file that fails to lex prints its
//! error to stderr and makes the exit status 1.

use chl_parser::lexer::{HighlightClass, highlight};
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
        let spans = match highlight(&source) {
            Ok(spans) => spans,
            Err(e) => {
                let (line, col) = line_col(&source, e.span().start);
                eprintln!("{path}:{line}:{col}: {e}");
                failed = true;
                continue;
            }
        };
        let file = json_string(&path);
        for (class, span) in spans {
            let (line, col) = line_col(&source, span.start);
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
fn line_col(source: &str, offset: usize) -> (usize, usize) {
    let before = &source[..offset];
    let line = before.bytes().filter(|&b| b == b'\n').count() + 1;
    let line_start = before.rfind('\n').map_or(0, |i| i + 1);
    (line, offset - line_start + 1)
}

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
