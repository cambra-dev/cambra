//! CHL lexer: logos for raw tokens, plus a layout post-pass that emits
//! `NEWLINE` / `INDENT` / `DEDENT` tokens following Python's off-side rule.
//!
//! Public entry point is [`tokenize`], which returns a flat `Vec` of
//! `(Token, Span)` ready to feed to the chumsky parser.
//!
//! ## Off-side rule mechanics
//!
//! At the start of each logical line, the lexer compares the line's
//! indentation (byte count of leading `' '` / `\t`) against an indent stack
//! (initialised to `[0]`):
//!
//! - `indent > stack.top` → push the new indent, emit `INDENT`.
//! - `indent < stack.top` → pop until `stack.top == indent`, emitting one
//!   `DEDENT` per pop. If no equal indent exists on the stack, emit an
//!   `InconsistentIndent` error.
//! - `indent == stack.top` → no layout tokens; the line continues the current
//!   block.
//!
//! Inside `(`/`[`/`{`, newlines are swallowed and indentation is ignored
//! (Python's implicit line continuation). At EOF, a synthetic `NEWLINE` is
//! emitted if the last token wasn't one, and the stack is fully unwound with
//! `DEDENT`s so every `INDENT` has a partner.

use crate::chl_parser::ast::Span;
use logos::Logos;
use smol_str::SmolStr;
use std::fmt;

/// The CHL token alphabet.
///
/// All variants except [`Token::Indent`] and [`Token::Dedent`] are produced
/// directly by logos. `Indent`/`Dedent` are synthesised by the layout pass in
/// [`tokenize`].
#[derive(Logos, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[logos(skip r"[ \t]+")] // horizontal whitespace inside a line
#[logos(skip r"#[^\n]*")] // comments (excluding the terminating newline)
pub enum Token {
    /// Physical newline. Suppressed inside brackets by the layout pass.
    #[token("\n")]
    Newline,

    /// Synthesised by the layout pass; never produced by logos.
    Indent,
    /// Synthesised by the layout pass; never produced by logos.
    Dedent,

    // -- Keywords ---------------------------------------------------------
    //
    // Priority 3 (vs. 2 for `Ident`'s regex) so keywords win when they would
    // otherwise tie with an identifier match of the same length.
    #[token("True", priority = 3)]
    True,
    #[token("False", priority = 3)]
    False,
    #[token("None", priority = 3)]
    None,
    #[token("and", priority = 3)]
    And,
    #[token("or", priority = 3)]
    Or,
    #[token("not", priority = 3)]
    Not,
    #[token("if", priority = 3)]
    If,
    #[token("elif", priority = 3)]
    Elif,
    #[token("else", priority = 3)]
    Else,
    #[token("for", priority = 3)]
    For,
    #[token("in", priority = 3)]
    In,
    #[token("def", priority = 3)]
    Def,
    #[token("lambda", priority = 3)]
    Lambda,
    #[token("return", priority = 3)]
    Return,
    #[token("yield", priority = 3)]
    Yield,
    #[token("pass", priority = 3)]
    Pass,

    // -- Multi-char operators (must precede their single-char prefixes) ---
    #[token("<<=")]
    LShiftEq,
    #[token("<<")]
    LShift,
    #[token("==")]
    EqEq,
    #[token("!=")]
    NotEq,
    #[token("<=")]
    LtE,
    #[token(">=")]
    GtE,
    #[token("++")]
    PlusPlus,
    #[token("+=")]
    PlusEq,
    #[token("-=")]
    MinusEq,
    #[token("*=")]
    StarEq,
    #[token("//=")]
    DoubleSlashEq,
    #[token("//")]
    DoubleSlash,

    // -- Single-char operators --------------------------------------------
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("&")]
    Amp,
    #[token("|")]
    Pipe,
    #[token("^")]
    Caret,
    #[token("=")]
    Eq,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,

    // -- Punctuation ------------------------------------------------------
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token(",")]
    Comma,
    #[token(":")]
    Colon,
    #[token(".")]
    Dot,
    #[token(";")]
    Semi,

    // -- Literals ---------------------------------------------------------
    /// Decimal integer literal. `_` digit separators are not supported.
    #[regex(r"[0-9]+", |lex| lex.slice().parse::<i64>().ok())]
    Int(i64),

    /// String literal in either double-quoted (`"…"`) or single-quoted
    /// (`'…'`) form, with surrounding quotes stripped and the basic Python
    /// escape sequences (`\n`, `\t`, `\r`, `\\`, `\"`, `\'`, `\0`)
    /// processed. Unknown escapes preserve the backslash, matching the
    /// permissive behaviour the existing CHL tests rely on.
    #[regex(r#""([^"\\]|\\.)*""#, |lex| process_string(lex.slice(), '"'))]
    #[regex(r#"'([^'\\]|\\.)*'"#, |lex| process_string(lex.slice(), '\''))]
    String(String),

    /// Identifier. Priority 2 so a longer keyword like `else` is preferred
    /// over an `Ident` of equal length.
    #[regex(r"[A-Za-z_][A-Za-z0-9_]*", |lex| SmolStr::from(lex.slice()), priority = 2)]
    Ident(SmolStr),
}

/// User-facing rendering of a token, used by the parser's `Rich` error
/// formatter. Returns the bare symbol or literal text — chumsky's error
/// rendering already wraps it in `'…'`, so we deliberately do not.
///
/// Layout tokens (`Newline`/`Indent`/`Dedent`) and value-carrying tokens
/// (`Int`/`String`/`Ident`) use short descriptive names rather than their
/// content, since their content is rarely the discriminating fact in an
/// error message.
impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            // Layout
            Token::Newline => "newline",
            Token::Indent => "indent",
            Token::Dedent => "dedent",
            // Keywords
            Token::True => "True",
            Token::False => "False",
            Token::None => "None",
            Token::And => "and",
            Token::Or => "or",
            Token::Not => "not",
            Token::If => "if",
            Token::Elif => "elif",
            Token::Else => "else",
            Token::For => "for",
            Token::In => "in",
            Token::Def => "def",
            Token::Lambda => "lambda",
            Token::Return => "return",
            Token::Yield => "yield",
            Token::Pass => "pass",
            // Operators (multi-char before single-char)
            Token::LShiftEq => "<<=",
            Token::LShift => "<<",
            Token::EqEq => "==",
            Token::NotEq => "!=",
            Token::LtE => "<=",
            Token::GtE => ">=",
            Token::PlusPlus => "++",
            Token::PlusEq => "+=",
            Token::MinusEq => "-=",
            Token::StarEq => "*=",
            Token::DoubleSlashEq => "//=",
            Token::DoubleSlash => "//",
            Token::Plus => "+",
            Token::Minus => "-",
            Token::Star => "*",
            Token::Amp => "&",
            Token::Pipe => "|",
            Token::Caret => "^",
            Token::Eq => "=",
            Token::Lt => "<",
            Token::Gt => ">",
            // Punctuation
            Token::LParen => "(",
            Token::RParen => ")",
            Token::LBracket => "[",
            Token::RBracket => "]",
            Token::LBrace => "{",
            Token::RBrace => "}",
            Token::Comma => ",",
            Token::Colon => ":",
            Token::Dot => ".",
            Token::Semi => ";",
            // Value-carrying tokens — chumsky's `select!` matches the
            // variant, not a specific value, so these typically appear
            // only in "found …" positions. Descriptive names keep
            // diagnostics readable.
            Token::Int(_) => "integer literal",
            Token::String(_) => "string literal",
            Token::Ident(_) => "identifier",
        };
        f.write_str(s)
    }
}

/// Strip surrounding `quote` characters from `raw` and process backslash
/// escapes. `quote` is one of `'"'` / `'\''` — whichever the lexer rule
/// matched.
fn process_string(raw: &str, quote: char) -> Option<String> {
    let inner = raw.strip_prefix(quote)?.strip_suffix(quote)?;
    let mut out = String::with_capacity(inner.len());
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next()? {
            'n' => out.push('\n'),
            't' => out.push('\t'),
            'r' => out.push('\r'),
            '\\' => out.push('\\'),
            '"' => out.push('"'),
            '\'' => out.push('\''),
            '0' => out.push('\0'),
            // Unknown escapes: preserve the backslash, matching `rustpython`'s
            // permissive handling of source like `"\d+"` used in tests.
            other => {
                out.push('\\');
                out.push(other);
            }
        }
    }
    Some(out)
}

/// Errors produced by [`tokenize`].
#[derive(Debug, Clone, PartialEq)]
pub enum LexError {
    /// Logos failed to match any token rule starting at this span.
    InvalidToken { span: Span },
    /// A close bracket appeared with no matching open.
    UnmatchedClose { span: Span },
    /// EOF was reached with at least one open `(`, `[`, or `{` still
    /// unclosed. The `span` points at the end of input. We surface this
    /// explicitly because the layout pass swallows newlines inside
    /// brackets — without this error, an unclosed bracket would silently
    /// eat the rest of the file (no `NEWLINE`/`INDENT`/`DEDENT` emitted),
    /// making the surrounding parser useless.
    UnclosedBracket { span: Span },
    /// A dedent did not return the indent stack to a previous indent level
    /// (e.g. `0, 4, 2` — the `2` doesn't match `0` or `4`).
    InconsistentIndent { span: Span },
}

/// Tokenise `source` into a layout-resolved token stream.
///
/// Caller-visible invariants of the returned stream:
/// - Always ends with a `Newline` followed by zero or more `Dedent`s back to
///   indent zero, so block-closing rules in the parser have a uniform exit.
/// - `Indent` and `Dedent` are balanced (every `Indent` has a matching
///   `Dedent` later in the stream).
/// - No `Newline` appears between a `LParen`/`LBracket`/`LBrace` and its
///   matching closer.
pub fn tokenize(source: &str) -> Result<Vec<(Token, Span)>, LexError> {
    // Phase 1: raw logos token stream (span-attached, errors surfaced).
    let mut raw: Vec<(Token, Span)> = Vec::new();
    let mut lex = Token::lexer(source);
    while let Some(result) = lex.next() {
        let span = Span::from(lex.span());
        match result {
            Ok(tok) => raw.push((tok, span)),
            Err(()) => return Err(LexError::InvalidToken { span }),
        }
    }

    // Phase 2: apply the off-side rule.
    let mut out: Vec<(Token, Span)> = Vec::new();
    let mut indent_stack: Vec<usize> = vec![0];
    let mut bracket_depth: usize = 0;
    let mut at_line_start = true;

    for (tok, span) in &raw {
        // Blank lines and comment-only lines: their only token is `Newline`,
        // and we want them to not affect indentation or appear in the output.
        if at_line_start && matches!(tok, Token::Newline) {
            continue;
        }

        if at_line_start && bracket_depth == 0 {
            let line_start = source[..span.start].rfind('\n').map(|i| i + 1).unwrap_or(0);
            let indent = span.start - line_start;
            let current = *indent_stack.last().expect("stack invariant: non-empty");
            if indent > current {
                indent_stack.push(indent);
                out.push((Token::Indent, Span::new(line_start, span.start)));
            } else {
                while *indent_stack.last().expect("stack invariant: non-empty") > indent {
                    indent_stack.pop();
                    out.push((Token::Dedent, Span::new(span.start, span.start)));
                }
                if *indent_stack.last().expect("stack invariant: non-empty") != indent {
                    return Err(LexError::InconsistentIndent { span: *span });
                }
            }
        }
        at_line_start = false;

        match tok {
            Token::LParen | Token::LBracket | Token::LBrace => {
                bracket_depth += 1;
                out.push((tok.clone(), *span));
            }
            Token::RParen | Token::RBracket | Token::RBrace => {
                bracket_depth = bracket_depth
                    .checked_sub(1)
                    .ok_or(LexError::UnmatchedClose { span: *span })?;
                out.push((tok.clone(), *span));
            }
            Token::Newline => {
                if bracket_depth == 0 {
                    out.push((tok.clone(), *span));
                    at_line_start = true;
                }
                // Newlines inside brackets are swallowed (implicit continuation).
            }
            _ => out.push((tok.clone(), *span)),
        }
    }

    // Tail: surface unclosed brackets explicitly. Without this, the
    // bracket-depth tracker would have swallowed every `NEWLINE` after the
    // unclosed `(`/`[`/`{`, leaving the parser unable to see statement
    // boundaries for the rest of the file.
    let end_span = Span::new(source.len(), source.len());
    if bracket_depth > 0 {
        return Err(LexError::UnclosedBracket { span: end_span });
    }
    // Synthesise a trailing newline if needed, then dedent all the way
    // back to zero. Parsers can rely on this uniform shape.
    if !matches!(out.last(), Some((Token::Newline, _))) {
        out.push((Token::Newline, end_span));
    }
    while indent_stack.len() > 1 {
        indent_stack.pop();
        out.push((Token::Dedent, end_span));
    }

    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Strip spans for assertion brevity; spans are exercised separately.
    fn tokens(src: &str) -> Vec<Token> {
        tokenize(src).unwrap().into_iter().map(|(t, _)| t).collect()
    }

    #[test]
    fn empty_source() {
        assert_eq!(tokens(""), vec![Token::Newline]);
    }

    #[test]
    fn just_a_literal() {
        assert_eq!(tokens("42"), vec![Token::Int(42), Token::Newline]);
    }

    #[test]
    fn string_with_escapes() {
        let toks = tokens(r#""hello\n\tworld""#);
        assert_eq!(
            toks,
            vec![Token::String("hello\n\tworld".to_string()), Token::Newline]
        );
    }

    #[test]
    fn keywords_beat_idents() {
        let toks = tokens("if elif else for in def lambda not and or True False None");
        assert_eq!(
            toks,
            vec![
                Token::If,
                Token::Elif,
                Token::Else,
                Token::For,
                Token::In,
                Token::Def,
                Token::Lambda,
                Token::Not,
                Token::And,
                Token::Or,
                Token::True,
                Token::False,
                Token::None,
                Token::Newline,
            ]
        );
    }

    #[test]
    fn multi_char_operators() {
        assert_eq!(
            tokens("<< <<= == != <= >= // //= += -= *="),
            vec![
                Token::LShift,
                Token::LShiftEq,
                Token::EqEq,
                Token::NotEq,
                Token::LtE,
                Token::GtE,
                Token::DoubleSlash,
                Token::DoubleSlashEq,
                Token::PlusEq,
                Token::MinusEq,
                Token::StarEq,
                Token::Newline,
            ]
        );
    }

    #[test]
    fn comments_are_skipped_but_newline_is_preserved() {
        let toks = tokens("x # this is a comment\ny");
        assert_eq!(
            toks,
            vec![
                Token::Ident("x".into()),
                Token::Newline,
                Token::Ident("y".into()),
                Token::Newline,
            ]
        );
    }

    #[test]
    fn indent_dedent_basic_block() {
        let src = "def f():\n    x\n";
        assert_eq!(
            tokens(src),
            vec![
                Token::Def,
                Token::Ident("f".into()),
                Token::LParen,
                Token::RParen,
                Token::Colon,
                Token::Newline,
                Token::Indent,
                Token::Ident("x".into()),
                Token::Newline,
                Token::Dedent,
            ]
        );
    }

    #[test]
    fn nested_blocks() {
        let src = "def f():\n    if x:\n        y\n    z\n";
        let toks = tokens(src);
        // Sanity check: one Indent at the function level, one at the if, two
        // Dedents at the end (closing the if and the function).
        let indents = toks.iter().filter(|t| matches!(t, Token::Indent)).count();
        let dedents = toks.iter().filter(|t| matches!(t, Token::Dedent)).count();
        assert_eq!(indents, 2);
        assert_eq!(dedents, 2);
    }

    #[test]
    fn newlines_suppressed_inside_brackets() {
        // A list literal split across lines should produce no Newline between
        // the bracketed tokens.
        let toks = tokens("xs = [\n    1,\n    2,\n    3,\n]\n");
        let newlines_inside_brackets = toks
            .iter()
            .scan(0u32, |depth, t| {
                let prev_depth = *depth;
                match t {
                    Token::LBracket | Token::LParen | Token::LBrace => *depth += 1,
                    Token::RBracket | Token::RParen | Token::RBrace => *depth -= 1,
                    _ => {}
                }
                Some((prev_depth, t.clone()))
            })
            .filter(|(d, t)| *d > 0 && matches!(t, Token::Newline))
            .count();
        assert_eq!(newlines_inside_brackets, 0);
    }

    #[test]
    fn blank_lines_do_not_affect_indent() {
        let src = "def f():\n    x\n\n    y\n";
        let toks = tokens(src);
        let indents = toks.iter().filter(|t| matches!(t, Token::Indent)).count();
        let dedents = toks.iter().filter(|t| matches!(t, Token::Dedent)).count();
        assert_eq!(indents, 1);
        assert_eq!(dedents, 1);
    }

    #[test]
    fn inconsistent_indent_is_an_error() {
        // Indent to 4, dedent to 2 (which is neither 4 nor 0) — error.
        let src = "def f():\n    x\n  y\n";
        assert!(matches!(
            tokenize(src),
            Err(LexError::InconsistentIndent { .. })
        ));
    }
}
