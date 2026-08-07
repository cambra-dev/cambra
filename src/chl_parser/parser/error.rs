//! Error-handling and diagnostics types for the CHL parser.
//!
//! The grammar combinators in the parent [`super`] module produce chumsky
//! `Rich<Token, Span>` errors; this module owns the `'src`-free structured
//! form ([`ParseError`] / [`ParseErrorInfo`]) those are converted into, the
//! [`ParseResult`] wrapper that threads partial ASTs plus error lists out to
//! callers, and the ariadne-based rendering.
//!
//! ## Error message quality
//!
//! Errors are stored as structured [`ParseErrorInfo`] (preserving the
//! found token, the categorised expected set, and `.as_context()` spans)
//! rather than pre-rendered strings, so callers can render via:
//!
//! - `Display` for a one-line summary,
//! - [`ParseResult::render_errors`] / [`ParseResult::eprint_errors`] for
//!   ariadne output with source-code context and secondary spans,
//! - or directly off [`ParseErrorInfo`] for a custom diagnostic UI.
//!
//! See the design doc's "Error message quality" section for the three
//! layers (`Display` for tokens, targeted `.labelled(…)` annotations,
//! and operator-category collapsing in [`collect_errors`]).

use std::fmt;

use ariadne::{Color, Config, Label, Report, ReportKind, Source};
use chumsky::error::{Rich, RichPattern, RichReason};

use crate::chl_parser::ast::Span;
use crate::chl_parser::lexer::{LexError, Token};

/// Errors produced by [`parse_module`](super::parse_module) /
/// [`parse_expression`](super::parse_expression).
#[derive(Debug, Clone, PartialEq)]
pub enum ParseError {
    /// The lexer rejected the input before parsing could begin.
    Lex(LexError),
    /// A chumsky parser error, preserved in a `'src`-free structured form so
    /// it can be rendered later (with or without an ariadne source code
    /// context, see [`ParseResult::render_errors`]).
    Parse(ParseErrorInfo),
}

impl From<LexError> for ParseError {
    fn from(e: LexError) -> Self {
        ParseError::Lex(e)
    }
}

/// Structured payload for [`ParseError::Parse`].
///
/// Carries the same information chumsky's `Rich<Token, Span>` carries, but
/// dropped of `'src` lifetime and pre-categorised so the renderer doesn't
/// have to do the work twice.
#[derive(Debug, Clone, PartialEq)]
pub struct ParseErrorInfo {
    /// Primary span — the source range where the parser failed.
    pub span: Span,
    /// The message of a **custom** error — one a grammar rule raised itself
    /// with `Rich::custom` from a `validate`, rather than one chumsky derived
    /// from a failed token match. A rule raises one when the token sequence
    /// parsed fine but says something the grammar rejects (`{T}` is a
    /// well-formed brace group that is not a valid type), so the useful
    /// diagnostic is the rule's own sentence, not "found X, expected Y".
    /// Carrying it is load-bearing rather than cosmetic: `found`/`expected` are
    /// both empty for a custom error, so without this the whole diagnostic
    /// degrades to a bare "found end of input".
    pub custom: Option<String>,
    /// Token actually found at the failure point, or `None` for EOF.
    pub found: Option<Token>,
    /// What the parser would have accepted at this position, post-collapse:
    /// complete operator/postfix categories are merged into a single
    /// [`Expected::Category`] entry, the rest stay as [`Expected::Token`] /
    /// [`Expected::Label`] / [`Expected::EndOfInput`] / [`Expected::Other`].
    pub expected: Vec<Expected>,
    /// Surrounding-context labels populated by `.as_context()` on labelled
    /// productions, each paired with the span of the in-progress
    /// production. Outer contexts come *later* in the vector (chumsky
    /// pushes them inside-out as the call stack unwinds).
    pub context: Vec<(String, Span)>,
}

/// One entry in [`ParseErrorInfo::expected`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expected {
    /// A specific token. Rendered via [`Token`]'s `Display` impl.
    Token(Token),
    /// A named label attached with `.labelled(...)`, e.g. `"expression"`,
    /// `"identifier"`, `"function name"`.
    Label(String),
    /// A category produced by [`collect_errors`]'s collapsing pass when
    /// every member of the category appeared in the expected set. Static
    /// strings: `"binary operator"`, `"comparison operator"`,
    /// `"postfix operation"`, `"augmented-assignment operator"`.
    Category(&'static str),
    /// End-of-input.
    EndOfInput,
    /// Catch-all for chumsky's `Any` / `SomethingElse` / `Identifier`
    /// patterns we don't otherwise specialise. Rendered as
    /// `"something else"`.
    Other,
}

impl fmt::Display for Expected {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expected::Token(t) => write!(f, "'{t}'"),
            Expected::Label(l) => f.write_str(l),
            Expected::Category(c) => f.write_str(c),
            Expected::EndOfInput => f.write_str("end of input"),
            Expected::Other => f.write_str("something else"),
        }
    }
}

impl fmt::Display for ParseError {
    /// Single-line human-readable rendering. For source-context output
    /// (ariadne reports), call [`ParseResult::render_errors`] instead.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::Lex(e) => write!(f, "lex error: {e:?}"),
            ParseError::Parse(info) if info.custom.is_some() => {
                let msg = info.custom.as_deref().expect("guarded by the match arm");
                f.write_str(msg)?;
                for (label, span) in &info.context {
                    write!(f, " (in {label} at {span})")?;
                }
                Ok(())
            }
            ParseError::Parse(info) => {
                match &info.found {
                    Some(t) => write!(f, "found '{t}'")?,
                    None => write!(f, "found end of input")?,
                }
                if !info.expected.is_empty() {
                    f.write_str(", expected ")?;
                    for (i, exp) in info.expected.iter().enumerate() {
                        if i > 0 {
                            if i + 1 == info.expected.len() {
                                f.write_str(", or ")?;
                            } else {
                                f.write_str(", ")?;
                            }
                        }
                        write!(f, "{exp}")?;
                    }
                }
                for (label, span) in &info.context {
                    write!(f, " (in {label} at {span})")?;
                }
                Ok(())
            }
        }
    }
}

/// Output of [`parse_module`](super::parse_module) /
/// [`parse_expression`](super::parse_expression).
///
/// Carries *both* a (possibly partial) AST and a list of errors, so callers
/// can take advantage of error recovery: when a syntax error is hit, the
/// parser inserts an [`Expr::Error`](crate::chl_parser::ast::Expr::Error) or
/// [`Stmt::Error`](crate::chl_parser::ast::Stmt::Error) placeholder, records
/// the error, and keeps going. A file with three independent syntax errors
/// produces a `value: Some(_)` AST with three `Error` holes and a `errors`
/// vector of length three — all reported in one pass.
///
/// The `value` is `None` only when recovery could not produce *anything*
/// (currently: a lexer error, which aborts before parsing starts).
#[derive(Debug, Clone)]
pub struct ParseResult<T> {
    /// The (possibly partial) AST. Holes are filled with `Error` placeholders.
    pub value: Option<T>,
    /// Errors collected during parsing. Non-empty implies the AST contains
    /// `Error` placeholders.
    pub errors: Vec<ParseError>,
}

impl<T> ParseResult<T> {
    /// `true` iff parsing succeeded with no errors at all.
    pub fn is_ok(&self) -> bool {
        self.errors.is_empty() && self.value.is_some()
    }

    /// Collapse into a `Result`, treating any errors as failure. Convenient
    /// for call sites that don't care about partial output.
    pub fn into_result(self) -> Result<T, Vec<ParseError>> {
        if !self.errors.is_empty() {
            Err(self.errors)
        } else {
            self.value.ok_or_else(|| {
                vec![ParseError::Parse(ParseErrorInfo {
                    span: Span::new(0, 0),
                    custom: None,
                    found: None,
                    expected: vec![],
                    context: vec![],
                })]
            })
        }
    }

    /// Render every error as an ariadne report and return the combined
    /// output as a plain-ASCII string (ANSI colour codes stripped).
    /// `src_name` is the file/source identifier shown in the report
    /// header; `src` is the original source text.
    ///
    /// Each [`ParseError::Parse`] becomes one [`Report`] with a red
    /// primary label at the failure span plus one yellow secondary label
    /// per context entry (from `.as_context()` on labelled productions),
    /// showing the enclosing production. Lex errors get a single red
    /// label at the failure location.
    ///
    /// For interactive use, prefer [`Self::eprint_errors`] which writes directly
    /// to stderr with colour.
    pub fn render_errors(&self, src_name: &str, src: &str) -> String {
        let mut buf: Vec<u8> = Vec::new();
        for err in &self.errors {
            err.to_report_with_config(src_name, Config::default().with_color(false))
                .write((src_name, Source::from(src)), &mut buf)
                .expect("ariadne write should not fail on Vec<u8>");
        }
        String::from_utf8_lossy(&buf).into_owned()
    }

    /// Print every error to stderr via ariadne with colour.
    pub fn eprint_errors(&self, src_name: &str, src: &str) {
        for err in &self.errors {
            err.to_report(src_name)
                .eprint((src_name, Source::from(src)))
                .expect("ariadne eprint should not fail on stderr");
        }
    }
}

/// A byte range for an ariadne [`Label`], normalized so `start <= end`.
///
/// ariadne panics ("Label start is after its end") on an inverted range, and
/// chumsky hands us one for the `.as_context()` spans of an error raised by
/// `emitter.emit(…)` inside a `validate`: the context's start is recorded where
/// the labelled parser opened, while the error's own offset has not advanced
/// past it, so an outer context can come out as e.g. `3..2`. An inverted span
/// carries no extent, only a position, so collapse it to an empty span at the
/// context's start — that still points the "while parsing …" note at the right
/// place instead of aborting the whole report.
fn label_range(span: Span) -> std::ops::Range<usize> {
    span.start..span.end.max(span.start)
}

impl ParseError {
    /// Build an ariadne [`Report`] with default (colour-on) configuration.
    pub fn to_report<'a>(
        &self,
        src_name: &'a str,
    ) -> Report<'a, (&'a str, std::ops::Range<usize>)> {
        self.to_report_with_config(src_name, Config::default())
    }

    /// Build an ariadne [`Report`] using the supplied [`Config`]. Used by
    /// [`ParseResult::render_errors`] to disable colour for snapshot-style
    /// output; interactive callers should use [`Self::to_report`] (or
    /// [`ParseResult::eprint_errors`]) for the coloured default.
    pub fn to_report_with_config<'a>(
        &self,
        src_name: &'a str,
        config: Config,
    ) -> Report<'a, (&'a str, std::ops::Range<usize>)> {
        match self {
            ParseError::Lex(e) => {
                let (span, msg): (Span, &'static str) = match e {
                    LexError::InvalidToken { span } => (*span, "invalid token"),
                    LexError::UnmatchedClose { span } => (*span, "unmatched close-bracket"),
                    LexError::UnclosedBracket { span } => {
                        (*span, "unclosed bracket at end of input")
                    }
                    LexError::InconsistentIndent { span } => (*span, "inconsistent indentation"),
                };
                Report::build(ReportKind::Error, src_name, span.start)
                    .with_config(config)
                    .with_message("lex error")
                    .with_label(
                        Label::new((src_name, label_range(span)))
                            .with_message(msg)
                            .with_color(Color::Red),
                    )
                    .finish()
            }
            ParseError::Parse(info) => {
                let mut report = Report::build(ReportKind::Error, src_name, info.span.start)
                    .with_config(config)
                    .with_message("parse error")
                    .with_label(
                        Label::new((src_name, label_range(info.span)))
                            .with_message(primary_label_message(info))
                            .with_color(Color::Red),
                    );
                // chumsky pushes contexts inside-out as the parse stack
                // unwinds; reverse so the report reads outside-in.
                for (label, span) in info.context.iter().rev() {
                    report = report.with_label(
                        Label::new((src_name, label_range(*span)))
                            .with_message(format!("while parsing {label}"))
                            .with_color(Color::Yellow),
                    );
                }
                report.finish()
            }
        }
    }
}

fn primary_label_message(info: &ParseErrorInfo) -> String {
    // A rule that rejected what it parsed already said why, in a sentence
    // aimed at the construct; the derived found/expected pair would only
    // restate the tokens it accepted.
    if let Some(msg) = &info.custom {
        return msg.clone();
    }
    let mut s = String::new();
    match &info.found {
        Some(t) => s.push_str(&format!("found '{t}'")),
        None => s.push_str("found end of input"),
    }
    if !info.expected.is_empty() {
        s.push_str(", expected ");
        for (i, exp) in info.expected.iter().enumerate() {
            if i > 0 {
                if i + 1 == info.expected.len() {
                    s.push_str(", or ");
                } else {
                    s.push_str(", ");
                }
            }
            s.push_str(&format!("{exp}"));
        }
    }
    s
}

// ---------------------------------------------------------------------------
// Conversion from chumsky's `Rich` to our `ParseError` (with categorisation)
// ---------------------------------------------------------------------------

/// Operator/postfix categories. Each entry is `(category_name, members)`.
///
/// In [`rich_to_info`], if **every** member of a category appears in the
/// chumsky "expected" set, those members are removed from the per-token
/// list and a single [`Expected::Category`] entry is emitted in their
/// place. So `if x\n` (missing `:`) reports
/// `"expected binary operator, comparison operator, …, or ':'"` instead
/// of a 22-token wall.
///
/// Categories are non-overlapping. Tokens not in any category
/// (`Newline`, `Colon`, keywords like `if`/`for`/`def`, `Eq`, `LShift`)
/// always render individually — they carry the most disambiguating
/// information and rarely show up in large groups anyway.
const CATEGORIES: &[(&str, &[Token])] = &[
    (
        "binary operator",
        &[
            Token::Plus,
            Token::Minus,
            Token::Star,
            Token::DoubleSlash,
            Token::Amp,
            Token::Pipe,
            Token::Caret,
            Token::PlusPlus,
        ],
    ),
    (
        "comparison operator",
        &[
            Token::EqEq,
            Token::NotEq,
            Token::Lt,
            Token::LtE,
            Token::Gt,
            Token::GtE,
        ],
    ),
    ("boolean operator", &[Token::And, Token::Or]),
    (
        "postfix operation",
        &[Token::Dot, Token::LParen, Token::LBracket],
    ),
    (
        "augmented-assignment operator",
        &[
            Token::PlusEq,
            Token::MinusEq,
            Token::StarEq,
            Token::DoubleSlashEq,
            Token::LShiftEq,
        ],
    ),
];

/// Turn one chumsky `Rich` error into our `ParseErrorInfo`, applying the
/// category collapsing described on [`CATEGORIES`].
fn rich_to_info(err: Rich<'_, Token, Span>) -> ParseErrorInfo {
    let span = *err.span();
    let found = err.found().cloned();
    let custom = match err.reason() {
        RichReason::Custom(msg) => Some(msg.clone()),
        _ => None,
    };

    // Bucket each `RichPattern` entry.
    let mut tokens: Vec<Token> = Vec::new();
    let mut labels: Vec<String> = Vec::new();
    let mut has_eoi = false;
    let mut has_other = false;
    for pat in err.expected() {
        match pat {
            RichPattern::Token(t) => tokens.push((**t).clone()),
            RichPattern::Label(l) => labels.push(l.to_string()),
            RichPattern::EndOfInput => has_eoi = true,
            // `Any` / `SomethingElse` / `Identifier` fold into the
            // "something else" catch-all to avoid noise.
            _ => has_other = true,
        }
    }

    // Deduplicate.
    tokens.sort();
    tokens.dedup();
    labels.sort();
    labels.dedup();

    // Apply category collapsing: for each category, if every member is
    // present in `tokens`, remove them and emit a single category entry.
    let mut categories: Vec<&'static str> = Vec::new();
    for (name, members) in CATEGORIES {
        if members.iter().all(|m| tokens.contains(m)) {
            tokens.retain(|t| !members.contains(t));
            categories.push(name);
        }
    }

    // Assemble the final expected list: labels first (most semantic),
    // then categories, then specific tokens, then catch-alls.
    let mut expected: Vec<Expected> = Vec::new();
    expected.extend(labels.into_iter().map(Expected::Label));
    expected.extend(categories.into_iter().map(Expected::Category));
    expected.extend(tokens.into_iter().map(Expected::Token));
    if has_eoi {
        expected.push(Expected::EndOfInput);
    }
    if has_other {
        expected.push(Expected::Other);
    }

    let context = err
        .contexts()
        .map(|(pat, span)| {
            let label = match pat {
                RichPattern::Label(l) => l.to_string(),
                RichPattern::Token(t) => format!("'{}'", **t),
                _ => "...".to_string(),
            };
            (label, *span)
        })
        .collect();

    ParseErrorInfo {
        span,
        custom,
        found,
        expected,
        context,
    }
}

/// Convert a batch of chumsky errors (as returned by `into_output_errors`)
/// into the public [`ParseError`] form, applying category collapsing.
pub(super) fn collect_errors(errs: Vec<Rich<'_, Token, Span>>) -> Vec<ParseError> {
    errs.into_iter()
        .map(rich_to_info)
        .map(ParseError::Parse)
        .collect()
}
