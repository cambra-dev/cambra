//! Chumsky parser for the CHL token stream produced by [`super::lexer`].
//!
//! The grammar lives in one big [`recursive`] expression parser plus a
//! recursive statement parser. The lexer-emitted `INDENT`/`DEDENT`/`NEWLINE`
//! tokens stand in for block structure, so the parser itself is layout-free —
//! it just matches `NEWLINE INDENT stmt+ DEDENT` for a multi-line block or
//! `simple_stmt NEWLINE` for a one-liner.
//!
//! ## Why `.boxed()` is liberal
//!
//! Chumsky 1.0-alpha leans on rustc's type inference for parser types, and
//! deeply-nested combinator chains create exponentially-sized types that
//! compile slowly (or not at all). `.boxed()` heap-allocates the parser at
//! that point and replaces the type with the uniform `Boxed<…>`, which both
//! speeds up compilation and avoids the `'static`-lifetime footguns that
//! deep dyn-trait inference produces (see [[reference-chumsky-gotchas]] in
//! Claude memory for the gory details).
//!
//! ## Recovery
//!
//! Two complementary layers, both implemented with chumsky's
//! `recover_with(via_parser(…))`:
//!
//! 1. **Bracket-level** (atom): a syntax error inside a balanced `(…)` /
//!    `[…]` / `{…}` region is skipped to the matching close-delimiter and
//!    produces an `Expr::Error` placeholder.
//! 2. **Statement-level** (statement): a syntax error that doesn't fit
//!    inside brackets makes the parser skip to the next `NEWLINE` (plus
//!    any attached `INDENT…DEDENT` block), produce a `Stmt::Error`
//!    placeholder, and resume with the next top-level statement.
//!
//! Both layers preserve the original chumsky error in the returned
//! `ParseResult::errors` list, so a file with multiple syntax errors
//! reports them all in one pass. See `design-chl-parser.md` (sibling
//! file) for the "Load-bearing detail" about `.at_least(1)` and the
//! lexer-level `UnclosedBracket` interaction.
//!
//! ## Error message quality
//!
//! Errors are stored as structured [`ParseErrorInfo`] (preserving the
//! found token, the categorised expected set, and `.as_context()` spans)
//! rather than pre-rendered strings, so callers can render via:
//!
//! - `Display` for a one-line summary,
//! - `ParseResult::render_errors` / `ParseResult::eprint_errors` for ariadne output
//!   with source-code context and secondary spans,
//! - or directly off `ParseErrorInfo` for a custom diagnostic UI.
//!
//! See the design doc's "Error message quality" section for the three
//! layers (`Display` for tokens, targeted `.labelled(…)` annotations,
//! and operator-category collapsing in [`collect_errors`]).

use std::fmt;

use ariadne::{Color, Config, Label, Report, ReportKind, Source};
use chumsky::error::{Rich, RichPattern};
use chumsky::input::{Input, ValueInput};
use chumsky::prelude::*;
use smol_str::SmolStr;

use crate::chl_parser::ast::{
    AssignTarget, AugOp, BinOp, BoolOp, CmpOp, CompClause, Comprehension, Expr, IfBranch, Lit,
    Module, Param, RecordField, Span, Spanned, Stmt, UnaryOp,
};
use crate::chl_parser::lexer::{self, LexError, Token};

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Errors produced by [`parse_module`] / [`parse_expression`].
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

/// Output of [`parse_module`] / [`parse_expression`].
///
/// Carries *both* a (possibly partial) AST and a list of errors, so callers
/// can take advantage of error recovery: when a syntax error is hit, the
/// parser inserts an [`Expr::Error`] or [`Stmt::Error`] placeholder, records
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
                        Label::new((src_name, span.into()))
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
                        Label::new((src_name, info.span.into()))
                            .with_message(primary_label_message(info))
                            .with_color(Color::Red),
                    );
                // chumsky pushes contexts inside-out as the parse stack
                // unwinds; reverse so the report reads outside-in.
                for (label, span) in info.context.iter().rev() {
                    report = report.with_label(
                        Label::new((src_name, (*span).into()))
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
            Token::At,
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
        found,
        expected,
        context,
    }
}

fn collect_errors(errs: Vec<Rich<'_, Token, Span>>) -> Vec<ParseError> {
    errs.into_iter()
        .map(rich_to_info)
        .map(ParseError::Parse)
        .collect()
}

/// Parse a CHL module: a sequence of top-level statements.
///
/// Returns a [`ParseResult`] carrying both the (possibly partial) AST and
/// the list of all parser errors. See [`ParseResult`] for the recovery
/// semantics.
pub fn parse_module(source: &str) -> ParseResult<Module> {
    let tokens = match lexer::tokenize(source) {
        Ok(t) => t,
        Err(e) => {
            return ParseResult {
                value: None,
                errors: vec![ParseError::from(e)],
            };
        }
    };
    let eof = Span::new(source.len(), source.len());
    let input = tokens.as_slice().map(eof, |(t, s)| (t, s));
    let (out, errs) = module_parser().parse(input).into_output_errors();
    ParseResult {
        value: out,
        errors: collect_errors(errs),
    }
}

/// Parse a single CHL expression. Used by the lowering tests that build
/// expressions in isolation; the parser still consumes the layout-resolved
/// token stream so `lambda` bodies and other multi-line forms work.
///
/// Recovery is in effect here too: a bracketed sub-expression with a syntax
/// error produces an [`Expr::Error`] node rather than aborting the whole
/// parse.
pub fn parse_expression(source: &str) -> ParseResult<Spanned<Expr>> {
    let tokens = match lexer::tokenize(source) {
        Ok(t) => t,
        Err(e) => {
            return ParseResult {
                value: None,
                errors: vec![ParseError::from(e)],
            };
        }
    };
    let eof = Span::new(source.len(), source.len());
    let input = tokens.as_slice().map(eof, |(t, s)| (t, s));
    let parser = expression()
        .then_ignore(just(Token::Newline).repeated())
        .then_ignore(end());
    let (out, errs) = parser.parse(input).into_output_errors();
    ParseResult {
        value: out,
        errors: collect_errors(errs),
    }
}

// ---------------------------------------------------------------------------
// Parser plumbing
// ---------------------------------------------------------------------------

/// Shorthand for the parser-error type used by every parser in this module.
///
/// Public combinator signatures take a generic `I: ValueInput<'src, Token =
/// Token, Span = Span>` rather than a concrete input alias, which lets
/// chumsky's type inference resolve the deeply-nested combinator types
/// without forcing us to name the mapper closure (see [[reference-chumsky-gotchas]]).
type PErr<'src> = extra::Err<Rich<'src, Token, Span>>;

// ---------------------------------------------------------------------------
// Expression parser
// ---------------------------------------------------------------------------

/// The full CHL expression grammar.
///
/// Precedence (lowest → highest):
/// 1. `lambda`, `yield`
/// 2. `x << y` (feed)
/// 3. `then if cond else else_` (ternary)
/// 4. `or`
/// 5. `and`
/// 6. `not`
/// 7. comparison chain (`==`, `!=`, `<`, `<=`, `>`, `>=`)
/// 8. `|`
/// 9. `^`
/// 10. `&`
/// 11. `@`
/// 12. `+`, `-`
/// 13. `*`, `//`
/// 14. unary `-`
/// 15. postfix: call `f(...)`, subscript `x[...]`, attribute `x.name`
/// 16. atom: literal, name, parenthesised, list, dict/record, comprehension
fn expression<'src, I>() -> impl Parser<'src, I, Spanned<Expr>, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
{
    recursive(|expr| {
        // ---- Atoms ---------------------------------------------------
        let lit = select! {
            Token::Int(n) => Expr::Lit(Lit::Int(n)),
            Token::String(s) => Expr::Lit(Lit::String(s)),
            Token::True => Expr::Lit(Lit::Bool(true)),
            Token::False => Expr::Lit(Lit::Bool(false)),
            Token::None => Expr::Lit(Lit::None),
        }
        .map_with(|node, e| Spanned::new(e.span(), node));

        let name =
            select! { Token::Ident(s) => s }.map_with(|s, e| Spanned::new(e.span(), Expr::Name(s)));

        let ident_only = select! { Token::Ident(s) => s }
            .map_with(|s, e| (s, e.span()))
            .labelled("identifier");

        // List literal / list comprehension. We parse the first element,
        // then peek for `for` (comprehension) vs `,` / `]` (list).
        let list_elements = expr
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect::<Vec<_>>();

        let comp_clauses = {
            let for_clause = just(Token::For)
                .ignore_then(expr.clone().try_map(|t, _| {
                    expr_to_assign_target(t)
                        .map_err(|bad| Rich::custom(bad, "invalid comprehension target"))
                }))
                .then_ignore(just(Token::In))
                .then(expr.clone())
                .map(|(target, iter)| CompClause::For { target, iter });
            let if_clause = just(Token::If)
                .ignore_then(expr.clone())
                .map(CompClause::If);
            choice((for_clause, if_clause))
                .repeated()
                .at_least(1)
                .collect::<Vec<_>>()
        };

        let list_or_listcomp = just(Token::LBracket)
            .ignore_then(
                // Empty list `[]`.
                just(Token::RBracket)
                    .map_with(|_, e| Spanned::new(e.span(), Expr::List(vec![])))
                    .or(expr
                        .clone()
                        .then(choice((
                            // Comprehension: first element, then `for ...`
                            comp_clauses.clone().map(Some),
                            // List: more elements (with optional leading comma)
                            empty().to(None),
                        )))
                        .then(
                            // After first element + optional comp, allow `, more...` for list
                            just(Token::Comma)
                                .ignore_then(list_elements.clone())
                                .or_not(),
                        )
                        .then_ignore(just(Token::RBracket))
                        .map_with(|((first, comp), rest), e| {
                            let span = e.span();
                            if let Some(clauses) = comp {
                                Spanned::new(
                                    span,
                                    Expr::ListComp(Comprehension {
                                        element: Box::new(first),
                                        clauses,
                                    }),
                                )
                            } else {
                                let mut elts = vec![first];
                                if let Some(rest) = rest {
                                    elts.extend(rest);
                                }
                                Spanned::new(span, Expr::List(elts))
                            }
                        })),
            )
            .boxed();

        // Parenthesised expression / tuple / generator expression.
        let paren_group = just(Token::LParen)
            .ignore_then(choice((
                // Empty tuple `()`.
                just(Token::RParen).map_with(|_, e| Spanned::new(e.span(), Expr::Tuple(vec![]))),
                expr.clone()
                    .then(choice((
                        // Generator expression `(expr for ...)`.
                        comp_clauses.clone().map(GroupTail::Gen),
                        // Tuple with trailing comma or more: `(a,)` or `(a, b, ...)`.
                        just(Token::Comma)
                            .ignore_then(list_elements.clone().or_not())
                            .map(|rest| GroupTail::Tuple(rest.unwrap_or_default())),
                        // Plain parenthesised expr.
                        empty().to(GroupTail::Group),
                    )))
                    .then_ignore(just(Token::RParen))
                    .map_with(|(first, tail), e| match tail {
                        GroupTail::Group => first, // re-use sub-expression's span via .node
                        GroupTail::Tuple(rest) => {
                            let mut elts = vec![first];
                            elts.extend(rest);
                            Spanned::new(e.span(), Expr::Tuple(elts))
                        }
                        GroupTail::Gen(clauses) => Spanned::new(
                            e.span(),
                            Expr::GenExp(Comprehension {
                                element: Box::new(first),
                                clauses,
                            }),
                        ),
                    }),
            )))
            .boxed();

        // Dict or record literal: `{}`, `{ident: expr, ...}` (record),
        // or `{expr: expr, ...}` (dict). We detect record-vs-dict by
        // whether *every* key parses as a bare identifier followed by
        // `:` — implemented by parsing an entry first as ident-or-expr.
        let dict_entry = expr
            .clone()
            .then_ignore(just(Token::Colon))
            .then(expr.clone())
            .map(|(k, v)| (k, v));
        let dict_or_record = just(Token::LBrace)
            .ignore_then(
                dict_entry
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>(),
            )
            .then_ignore(just(Token::RBrace))
            .map_with(|entries, e| {
                let span = e.span();
                // If every key is a bare Name, produce a Record; else a Dict.
                let all_idents = !entries.is_empty()
                    && entries.iter().all(|(k, _)| matches!(k.node, Expr::Name(_)));
                if all_idents {
                    let fields = entries
                        .into_iter()
                        .map(|(k, v)| match k.node {
                            Expr::Name(name) => RecordField {
                                name,
                                name_span: k.span,
                                value: v,
                            },
                            _ => unreachable!(),
                        })
                        .collect();
                    Spanned::new(span, Expr::Record(fields))
                } else {
                    Spanned::new(span, Expr::Dict(entries))
                }
            })
            .boxed();

        // The atom is the lowest level of expression precedence — failure
        // here is the most common "expected an expression here" diagnostic.
        // We label it so error messages collapse the 5+ atom alternatives
        // (literal, name, `(…)`, list, dict) into a single "expression"
        // label when the failure is at the atom's start position.
        let atom = choice((lit, list_or_listcomp, paren_group, dict_or_record, name))
            .labelled("expression")
            .recover_with(via_parser(nested_delimiters(
                Token::LParen,
                Token::RParen,
                [
                    (Token::LBracket, Token::RBracket),
                    (Token::LBrace, Token::RBrace),
                ],
                |span| Spanned::new(span, Expr::Error),
            )))
            .recover_with(via_parser(nested_delimiters(
                Token::LBracket,
                Token::RBracket,
                [
                    (Token::LParen, Token::RParen),
                    (Token::LBrace, Token::RBrace),
                ],
                |span| Spanned::new(span, Expr::Error),
            )))
            .recover_with(via_parser(nested_delimiters(
                Token::LBrace,
                Token::RBrace,
                [
                    (Token::LParen, Token::RParen),
                    (Token::LBracket, Token::RBracket),
                ],
                |span| Spanned::new(span, Expr::Error),
            )))
            .boxed();

        // ---- Postfix: call, subscript, attribute ---------------------
        let call_args = expr
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map(PostfixOp::Call);
        let subscript = expr
            .clone()
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map(|idx| PostfixOp::Subscript(Box::new(idx)));
        let attribute = just(Token::Dot)
            .ignore_then(ident_only)
            .map(|(name, span)| PostfixOp::Attribute(name, span));

        let postfix = atom
            .clone()
            .foldl_with(
                choice((call_args, subscript, attribute)).repeated(),
                |target, op, e| {
                    let span = e.span();
                    let node = match op {
                        PostfixOp::Call(args) => Expr::Call {
                            func: Box::new(target),
                            args,
                        },
                        PostfixOp::Subscript(index) => Expr::Subscript {
                            target: Box::new(target),
                            index,
                        },
                        PostfixOp::Attribute(attr, attr_span) => Expr::Attribute {
                            target: Box::new(target),
                            attr,
                            attr_span,
                        },
                    };
                    Spanned::new(span, node)
                },
            )
            .boxed();

        // ---- Unary minus --------------------------------------------
        let unary = recursive(|u| {
            just(Token::Minus)
                .ignore_then(u.clone())
                .map_with(|operand, e| {
                    Spanned::new(
                        e.span(),
                        Expr::UnaryOp {
                            op: UnaryOp::Neg,
                            operand: Box::new(operand),
                        },
                    )
                })
                .or(postfix.clone())
        })
        .boxed();

        // ---- Binary precedence chain --------------------------------
        // Helper: build a left-associative binop layer.
        let make_binop =
            |lhs: Spanned<Expr>, op: BinOp, rhs: Spanned<Expr>, span: Span| -> Spanned<Expr> {
                Spanned::new(
                    span,
                    Expr::BinOp {
                        left: Box::new(lhs),
                        op,
                        right: Box::new(rhs),
                    },
                )
            };

        // `.boxed()` at every precedence layer is load-bearing for stack
        // usage: without it, each `expr.clone()` re-entry monomorphizes
        // through 15+ deeply-nested combinator types, and ~4 levels of
        // nested function calls (`f(f(f(f(1))))`) is enough to overflow a
        // 2 MiB test thread stack. Boxing collapses the type at each
        // layer to a uniform `Boxed<…>`, so per-frame stack size stays
        // bounded.
        let product = unary
            .clone()
            .foldl_with(
                choice((
                    just(Token::Star).to(BinOp::Mul),
                    just(Token::DoubleSlash).to(BinOp::FloorDiv),
                ))
                .then(unary.clone())
                .repeated(),
                move |lhs, (op, rhs), e| make_binop(lhs, op, rhs, e.span()),
            )
            .boxed();

        let sum = product
            .clone()
            .foldl_with(
                choice((
                    just(Token::Plus).to(BinOp::Add),
                    just(Token::Minus).to(BinOp::Sub),
                ))
                .then(product.clone())
                .repeated(),
                move |lhs, (op, rhs), e| make_binop(lhs, op, rhs, e.span()),
            )
            .boxed();

        let collection_union = sum
            .clone()
            .foldl_with(
                just(Token::At)
                    .to(BinOp::CollectionUnion)
                    .then(sum.clone())
                    .repeated(),
                move |lhs, (op, rhs), e| make_binop(lhs, op, rhs, e.span()),
            )
            .boxed();

        let log_and = collection_union
            .clone()
            .foldl_with(
                just(Token::Amp)
                    .to(BinOp::LogicalAnd)
                    .then(collection_union.clone())
                    .repeated(),
                move |lhs, (op, rhs), e| make_binop(lhs, op, rhs, e.span()),
            )
            .boxed();

        let log_xor = log_and
            .clone()
            .foldl_with(
                just(Token::Caret)
                    .to(BinOp::LogicalXor)
                    .then(log_and.clone())
                    .repeated(),
                move |lhs, (op, rhs), e| make_binop(lhs, op, rhs, e.span()),
            )
            .boxed();

        let log_or = log_xor
            .clone()
            .foldl_with(
                just(Token::Pipe)
                    .to(BinOp::LogicalOr)
                    .then(log_xor.clone())
                    .repeated(),
                move |lhs, (op, rhs), e| make_binop(lhs, op, rhs, e.span()),
            )
            .boxed();

        // ---- Comparison chain (special: n-ary) ----------------------
        let cmp_op = choice((
            just(Token::EqEq).to(CmpOp::Eq),
            just(Token::NotEq).to(CmpOp::NotEq),
            just(Token::Lt).to(CmpOp::Lt),
            just(Token::LtE).to(CmpOp::LtE),
            just(Token::Gt).to(CmpOp::Gt),
            just(Token::GtE).to(CmpOp::GtE),
        ));
        let comparison = log_or
            .clone()
            .then(cmp_op.then(log_or.clone()).repeated().collect::<Vec<_>>())
            .map_with(|(first, rest), e| {
                if rest.is_empty() {
                    first
                } else {
                    let (ops, comparators): (Vec<_>, Vec<_>) = rest.into_iter().unzip();
                    Spanned::new(
                        e.span(),
                        Expr::Compare {
                            left: Box::new(first),
                            ops,
                            comparators,
                        },
                    )
                }
            })
            .boxed();

        // ---- `not` (right-associative prefix) -----------------------
        let bool_not = recursive(|n| {
            just(Token::Not)
                .ignore_then(n.clone())
                .map_with(|operand, e| {
                    Spanned::new(
                        e.span(),
                        Expr::UnaryOp {
                            op: UnaryOp::Not,
                            operand: Box::new(operand),
                        },
                    )
                })
                .or(comparison.clone())
        })
        .boxed();

        // ---- `and` / `or` (n-ary, flattened) ------------------------
        let bool_and = bool_not
            .clone()
            .then(
                just(Token::And)
                    .ignore_then(bool_not.clone())
                    .repeated()
                    .collect::<Vec<_>>(),
            )
            .map_with(|(first, rest), e| {
                if rest.is_empty() {
                    first
                } else {
                    let mut operands = vec![first];
                    operands.extend(rest);
                    Spanned::new(
                        e.span(),
                        Expr::BoolOp {
                            op: BoolOp::And,
                            operands,
                        },
                    )
                }
            })
            .boxed();

        let bool_or = bool_and
            .clone()
            .then(
                just(Token::Or)
                    .ignore_then(bool_and.clone())
                    .repeated()
                    .collect::<Vec<_>>(),
            )
            .map_with(|(first, rest), e| {
                if rest.is_empty() {
                    first
                } else {
                    let mut operands = vec![first];
                    operands.extend(rest);
                    Spanned::new(
                        e.span(),
                        Expr::BoolOp {
                            op: BoolOp::Or,
                            operands,
                        },
                    )
                }
            })
            .boxed();

        // ---- Ternary `then if cond else else_` ----------------------
        let ternary = bool_or
            .clone()
            .then(
                just(Token::If)
                    .ignore_then(bool_or.clone())
                    .then_ignore(just(Token::Else))
                    .then(expr.clone())
                    .or_not(),
            )
            .map_with(|(then_expr, tail), e| match tail {
                None => then_expr,
                Some((cond, else_expr)) => Spanned::new(
                    e.span(),
                    Expr::IfExp {
                        cond: Box::new(cond),
                        then_expr: Box::new(then_expr),
                        else_expr: Box::new(else_expr),
                    },
                ),
            })
            .boxed();

        // ---- Feed `x << y` (single, not chainable) -----------------
        let feed = ternary
            .clone()
            .then(just(Token::LShift).ignore_then(ternary.clone()).or_not())
            .map_with(|(lhs, rhs), e| match rhs {
                None => lhs,
                Some(value) => Spanned::new(
                    e.span(),
                    Expr::Feed {
                        target: Box::new(lhs),
                        value: Box::new(value),
                    },
                ),
            });

        // ---- Lambda / Yield (top-level expression forms) ------------
        //
        // Lambda params do NOT allow `:` type annotations (the `:` is
        // already taken to terminate the param list before the body), so
        // we use a bare-ident-only param parser here. Function-def params
        // (which use `(...)` to delimit) get the annotated form down in
        // `statement()`.
        let lambda_param = ident_only.map(|(name, name_span)| Param {
            name,
            name_span,
            annotation: None,
        });
        let lambda = just(Token::Lambda)
            .ignore_then(
                lambda_param
                    .separated_by(just(Token::Comma))
                    .collect::<Vec<_>>(),
            )
            .then_ignore(just(Token::Colon))
            .then(expr.clone())
            .map_with(|(params, body), e| {
                Spanned::new(
                    e.span(),
                    Expr::Lambda {
                        params,
                        body: Box::new(body),
                    },
                )
            });

        let yield_expr = just(Token::Yield)
            .ignore_then(expr.clone())
            .map_with(|value, e| Spanned::new(e.span(), Expr::Yield(Box::new(value))));

        // Label the whole expression production so a failure here reports
        // "expected expression" instead of unpacking the 20+ tokens that
        // could legitimately start one. Lower-level productions
        // (atoms, operators) deliberately stay unlabelled, so when a
        // statement-level guide-post fails (e.g. `:` after `if cond`) the
        // diagnostic still names the expected separator.
        // `.as_context()` populates a context entry on every error that
        // occurs *inside* this expression production, not just failures
        // at its start. The renderer turns that into a yellow "while
        // parsing expression" secondary span pointing at the partially-
        // matched expression, which is what lets `if x` (no colon) show
        // *where* the in-progress expression was when the missing `:`
        // was hit.
        choice((lambda, yield_expr, feed))
            .labelled("expression")
            .as_context()
            .boxed()
    })
}

/// Intermediate type used inside `paren_group` so we know what shape to build.
#[derive(Clone)]
enum GroupTail {
    Group,
    Tuple(Vec<Spanned<Expr>>),
    Gen(Vec<CompClause>),
}

/// Intermediate type used by the postfix-chain fold.
#[derive(Clone)]
enum PostfixOp {
    Call(Vec<Spanned<Expr>>),
    Subscript(Box<Spanned<Expr>>),
    Attribute(SmolStr, Span),
}

// ---------------------------------------------------------------------------
// Statement parser
// ---------------------------------------------------------------------------

fn module_parser<'src, I>() -> impl Parser<'src, I, Module, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
{
    // A module is zero or more statements, optionally preceded/followed by
    // stray NEWLINEs (the lexer always trails one).
    just(Token::Newline)
        .repeated()
        .ignore_then(
            statement()
                .then_ignore(just(Token::Newline).repeated())
                .repeated()
                .collect::<Vec<_>>(),
        )
        .then_ignore(end())
        .map(|body| Module { body })
}

fn statement<'src, I>() -> impl Parser<'src, I, Spanned<Stmt>, PErr<'src>> + Clone
where
    I: ValueInput<'src, Token = Token, Span = Span>,
{
    recursive(|stmt| {
        let expr = expression();

        // A block is either:
        //   - NEWLINE INDENT stmt+ DEDENT     (Python-style indented body)
        //   - or a single simple statement on the same line: `if x: y`
        //
        // We model the multi-line form; the single-line form is handled
        // explicitly in each compound statement's grammar below.
        let block = just(Token::Newline)
            .ignore_then(just(Token::Indent))
            .labelled("indented block")
            .ignore_then(
                stmt.clone()
                    .then_ignore(just(Token::Newline).repeated())
                    .repeated()
                    .at_least(1)
                    .collect::<Vec<_>>(),
            )
            .then_ignore(just(Token::Dedent))
            .boxed();

        // ---- if / elif / else ---------------------------------------
        let if_stmt = just(Token::If)
            .ignore_then(expr.clone())
            .then_ignore(just(Token::Colon))
            .then(block.clone())
            .then(
                just(Token::Elif)
                    .ignore_then(expr.clone())
                    .then_ignore(just(Token::Colon))
                    .then(block.clone())
                    .repeated()
                    .collect::<Vec<_>>(),
            )
            .then(
                just(Token::Else)
                    .ignore_then(just(Token::Colon))
                    .ignore_then(block.clone())
                    .or_not(),
            )
            .map_with(|(((first_cond, first_body), elifs), else_body), e| {
                let mut branches = vec![IfBranch {
                    cond: first_cond,
                    body: first_body,
                }];
                for (cond, body) in elifs {
                    branches.push(IfBranch { cond, body });
                }
                Spanned::new(
                    e.span(),
                    Stmt::If {
                        branches,
                        else_body,
                    },
                )
            });

        // ---- for x in iter: body ------------------------------------
        let for_stmt = just(Token::For)
            .ignore_then(expr.clone().try_map(|t, _| {
                expr_to_assign_target(t).map_err(|bad| Rich::custom(bad, "invalid for-loop target"))
            }))
            .then_ignore(just(Token::In))
            .then(expr.clone())
            .then_ignore(just(Token::Colon))
            .then(block.clone())
            .map_with(|((target, iter), body), e| {
                Spanned::new(e.span(), Stmt::For { target, iter, body })
            });

        // ---- def name(params): body ---------------------------------
        let param = select! { Token::Ident(s) => s }
            .map_with(|s, e| (s, e.span()))
            .labelled("parameter name")
            .then(just(Token::Colon).ignore_then(expr.clone()).or_not())
            .map(|((name, name_span), annotation)| Param {
                name,
                name_span,
                annotation,
            });
        let def_stmt = just(Token::Def)
            .ignore_then(select! { Token::Ident(s) => s }.labelled("function name"))
            .then(
                param
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .then_ignore(just(Token::Colon))
            .then(block.clone())
            .map_with(|((name, params), body), e| {
                Spanned::new(e.span(), Stmt::FunctionDef { name, params, body })
            });

        // ---- simple statements (must end at NEWLINE) ----------------
        let return_stmt = just(Token::Return)
            .ignore_then(expr.clone().or_not())
            .map_with(|value, e| Spanned::new(e.span(), Stmt::Return(value)));

        let pass_stmt = just(Token::Pass).map_with(|_, e| Spanned::new(e.span(), Stmt::Pass));

        // Augmented assignment: `target OP= value`.
        let aug_op = choice((
            just(Token::PlusEq).to(AugOp::Add),
            just(Token::MinusEq).to(AugOp::Sub),
            just(Token::StarEq).to(AugOp::Mul),
            just(Token::DoubleSlashEq).to(AugOp::FloorDiv),
        ));

        // Statement-level rules that begin with an expression. We parse
        // a comma-separated *list* of expressions first (so bare-tuple
        // targets `a, b = …` and bare-tuple expression statements
        // `a, b` both work), then dispatch on the trailing token:
        //   `target = value`       → Assign
        //   `target : ty = value`  → AnnAssign
        //   `target OP= value`     → AugAssign
        //   `target <<= value`     → Define
        //   `target`               → Expr-statement
        let bare_tuple = expr
            .clone()
            .separated_by(just(Token::Comma))
            .at_least(1)
            .allow_trailing()
            .collect::<Vec<_>>()
            .map_with(|mut elts: Vec<Spanned<Expr>>, e| {
                if elts.len() == 1 {
                    elts.pop().unwrap()
                } else {
                    Spanned::new(e.span(), Expr::Tuple(elts))
                }
            });
        let expr_or_assign = bare_tuple
            .then(choice((
                just(Token::Eq)
                    .ignore_then(expr.clone())
                    .map(AssignTail::Plain),
                just(Token::Colon)
                    .ignore_then(expr.clone())
                    .then_ignore(just(Token::Eq))
                    .then(expr.clone())
                    .map(|(ann, val)| AssignTail::Annotated(ann, val)),
                aug_op
                    .then(expr.clone())
                    .map(|(op, val)| AssignTail::Aug(op, val)),
                just(Token::LShiftEq)
                    .ignore_then(expr.clone())
                    .map(AssignTail::Define),
                empty().to(AssignTail::None),
            )))
            // `try_map_with` so an LHS that doesn't reduce to a binding
            // pattern (e.g. `1 + 2 = x`) becomes a parse error rather than
            // a lowering-time rejection. Expression statements
            // (`AssignTail::None`) keep the full `Expr` shape.
            .try_map_with(|(target, tail), e| {
                let span = e.span();
                let to_target = |t| {
                    expr_to_assign_target(t)
                        .map_err(|bad| Rich::custom(bad, "invalid assignment target"))
                };
                let stmt = match tail {
                    AssignTail::Plain(value) => Stmt::Assign {
                        target: to_target(target)?,
                        value,
                    },
                    AssignTail::Annotated(ann, val) => Stmt::AnnAssign {
                        target: to_target(target)?,
                        annotation: ann,
                        value: val,
                    },
                    AssignTail::Aug(op, val) => Stmt::AugAssign {
                        target: to_target(target)?,
                        op,
                        value: val,
                    },
                    AssignTail::Define(value) => Stmt::Define {
                        target: to_target(target)?,
                        value,
                    },
                    AssignTail::None => Stmt::Expr(target),
                };
                Ok(Spanned::new(span, stmt))
            });

        // A simple statement ends in either `Newline` or `;` (Python-style
        // one-liners: `x = 1; y = 2`). A statement followed by `;` may also
        // be the last on its line, in which case both `;` and the trailing
        // `Newline` are consumed.
        let stmt_terminator = choice((
            just(Token::Semi).then_ignore(just(Token::Newline).or_not()),
            just(Token::Newline),
        ));
        let simple_stmt =
            choice((return_stmt, pass_stmt, expr_or_assign)).then_ignore(stmt_terminator);

        // ---- Statement-level recovery -------------------------------
        //
        // If a whole statement fails to parse, fall back to:
        //   1. consume tokens up to (and including) the next `Newline` at
        //      the current bracket depth (the Newline ends the broken
        //      statement);
        //   2. if the next token after that is `Indent`, also swallow the
        //      whole balanced `Indent…Dedent` block. This is what lets a
        //      bad header line (`if x;`, `def f(:`) discard its attached
        //      body instead of producing a cascade of orphan-block errors
        //      from the outer module parser.
        //
        // The recovered statement is a `Stmt::Error` placeholder spanning
        // the whole skipped region. The original chumsky error is preserved
        // in the returned error list — recovery doesn't hide diagnostics,
        // it just lets the parser keep going past them.
        // `at_least(1)` is load-bearing for TWO reasons:
        //   - **Termination.** Without it, recovery "succeeds" by matching
        //     zero tokens at `Newline`/`Dedent`/EOF, which makes the
        //     enclosing `statement().repeated()` loop forever (chumsky
        //     panics with `Collect making no progress`).
        //   - **No-cascade nested-block recovery.** A bad statement deep
        //     inside nested blocks would otherwise emit one
        //     "unexpected `Dedent`" parse error per block boundary on the
        //     way out. With `at_least(1)`, recovery declines at each
        //     intermediate `Dedent`, the enclosing `repeated()` exits
        //     normally, and the surrounding `then_ignore(Dedent)`
        //     consumes the `Dedent` without producing a spurious error.
        //     `nested_block_recovery_reports_one_error_per_mistake` in the
        //     integration tests guards this.
        let skip_to_newline = any()
            .and_is(just(Token::Newline).not())
            .and_is(just(Token::Dedent).not())
            .repeated()
            .at_least(1)
            .then_ignore(just(Token::Newline).or_not());
        let skip_indented_block =
            nested_delimiters(Token::Indent, Token::Dedent, [], |_span| ()).or_not();
        let stmt_recovery = skip_to_newline
            .then(skip_indented_block)
            .map_with(|_, e| Spanned::new(e.span(), Stmt::Error));

        choice((if_stmt, for_stmt, def_stmt, simple_stmt))
            .labelled("statement")
            .as_context()
            .recover_with(via_parser(stmt_recovery))
            .boxed()
    })
}

/// Intermediate type used inside the statement-level expression dispatch.
#[derive(Clone)]
enum AssignTail {
    Plain(Spanned<Expr>),
    Annotated(Spanned<Expr>, Spanned<Expr>),
    Aug(AugOp, Spanned<Expr>),
    Define(Spanned<Expr>),
    None,
}

/// Convert an [`Expr`] parsed in target position into an [`AssignTarget`].
///
/// CHL binding patterns are bare names and (possibly-nested) tuples of
/// patterns. We parse the LHS as a full expression so the regular grammar
/// (with its error recovery) handles it, then narrow to the binding-pattern
/// shape here. On failure, returns the [`Span`] of the offending
/// sub-expression so the caller can attach it to a diagnostic.
fn expr_to_assign_target(spanned: Spanned<Expr>) -> Result<Spanned<AssignTarget>, Span> {
    let span = spanned.span;
    let node = match spanned.node {
        Expr::Name(name) => AssignTarget::Name(name),
        Expr::Tuple(elts) => {
            let mut out = Vec::with_capacity(elts.len());
            for elt in elts {
                out.push(expr_to_assign_target(elt)?);
            }
            AssignTarget::Tuple(out)
        }
        _ => return Err(span),
    };
    Ok(Spanned::new(span, node))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_e(src: &str) -> Spanned<Expr> {
        parse_expression(src)
            .into_result()
            .unwrap_or_else(|errs| panic!("parse errors: {errs:#?}"))
    }

    fn parse_m(src: &str) -> Module {
        parse_module(src)
            .into_result()
            .unwrap_or_else(|errs| panic!("parse errors: {errs:#?}"))
    }

    #[test]
    fn int_literal() {
        assert_eq!(parse_e("42").node, Expr::Lit(Lit::Int(42)));
    }

    #[test]
    fn string_literal() {
        assert_eq!(parse_e(r#""hi""#).node, Expr::Lit(Lit::String("hi".into())));
    }

    #[test]
    fn arithmetic_precedence() {
        // 1 + 2 * 3 should parse as 1 + (2 * 3)
        let e = parse_e("1 + 2 * 3").node;
        match e {
            Expr::BinOp {
                op: BinOp::Add,
                left,
                right,
            } => {
                assert_eq!(left.node, Expr::Lit(Lit::Int(1)));
                assert!(matches!(right.node, Expr::BinOp { op: BinOp::Mul, .. }));
            }
            other => panic!("expected Add, got {other:?}"),
        }
    }

    #[test]
    fn comparison_chain() {
        let e = parse_e("1 < 2 < 3").node;
        match e {
            Expr::Compare {
                ops, comparators, ..
            } => {
                assert_eq!(ops, vec![CmpOp::Lt, CmpOp::Lt]);
                assert_eq!(comparators.len(), 2);
            }
            other => panic!("expected Compare, got {other:?}"),
        }
    }

    #[test]
    fn list_literal_and_comprehension() {
        assert!(matches!(parse_e("[1, 2, 3]").node, Expr::List(v) if v.len() == 3));
        let e = parse_e("[x + 1 for x in [1, 2, 3] if x > 0]").node;
        match e {
            Expr::ListComp(comp) => {
                assert_eq!(comp.clauses.len(), 2);
                assert!(matches!(comp.clauses[0], CompClause::For { .. }));
                assert!(matches!(comp.clauses[1], CompClause::If(_)));
            }
            other => panic!("expected ListComp, got {other:?}"),
        }
    }

    #[test]
    fn tuple_vs_paren_group() {
        // `(1)` is just `1`, not a tuple.
        assert_eq!(parse_e("(1)").node, Expr::Lit(Lit::Int(1)));
        // `(1,)` is a single-element tuple.
        assert!(matches!(parse_e("(1,)").node, Expr::Tuple(v) if v.len() == 1));
        // `(1, 2)` is a tuple.
        assert!(matches!(parse_e("(1, 2)").node, Expr::Tuple(v) if v.len() == 2));
    }

    #[test]
    fn record_vs_dict() {
        // Bare-ident keys → Record.
        assert!(matches!(parse_e("{x: 1, y: 2}").node, Expr::Record(_)));
        // String keys → Dict.
        assert!(matches!(
            parse_e(r#"{"name": "alice"}"#).node,
            Expr::Dict(_)
        ));
    }

    #[test]
    fn call_and_subscript_and_attr() {
        let e = parse_e("f(x)[0].name").node;
        // f(x)[0].name = Attribute(Subscript(Call(Name(f), [Name(x)]), 0), "name")
        match e {
            Expr::Attribute { target, attr, .. } => {
                assert_eq!(attr.as_str(), "name");
                assert!(matches!(target.node, Expr::Subscript { .. }));
            }
            other => panic!("expected Attribute, got {other:?}"),
        }
    }

    #[test]
    fn lambda_and_ternary() {
        let e = parse_e("lambda x: x + 1 if x > 0 else 0").node;
        match e {
            Expr::Lambda { params, body } => {
                assert_eq!(params.len(), 1);
                assert!(matches!(body.node, Expr::IfExp { .. }));
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    #[test]
    fn feed_expression() {
        let e = parse_e("x << 1").node;
        assert!(matches!(e, Expr::Feed { .. }));
    }

    #[test]
    fn collection_union_operator() {
        let e = parse_e("[1, 2] @ [3, 4]").node;
        assert!(matches!(
            e,
            Expr::BinOp {
                op: BinOp::CollectionUnion,
                ..
            }
        ));
    }

    #[test]
    fn boolean_ops_flatten() {
        let e = parse_e("a or b or c").node;
        match e {
            Expr::BoolOp {
                op: BoolOp::Or,
                operands,
            } => {
                assert_eq!(operands.len(), 3);
            }
            other => panic!("expected BoolOp::Or, got {other:?}"),
        }
    }

    #[test]
    fn unary_neg_and_not() {
        assert!(matches!(
            parse_e("-x").node,
            Expr::UnaryOp {
                op: UnaryOp::Neg,
                ..
            }
        ));
        assert!(matches!(
            parse_e("not x").node,
            Expr::UnaryOp {
                op: UnaryOp::Not,
                ..
            }
        ));
    }

    // ---- Statement-level tests ---------------------------------------

    #[test]
    fn simple_assignment() {
        let m = parse_m("x = 1\n");
        assert_eq!(m.body.len(), 1);
        match &m.body[0].node {
            Stmt::Assign { target, .. } => {
                assert!(matches!(&target.node, AssignTarget::Name(n) if n == "x"));
            }
            other => panic!("expected Assign, got {other:?}"),
        }
    }

    #[test]
    fn tuple_destructuring_assignment() {
        let m = parse_m("a, b = (1, 2)\n");
        match &m.body[0].node {
            Stmt::Assign { target, .. } => match &target.node {
                AssignTarget::Tuple(elts) => {
                    assert_eq!(elts.len(), 2);
                    assert!(matches!(&elts[0].node, AssignTarget::Name(n) if n == "a"));
                    assert!(matches!(&elts[1].node, AssignTarget::Name(n) if n == "b"));
                }
                other => panic!("expected Tuple target, got {other:?}"),
            },
            other => panic!("expected Assign, got {other:?}"),
        }
    }

    #[test]
    fn assign_to_non_binding_is_parse_error() {
        // `1 + 2 = x` — the LHS isn't a valid binding pattern; the parser
        // must surface this rather than handing a malformed target to lowering.
        let r = parse_module("1 + 2 = x\n");
        assert!(
            !r.errors.is_empty(),
            "expected parse error for non-binding assignment LHS"
        );
    }

    #[test]
    fn annotated_assignment() {
        let m = parse_m("x: int = 1\n");
        assert!(matches!(m.body[0].node, Stmt::AnnAssign { .. }));
    }

    #[test]
    fn aug_assignment() {
        let m = parse_m("x += 1\n");
        assert!(matches!(
            m.body[0].node,
            Stmt::AugAssign { op: AugOp::Add, .. }
        ));
    }

    #[test]
    fn define_statement() {
        let m = parse_m("x <<= 1\n");
        assert!(matches!(m.body[0].node, Stmt::Define { .. }));
    }

    #[test]
    fn if_elif_else() {
        let m = parse_m("if x:\n    y\nelif z:\n    w\nelse:\n    q\n");
        match &m.body[0].node {
            Stmt::If {
                branches,
                else_body,
            } => {
                assert_eq!(branches.len(), 2);
                assert!(else_body.is_some());
            }
            other => panic!("expected If, got {other:?}"),
        }
    }

    #[test]
    fn for_loop() {
        let m = parse_m("for x in [1, 2, 3]:\n    y\n");
        assert!(matches!(m.body[0].node, Stmt::For { .. }));
    }

    #[test]
    fn function_def() {
        let m = parse_m("def f(x, y):\n    x + y\n");
        match &m.body[0].node {
            Stmt::FunctionDef { name, params, body } => {
                assert_eq!(name.as_str(), "f");
                assert_eq!(params.len(), 2);
                assert_eq!(body.len(), 1);
            }
            other => panic!("expected FunctionDef, got {other:?}"),
        }
    }

    #[test]
    fn nested_function_with_for_and_yield() {
        let src = "def doubles(xs):\n    for x in xs:\n        yield x * 2\n";
        let m = parse_m(src);
        assert_eq!(m.body.len(), 1);
    }
}
