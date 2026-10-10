//! CHL tokenization and indentation-sensitive layout.
//!
//! [`tokenize`] returns span-bearing tokens for the parser. Raw tokenization and
//! tag-adjacency checks precede layout processing.
//!
//! Source layout is specified in `docs/chl-spec.md`, "1.3 Indentation (off-side rule)".
//! [`Level::Pending`] handles assignment-side blocks, whose closing `Dedent` has no
//! corresponding `Indent`; see [`tokenize`] for the parser-facing token contract.

use crate::ast::{FileId, Span};
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
    #[token("where", priority = 3)]
    Where,
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
    #[token("return", priority = 3)]
    Return,
    #[token("yield", priority = 3)]
    Yield,
    #[token("pass", priority = 3)]
    Pass,
    #[token("with", priority = 3)]
    With,
    #[token("match", priority = 3)]
    Match,
    #[token("case", priority = 3)]
    Case,
    #[token("forall", priority = 3)]
    Forall,
    #[token("requires", priority = 3)]
    Requires,
    /// Opens a nominal type declaration (`docs/chl-spec.md`, "Declaring a nominal type").
    #[token("type", priority = 3)]
    Type,
    // The module keywords (`docs/chl-spec.md`, "9. Modules [Decided]").
    #[token("import", priority = 3)]
    Import,
    #[token("use", priority = 3)]
    Use,
    #[token("as", priority = 3)]
    As,
    #[token("pub", priority = 3)]
    Pub,
    #[token("run", priority = 3)]
    Run,
    #[token("param", priority = 3)]
    Param,
    /// The qualifier naming the current module's own labels, `this::f1`.
    #[token("this", priority = 3)]
    This,

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
    /// Subtype-bound annotation `<:` — `x <: T` declares an *inferred* type
    /// bounded above by `T`, where `x: T` declares `T` exactly. Two chars, so
    /// maximal munch takes it over `Lt` then `Colon`; no expression can put a
    /// `:` directly after a `<`, so the two never compete.
    #[token("<:")]
    LtColon,
    #[token(">=")]
    GtE,
    #[token("++")]
    PlusPlus,
    #[token("+=")]
    PlusEq,
    /// Refining addition `^+` — addition whose result type records the sum
    /// (`ArithmeticKind::AddRefined`, in `src/ccl/ops.rs`). Two chars, so maximal
    /// munch takes it over `Caret` then `Plus`; CHL has no unary `+`, so `a ^ +b`
    /// is not a competing parse.
    ///
    /// Experimental, and so absent from `docs/chl-spec.md`.
    #[token("^+")]
    CaretPlus,
    /// Opaque binding `^=` — a `let` whose binder is bound at the initializer's
    /// type and never discharged to the initializer, so a refinement mentioning
    /// the binder keeps the initializer's term out
    /// (`cambra::ccl::BindingTransparency`). Two chars, so
    /// maximal munch takes it over `Caret` then `Eq`; `=` starts no expression,
    /// so `a ^ = b` is not a competing parse.
    ///
    /// Experimental, and so absent from `docs/chl-spec.md`.
    #[token("^=")]
    CaretEq,
    #[token("-=")]
    MinusEq,
    /// Lambda body arrow `->`. Also the planned pair / map-entry arrow — `a -> b`
    /// for a two-tuple, `[k -> v, …]` for a map literal (`docs/chl-spec.md`,
    /// "2.4 Atoms").
    /// Two chars, so maximal munch takes it over `-` then `>`.
    #[token("->")]
    Arrow,
    /// Function-type arrow `=>`, the return-type annotation separator on a `def`
    /// (`docs/chl-spec.md`, "4.1 `def` — function definition"). Two chars, so
    /// maximal munch takes it over `=` then `>`.
    #[token("=>")]
    DoubleArrow,
    /// Exponentiation `**` (`docs/chl-spec.md`, "3.3 Arithmetic and logical
    /// operators"). Two chars, so maximal munch takes it over `Star` then
    /// `Star`; CHL has no unary `*`, so `a * *b` is not a competing parse.
    #[token("**")]
    StarStar,
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
    /// The **checked**-lookup suffix, only meaningful directly after a `]`
    /// (`c[k]?`, `docs/chl-spec.md`, "3.9 Subscript and attribute access").
    #[token("?")]
    Question,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token(",")]
    Comma,
    #[token(":")]
    Colon,
    /// Mutable-assignment operator `:=` (initial + subsequent). Longer-match wins
    /// over `Colon` + `Eq`, so `x := e` lexes as one `ColonEq`, while an annotated
    /// mutable intro `x: T := e` is `Colon` (before `T`) then `ColonEq`.
    #[token(":=")]
    ColonEq,
    /// Path separator `::`, between a qualifier and the name it qualifies
    /// (`cart::total`, `shop::cart`). Longer-match wins over two `Colon`s; no
    /// expression puts a `:` directly after a `:`, so the two never compete.
    #[token("::")]
    ColonColon,
    #[token(".")]
    Dot,
    /// Variant-arm introducer `` ` `` (`` `some(1) ``, `` { `some{Int} | `none } ``).
    /// One token marks the form in every position — term, pattern and type —
    /// so a tag never has to be told apart from a name by context.
    #[token("`")]
    Backtick,
    #[token(";")]
    Semi,
    /// Lambda binder introducer `\` (`\x -> body`).
    #[token("\\")]
    Backslash,

    /// Decorator introducer `@`, as in `@LoadFrom(x)` on the line above a
    /// declaration.
    #[token("@")]
    At,

    // -- Literals ---------------------------------------------------------
    /// Decimal integer literal. `_` digit separators are not supported.
    #[regex(r"[0-9]+", |lex| lex.slice().parse::<i64>().ok())]
    Int(i64),

    /// String literal in either double-quoted (`"…"`) or single-quoted
    /// (`'…'`) form, with surrounding quotes stripped and the basic Python
    /// escape sequences (`\n`, `\t`, `\r`, `\\`, `\"`, `\'`, `\0`)
    /// processed. Unknown escapes preserve the backslash, matching the
    /// permissive behaviour the existing CHL tests rely on.
    ///
    /// A literal ends on the line it starts on: neither a character nor an
    /// escaped character may be a raw newline, so a quote with no partner
    /// before the line ends matches no rule, and [`lex_failure`] reports it as
    /// [`LexError::UnterminatedString`].
    #[regex(r#""([^"\\\n]|\\[^\n])*""#, |lex| process_string(lex.slice(), '"'))]
    #[regex(r#"'([^'\\\n]|\\[^\n])*'"#, |lex| process_string(lex.slice(), '\''))]
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
            Token::Where => "where",
            Token::Forall => "forall",
            Token::Requires => "requires",
            Token::Type => "type",
            Token::And => "and",
            Token::Or => "or",
            Token::Not => "not",
            Token::If => "if",
            Token::Elif => "elif",
            Token::Else => "else",
            Token::For => "for",
            Token::In => "in",
            Token::Def => "def",
            Token::Return => "return",
            Token::Yield => "yield",
            Token::Pass => "pass",
            Token::With => "with",
            Token::Match => "match",
            Token::Case => "case",
            Token::Import => "import",
            Token::Use => "use",
            Token::As => "as",
            Token::Pub => "pub",
            Token::Run => "run",
            Token::Param => "param",
            Token::This => "this",
            // Operators (multi-char before single-char)
            Token::LShiftEq => "<<=",
            Token::LShift => "<<",
            Token::EqEq => "==",
            Token::NotEq => "!=",
            Token::LtE => "<=",
            Token::LtColon => "<:",
            Token::GtE => ">=",
            Token::PlusPlus => "++",
            Token::PlusEq => "+=",
            Token::CaretPlus => "^+",
            Token::CaretEq => "^=",
            Token::MinusEq => "-=",
            Token::Arrow => "->",
            Token::DoubleArrow => "=>",
            Token::StarStar => "**",
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
            Token::Question => "?",
            Token::LBrace => "{",
            Token::RBrace => "}",
            Token::Comma => ",",
            Token::Colon => ":",
            Token::ColonEq => ":=",
            Token::ColonColon => "::",
            Token::Dot => ".",
            Token::Backtick => "`",
            Token::Semi => ";",
            Token::At => "@",
            Token::Backslash => "\\",
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
    /// A string literal's opening quote has no closing quote before the end of
    /// its line. The span is the opening quote.
    UnterminatedString { span: Span },
    /// A backtick is not immediately followed by an identifier, so it begins no
    /// variant tag. The span is the backtick.
    DetachedBacktick { span: Span },
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

impl fmt::Display for LexError {
    /// What went wrong, in one line and with no span — a caller renders the span
    /// itself. Without this, a caller showing the error text shows the struct
    /// dump `Debug` produces.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match self {
            LexError::InvalidToken { .. } => "unrecognized token",
            LexError::UnterminatedString { .. } => {
                "string literal has no closing quote on its line"
            }
            LexError::DetachedBacktick { .. } => {
                "backtick is not immediately followed by a tag name"
            }
            LexError::UnmatchedClose { .. } => "closing bracket with no opening bracket",
            LexError::UnclosedBracket { .. } => "unclosed bracket at end of input",
            LexError::InconsistentIndent { .. } => "indentation does not match any enclosing level",
        };
        f.write_str(message)
    }
}

impl LexError {
    /// The source span this error points at. Every variant carries one, so a
    /// caller rendering a diagnostic always has a range to underline.
    pub fn span(&self) -> Span {
        match self {
            LexError::InvalidToken { span }
            | LexError::UnterminatedString { span }
            | LexError::DetachedBacktick { span }
            | LexError::UnmatchedClose { span }
            | LexError::UnclosedBracket { span }
            | LexError::InconsistentIndent { span } => *span,
        }
    }
}

/// Every backtick in `raw` begins a variant tag: an identifier starts where
/// the backtick ends ([`LexError::DetachedBacktick`] otherwise). The check reads
/// the raw stream because the layout pass inserts tokens of its own.
fn check_tags(raw: &[(Token, Span)]) -> Result<(), LexError> {
    for (i, (tok, span)) in raw.iter().enumerate() {
        if !matches!(tok, Token::Backtick) {
            continue;
        }
        match raw.get(i + 1) {
            Some((Token::Ident(_), next)) if next.start == span.end => {}
            _ => return Err(LexError::DetachedBacktick { span: *span }),
        }
    }
    Ok(())
}

/// The error for a span at which logos matched no rule. A quote starts no
/// token but a string literal, so a failure at a quote is a literal whose line
/// ends before its closing quote.
fn lex_failure(source: &str, span: Span) -> LexError {
    match source[span.start..].chars().next() {
        Some('"' | '\'') => LexError::UnterminatedString {
            span: Span::new(span.file, span.start, span.start + 1),
        },
        _ => LexError::InvalidToken { span },
    }
}

/// One entry of the layout stack: a column a line returns to in order to
/// continue the block that opened it.
///
/// A block whose header starts its own line takes that line's column, known
/// when the block opens — `elif` returns to the `if`'s column, already on the
/// stack as the enclosing level. A block standing on the right of an assignment
/// has no column of its own, because its header sits mid-line, so it opens a
/// level whose column the first continuation line supplies: any column past
/// `min` pins it. That is what makes `elif` and `else` indent one level in from
/// the statement and the branch bodies one level further
/// (`docs/chl-spec.md`, "4.3 Assignment forms").
///
/// Telling the two apart is the one place layout reads what a line says rather
/// than only where it starts: where a block may open mid-line, where the block
/// began is what decides where it continues.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Level {
    /// A line must match this column exactly to continue the block.
    Fixed(usize),
    /// A block right-hand side's level, before a continuation line has fixed
    /// its column. `min` is the column of the statement that opened it.
    Pending { min: usize },
}

impl Level {
    /// The column a line must exceed to open a block under this level.
    fn floor(self) -> usize {
        match self {
            Level::Fixed(c) => c,
            Level::Pending { min } => min,
        }
    }

    /// Whether a line at `indent` closes this level. An unpinned level closes
    /// only at or below the statement that opened it: every column above that
    /// is a continuation it can still take.
    fn closes_at(self, indent: usize) -> bool {
        match self {
            Level::Fixed(c) => c > indent,
            Level::Pending { min } => min >= indent,
        }
    }
}

/// Whether a statement whose head is `tok` opens its block from that keyword,
/// rather than from an assignment's right-hand side.
fn opens_block_at_line_start(tok: &Token) -> bool {
    matches!(
        tok,
        Token::If
            | Token::Elif
            | Token::Else
            | Token::For
            | Token::Def
            | Token::Type
            | Token::With
            | Token::Match
            | Token::Case
    )
}

/// Tokenise `source`, the text of `file`, into a layout-resolved token stream.
///
/// Caller-visible invariants of the returned stream:
/// - Always ends with a `Newline` followed by zero or more `Dedent`s back to
///   indent zero, so block-closing rules in the parser have a uniform exit.
/// - `Indent` and `Dedent` are balanced, except that a block standing on the
///   right of an assignment closes with one `Dedent` more — the level it opened
///   for its `elif`/`else` chain, which never had a line of its own to indent
///   on. `block_value` in the parser consumes that one.
/// - No `Newline` appears between a `LParen`/`LBracket`/`LBrace` and its
///   matching closer.
pub fn tokenize(file: FileId, source: &str) -> Result<Vec<(Token, Span)>, LexError> {
    // Phase 1: raw logos token stream (span-attached, errors surfaced).
    let mut raw: Vec<(Token, Span)> = Vec::new();
    let mut lex = Token::lexer(source);
    while let Some(result) = lex.next() {
        let range = lex.span();
        let span = Span::new(file, range.start, range.end);
        match result {
            Ok(tok) => raw.push((tok, span)),
            Err(()) => return Err(lex_failure(source, span)),
        }
    }
    check_tags(&raw)?;

    // Phase 2: apply the off-side rule.
    let mut out: Vec<(Token, Span)> = Vec::new();
    let mut indent_stack: Vec<Level> = vec![Level::Fixed(0)];
    let mut bracket_depth: usize = 0;
    let mut at_line_start = true;
    // Set when the line just closed opened a block from somewhere other than
    // its first token — an assignment's block right-hand side. Carries the
    // statement's own column, the floor for the level that block opens.
    let mut block_value_open: Option<usize> = None;
    // Whether the current line's first token is a block keyword, which is what
    // separates a block that starts its line from one that does not.
    let mut line_opens_at_first_token = false;
    // Whether the current line's first token is `pub`, so that its second token
    // is the statement's head.
    let mut line_head_after_pub = false;
    // The indent of the line the current *logical* line started on. A bracketed
    // header spans several physical lines, and the floor a block right-hand side
    // opens belongs to the statement, not to the physical line its `:` lands on.
    let mut line_indent = 0usize;

    for (tok, span) in &raw {
        // Blank lines and comment-only lines: their only token is `Newline`,
        // and we want them to not affect indentation or appear in the output.
        if at_line_start && matches!(tok, Token::Newline) {
            continue;
        }

        if at_line_start && bracket_depth == 0 {
            let line_start = source[..span.start].rfind('\n').map(|i| i + 1).unwrap_or(0);
            let indent = span.start - line_start;
            line_indent = indent;
            if let Some(min) = block_value_open.take() {
                indent_stack.push(Level::Pending { min });
            }
            let current = indent_stack
                .last()
                .expect("stack invariant: non-empty")
                .floor();
            if indent > current {
                indent_stack.push(Level::Fixed(indent));
                out.push((Token::Indent, Span::new(file, line_start, span.start)));
            } else {
                while indent_stack
                    .last()
                    .expect("stack invariant: non-empty")
                    .closes_at(indent)
                {
                    indent_stack.pop();
                    out.push((Token::Dedent, Span::new(file, span.start, span.start)));
                }
                match indent_stack.last_mut().expect("stack invariant: non-empty") {
                    Level::Fixed(c) if *c == indent => {}
                    // The first line to land in a block right-hand side's level
                    // fixes its column for the rest of the chain.
                    slot @ Level::Pending { .. } => *slot = Level::Fixed(indent),
                    Level::Fixed(_) => return Err(LexError::InconsistentIndent { span: *span }),
                }
            }
            // `pub` prefixes the statement it marks, so the token after it is
            // the one that says whether the statement opens a block itself.
            line_head_after_pub = matches!(tok, Token::Pub);
            line_opens_at_first_token = opens_block_at_line_start(tok);
        } else if line_head_after_pub {
            line_head_after_pub = false;
            line_opens_at_first_token = opens_block_at_line_start(tok);
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
                    // A `:` last on the line opens a block. Where the line did
                    // not start with the keyword that opened it, the block is
                    // an assignment's right-hand side and continues at a column
                    // of its own rather than at the statement's.
                    if matches!(out.last(), Some((Token::Colon, _))) && !line_opens_at_first_token {
                        block_value_open = Some(line_indent);
                    }
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
    let end_span = Span::new(file, source.len(), source.len());
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
    use crate::FileId;
    use indoc::indoc;

    /// Tokenise `src` as the root of its own one-file map.
    fn lex(src: &str) -> Result<Vec<(Token, Span)>, LexError> {
        tokenize(FileId::ROOT, src)
    }

    /// Strip spans for assertion brevity; spans are exercised separately.
    fn tokens(src: &str) -> Vec<Token> {
        lex(src).unwrap().into_iter().map(|(t, _)| t).collect()
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

    /// A raw newline ends the line a string literal must close on, in either
    /// quote style and after a backslash alike. The error points at the
    /// opening quote, not at the line break.
    #[test]
    fn a_newline_inside_a_string_is_an_error() {
        let file = FileId::ROOT;
        for source in [
            "x = \"ab\ncd\"",
            "x = 'ab\ncd'",
            "x = \"ab\\\ncd\"",
            "x = \"ab",
        ] {
            assert_eq!(
                lex(source),
                Err(LexError::UnterminatedString {
                    span: Span::new(file, 4, 5)
                }),
                "{source:?}"
            );
        }
    }

    /// A tag is a backtick with an identifier directly after it, so a backtick
    /// followed by whitespace, a non-identifier token, or the end of input is
    /// an error at the backtick.
    #[test]
    fn a_backtick_must_touch_its_tag_name() {
        let file = FileId::ROOT;
        for (source, start) in [
            ("x = ` foo", 4),
            ("x = `(1)", 4),
            ("x = `", 4),
            ("x = `\nfoo", 4),
            ("x = `if", 4),
        ] {
            assert_eq!(
                lex(source),
                Err(LexError::DetachedBacktick {
                    span: Span::new(file, start, start + 1)
                }),
                "{source:?}"
            );
        }
        assert_eq!(
            tokens("x = `foo"),
            vec![
                Token::Ident("x".into()),
                Token::Eq,
                Token::Backtick,
                Token::Ident("foo".into()),
                Token::Newline,
            ]
        );
        assert!(lex("x = `some(1)").is_ok());
    }

    /// The escape `\n` is two source characters on one line, so it still lexes
    /// to a newline inside the value.
    #[test]
    fn an_escaped_newline_still_lexes() {
        assert_eq!(
            tokens(r#"x = "ab\ncd""#),
            vec![
                Token::Ident("x".into()),
                Token::Eq,
                Token::String("ab\ncd".to_string()),
                Token::Newline,
            ]
        );
    }

    /// Python operators CHL lacks: `/`, `%` and `~` start no token, while `>>`
    /// lexes as two `>` and is left for the parser to reject
    /// (`docs/chl-spec.md`, "1.8 Operators and punctuation").
    #[test]
    fn operators_absent_from_chl() {
        let file = FileId::ROOT;
        for (source, start) in [("a / b", 2), ("a % b", 2), ("~a", 0)] {
            assert_eq!(
                lex(source),
                Err(LexError::InvalidToken {
                    span: Span::new(file, start, start + 1)
                }),
                "{source:?}"
            );
        }
        assert_eq!(
            tokens("a >> b"),
            vec![
                Token::Ident("a".into()),
                Token::Gt,
                Token::Gt,
                Token::Ident("b".into()),
                Token::Newline,
            ]
        );
    }

    #[test]
    fn keywords_beat_idents() {
        let toks = tokens("if elif else for in def not and or True False where forall requires");
        assert_eq!(
            toks,
            vec![
                Token::If,
                Token::Elif,
                Token::Else,
                Token::For,
                Token::In,
                Token::Def,
                Token::Not,
                Token::And,
                Token::Or,
                Token::True,
                Token::False,
                Token::Where,
                Token::Forall,
                Token::Requires,
                Token::Newline,
            ]
        );
    }

    /// `where` separates a refinement's base type from its predicate
    /// (`docs/chl-spec.md`, "6.4 Refinement syntax"), so it lexes as a keyword
    /// and never as an identifier.
    #[test]
    fn where_is_reserved_not_an_ident() {
        assert_eq!(tokens("where"), vec![Token::Where, Token::Newline]);
    }

    #[test]
    fn lambda_tokens() {
        // `\` introduces a lambda binder; `->` separates it from the body.
        // `->` wins over `-` then `>` by maximal munch.
        assert_eq!(
            tokens("\\x -> x"),
            vec![
                Token::Backslash,
                Token::Ident("x".into()),
                Token::Arrow,
                Token::Ident("x".into()),
                Token::Newline,
            ]
        );
        // `lambda` is no longer a keyword — it lexes as an ordinary identifier.
        assert_eq!(
            tokens("lambda"),
            vec![Token::Ident("lambda".into()), Token::Newline]
        );
    }

    #[test]
    fn multi_char_operators() {
        assert_eq!(
            tokens("<< <<= == != <= >= // //= += -= *= ** ^+ ^="),
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
                Token::StarStar,
                Token::CaretPlus,
                Token::CaretEq,
                Token::Newline,
            ]
        );
    }

    /// `^+` is one token and `^` is another; the two operators share a first
    /// character, and maximal munch is what separates them.
    #[test]
    fn caret_plus_wins_over_caret_then_plus() {
        assert_eq!(
            tokens("a ^+ b ^ c + d"),
            vec![
                Token::Ident("a".into()),
                Token::CaretPlus,
                Token::Ident("b".into()),
                Token::Caret,
                Token::Ident("c".into()),
                Token::Plus,
                Token::Ident("d".into()),
                Token::Newline,
            ]
        );
    }

    /// `**` is one token and `*` is another; the two operators share a first
    /// character, and maximal munch is what separates them.
    #[test]
    fn star_star_wins_over_star_then_star() {
        assert_eq!(
            tokens("a ** b * c"),
            vec![
                Token::Ident("a".into()),
                Token::StarStar,
                Token::Ident("b".into()),
                Token::Star,
                Token::Ident("c".into()),
                Token::Newline,
            ]
        );
    }

    /// `^=` is one token: an opaque binding, not `^` applied to whatever `=`
    /// starts. Maximal munch is what separates them.
    #[test]
    fn caret_eq_wins_over_caret_then_eq() {
        assert_eq!(
            tokens("a ^= b ^ c"),
            vec![
                Token::Ident("a".into()),
                Token::CaretEq,
                Token::Ident("b".into()),
                Token::Caret,
                Token::Ident("c".into()),
                Token::Newline,
            ]
        );
    }

    /// `**=` is not a token: the spec says so, and the lexer has to agree. `**` takes the
    /// first two characters and `=` stands alone, which the parser then rejects — an
    /// augmented `**=` would have to be added deliberately, not arrive by a rule ordering.
    #[test]
    fn star_star_equals_is_not_a_token() {
        assert_eq!(
            tokens("x **= 2"),
            vec![
                Token::Ident("x".into()),
                Token::StarStar,
                Token::Eq,
                Token::Int(2),
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

    /// A block on the right of an assignment opens a level of its own, which
    /// the `elif` line fixes. The chain's `Dedent`s therefore outnumber its
    /// `Indent`s by one — the level no line indented onto.
    #[test]
    fn block_right_hand_side_opens_a_level_of_its_own() {
        let src = indoc! {"
            x = if c:
                    1
                elif d:
                    2
                else:
                    3
            y
        "};
        let toks = tokens(src);
        let indents = toks.iter().filter(|t| **t == Token::Indent).count();
        let dedents = toks.iter().filter(|t| **t == Token::Dedent).count();
        assert_eq!((indents, dedents), (3, 4));
    }

    /// A block whose header starts its own line takes that line's column, so a
    /// statement `if` is unaffected: its `Indent`s and `Dedent`s stay balanced.
    #[test]
    fn a_statement_if_opens_no_extra_level() {
        let src = indoc! {"
            if c:
                1
            else:
                2
        "};
        let toks = tokens(src);
        let indents = toks.iter().filter(|t| **t == Token::Indent).count();
        let dedents = toks.iter().filter(|t| **t == Token::Dedent).count();
        assert_eq!((indents, dedents), (2, 2));
    }

    /// A bracketed header wraps onto further physical lines, and the level the
    /// block opens is floored at the *statement's* column, not at the column of
    /// the line the `:` lands on. Reading the latter would put the floor above
    /// the branch bodies and reject the chain.
    #[test]
    fn a_wrapped_header_floors_the_level_at_the_statement() {
        assert_eq!(
            tokens(indoc! {"
                x = if f(c,
                         d):
                        1
                    else:
                        2
                y
            "}),
            tokens(indoc! {"
                x = if f(c, d):
                        1
                    else:
                        2
                y
            "})
        );
    }

    /// The chain's column is the writer's, like every other indentation here:
    /// any column past the statement's works, and the first continuation line
    /// fixes it for the rest of the chain.
    #[test]
    fn the_chain_column_is_fixed_by_its_first_line() {
        let wide = indoc! {"
            x = if c:
                          1
              else:
                          2
            y
        "};
        assert_eq!(
            tokens(wide),
            tokens(indoc! {"
                x = if c:
                        1
                    else:
                        2
                y
            "})
        );
        // A later continuation at a different column no longer fits.
        assert!(matches!(
            lex(indoc! {"
                x = if c:
                        1
                    elif d:
                        2
                  else:
                        3
                y
            "}),
            Err(LexError::InconsistentIndent { .. })
        ));
    }

    /// A `match` on the right needs no level of its own to be pinned: its arms
    /// are the block's body, so nothing dedents between the statement and them.
    /// The level it opens still closes, which is what keeps the extra `Dedent`
    /// uniform across the two block right-hand sides.
    #[test]
    fn a_match_right_hand_side_closes_its_level_unpinned() {
        let src = indoc! {"
            n = match m:
                case `a(v):
                    v
                case `b:
                    0
            y
        "};
        let toks = tokens(src);
        let indents = toks.iter().filter(|t| **t == Token::Indent).count();
        let dedents = toks.iter().filter(|t| **t == Token::Dedent).count();
        assert_eq!((indents, dedents), (3, 4));
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
        assert!(matches!(lex(src), Err(LexError::InconsistentIndent { .. })));
    }
}
