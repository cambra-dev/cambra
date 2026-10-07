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

use crate::ast::Span;
use crate::builtins::SurfaceBuiltin;
use logos::Logos;
use smol_str::SmolStr;
use std::fmt;

/// The CHL token alphabet.
///
/// All variants except [`Token::Indent`] and [`Token::Dedent`] are produced
/// directly by logos. `Indent`/`Dedent` are synthesised by the layout pass in
/// [`tokenize`].
#[derive(Logos, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
// The tests enumerate every variant. A data field holds its `Default` value.
#[cfg_attr(test, derive(strum::EnumIter))]
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

/// Every keyword spelling and the token it lexes to: the identifier-shaped
/// spellings that lex as something other than [`Token::Ident`].
///
/// The editor grammars under `editors/` list the same spellings, and
/// `tests/editor_grammars.rs` fails when either grammar differs from this
/// table. `True` and `False` are listed here although the grammars highlight
/// them as constants rather than as keywords. It is public for the planned
/// language server (`editors/README.md`).
pub const KEYWORDS: &[(&str, Token)] = &[
    ("True", Token::True),
    ("False", Token::False),
    ("where", Token::Where),
    ("and", Token::And),
    ("or", Token::Or),
    ("not", Token::Not),
    ("if", Token::If),
    ("elif", Token::Elif),
    ("else", Token::Else),
    ("for", Token::For),
    ("in", Token::In),
    ("def", Token::Def),
    ("return", Token::Return),
    ("yield", Token::Yield),
    ("pass", Token::Pass),
    ("with", Token::With),
    ("match", Token::Match),
    ("case", Token::Case),
];

/// What an editor colors a span of CHL source as. The grammars under `editors/`
/// assign each class one TextMate scope and one Vim group, recorded in
/// `editors/highlight-classes.json`; `./ci.sh editors` checks both grammars
/// against [`highlight`] (see `editors/README.md`, "Editor highlight check").
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HighlightClass {
    /// `# …` to the end of the line, except its [`HighlightClass::Todo`] words.
    /// Logos skips comments, so [`highlight`] recovers them from the gaps
    /// between tokens.
    Comment,
    /// A [`TODO_WORDS`] word inside a comment.
    Todo,
    /// A string literal's quotes and characters, except its escapes.
    String,
    /// An escape sequence the lexer interprets inside a string literal.
    Escape,
    Integer,
    Boolean,
    KeywordControl,
    KeywordOther,
    /// The identifier directly after `def`.
    FunctionName,
    /// An identifier that spells a [`SurfaceBuiltin`], wherever it appears,
    /// except where the identifier after `def`, a backtick or `@` takes its
    /// own class. A binding that shadows a builtin keeps this class.
    Builtin,
    /// An identifier whose first character is an ASCII capital, or the type
    /// hole `_` directly after `:`, `<:`, `=>` or `{`.
    Type,
    Identifier,
    /// A backtick and the identifier directly after it.
    VariantTag,
    /// `@` and the identifier directly after it.
    Decorator,
    Lambda,
    Mutation,
    Feed,
    Define,
    Operator,
    Punctuation,
    Bracket,
}

impl HighlightClass {
    /// Every class, in declaration order. `tests/editor_grammars.rs` requires
    /// `editors/highlight-classes.json` to name exactly these.
    pub const ALL: &[HighlightClass] = &[
        HighlightClass::Comment,
        HighlightClass::Todo,
        HighlightClass::String,
        HighlightClass::Escape,
        HighlightClass::Integer,
        HighlightClass::Boolean,
        HighlightClass::KeywordControl,
        HighlightClass::KeywordOther,
        HighlightClass::FunctionName,
        HighlightClass::Builtin,
        HighlightClass::Type,
        HighlightClass::Identifier,
        HighlightClass::VariantTag,
        HighlightClass::Decorator,
        HighlightClass::Lambda,
        HighlightClass::Mutation,
        HighlightClass::Feed,
        HighlightClass::Define,
        HighlightClass::Operator,
        HighlightClass::Punctuation,
        HighlightClass::Bracket,
    ];

    /// The class's key in `editors/highlight-classes.json`.
    pub fn name(self) -> &'static str {
        match self {
            HighlightClass::Comment => "comment",
            HighlightClass::Todo => "todo",
            HighlightClass::String => "string",
            HighlightClass::Escape => "escape",
            HighlightClass::Integer => "integer",
            HighlightClass::Boolean => "boolean",
            HighlightClass::KeywordControl => "keyword-control",
            HighlightClass::KeywordOther => "keyword-other",
            HighlightClass::FunctionName => "function-name",
            HighlightClass::Builtin => "builtin",
            HighlightClass::Type => "type",
            HighlightClass::Identifier => "identifier",
            HighlightClass::VariantTag => "variant-tag",
            HighlightClass::Decorator => "decorator",
            HighlightClass::Lambda => "lambda",
            HighlightClass::Mutation => "mutation",
            HighlightClass::Feed => "feed",
            HighlightClass::Define => "define",
            HighlightClass::Operator => "operator",
            HighlightClass::Punctuation => "punctuation",
            HighlightClass::Bracket => "bracket",
        }
    }
}

/// The highlight class of `token` read on its own, or `None` for a layout
/// token. [`highlight`] overrides it for an identifier after `def`, a backtick
/// or `@`, and for `_` after an annotation's `:`, `<:` or `=>` or a `{`. The
/// match has no wildcard arm, so a new `Token` variant does not compile until
/// it is classified here.
pub fn highlight_class(token: &Token) -> Option<HighlightClass> {
    use HighlightClass as C;
    let class = match token {
        Token::Newline | Token::Indent | Token::Dedent => return None,
        Token::True | Token::False => C::Boolean,
        Token::If
        | Token::Elif
        | Token::Else
        | Token::For
        | Token::In
        | Token::Return
        | Token::Yield
        | Token::Pass
        | Token::With
        | Token::Match
        | Token::Case => C::KeywordControl,
        Token::Def | Token::Where | Token::And | Token::Or | Token::Not => C::KeywordOther,
        Token::ColonEq => C::Mutation,
        Token::LShift => C::Feed,
        Token::LShiftEq => C::Define,
        Token::EqEq
        | Token::NotEq
        | Token::LtE
        | Token::LtColon
        | Token::GtE
        | Token::PlusPlus
        | Token::PlusEq
        | Token::CaretPlus
        | Token::CaretEq
        | Token::MinusEq
        | Token::Arrow
        | Token::DoubleArrow
        | Token::StarStar
        | Token::StarEq
        | Token::DoubleSlashEq
        | Token::DoubleSlash
        | Token::Plus
        | Token::Minus
        | Token::Star
        | Token::Amp
        | Token::Pipe
        | Token::Caret
        | Token::Eq
        | Token::Lt
        | Token::Gt
        | Token::Question => C::Operator,
        Token::Comma | Token::Colon | Token::Dot | Token::Semi => C::Punctuation,
        Token::LParen
        | Token::RParen
        | Token::LBracket
        | Token::RBracket
        | Token::LBrace
        | Token::RBrace => C::Bracket,
        Token::Backtick => C::VariantTag,
        Token::At => C::Decorator,
        Token::Backslash => C::Lambda,
        Token::Int(_) => C::Integer,
        Token::String(_) => C::String,
        Token::Ident(name) => {
            if SurfaceBuiltin::from_name(name).is_some() {
                C::Builtin
            } else if name.starts_with(|c: char| c.is_ascii_uppercase()) {
                C::Type
            } else {
                C::Identifier
            }
        }
    };
    Some(class)
}

/// The highlight spans of `source`, in source order: one per logos token except
/// layout tokens, a string literal split into [`HighlightClass::String`] and
/// [`HighlightClass::Escape`] runs, and a comment split into
/// [`HighlightClass::Comment`] and [`HighlightClass::Todo`] runs. The spans are
/// disjoint, none contains a newline, and the bytes they leave uncovered are
/// whitespace and newlines.
///
/// `_` directly after `:`, `<:`, `=>` or `{` is the type hole, so it is a
/// [`HighlightClass::Type`]. The one `_` in that position that is a term is a
/// one-line `match` arm body in a refinement predicate, such as
/// `` case `some(x): _ ``, which this misclassifies (`editors/README.md`,
/// "Type annotations").
///
/// It fails where [`tokenize`]'s first phase fails: at a span no token rule
/// matches, and at a [`LexError::DetachedBacktick`]. It does not apply the
/// off-side rule, so a layout error does not fail it.
pub fn highlight(source: &str) -> Result<Vec<(HighlightClass, Span)>, LexError> {
    let mut out = Vec::new();
    let mut raw = Vec::new();
    let mut lex = Token::lexer(source);
    let mut previous: Option<Token> = None;
    let mut gap_start = 0;
    while let Some(result) = lex.next() {
        let span = Span::from(lex.span());
        let token = result.map_err(|()| lex_failure(source, span))?;
        raw.push((token.clone(), span));
        push_comment(source, gap_start, span.start, &mut out);
        gap_start = span.end;
        let class = match (&previous, &token) {
            (Some(Token::Def), Token::Ident(_)) => Some(HighlightClass::FunctionName),
            (Some(Token::Backtick), Token::Ident(_)) => Some(HighlightClass::VariantTag),
            (Some(Token::At), Token::Ident(_)) => Some(HighlightClass::Decorator),
            (
                Some(Token::Colon | Token::LtColon | Token::DoubleArrow | Token::LBrace),
                Token::Ident(name),
            ) if name == "_" => Some(HighlightClass::Type),
            _ => highlight_class(&token),
        };
        match class {
            Some(HighlightClass::String) => push_string(source, span, &mut out),
            Some(class) => out.push((class, span)),
            None => {}
        }
        previous = Some(token);
    }
    push_comment(source, gap_start, source.len(), &mut out);
    check_tags(&raw)?;
    Ok(out)
}

/// The comment in the gap `source[start..end]` between two tokens, if any. A
/// comment runs to the newline, which is a token, so a gap holds at most one
/// comment and nothing but horizontal whitespace before it.
fn push_comment(source: &str, start: usize, end: usize, out: &mut Vec<(HighlightClass, Span)>) {
    let gap = &source[start..end];
    let Some(hash) = gap.find('#') else {
        debug_assert!(
            gap.bytes().all(|b| b == b' ' || b == b'\t'),
            "a gap between tokens holds only whitespace and a comment: {gap:?}"
        );
        return;
    };
    debug_assert!(
        gap[..hash].bytes().all(|b| b == b' ' || b == b'\t'),
        "only whitespace precedes a comment in a gap between tokens: {gap:?}"
    );
    let comment_start = start + hash;
    let mut run_start = comment_start;
    for (word_start, word) in todo_words(&source[comment_start..end]) {
        let word_start = comment_start + word_start;
        if run_start < word_start {
            out.push((HighlightClass::Comment, Span::new(run_start, word_start)));
        }
        run_start = word_start + word.len();
        out.push((HighlightClass::Todo, Span::new(word_start, run_start)));
    }
    if run_start < end {
        out.push((HighlightClass::Comment, Span::new(run_start, end)));
    }
}

/// The words an editor marks inside a comment as [`HighlightClass::Todo`].
pub const TODO_WORDS: &[&str] = &["TODO", "FIXME", "XXX"];

/// The [`TODO_WORDS`] occurrences in `comment` that stand as whole words, with
/// their byte offsets. A word is bounded by a character that cannot continue an
/// identifier (an ASCII letter, digit or `_`), or by the comment's ends. Both
/// editor grammars spell the same boundary out rather than using their own
/// word definitions, which include non-ASCII letters.
fn todo_words(comment: &str) -> impl Iterator<Item = (usize, &'static str)> + '_ {
    let word_char = |c: char| c.is_ascii_alphanumeric() || c == '_';
    comment.char_indices().filter_map(move |(i, _)| {
        let before = comment[..i].chars().next_back();
        if before.is_some_and(word_char) {
            return None;
        }
        TODO_WORDS
            .iter()
            .copied()
            .find(|word| {
                comment[i..].starts_with(word) && !comment[i + word.len()..].starts_with(word_char)
            })
            .map(|word| (i, word))
    })
}

/// The string literal at `span`, as maximal runs of escapes and of other
/// characters. A backslash before a character [`escaped`] does not interpret is
/// part of the string, as [`process_string`] keeps it.
fn push_string(source: &str, span: Span, out: &mut Vec<(HighlightClass, Span)>) {
    let mut push = |class: HighlightClass, start: usize, end: usize| match out.last_mut() {
        Some((last, run)) if *last == class && run.end == start => run.end = end,
        _ => out.push((class, Span::new(start, end))),
    };
    let mut chars = source[span.start..span.end].char_indices().peekable();
    while let Some((offset, c)) = chars.next() {
        let start = span.start + offset;
        let escape = (c == '\\')
            .then(|| chars.peek().copied())
            .flatten()
            .filter(|&(_, next)| escaped(next).is_some());
        match escape {
            Some((next_offset, next)) => {
                chars.next();
                let end = span.start + next_offset + next.len_utf8();
                push(HighlightClass::Escape, start, end);
            }
            None => push(HighlightClass::String, start, start + c.len_utf8()),
        }
    }
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
        let next = chars.next()?;
        match escaped(next) {
            Some(value) => out.push(value),
            // Unknown escapes: preserve the backslash, matching `rustpython`'s
            // permissive handling of source like `"\d+"` used in tests.
            None => {
                out.push('\\');
                out.push(next);
            }
        }
    }
    Some(out)
}

/// The escape sequences the lexer interprets: `\c` for each `(c, value)`
/// stands for `value`. The test `editor_sample_contains_every_escape` requires
/// `editors/sample.cambra` to contain each one.
pub const ESCAPES: &[(char, char)] = &[
    ('n', '\n'),
    ('t', '\t'),
    ('r', '\r'),
    ('\\', '\\'),
    ('"', '"'),
    ('\'', '\''),
    ('0', '\0'),
];

/// The character the escape sequence `\c` stands for, or `None` when the
/// lexer does not interpret `\c`.
fn escaped(c: char) -> Option<char> {
    ESCAPES
        .iter()
        .find(|&&(escape, _)| escape == c)
        .map(|&(_, value)| value)
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
            span: Span::new(span.start, span.start + 1),
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

/// Tokenise `source` into a layout-resolved token stream.
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
pub fn tokenize(source: &str) -> Result<Vec<(Token, Span)>, LexError> {
    // Phase 1: raw logos token stream (span-attached, errors surfaced).
    let mut raw: Vec<(Token, Span)> = Vec::new();
    let mut lex = Token::lexer(source);
    while let Some(result) = lex.next() {
        let span = Span::from(lex.span());
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
                out.push((Token::Indent, Span::new(line_start, span.start)));
            } else {
                while indent_stack
                    .last()
                    .expect("stack invariant: non-empty")
                    .closes_at(indent)
                {
                    indent_stack.pop();
                    out.push((Token::Dedent, Span::new(span.start, span.start)));
                }
                match indent_stack.last_mut().expect("stack invariant: non-empty") {
                    Level::Fixed(c) if *c == indent => {}
                    // The first line to land in a block right-hand side's level
                    // fixes its column for the rest of the chain.
                    slot @ Level::Pending { .. } => *slot = Level::Fixed(indent),
                    Level::Fixed(_) => return Err(LexError::InconsistentIndent { span: *span }),
                }
            }
            line_opens_at_first_token = matches!(
                tok,
                Token::If
                    | Token::Elif
                    | Token::Else
                    | Token::For
                    | Token::Def
                    | Token::With
                    | Token::Match
                    | Token::Case
            );
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
    use indoc::indoc;

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

    /// A raw newline ends the line a string literal must close on, in either
    /// quote style and after a backslash alike. The error points at the
    /// opening quote, not at the line break.
    #[test]
    fn a_newline_inside_a_string_is_an_error() {
        for source in [
            "x = \"ab\ncd\"",
            "x = 'ab\ncd'",
            "x = \"ab\\\ncd\"",
            "x = \"ab",
        ] {
            assert_eq!(
                tokenize(source),
                Err(LexError::UnterminatedString {
                    span: Span::new(4, 5)
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
        for (source, start) in [
            ("x = ` foo", 4),
            ("x = `(1)", 4),
            ("x = `", 4),
            ("x = `\nfoo", 4),
            ("x = `if", 4),
        ] {
            assert_eq!(
                tokenize(source),
                Err(LexError::DetachedBacktick {
                    span: Span::new(start, start + 1)
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
        assert!(tokenize("x = `some(1)").is_ok());
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
        for (source, start) in [("a / b", 2), ("a % b", 2), ("~a", 0)] {
            assert_eq!(
                tokenize(source),
                Err(LexError::InvalidToken {
                    span: Span::new(start, start + 1)
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
        let toks = tokens("if elif else for in def not and or True False where");
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
                Token::Newline,
            ]
        );
    }

    #[test]
    fn highlight_splits_escapes_and_recovers_comments() {
        use HighlightClass as C;
        let source = "def f(x): # c\n    `t <- \"a\\nb\\d\"";
        let spans: Vec<(C, &str)> = highlight(source)
            .unwrap()
            .into_iter()
            .map(|(class, span)| (class, &source[span.start..span.end]))
            .collect();
        assert_eq!(
            spans,
            vec![
                (C::KeywordOther, "def"),
                (C::FunctionName, "f"),
                (C::Bracket, "("),
                (C::Identifier, "x"),
                (C::Bracket, ")"),
                (C::Punctuation, ":"),
                (C::Comment, "# c"),
                (C::VariantTag, "`"),
                (C::VariantTag, "t"),
                (C::Operator, "<"),
                (C::Operator, "-"),
                (C::String, "\"a"),
                (C::Escape, "\\n"),
                (C::String, "b\\d\""),
            ]
        );
    }

    /// The spans of `source` with their text, for assertions.
    fn highlighted(source: &str) -> Vec<(HighlightClass, &str)> {
        highlight(source)
            .unwrap()
            .into_iter()
            .map(|(class, span)| (class, &source[span.start..span.end]))
            .collect()
    }

    /// A `TODO_WORDS` word is a `Todo` only as a whole word; the rest of the
    /// comment stays one `Comment` run on each side of it.
    #[test]
    fn highlight_splits_todo_words_out_of_comments() {
        use HighlightClass as C;
        assert_eq!(
            highlighted("x # TODO: TODOs, _XXX and FIXME"),
            vec![
                (C::Identifier, "x"),
                (C::Comment, "# "),
                (C::Todo, "TODO"),
                (C::Comment, ": TODOs, _XXX and "),
                (C::Todo, "FIXME"),
            ]
        );
        // Only an ASCII letter, digit or `_` continues a word, so an emoji or
        // a non-ASCII letter after the word leaves it whole.
        for source in ["# TODO\u{1F600}", "# TODO\u{e9}"] {
            assert_eq!(
                highlighted(source)
                    .into_iter()
                    .filter(|(class, _)| *class == C::Todo)
                    .count(),
                1,
                "{source:?}"
            );
        }
    }

    /// A builtin spelling is a `Builtin` wherever it stands, a shadowing
    /// binding included, except where `def`, a backtick or `@` decides the class.
    #[test]
    fn highlight_marks_builtin_spellings() {
        use HighlightClass as C;
        assert_eq!(
            highlighted("max = sum(xs)\ndef map(): `set"),
            vec![
                (C::Builtin, "max"),
                (C::Operator, "="),
                (C::Builtin, "sum"),
                (C::Bracket, "("),
                (C::Identifier, "xs"),
                (C::Bracket, ")"),
                (C::KeywordOther, "def"),
                (C::FunctionName, "map"),
                (C::Bracket, "("),
                (C::Bracket, ")"),
                (C::Punctuation, ":"),
                (C::VariantTag, "`"),
                (C::VariantTag, "set"),
            ]
        );
    }

    /// `_` after `:`, `<:`, `=>` or `{` is the type hole; after `where` it is the
    /// refinement's subject, and inside a pattern it is a binder.
    #[test]
    fn highlight_marks_the_type_hole() {
        use HighlightClass as C;
        let classes = |source| -> Vec<HighlightClass> {
            highlighted(source)
                .into_iter()
                .filter(|(_, text)| *text == "_")
                .map(|(class, _)| class)
                .collect()
        };
        assert_eq!(classes("x: _ = 1"), vec![C::Type]);
        assert_eq!(classes("x <: _ = 1"), vec![C::Type]);
        assert_eq!(classes("def f() => _:"), vec![C::Type]);
        assert_eq!(classes("T = {_ where _ > 0}"), vec![C::Type, C::Identifier]);
        assert_eq!(classes("case `some(_):"), vec![C::Identifier]);
        // `==>` lexes as `==` and `>`, and `<=>` as `<=` and `>`: no arrow.
        assert_eq!(classes("a ==> _"), vec![C::Identifier]);
        assert_eq!(classes("b <=> _"), vec![C::Identifier]);
    }

    /// A backtick with no tag name directly after it is the same error from
    /// `highlight` as from `tokenize`.
    #[test]
    fn highlight_reports_a_detached_backtick() {
        assert_eq!(
            highlight("x = ` foo"),
            Err(LexError::DetachedBacktick {
                span: Span::new(4, 5)
            })
        );
    }

    /// Every variant, by an exhaustive match: a new variant fails to compile
    /// here until it is listed, and then fails the test until
    /// [`HighlightClass::ALL`] lists it too.
    #[test]
    fn highlight_class_all_lists_every_variant() {
        use HighlightClass as C;
        let every = |c: C| match c {
            C::Comment
            | C::Todo
            | C::String
            | C::Escape
            | C::Integer
            | C::Boolean
            | C::KeywordControl
            | C::KeywordOther
            | C::FunctionName
            | C::Builtin
            | C::Type
            | C::Identifier
            | C::VariantTag
            | C::Decorator
            | C::Lambda
            | C::Mutation
            | C::Feed
            | C::Define
            | C::Operator
            | C::Punctuation
            | C::Bracket => c,
        };
        let variants: Vec<C> = [
            C::Comment,
            C::Todo,
            C::String,
            C::Escape,
            C::Integer,
            C::Boolean,
            C::KeywordControl,
            C::KeywordOther,
            C::FunctionName,
            C::Builtin,
            C::Type,
            C::Identifier,
            C::VariantTag,
            C::Decorator,
            C::Lambda,
            C::Mutation,
            C::Feed,
            C::Define,
            C::Operator,
            C::Punctuation,
            C::Bracket,
        ]
        .into_iter()
        .map(every)
        .collect();
        assert_eq!(HighlightClass::ALL, variants.as_slice());
    }

    /// A string with no closing quote on its line is the same error from
    /// `highlight` as from `tokenize`.
    #[test]
    fn highlight_reports_an_unterminated_string() {
        assert_eq!(
            highlight("x = 'ab\ncd'"),
            Err(LexError::UnterminatedString {
                span: Span::new(4, 5)
            })
        );
    }

    #[test]
    fn every_keyword_spelling_lexes_to_its_token() {
        for (spelling, token) in KEYWORDS {
            assert_eq!(
                tokens(spelling),
                vec![token.clone(), Token::Newline],
                "`{spelling}` does not lex to its KEYWORDS token"
            );
            assert_eq!(token.to_string(), *spelling);
        }
    }

    /// How a variant is spelled in source.
    #[derive(Debug, PartialEq)]
    enum Spelling {
        /// An identifier-shaped spelling that lexes as something other than
        /// [`Token::Ident`].
        Keyword,
        /// An operator or punctuation spelling.
        Symbol,
        /// A layout token, which is a newline or synthesized, or a literal or
        /// identifier, which has no one spelling. Its `Display` text is a
        /// description, not source.
        Other,
    }

    /// The match has no wildcard arm, so a new variant does not compile until it
    /// is classified here.
    fn spelling(token: &Token) -> Spelling {
        match token {
            Token::True
            | Token::False
            | Token::Where
            | Token::And
            | Token::Or
            | Token::Not
            | Token::If
            | Token::Elif
            | Token::Else
            | Token::For
            | Token::In
            | Token::Def
            | Token::Return
            | Token::Yield
            | Token::Pass
            | Token::With
            | Token::Match
            | Token::Case => Spelling::Keyword,
            Token::Newline
            | Token::Indent
            | Token::Dedent
            | Token::Int(_)
            | Token::String(_)
            | Token::Ident(_) => Spelling::Other,
            Token::LShiftEq
            | Token::LShift
            | Token::EqEq
            | Token::NotEq
            | Token::LtE
            | Token::LtColon
            | Token::GtE
            | Token::PlusPlus
            | Token::PlusEq
            | Token::CaretPlus
            | Token::CaretEq
            | Token::MinusEq
            | Token::Arrow
            | Token::DoubleArrow
            | Token::StarStar
            | Token::StarEq
            | Token::DoubleSlashEq
            | Token::DoubleSlash
            | Token::Plus
            | Token::Minus
            | Token::Star
            | Token::Amp
            | Token::Pipe
            | Token::Caret
            | Token::Eq
            | Token::Lt
            | Token::Gt
            | Token::LParen
            | Token::RParen
            | Token::LBracket
            | Token::RBracket
            | Token::Question
            | Token::LBrace
            | Token::RBrace
            | Token::Comma
            | Token::Colon
            | Token::ColonEq
            | Token::Dot
            | Token::Backtick
            | Token::Semi
            | Token::Backslash
            | Token::At => Spelling::Symbol,
        }
    }

    fn is_keyword(token: &Token) -> bool {
        spelling(token) == Spelling::Keyword
    }

    /// `KEYWORDS` lists a variant exactly when [`is_keyword`] classifies it as
    /// one, each variant once.
    #[test]
    fn keywords_lists_exactly_the_keyword_variants() {
        use strum::IntoEnumIterator;
        for token in Token::iter() {
            let rows = KEYWORDS.iter().filter(|(_, t)| *t == token).count();
            assert_eq!(
                rows,
                usize::from(is_keyword(&token)),
                "{token:?}: {rows} KEYWORDS rows, is_keyword = {}",
                is_keyword(&token)
            );
        }
    }

    /// `editors/sample.cambra`, the sample the editor highlight check runs both
    /// grammars over (`editors/README.md`, "Editor highlight check").
    fn editor_sample() -> String {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../editors/sample.cambra");
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("reading {path}: {e}"))
    }

    /// The editor sample contains every keyword and symbol spelling, so a new
    /// one is checked against both grammars as soon as it exists. Literals and
    /// identifiers are covered by `sample_covers_every_highlight_class` in
    /// `tests/editor_grammars.rs`.
    #[test]
    fn editor_sample_contains_every_token_spelling() {
        use strum::IntoEnumIterator;
        let sample = editor_sample();
        let spans = highlight(&sample).expect("the sample lexes");
        let present: std::collections::BTreeSet<&str> = spans
            .iter()
            .map(|(_, span)| &sample[span.start..span.end])
            .collect();
        let missing: Vec<String> = Token::iter()
            .filter(|token| spelling(token) != Spelling::Other)
            .map(|token| token.to_string())
            .filter(|s| !present.contains(s.as_str()))
            .collect();
        assert!(
            missing.is_empty(),
            "editors/sample.cambra has no token spelled {missing:?}"
        );
    }

    /// The editor sample contains every escape the lexer interprets, so the
    /// editor highlight check fails a grammar whose escape rule misses one.
    #[test]
    fn editor_sample_contains_every_escape() {
        let sample = editor_sample();
        let spans = highlight(&sample).expect("the sample lexes");
        // An escape run holds one or more two-character escapes, `\` and the
        // escaped character.
        let present: std::collections::BTreeSet<char> = spans
            .iter()
            .filter(|(class, _)| *class == HighlightClass::Escape)
            .flat_map(|(_, span)| sample[span.start..span.end].chars().skip(1).step_by(2))
            .collect();
        let missing: Vec<char> = ESCAPES
            .iter()
            .map(|&(escape, _)| escape)
            .filter(|escape| !present.contains(escape))
            .collect();
        assert!(
            missing.is_empty(),
            "editors/sample.cambra has no escape of {missing:?}"
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
            tokenize(indoc! {"
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
        assert!(matches!(
            tokenize(src),
            Err(LexError::InconsistentIndent { .. })
        ));
    }
}
