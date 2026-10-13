//! CHL tokenization and indentation-sensitive layout.
//!
//! [`tokenize`] returns span-bearing tokens for the parser, and every lexical
//! error, for any input. [`raw_tokens`] runs logos and the tag-adjacency check
//! for both [`tokenize`] and [`highlight`]; layout processing follows it in
//! [`tokenize`]. The recovery rules are in `chl-parser/design-chl-parser.md`,
//! "Lexer recovery".
//!
//! Source layout is specified in `docs/chl-spec.md`, "1.3 Indentation (off-side rule)".
//! [`Level::Pending`] handles assignment-side blocks, whose closing `Dedent` has no
//! corresponding `Indent`; see [`tokenize`] for the parser-facing token contract.

use crate::ast::{FileId, Span};
use crate::builtins::SurfaceBuiltin;
use logos::Logos;
use smol_str::SmolStr;
use std::fmt;

/// The CHL token alphabet.
///
/// All variants except [`Token::Indent`], [`Token::Dedent`] and [`Token::Error`]
/// are produced directly by logos. `Indent`/`Dedent` are synthesised by the
/// layout pass in [`tokenize`], and `Error` by [`raw_tokens`].
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
    /// A maximal run of characters at which no rule matches, synthesised by
    /// [`raw_tokens`] with one [`LexError::InvalidToken`]. No grammar rule
    /// accepts it.
    Error,

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
    /// before the line ends matches no rule. [`raw_tokens`] turns that failure
    /// into a `String` of the rest of the line and a
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
    ("forall", Token::Forall),
    ("requires", Token::Requires),
    ("import", Token::Import),
    ("use", Token::Use),
    ("as", Token::As),
    ("pub", Token::Pub),
    ("run", Token::Run),
    ("param", Token::Param),
    ("this", Token::This),
];

/// What an editor colors a span of CHL source as. The grammars under `editors/`
/// assign each class one TextMate scope and one Vim group, recorded in
/// `editors/highlight-classes.json`; `./ci.sh editors` checks both grammars
/// against [`highlight`] (see `editors/README.md`, "Editor highlight check").
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(test, derive(strum::EnumIter))]
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
/// token or a [`Token::Error`]. [`highlight`] overrides it for an identifier after `def`, a backtick
/// or `@`, and for `_` after an annotation's `:`, `<:` or `=>` or a `{`. The
/// match has no wildcard arm, so a new `Token` variant does not compile until
/// it is classified here.
pub fn highlight_class(token: &Token) -> Option<HighlightClass> {
    use HighlightClass as C;
    let class = match token {
        Token::Newline | Token::Indent | Token::Dedent | Token::Error => return None,
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
        Token::Def
        | Token::Where
        | Token::And
        | Token::Or
        | Token::Not
        | Token::Forall
        | Token::Requires
        | Token::Import
        | Token::Use
        | Token::As
        | Token::Pub
        | Token::Run
        | Token::Param
        | Token::This => C::KeywordOther,
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
        Token::Comma | Token::Colon | Token::ColonColon | Token::Dot | Token::Semi => {
            C::Punctuation
        }
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

/// The highlight spans of `source`, in source order, and the errors
/// [`raw_tokens`] found.
#[derive(Debug, Clone, PartialEq)]
pub struct Highlighted {
    pub spans: Vec<(HighlightClass, Span)>,
    pub errors: Vec<LexError>,
}

/// The highlight spans of `source`, in source order: one per logos token except
/// layout tokens and [`Token::Error`], a string literal split into
/// [`HighlightClass::String`] and [`HighlightClass::Escape`] runs, and a comment
/// split into [`HighlightClass::Comment`] and [`HighlightClass::Todo`] runs. The
/// spans are disjoint, none contains a newline, and the bytes they leave
/// uncovered are whitespace, newlines and [`Token::Error`] runs.
///
/// `_` directly after `:`, `<:`, `=>` or `{` is the type hole, so it is a
/// [`HighlightClass::Type`]. The one `_` in that position that is a term is a
/// one-line `match` arm body in a refinement predicate, such as
/// `` case `some(x): _ ``, which this misclassifies (`editors/README.md`,
/// "Type annotations").
///
/// It reports the errors of [`tokenize`]'s first phase and none of layout's: a
/// detached backtick keeps its [`HighlightClass::VariantTag`] and an
/// unterminated string its [`HighlightClass::String`].
pub fn highlight(file: FileId, source: &str) -> Highlighted {
    let raw = raw_tokens(file, source);
    let mut spans = Vec::new();
    let mut previous: Option<&Token> = None;
    let mut gap_start = 0;
    for (token, span) in &raw.tokens {
        push_comment(file, source, gap_start, span.start, &mut spans);
        gap_start = span.end;
        let class = match (previous, token) {
            (Some(Token::Def), Token::Ident(_)) => Some(HighlightClass::FunctionName),
            (Some(Token::Backtick), Token::Ident(_)) => Some(HighlightClass::VariantTag),
            (Some(Token::At), Token::Ident(_)) => Some(HighlightClass::Decorator),
            (
                Some(Token::Colon | Token::LtColon | Token::DoubleArrow | Token::LBrace),
                Token::Ident(name),
            ) if name == "_" => Some(HighlightClass::Type),
            _ => highlight_class(token),
        };
        match class {
            Some(HighlightClass::String) => push_string(source, *span, &mut spans),
            Some(class) => spans.push((class, *span)),
            None => {}
        }
        previous = Some(token);
    }
    push_comment(file, source, gap_start, source.len(), &mut spans);
    Highlighted {
        spans,
        errors: raw.errors,
    }
}

/// The comment in the gap `source[start..end]` between two tokens, if any. A
/// comment runs to the newline, which is a token, so a gap holds at most one
/// comment and nothing but horizontal whitespace before it.
fn push_comment(
    file: FileId,
    source: &str,
    start: usize,
    end: usize,
    out: &mut Vec<(HighlightClass, Span)>,
) {
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
            out.push((
                HighlightClass::Comment,
                Span::new(file, run_start, word_start),
            ));
        }
        run_start = word_start + word.len();
        out.push((HighlightClass::Todo, Span::new(file, word_start, run_start)));
    }
    if run_start < end {
        out.push((HighlightClass::Comment, Span::new(file, run_start, end)));
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
        _ => out.push((class, Span::new(span.file, start, end))),
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
            Token::Error => "unrecognized characters",
            // Keywords
            Token::True => "True",
            Token::False => "False",
            Token::Where => "where",
            Token::Forall => "forall",
            Token::Requires => "requires",
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
    Some(unescape(inner))
}

/// `inner`, a string literal's text between its quotes, with its escapes
/// processed. A backslash ending `inner` is kept: only an unterminated
/// literal's text can end in one.
fn unescape(inner: &str) -> String {
    let mut out = String::with_capacity(inner.len());
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        let Some(next) = chars.next() else {
            out.push('\\');
            break;
        };
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
    out
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

/// The lexical errors [`tokenize`] reports. Each describes a place where the
/// token stream differs from the source; `chl-parser/design-chl-parser.md`,
/// "Lexer recovery" gives the stream each one leaves.
#[derive(Debug, Clone, PartialEq)]
pub enum LexError {
    /// A maximal run of characters at which no rule matches. The run lexes as
    /// one [`Token::Error`].
    InvalidToken { span: Span },
    /// A string literal's opening quote has no closing quote before the end of
    /// its line. The span is the opening quote.
    UnterminatedString { span: Span },
    /// A backtick is not immediately followed by an identifier, so it begins no
    /// variant tag. The span is the backtick, which [`tokenize`] drops.
    DetachedBacktick { span: Span },
    /// A close bracket that matches no open bracket. [`tokenize`] drops it.
    UnmatchedClose { span: Span },
    /// A close bracket that matches no open bracket, met while the open
    /// bracket at `open` was innermost, where that open bracket is never
    /// closed. One error covers both: either bracket can be the mistake.
    /// [`tokenize`] drops the close bracket and closes the open one as for
    /// [`LexError::UnclosedBracket`].
    MismatchedClose {
        span: Span,
        close: Token,
        open: Span,
        opener: Token,
    },
    /// An open bracket the source never closes. The span is the open bracket;
    /// [`tokenize`] closes it with a zero-width closer.
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
        match self {
            LexError::InvalidToken { .. } => f.write_str("unrecognized token"),
            LexError::UnterminatedString { .. } => {
                f.write_str("string literal has no closing quote on its line")
            }
            LexError::DetachedBacktick { .. } => {
                f.write_str("backtick is not immediately followed by a tag name")
            }
            LexError::UnmatchedClose { .. } => {
                f.write_str("closing bracket with no opening bracket")
            }
            LexError::UnclosedBracket { .. } => f.write_str("bracket is never closed"),
            LexError::InconsistentIndent { .. } => {
                f.write_str("indentation does not match any enclosing level")
            }
            LexError::MismatchedClose { close, opener, .. } => {
                write!(f, "`{close}` does not match `{opener}`")
            }
        }
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
            | LexError::InconsistentIndent { span }
            | LexError::MismatchedClose { span, .. } => *span,
        }
    }

    /// A second span the error concerns, with what it is: the open bracket of
    /// a [`LexError::MismatchedClose`].
    pub fn related(&self) -> Option<(Span, &'static str)> {
        match self {
            LexError::MismatchedClose { open, .. } => Some((*open, "this bracket is never closed")),
            _ => None,
        }
    }
}

/// A token stream and the lexical errors found producing it, in source order.
#[derive(Debug, Clone, PartialEq)]
pub struct Lexed {
    pub tokens: Vec<(Token, Span)>,
    pub errors: Vec<LexError>,
}

/// The logos tokens of `source`, before layout, and the errors found in them.
/// Shared by [`tokenize`] and [`highlight`]; it never fails.
///
/// - A quote at which no rule matches starts a string literal with no closing
///   quote on its line. It becomes a [`Token::String`] of the rest of the line
///   and an [`LexError::UnterminatedString`] at the quote; the newline stays a
///   token. Logos's failed span stops short of a backslash that ends the line,
///   so the lexer is advanced to the line's end by hand.
/// - Adjacent failed spans anywhere else merge into one [`Token::Error`] and
///   one [`LexError::InvalidToken`]: logos fails one character at a time.
/// - A backtick not immediately followed by an identifier stays in the stream
///   with a [`LexError::DetachedBacktick`]; [`tokenize`] drops it.
fn raw_tokens(file: FileId, source: &str) -> Lexed {
    let mut tokens: Vec<(Token, Span)> = Vec::new();
    let mut errors = Vec::new();
    let mut lex = Token::lexer(source);
    while let Some(result) = lex.next() {
        let range = lex.span();
        let span = Span::new(file, range.start, range.end);
        let Err(()) = result else {
            tokens.push((result.expect("matched Err above"), span));
            continue;
        };
        if let Some(quote @ ('"' | '\'')) = source[span.start..].chars().next() {
            let line_end = source[span.start..]
                .find('\n')
                .map_or(source.len(), |i| span.start + i);
            lex.bump(line_end - span.end);
            let span = Span::new(file, span.start, line_end);
            let text = &source[span.start + quote.len_utf8()..span.end];
            tokens.push((Token::String(unescape(text)), span));
            errors.push(LexError::UnterminatedString {
                span: Span::new(file, span.start, span.start + quote.len_utf8()),
            });
            continue;
        }
        match (tokens.last_mut(), errors.last_mut()) {
            (Some((Token::Error, run)), Some(LexError::InvalidToken { span: error }))
                if run.end == span.start =>
            {
                run.end = span.end;
                error.end = span.end;
            }
            _ => {
                tokens.push((Token::Error, span));
                errors.push(LexError::InvalidToken { span });
            }
        }
    }
    for (i, (tok, span)) in tokens.iter().enumerate() {
        if !matches!(tok, Token::Backtick) {
            continue;
        }
        match tokens.get(i + 1) {
            Some((Token::Ident(_), next)) if next.start == span.end => {}
            _ => errors.push(LexError::DetachedBacktick { span: *span }),
        }
    }
    errors.sort_by_key(|e| e.span().start);
    Lexed { tokens, errors }
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
            | Token::With
            | Token::Match
            | Token::Case
    )
}

/// Tokenise `source`, the text of `file`, into a layout-resolved token stream,
/// with every lexical error. It never fails.
///
/// Caller-visible invariants of the returned stream, for every input:
/// - Always ends with a `Newline` followed by zero or more `Dedent`s back to
///   indent zero, so block-closing rules in the parser have a uniform exit.
/// - `Indent` and `Dedent` are balanced, except that a block standing on the
///   right of an assignment closes with one `Dedent` more — the level it opened
///   for its `elif`/`else` chain, which never had a line of its own to indent
///   on. `block_value` in the parser consumes that one.
/// - Brackets balance: every `LParen`/`LBracket`/`LBrace` has a closer of its
///   kind, possibly zero-width, and no `Newline` appears between them.
///
/// Layout runs a second time when the first run ends with open brackets, so
/// that those brackets close before the line their statement should have
/// ended at (`chl-parser/design-chl-parser.md`, "Unclosed brackets"). A source
/// whose first run leaves no bracket open is laid out once.
pub fn tokenize(file: FileId, source: &str) -> Lexed {
    let raw = raw_tokens(file, source);
    let detached: Vec<usize> = raw
        .errors
        .iter()
        .filter_map(|e| match e {
            LexError::DetachedBacktick { span } => Some(span.start),
            _ => None,
        })
        .collect();
    let tokens: Vec<(Token, Span)> = raw
        .tokens
        .into_iter()
        .filter(|(tok, span)| !(matches!(tok, Token::Backtick) && detached.contains(&span.start)))
        .collect();
    let first = Layout::run(file, source, &tokens, &[]);
    let unclosed = first.unclosed.clone();
    let laid = if unclosed.is_empty() {
        first
    } else {
        Layout::run(file, source, &tokens, &unclosed)
    };
    let mut errors = raw.errors;
    errors.extend(laid.errors);
    errors.sort_by_key(|e| e.span().start);
    Lexed {
        tokens: laid.out,
        errors,
    }
}

/// An open bracket on the layout pass's stack.
struct OpenBracket {
    /// The bracket's own token, which says which closer matches it.
    open: Token,
    span: Span,
    /// The indentation of the line its statement began on.
    line_indent: usize,
    /// Whether this bracket closes before a line at or left of `line_indent`:
    /// the previous layout run left it open.
    resync: bool,
    /// The first close bracket that matched no open bracket while this one was
    /// innermost. Its error waits until this bracket closes: one
    /// [`LexError::MismatchedClose`] if it never does, a
    /// [`LexError::UnmatchedClose`] if it does.
    stray: Option<(Token, Span)>,
}

/// The closer that matches the open bracket `open`.
fn closer(open: &Token) -> Token {
    match open {
        Token::LParen => Token::RParen,
        Token::LBracket => Token::RBracket,
        Token::LBrace => Token::RBrace,
        other => unreachable!("only open brackets go on the bracket stack, got {other:?}"),
    }
}

/// One run of the off-side rule over the raw tokens.
struct Layout<'a> {
    file: FileId,
    source: &'a str,
    out: Vec<(Token, Span)>,
    errors: Vec<LexError>,
    indent_stack: Vec<Level>,
    brackets: Vec<OpenBracket>,
    /// The spans of the open brackets this run closes early.
    resync: &'a [Span],
    /// The spans of the open brackets still open at the end of input.
    unclosed: Vec<Span>,
    at_line_start: bool,
    /// The first newline dropped inside brackets since the last token: the end
    /// of the physical line before the next token's.
    dropped_newline: Option<Span>,
    // Set when the line just closed opened a block from somewhere other than
    // its first token — an assignment's block right-hand side. Carries the
    // statement's own column, the floor for the level that block opens.
    block_value_open: Option<usize>,
    // Whether the current line's first token is a block keyword, which is what
    // separates a block that starts its line from one that does not.
    line_opens_at_first_token: bool,
    // Whether the current line's first token is `pub`, so that its second token
    // is the statement's head.
    line_head_after_pub: bool,
    // The indent of the line the current *logical* line started on. A bracketed
    // header spans several physical lines, and the floor a block right-hand side
    // opens belongs to the statement, not to the physical line its `:` lands on.
    line_indent: usize,
}

impl<'a> Layout<'a> {
    fn run(file: FileId, source: &'a str, raw: &[(Token, Span)], resync: &'a [Span]) -> Self {
        let mut layout = Layout {
            file,
            source,
            out: Vec::new(),
            errors: Vec::new(),
            indent_stack: vec![Level::Fixed(0)],
            brackets: Vec::new(),
            resync,
            unclosed: Vec::new(),
            at_line_start: true,
            dropped_newline: None,
            block_value_open: None,
            line_opens_at_first_token: false,
            line_head_after_pub: false,
            line_indent: 0,
        };
        for (tok, span) in raw {
            layout.token(tok, *span);
        }
        layout.finish();
        layout
    }

    /// The column of the token at `span`: its offset from its line's start.
    fn column(&self, span: Span) -> (usize, usize) {
        let line_start = self.source[..span.start]
            .rfind('\n')
            .map(|i| i + 1)
            .unwrap_or(0);
        (line_start, span.start - line_start)
    }

    fn token(&mut self, tok: &Token, span: Span) {
        // Blank lines and comment-only lines: their only token is `Newline`,
        // and we want them to not affect indentation or appear in the output.
        if self.at_line_start && matches!(tok, Token::Newline) {
            return;
        }
        if let Some(newline) = self.dropped_newline.take() {
            self.close_early(span, newline);
        }

        if self.at_line_start && self.brackets.is_empty() {
            self.line_start(tok, span);
        } else if self.line_head_after_pub {
            self.line_head_after_pub = false;
            self.line_opens_at_first_token = opens_block_at_line_start(tok);
        }
        self.at_line_start = false;

        match tok {
            Token::LParen | Token::LBracket | Token::LBrace => {
                self.brackets.push(OpenBracket {
                    open: tok.clone(),
                    span,
                    line_indent: self.line_indent,
                    resync: self.resync.contains(&span),
                    stray: None,
                });
                self.out.push((tok.clone(), span));
            }
            Token::RParen | Token::RBracket | Token::RBrace => self.close(tok, span),
            Token::Newline => {
                if self.brackets.is_empty() {
                    self.end_line(span);
                } else {
                    // Newlines inside brackets are swallowed (implicit
                    // continuation); the first one is kept in case the next
                    // line closes the brackets early.
                    self.dropped_newline.get_or_insert(span);
                }
            }
            _ => self.out.push((tok.clone(), span)),
        }
    }

    /// The first token of a logical line: open or close indentation levels.
    fn line_start(&mut self, tok: &Token, span: Span) {
        let (line_start, indent) = self.column(span);
        self.line_indent = indent;
        if let Some(min) = self.block_value_open.take() {
            self.indent_stack.push(Level::Pending { min });
        }
        let current = self
            .indent_stack
            .last()
            .expect("stack invariant: non-empty")
            .floor();
        if indent > current {
            self.indent_stack.push(Level::Fixed(indent));
            self.out
                .push((Token::Indent, Span::new(self.file, line_start, span.start)));
        } else {
            while self
                .indent_stack
                .last()
                .expect("stack invariant: non-empty")
                .closes_at(indent)
            {
                self.indent_stack.pop();
                self.out
                    .push((Token::Dedent, Span::new(self.file, span.start, span.start)));
            }
            match self
                .indent_stack
                .last_mut()
                .expect("stack invariant: non-empty")
            {
                Level::Fixed(c) if *c == indent => {}
                // The first line to land in a block right-hand side's level
                // fixes its column for the rest of the chain.
                slot @ Level::Pending { .. } => *slot = Level::Fixed(indent),
                // The line continues the deepest level left of it.
                Level::Fixed(_) => self.errors.push(LexError::InconsistentIndent { span }),
            }
        }
        // `pub` prefixes the statement it marks, so the token after it is
        // the one that says whether the statement opens a block itself.
        self.line_head_after_pub = matches!(tok, Token::Pub);
        self.line_opens_at_first_token = opens_block_at_line_start(tok);
    }

    /// A `Newline` outside brackets: the logical line ends.
    fn end_line(&mut self, span: Span) {
        // A `:` last on the line opens a block. Where the line did not start
        // with the keyword that opened it, the block is an assignment's
        // right-hand side and continues at a column of its own rather than at
        // the statement's.
        if matches!(self.out.last(), Some((Token::Colon, _))) && !self.line_opens_at_first_token {
            self.block_value_open = Some(self.line_indent);
        }
        self.out.push((Token::Newline, span));
        self.at_line_start = true;
    }

    /// The token at `span` starts a physical line inside brackets, after
    /// `newline`. Close each innermost bracket marked for resync whose
    /// statement began at or right of this line's column. Closing them all
    /// ends the logical line at `newline`.
    ///
    /// No later close bracket matches a bracket the previous run left open, so
    /// a line starting with one needs no exception: the close bracket is
    /// dropped whether or not the bracket closed before its line.
    fn close_early(&mut self, span: Span, newline: Span) {
        let (_, indent) = self.column(span);
        let at = Span::new(self.file, newline.start, newline.start);
        while let Some(top) = self.brackets.last() {
            if !top.resync || indent > top.line_indent {
                break;
            }
            let top = self.brackets.pop().expect("checked non-empty");
            self.out.push((closer(&top.open), at));
            self.never_closed(top);
        }
        if self.brackets.is_empty() {
            self.end_line(newline);
        }
    }

    /// A close bracket: it closes the innermost open bracket of its kind, after
    /// zero-width closers for the brackets inside that one, or it is dropped.
    fn close(&mut self, tok: &Token, span: Span) {
        let Some(i) = self.brackets.iter().rposition(|b| closer(&b.open) == *tok) else {
            match self.brackets.last_mut() {
                Some(OpenBracket {
                    stray: slot @ None, ..
                }) => *slot = Some((tok.clone(), span)),
                _ => self.errors.push(LexError::UnmatchedClose { span }),
            }
            return;
        };
        let at = Span::new(self.file, span.start, span.start);
        let inner: Vec<OpenBracket> = self.brackets.drain(i + 1..).rev().collect();
        for inner in inner {
            self.out.push((closer(&inner.open), at));
            self.never_closed(inner);
        }
        let matched = self.brackets.pop().expect("rposition found it");
        if let Some((_, stray)) = matched.stray {
            self.errors.push(LexError::UnmatchedClose { span: stray });
        }
        self.out.push((tok.clone(), span));
    }

    /// The error for `bracket`, closed by a zero-width closer.
    fn never_closed(&mut self, bracket: OpenBracket) {
        self.errors.push(match bracket.stray {
            Some((close, span)) => LexError::MismatchedClose {
                span,
                close,
                open: bracket.span,
                opener: bracket.open,
            },
            None => LexError::UnclosedBracket { span: bracket.span },
        });
    }

    /// End of input: close what is still open, end the last line, and dedent
    /// back to column zero.
    fn finish(&mut self) {
        let end_span = Span::new(self.file, self.source.len(), self.source.len());
        while let Some(open) = self.brackets.pop() {
            self.out.push((closer(&open.open), end_span));
            self.unclosed.push(open.span);
            self.never_closed(open);
        }
        // Synthesise a trailing newline if needed, then dedent all the way
        // back to zero. Parsers can rely on this uniform shape.
        if !matches!(self.out.last(), Some((Token::Newline, _))) {
            self.out.push((Token::Newline, end_span));
        }
        while self.indent_stack.len() > 1 {
            self.indent_stack.pop();
            self.out.push((Token::Dedent, end_span));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FileId;
    use indoc::indoc;

    /// Tokenise `src` as the root of its own one-file map.
    fn lex(src: &str) -> Lexed {
        tokenize(FileId::ROOT, src)
    }

    /// The tokens of `src`, which lexes with no error. Spans are stripped for
    /// assertion brevity; they are exercised separately.
    fn tokens(src: &str) -> Vec<Token> {
        let lexed = lex(src);
        assert_eq!(lexed.errors, vec![], "{src:?} lexes with errors");
        lexed.tokens.into_iter().map(|(t, _)| t).collect()
    }

    /// The tokens of `src` whatever its errors, spans stripped.
    fn recovered(src: &str) -> Vec<Token> {
        lex(src).tokens.into_iter().map(|(t, _)| t).collect()
    }

    /// The errors `src` lexes with.
    fn errors(src: &str) -> Vec<LexError> {
        lex(src).errors
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
    /// opening quote, not at the line break, and the literal holds the rest of
    /// its line.
    #[test]
    fn a_newline_inside_a_string_is_an_error() {
        let file = FileId::ROOT;
        for (source, text) in [
            ("x = \"ab\ncd", "ab"),
            ("x = 'ab\ncd", "ab"),
            ("x = \"ab\\\ncd", "ab\\"),
            ("x = \"ab", "ab"),
        ] {
            assert_eq!(
                errors(source),
                vec![LexError::UnterminatedString {
                    span: Span::new(file, 4, 5)
                }],
                "{source:?}"
            );
            assert_eq!(
                recovered(source)[..4],
                [
                    Token::Ident("x".into()),
                    Token::Eq,
                    Token::String(text.to_string()),
                    Token::Newline,
                ],
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
                errors(source),
                vec![LexError::DetachedBacktick {
                    span: Span::new(file, start, start + 1)
                }],
                "{source:?}"
            );
            assert!(
                !recovered(source).contains(&Token::Backtick),
                "{source:?} keeps its detached backtick"
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
        assert_eq!(errors("x = `some(1)"), vec![]);
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
                errors(source),
                vec![LexError::InvalidToken {
                    span: Span::new(file, start, start + 1)
                }],
                "{source:?}"
            );
            assert!(recovered(source).contains(&Token::Error), "{source:?}");
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

    #[test]
    fn highlight_splits_escapes_and_recovers_comments() {
        use HighlightClass as C;
        let source = "def f(x): # c\n    `t <- \"a\\nb\\d\"";
        let spans = highlighted(source);
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
        let Highlighted { spans, errors } = highlight(FileId::ROOT, source);
        assert_eq!(errors, vec![], "{source:?} lexes with errors");
        spans
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
    /// `highlight` as from `tokenize`, and keeps its class.
    #[test]
    fn highlight_reports_a_detached_backtick() {
        let source = "x = ` foo";
        let Highlighted { spans, errors } = highlight(FileId::ROOT, source);
        assert_eq!(errors, self::errors(source));
        assert_eq!(
            spans[2],
            (HighlightClass::VariantTag, Span::new(FileId::ROOT, 4, 5))
        );
    }

    /// A run of characters no rule matches is one error and no span; the
    /// spans around it keep their classes.
    #[test]
    fn highlight_leaves_unrecognized_characters_unclassified() {
        use HighlightClass as C;
        let source = "a $$ b";
        let Highlighted { spans, errors } = highlight(FileId::ROOT, source);
        assert_eq!(errors, self::errors(source));
        let classes: Vec<(C, &str)> = spans
            .into_iter()
            .map(|(class, span)| (class, &source[span.start..span.end]))
            .collect();
        assert_eq!(classes, vec![(C::Identifier, "a"), (C::Identifier, "b")]);
    }

    /// [`HighlightClass::ALL`] lists every variant, in declaration order.
    #[test]
    fn highlight_class_all_lists_every_variant() {
        use strum::IntoEnumIterator;
        assert_eq!(
            HighlightClass::iter().collect::<Vec<_>>(),
            HighlightClass::ALL
        );
    }

    /// A string with no closing quote on its line is the same error from
    /// `highlight` as from `tokenize`, and is a string to the end of its line.
    #[test]
    fn highlight_reports_an_unterminated_string() {
        let source = "x = 'ab\ncd";
        let Highlighted { spans, errors } = highlight(FileId::ROOT, source);
        assert_eq!(errors, self::errors(source));
        assert_eq!(
            spans[2],
            (HighlightClass::String, Span::new(FileId::ROOT, 4, 7))
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

    /// `token`'s source spelling: its `Display` text, when the logos lexer
    /// reads that text back as exactly `token`. Every keyword and symbol has
    /// one. A layout token is a newline or synthesized, and a literal or
    /// identifier has no one spelling, so their `Display` text is a description
    /// (`identifier`, …) that lexes as something else.
    fn source_spelling(token: &Token) -> Option<String> {
        let s = token.to_string();
        let mut lex = Token::lexer(&s);
        (lex.next() == Some(Ok(token.clone())) && lex.next().is_none()).then_some(s)
    }

    /// `KEYWORDS` lists exactly the keyword variants, in declaration order. A
    /// keyword is a variant whose [`source_spelling`] is identifier-shaped.
    /// `Display for Token` has no wildcard arm, so a new variant does not
    /// compile until it has a spelling, and the spelling decides whether it is
    /// a keyword.
    #[test]
    fn keywords_lists_exactly_the_keyword_variants() {
        use strum::IntoEnumIterator;
        let derived: Vec<Token> = Token::iter()
            .filter(|t| {
                source_spelling(t).is_some_and(|s| {
                    s.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
                        && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                })
            })
            .collect();
        let listed: Vec<Token> = KEYWORDS.iter().map(|(_, t)| t.clone()).collect();
        assert_eq!(derived, listed);
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
        let Highlighted { spans, errors } = highlight(FileId::ROOT, &sample);
        assert_eq!(errors, vec![], "the sample lexes");
        let present: std::collections::BTreeSet<&str> = spans
            .iter()
            .map(|(_, span)| &sample[span.start..span.end])
            .collect();
        let missing: Vec<String> = Token::iter()
            .filter_map(|token| source_spelling(&token))
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
        let Highlighted { spans, errors } = highlight(FileId::ROOT, &sample);
        assert_eq!(errors, vec![], "the sample lexes");
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
            errors(indoc! {"
                x = if c:
                        1
                    elif d:
                        2
                  else:
                        3
                y
            "})[..],
            [LexError::InconsistentIndent { .. }]
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
            errors(src)[..],
            [LexError::InconsistentIndent { .. }]
        ));
    }
}
