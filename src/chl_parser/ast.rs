//! CHL surface AST.
//!
//! Produced by [`super::parser`] and consumed (in a later phase) by
//! [`crate::ccl::lower`]. Until the lowering migration lands, this AST is only
//! used by the parser's own tests.
//!
//! # Design choices vs. `rustpython_ast`
//!
//! - **Every node carries a span.** Nodes are wrapped in [`Spanned<T>`], so
//!   diagnostics can point at any sub-expression without bolt-on span tables.
//! - **Operators are enums, not strings.** [`BinOp`], [`CmpOp`], [`BoolOp`],
//!   [`UnaryOp`], [`AugOp`] each enumerate exactly the operators CHL accepts;
//!   variants Python supports but CHL does not (`/`, `%`, `**`, `>>`, `~`,
//!   unary `+`, `is`, `in`) are simply absent. This makes lowering exhaustive
//!   without an `unimplemented!()` branch per operator.
//! - **`if`/`elif` flattens.** A chain of `if`/`elif`/`else` produces a single
//!   [`Stmt::If`] with one `branches` entry per `if`/`elif` and one
//!   optional `else_body`, rather than `rustpython_ast`'s nested
//!   `else: [If(...)]` representation.
//! - **Records are parens; braces are types.** A record *value* `(x=1, y=2)`
//!   parses as [`Expr::Record`]. A brace literal is type syntax: `{x: T}`
//!   (bare-identifier keys) is [`Expr::BraceRecord`] (a record type) and
//!   `{T, U}` is [`Expr::BraceGroup`] (a tuple type). Lowering reads the brace
//!   forms as types in annotation position and rejects them in value position.
//! - **Feed / Define get their own variants.** `x << v` is [`Expr::Feed`] and
//!   `x <<= v` is [`Stmt::Define`], rather than being a `BinOp(LShift)` and an
//!   `AugAssign(LShift)` that lowering has to special-case.

use smol_str::SmolStr;

/// Byte-offset span into the source text.
///
/// Half-open: `start..end` covers bytes `start, start+1, …, end-1`.
///
/// # Why byte offsets, not file/line/col
///
/// - **Composition is integer arithmetic.** Span joins, ordering, and
///   containment checks are `min` / `max` / `<=`. Line/col representations
///   need a same-line vs. different-line special case at every site.
/// - **AST stays cheap.** Two `usize`s, no allocations, `Copy`. Spans
///   appear on every node; file/line/col would be 3-4× the size and need
///   string interning for the file name.
/// - **Single source of truth.** Line/col is derivable from offset + the
///   source text via a one-time newline-index scan and an `O(log n)`
///   binary search. Storing line/col alongside risks drift; offsets only
///   ever degrade to "points at the wrong character", which is detectable.
///
/// The render-time tradeoff — needing the source text + a newline index to
/// turn `42` into "line 5, column 12" — is paid only when emitting
/// diagnostics, and ariadne / LSP / editor jump-to-location all want
/// offsets natively anyway.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
// Wire shape (inspector, feature `serde`): `{ "start": N, "end": N }` — byte
// offsets, exactly what the `/api/snapshot` schema specifies. The field names
// are already lowercase single words, so no `rename_all` is needed.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// Span covering both `self` and `other` (and any text between them).
    pub fn join(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    pub fn as_range(self) -> std::ops::Range<usize> {
        self.start..self.end
    }
}

impl From<std::ops::Range<usize>> for Span {
    fn from(r: std::ops::Range<usize>) -> Self {
        Span::new(r.start, r.end)
    }
}

impl From<Span> for std::ops::Range<usize> {
    fn from(s: Span) -> Self {
        s.as_range()
    }
}

/// Compact user-facing rendering: `start..end`. Used by chumsky's `Rich`
/// error formatter via its `S: Display` bound.
impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

/// Implement `chumsky::span::Span` so our AST's `Span` can be used as the
/// span type in the chumsky parser without copying spans through a separate
/// representation.
impl chumsky::span::Span for Span {
    type Context = ();
    type Offset = usize;

    fn new(_context: (), range: std::ops::Range<usize>) -> Self {
        Span::new(range.start, range.end)
    }

    fn context(&self) {}

    fn start(&self) -> usize {
        self.start
    }

    fn end(&self) -> usize {
        self.end
    }
}

/// A value of `T` together with the source span it came from.
#[derive(Debug, Clone, PartialEq)]
pub struct Spanned<T> {
    pub span: Span,
    pub node: T,
}

impl<T> Spanned<T> {
    pub fn new(span: Span, node: T) -> Self {
        Self { span, node }
    }
}

// ---------------------------------------------------------------------------
// Module
// ---------------------------------------------------------------------------

/// A complete CHL source file: a sequence of top-level statements.
#[derive(Debug, Clone, PartialEq)]
pub struct Module {
    pub body: Vec<Spanned<Stmt>>,
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

/// A CHL statement.
///
/// CHL statements correspond to lines (or block-introducing constructs) at
/// the top level of a function or module body. Expression-only lines are
/// wrapped in [`Stmt::Expr`].
#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    /// A bare expression evaluated for effect (or as a module's final value).
    Expr(Spanned<Expr>),

    /// Assignment: `target = value`.
    Assign {
        target: Spanned<AssignTarget>,
        value: Spanned<Expr>,
    },

    /// Annotated assignment: `target: ty = value`.
    ///
    /// CHL (unlike Python) requires a value; bare annotations are a parse
    /// error. `ty` is itself an [`Expr`] (Python's type expressions are
    /// arbitrary expressions); interpretation lives in lowering.
    AnnAssign {
        target: Spanned<AssignTarget>,
        annotation: Spanned<Expr>,
        value: Spanned<Expr>,
    },

    /// Augmented assignment: `target op= value`, e.g. `x += 1`.
    AugAssign {
        target: Spanned<AssignTarget>,
        op: AugOp,
        value: Spanned<Expr>,
    },

    /// Mutable assignment: `target := value`, or `target: ty := value` with an
    /// optional type annotation. `:=` is the *mutability* signal — it marks the
    /// assignment as a store introduction (first `:=` to a name) or a store write
    /// (subsequent), so lowering never has to guess `MutWrite`-vs-`Let` from a
    /// name registry. The annotation is optional: bare `x := 0` is an induction
    /// accumulator (domain inferred), `x: Mut(V, Txn) := 0` a transactional
    /// register (the annotation carries the `Txn` domain, exactly as before).
    MutAssign {
        target: Spanned<AssignTarget>,
        annotation: Option<Spanned<Expr>>,
        value: Spanned<Expr>,
    },

    /// Defer-define statement: `target <<= value`.
    ///
    /// Distinct from [`Stmt::AugAssign`] because it has no corresponding plain
    /// binary operator — it always defines a previously-deferred output.
    Define {
        target: Spanned<AssignTarget>,
        value: Spanned<Expr>,
    },

    /// `if cond: ... elif cond2: ... else: ...`.
    ///
    /// `branches` is non-empty and contains the `if` plus any `elif`s in
    /// source order. `else_body` is `Some` iff an `else:` block was written.
    If {
        branches: Vec<IfBranch>,
        else_body: Option<Vec<Spanned<Stmt>>>,
    },

    /// ``match scrutinee: case `tag(binder): … case `tag2: …`` — tag dispatch over
    /// a [`crate::ccl::Type::Variant`].
    ///
    /// A block statement mirroring [`Stmt::If`], and value-yielding by the same
    /// rule: in a position that requires a value, every arm's block must end in
    /// a value-yielding statement (`docs/chl-spec.md`, "4.5 `if` / `elif` / `else`").
    /// `arms` is non-empty and in source order; first match wins, though the
    /// arms are tag-disjoint so order is not observable.
    Match {
        scrutinee: Spanned<Expr>,
        arms: Vec<MatchArm>,
    },

    /// `for target in iter: body`.
    For {
        target: Spanned<AssignTarget>,
        iter: Spanned<Expr>,
        body: Vec<Spanned<Stmt>>,
    },

    /// `def name(params): body`.
    FunctionDef {
        name: SmolStr,
        params: Vec<Param>,
        body: Vec<Spanned<Stmt>>,
    },

    /// `with <binding> = <context>: body` — a transaction block. The context
    /// is `begin()` (the transaction marker); `binding`, when present, names
    /// the transaction's commit time (`with t = begin(): …`) — parsed but not
    /// yet consumed by lowering (reserved for transaction-handle operations).
    /// See src/ccl/design/mutability.md.
    With {
        binding: Option<SmolStr>,
        context: Spanned<Expr>,
        body: Vec<Spanned<Stmt>>,
    },

    /// `return value` (only valid inside a function body; not enforced here).
    Return(Option<Spanned<Expr>>),

    /// `pass` — no-op statement that holds a place where a block is required.
    Pass,

    /// Recovery placeholder inserted when the parser's statement-level
    /// `recover_with` fired. The placeholder's [`Span`] covers the source
    /// range that was skipped during recovery.
    ///
    /// **Contract.** This variant exists *only* when [`super::parser::ParseResult::errors`]
    /// is non-empty. Callers must inspect `errors` before consuming the AST;
    /// downstream passes given an error-free parse may treat this variant as
    /// unreachable. Mixing recovered ASTs into the compilation pipeline
    /// without first surfacing the parse errors is a caller bug.
    Error,
}

/// One branch of an [`Stmt::If`]: a guard and the body to run when it holds.
#[derive(Debug, Clone, PartialEq)]
pub struct IfBranch {
    pub cond: Spanned<Expr>,
    pub body: Vec<Spanned<Stmt>>,
}

/// One arm of a [`Stmt::Match`]: ``case `tag(binder): body``.
///
/// The pattern spells its tag exactly as [`Expr::VariantCtor`] does — the
/// backtick and the parenthesised payload — so destructuring reads as the
/// inverse of the construction it matches.
#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    /// The tag this arm matches, or `None` for the **default arm** `case _:`,
    /// which matches whatever the tagged arms did not.
    ///
    /// Mirrors [`crate::ccl::Branch`]'s `pattern: Option<Pattern>`, which is
    /// the shape this lowers to: a tag-less branch in a scrutinee-`Case`.
    pub pattern: Option<MatchPattern>,
    pub body: Vec<Spanned<Stmt>>,
}

/// The tag a [`MatchArm`] matches, and the name its payload binds to.
#[derive(Debug, Clone, PartialEq)]
pub struct MatchPattern {
    pub tag: SmolStr,
    pub tag_span: Span,
    /// Name bound to the tag's payload for the arm's body. `None` for the
    /// binder-less form `case tag:`, which discards a payload it does not read
    /// (and is the natural spelling for a `Unit` payload such as `none`).
    pub binder: Option<SmolStr>,
}

/// A function parameter: a name with an optional type annotation.
#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: SmolStr,
    pub name_span: Span,
    pub annotation: Option<Spanned<Expr>>,
}

/// The left-hand side of an assignment, augmented assignment, defer-define,
/// for-loop, or comprehension `for` clause — i.e. anywhere CHL binds names.
///
/// Restricted to bare names and (possibly-nested) tuple patterns. Subscript
/// (`xs[0] = ...`) and attribute (`obj.f = ...`) targets are not part of
/// CHL today; if added later they would extend this enum rather than
/// reopening the `target: Expr` escape hatch the previous AST allowed.
#[derive(Debug, Clone, PartialEq)]
pub enum AssignTarget {
    /// A bare identifier: `x = ...`.
    Name(SmolStr),
    /// A tuple destructuring pattern: `(a, b), c = ...`. May nest.
    Tuple(Vec<Spanned<AssignTarget>>),
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

/// What a [`Expr::VariantCtor`] carries, and which bracket wrote it.
///
/// A tag's payload is a term in term position and a field list in type
/// position, and the bracket says which: `` `some(1) `` against
/// `` `some{Int} ``. Keeping the bracket rather than normalising both to "the
/// payload" is what lets lowering name the *right* form when an author writes
/// the other one — the two are never interchangeable, so a plain "unsupported
/// payload" would leave the fix to be guessed.
#[derive(Debug, Clone, PartialEq)]
pub enum VariantPayload {
    /// `` `tag(𝑒) `` — a term payload, in a constructor or a pattern.
    Term(Box<Spanned<Expr>>),
    /// `` `tag{…} `` — the tag's **field list**, in a type. Positional
    /// (`` `pair{Int, Bool} ``, an [`Expr::BraceGroup`]) or named
    /// (`` `pair{a: Int, b: Bool} ``, an [`Expr::BraceRecord`]).
    Fields(Box<Spanned<Expr>>),
}

/// A CHL expression.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// A literal value: integer, string, bool, or `None`.
    Lit(Lit),

    /// A bare identifier — variable or function name.
    Name(SmolStr),

    /// A binary operation: `lhs op rhs`.
    BinOp {
        left: Box<Spanned<Expr>>,
        op: BinOp,
        right: Box<Spanned<Expr>>,
    },

    /// A unary operation: `op operand`.
    UnaryOp {
        op: UnaryOp,
        operand: Box<Spanned<Expr>>,
    },

    /// A short-circuiting boolean operation: `a and b and c`, `a or b or c`.
    ///
    /// Operands are stored flat (not as nested `BinOp`) to match Python's
    /// associativity-free n-ary form, which makes lowering to short-circuit
    /// evaluation cleaner.
    BoolOp {
        op: BoolOp,
        operands: Vec<Spanned<Expr>>,
    },

    /// A comparison chain: `a < b < c == d`.
    ///
    /// `comparators.len() == ops.len()`; the chain is `left ops[0] comparators[0]
    /// ops[1] comparators[1] …`. Semantically equivalent to a conjunction of
    /// adjacent pairwise comparisons.
    Compare {
        left: Box<Spanned<Expr>>,
        ops: Vec<CmpOp>,
        comparators: Vec<Spanned<Expr>>,
    },

    /// Function call: `func(args)`. CHL does not support keyword arguments.
    Call {
        func: Box<Spanned<Expr>>,
        args: Vec<Spanned<Expr>>,
    },

    /// List literal: `[e0, e1, …]`.
    List(Vec<Spanned<Expr>>),

    /// Tuple literal: `(e0, e1, …)` or `e0, e1, …` in target position.
    ///
    /// A single-element tuple is written `(e0,)`; without the trailing comma
    /// `(e0)` parses as parenthesised `e0`, not as a tuple.
    Tuple(Vec<Spanned<Expr>>),

    /// Record **value** with named fields: `(x=1, y=2)`.
    ///
    /// The product constructor is the parentheses (see `docs/chl-spec.md`);
    /// a record is a product with named fields, a tuple one with anonymous
    /// fields, both delimited by `( … )`.
    Record(Vec<RecordField>),

    /// A brace record: `{x: T, y: U}` (bare-identifier keys with `:` values).
    ///
    /// Term-level braces are reserved for structural **type** syntax (see
    /// `docs/chl-spec.md`), so this is a record *type*: lowering reads it as a
    /// [`crate::ccl::Type::Record`] in annotation position and rejects it in
    /// value position (a record *value* is `(x=1, y=2)`, [`Expr::Record`]).
    BraceRecord(Vec<RecordField>),

    /// A colon-free brace group: `{T, U}` (no `key: value` entries).
    ///
    /// Term-level braces are reserved for structural **type** syntax (see
    /// `docs/chl-spec.md`): a tuple type `{T, U}`. Lowering interprets it as a
    /// [`crate::ccl::Type::Tuple`] in annotation position and rejects it in
    /// value position.
    BraceGroup(Vec<Spanned<Expr>>),

    /// Subscript: `target[index]`.
    Subscript {
        target: Box<Spanned<Expr>>,
        index: Box<Spanned<Expr>>,
    },

    /// Attribute access: `target.attr`.
    Attribute {
        target: Box<Spanned<Expr>>,
        attr: SmolStr,
        attr_span: Span,
    },

    /// A backtick-introduced variant arm: `` `tag(payload) `` in a term,
    /// `` `tag{fields} `` in a type, and bare `` `tag `` for a tag that carries
    /// nothing.
    ///
    /// The backtick is what distinguishes a tag from a name, in every position:
    /// without it `some(1)` would be a [`Expr::Call`] to a function named
    /// `some`, and `` {some{Int}} `` a type application. Tags need no
    /// declaration — [`crate::ccl::Type::Variant`] is structural, so
    /// `` `tag(𝑒) `` synthesises the singleton variant `` {`tag{𝑇}} `` and width
    /// subtyping flows it into any consumer whose tag set contains it. See
    /// `docs/chl-spec.md`, "3.15 Variant constructors".
    ///
    /// One node covers the term and the type because the two differ only in
    /// their payload bracket; [`VariantPayload`] records which was written, and
    /// lowering rejects the bracket that does not belong in its position.
    VariantCtor {
        /// The tag name.
        tag: SmolStr,
        tag_span: Span,
        /// The payload, or `None` for the bare form `` `tag ``. A term's bare
        /// form lowers to a `Unit` payload — a nullary constructor is not a
        /// *distinct* kind of tag, just one whose payload carries no
        /// information.
        payload: Option<VariantPayload>,
    },

    /// Lambda: `\params -> body`.
    Lambda {
        params: Vec<Param>,
        body: Box<Spanned<Expr>>,
    },

    /// Ternary conditional: `then_expr if cond else else_expr`.
    IfExp {
        cond: Box<Spanned<Expr>>,
        then_expr: Box<Spanned<Expr>>,
        else_expr: Box<Spanned<Expr>>,
    },

    /// List comprehension: `[element for ... if ... for ... if ...]`.
    ListComp(Comprehension),

    /// Generator expression: `(element for ... if ...)`.
    GenExp(Comprehension),

    /// `yield value` inside a generator function body.
    Yield(Box<Spanned<Expr>>),

    /// Feed operator: `target << value`. Pushes `value` into a deferred
    /// output. Distinct from `BinOp` to prevent accidental optimisation as
    /// a pure operator.
    Feed {
        target: Box<Spanned<Expr>>,
        value: Box<Spanned<Expr>>,
    },

    /// Recovery placeholder inserted when chumsky's bracket-level
    /// `recover_with` matched. The placeholder's [`Span`] covers the
    /// bracketed region whose contents failed to parse.
    ///
    /// **Contract.** This variant exists *only* when [`super::parser::ParseResult::errors`]
    /// is non-empty. Callers must inspect `errors` before consuming the AST;
    /// downstream passes given an error-free parse may treat this variant as
    /// unreachable. See [`Stmt::Error`] for the matching statement-level
    /// placeholder.
    Error,
}

/// A literal value.
#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    Int(i64),
    /// String literal with escapes already processed.
    String(String),
    Bool(bool),
    /// Python `None` — the CHL unit value.
    None,
}

/// A named field: `name=value` in an [`Expr::Record`] value, or `name: T` in
/// an [`Expr::BraceRecord`] record type.
#[derive(Debug, Clone, PartialEq)]
pub struct RecordField {
    pub name: SmolStr,
    pub name_span: Span,
    pub value: Spanned<Expr>,
}

/// A comprehension body, shared by [`Expr::ListComp`] and [`Expr::GenExp`].
#[derive(Debug, Clone, PartialEq)]
pub struct Comprehension {
    /// The element expression evaluated for each iteration.
    pub element: Box<Spanned<Expr>>,
    /// The sequence of `for ... in ...` and `if ...` clauses, in source order.
    pub clauses: Vec<CompClause>,
}

/// One clause of a comprehension.
#[derive(Debug, Clone, PartialEq)]
pub enum CompClause {
    /// `for target in iter`.
    For {
        target: Spanned<AssignTarget>,
        iter: Spanned<Expr>,
    },
    /// `if guard`.
    If(Spanned<Expr>),
}

// ---------------------------------------------------------------------------
// Operators
// ---------------------------------------------------------------------------

/// Binary operators accepted by CHL.
///
/// Notably absent vs. Python: `/` (true division), `%` (modulo), `**` (power),
/// `>>` (right shift). CHL's lowering does not implement these and the parser
/// rejects them at the syntactic level.
///
/// CHL reuses several Python tokens with different semantics: `&`, `|`, `^`
/// denote logical (not bitwise) and/or/xor. `++` denotes collection union
/// (CHL has no string-concatenation operator — `+` on strings handles that).
/// The variant names below reflect CHL's semantics rather than the source
/// token spellings.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    FloorDiv,
    /// `&` — logical and (CHL reuses Python's bitwise-and token).
    LogicalAnd,
    /// `|` — logical or (CHL reuses Python's bitwise-or token).
    LogicalOr,
    /// `^` — logical xor (CHL reuses Python's bitwise-xor token).
    LogicalXor,
    /// `++` — collection union.
    CollectionUnion,
}

/// Unary operators accepted by CHL.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}

/// Short-circuiting boolean operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoolOp {
    And,
    Or,
}

/// Comparison operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpOp {
    Eq,
    NotEq,
    Lt,
    LtE,
    Gt,
    GtE,
}

/// Augmented-assignment operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AugOp {
    Add,
    Sub,
    Mul,
    FloorDiv,
}
