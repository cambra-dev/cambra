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
//!   [`Stmt::If`] with one [`If::branches`] entry per `if`/`elif` and one
//!   optional [`If::else_body`], rather than `rustpython_ast`'s nested
//!   `else: [If(...)]` representation.
//! - **Records vs. dicts are syntactically distinct.** `{x: 1, y: 2}` (bare
//!   identifier keys) parses as [`Expr::Record`]; `{"name": "alice"}`
//!   (expression keys) parses as [`Expr::Dict`]. This matches how CHL already
//!   interprets the two forms semantically and eliminates a re-classification
//!   pass.
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

    /// Defer-define statement: `target <<= value`.
    ///
    /// Distinct from [`AugAssign`] because it has no corresponding plain
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

    /// Record literal with bare-identifier keys: `{x: 1, y: 2}`.
    ///
    /// CHL treats this as a named-field product type, distinct from
    /// [`Expr::Dict`] (which has expression keys).
    Record(Vec<RecordField>),

    /// Dict literal with expression keys: `{"name": "alice", expr: value}`.
    Dict(Vec<(Spanned<Expr>, Spanned<Expr>)>),

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

    /// Lambda: `lambda params: body`.
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

/// A field in an [`Expr::Record`]: `name: value`.
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
