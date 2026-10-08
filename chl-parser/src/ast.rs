//! Span-bearing CHL syntax consumed by CCL lowering and `chl-interp`.
//!
//! AST shape choices are specified in `chl-parser/design-chl-parser.md`,
//! "Stage 3 — AST (`ast.rs`)". Type-expression nodes retain syntax for lowering to interpret.

use smol_str::SmolStr;

pub use super::source_map::FileId;

/// A byte range in one source file.
///
/// Half-open: `start..end` covers bytes `start, start+1, …, end-1` of the file
/// `file` names. Offsets count from the start of that file, so editing one file
/// moves no span in another.
///
/// # Why byte offsets, not line/col
///
/// - **Composition is integer arithmetic.** Span joins, ordering, and
///   containment checks are `min` / `max` / `<=`. Line/col representations
///   need a same-line vs. different-line special case at every site.
/// - **AST stays cheap.** A [`FileId`] and two `usize`s, no allocations,
///   `Copy`.
/// - **Single source of truth.** Line/col is derivable from offset + the
///   source text via a one-time newline-index scan and an `O(log n)`
///   binary search. Storing line/col alongside risks drift; offsets only
///   ever degrade to "points at the wrong character", which is detectable.
///
/// The render-time tradeoff — needing the source text + a newline index to
/// turn `42` into "line 5, column 12" — is paid only when emitting
/// diagnostics, through the [`SourceMap`](super::source_map::SourceMap) the
/// `file` indexes.
// Wire shape (inspector): `{ "file": N, "start": N, "end": N }` — the file's
// index and byte offsets, exactly what the `/api/snapshot` schema specifies.
// The field names are already lowercase single words, so no `rename_all` is
// needed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
pub struct Span {
    pub file: FileId,
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(file: FileId, start: usize, end: usize) -> Self {
        Self { file, start, end }
    }

    /// Span covering both `self` and `other` (and any text between them).
    ///
    /// Both spans lie in one file: no text lies between two files, so a join
    /// across them has no meaning.
    pub fn join(self, other: Span) -> Span {
        debug_assert_eq!(
            self.file, other.file,
            "Span::join of spans in two files: {self:?} and {other:?}"
        );
        Span {
            file: self.file,
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    pub fn as_range(self) -> std::ops::Range<usize> {
        self.start..self.end
    }
}

impl From<Span> for std::ops::Range<usize> {
    fn from(s: Span) -> Self {
        s.as_range()
    }
}

/// Compact user-facing rendering: `start..end`. Used by chumsky's `Rich`
/// error formatter via its `S: Display` bound, and by [`ParseError`]'s
/// one-line `Display`, which describes an error in a file the reader already
/// knows.
///
/// [`ParseError`]: super::parser::ParseError
impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

/// Implement `chumsky::span::Span` so our AST's `Span` can be used as the
/// span type in the chumsky parser without copying spans through a separate
/// representation. The context is the file: chumsky builds every span it
/// derives from the end-of-input span's context, so the file the parser was
/// handed reaches every node.
impl chumsky::span::Span for Span {
    type Context = FileId;
    type Offset = usize;

    fn new(file: FileId, range: std::ops::Range<usize>) -> Self {
        Span::new(file, range.start, range.end)
    }

    fn context(&self) -> FileId {
        self.file
    }

    fn start(&self) -> usize {
        self.start
    }

    fn end(&self) -> usize {
        self.end
    }
}

/// Implement `ariadne::Span` so a diagnostic labels a [`Span`] directly, and a
/// report's labels may lie in several files: ariadne fetches each label's file
/// from the [`SourceMap`](super::source_map::SourceMap) by its [`FileId`].
impl ariadne::Span for Span {
    type SourceId = FileId;

    fn source(&self) -> &FileId {
        &self.file
    }

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
    /// The file the module was parsed from. Every span in `body` lies in it.
    pub file: FileId,
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

    /// Assignment: `target = value`, or `target ^= value` for an opaque binder
    /// ([`BindingTransparency`]).
    Assign {
        target: Spanned<AssignTarget>,
        value: Spanned<Expr>,
        transparency: BindingTransparency,
    },

    /// Annotated assignment: `target: ty = value` or `target <: ty = value`.
    ///
    /// CHL (unlike Python) requires a value; a bare annotation is a parse error
    /// except under `@LoadFrom` ([`Stmt::LoadFrom`]), which supplies one. The
    /// annotation type is itself an [`Expr`] (type expressions are arbitrary
    /// expressions); interpretation lives in lowering.
    AnnAssign {
        target: Spanned<AssignTarget>,
        annotation: TypeAnnotation,
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
    /// mutable variable (the annotation carries the `Txn` domain, exactly as before).
    MutAssign {
        target: Spanned<AssignTarget>,
        annotation: Option<TypeAnnotation>,
        value: Spanned<Expr>,
    },

    /// A declaration seeded from the version this source replaces:
    ///
    /// ```text
    /// @LoadFrom(qty)
    /// qty_units: Map(String, Int)
    /// ```
    ///
    /// The only form in which a declaration carries an annotation and no value
    /// — the decorator is where the value comes from, so nothing is missing.
    /// A bare `y: T` is still a parse error
    /// ([`Stmt::AnnAssign`](Stmt::AnnAssign)).
    ///
    /// `source` names a mutable variable of the **previous** version, which this
    /// one need not declare; lowering resolves it against nothing in this scope.
    LoadFrom {
        target: Spanned<AssignTarget>,
        annotation: TypeAnnotation,
        source: Spanned<SmolStr>,
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
    /// a `cambra::ccl::Type::Variant`.
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

    /// `def name(type_params, params) => output requires …: body`.
    ///
    /// The type parameters are the capitalized leading parameters, kept apart from
    /// `params` because they are not arguments: `params` alone is the arity.
    FunctionDef {
        name: SmolStr,
        type_params: Vec<TypeParam>,
        params: Vec<Param>,
        output: Option<Spanned<Expr>>,
        requires: Vec<Spanned<Requirement>>,
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

    /// `import a::b as c use f, T as U` — bind the shared run of a module
    /// (`docs/chl-spec.md`, "9.2 Imports").
    Import {
        path: ModulePath,
        alias: Option<Spanned<SmolStr>>,
        uses: Vec<UseItem>,
    },

    /// `run m(arg=e, …) as n use f` — declare a run of a module
    /// (`docs/chl-spec.md`, "9.3 Runs"). `args` is empty for both `run m` and
    /// `run m()`.
    Run {
        path: ModulePath,
        args: Vec<RunArg>,
        alias: Option<Spanned<SmolStr>>,
        uses: Vec<UseItem>,
        /// The predecessor's run this one was, from `@RenamedFrom(eu)` on the
        /// line above (`docs/chl-spec.md`, "9.18 Reloading a program of
        /// modules"). The statement's span then begins at the decorator.
        renamed_from: Option<Spanned<SmolStr>>,
    },

    /// `param x: T = e`, or `param T <: B = U` for a type parameter
    /// (`docs/chl-spec.md`, "9.4 Parameters").
    ///
    /// A capitalized name is a type parameter. The parser accepts only the
    /// exact annotation on a value parameter and only the bounded one on a type
    /// parameter, so the annotation's mode always agrees with the name's case.
    Param {
        name: Spanned<SmolStr>,
        annotation: Option<TypeAnnotation>,
        default: Option<Spanned<Expr>>,
    },

    /// `@Discard` on the line above a declaration head: what the version this
    /// source replaces held there is intentionally gone (`docs/chl-spec.md`,
    /// "8.9 `@Discard` \[Decided\]").
    Discard(DiscardHead),

    /// `pub` before the statement that introduces a member (`docs/chl-spec.md`,
    /// "9.5 Visibility").
    ///
    /// `keyword` is the span of `pub` itself. It is where the statement starts,
    /// except on a decorated statement, whose `pub` stands on the line below the
    /// decorator: `@LoadFrom(qty)` above `pub held: Int`, and `@RenamedFrom(eu)`
    /// above `pub run storefront as eu_west`.
    ///
    /// **Invariant:** in a parse with no errors, the inner statement is a
    /// [`Stmt::Assign`], [`Stmt::AnnAssign`], [`Stmt::MutAssign`],
    /// [`Stmt::LoadFrom`], [`Stmt::FunctionDef`] or [`Stmt::Run`]. The parser
    /// reports `pub` on any other statement as a parse error. Whether a `:=`
    /// introduces a mutable variable, and whether the statement stands at a
    /// module's top level, are left to lowering.
    Pub {
        keyword: Span,
        stmt: Box<Spanned<Stmt>>,
    },

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

/// A module path, `shop::cart` (`docs/chl-spec.md`, "9.1 Vocabulary").
///
/// **Invariant:** at least one segment, each beginning with a lowercase letter
/// and none with `__` (`docs/chl-spec.md`, "9.15 Module files"). The parser
/// refuses any other path.
#[derive(Debug, Clone, PartialEq)]
pub struct ModulePath {
    pub segments: Vec<Spanned<SmolStr>>,
}

impl ModulePath {
    /// The span from the first segment to the last.
    pub fn span(&self) -> Span {
        let first = self.segments.first().expect("a module path has a segment");
        let last = self.segments.last().expect("a module path has a segment");
        first.span.join(last.span)
    }

    /// The module this path names, or `None` when a segment breaks the rule
    /// of [`crate::module_path::segment_error`], which the parser reported.
    pub fn to_path(&self) -> Option<crate::module_path::ModulePath> {
        self.segments
            .iter()
            .all(|s| crate::module_path::segment_error(&s.node).is_none())
            .then(|| {
                crate::module_path::ModulePath::new(self.segments.iter().map(|s| s.node.clone()))
            })
    }
}

/// One name a `use` clause binds: `f`, or `T as U` (`docs/chl-spec.md`, "9.2
/// Imports").
///
/// **Invariant:** `alias`, when present, has the case of `name`: a type member
/// is bound to a capitalized name and a value member to a lowercase one.
#[derive(Debug, Clone, PartialEq)]
pub struct UseItem {
    pub name: Spanned<SmolStr>,
    pub alias: Option<Spanned<SmolStr>>,
}

/// One keyword argument of a [`Stmt::Run`]: `port="8080"`.
#[derive(Debug, Clone, PartialEq)]
pub struct RunArg {
    pub name: Spanned<SmolStr>,
    pub value: Spanned<Expr>,
}

/// The declaration head a [`Stmt::Discard`] marks gone.
#[derive(Debug, Clone, PartialEq)]
pub enum DiscardHead {
    /// `stock` — a variable.
    Name(Spanned<SmolStr>),
    /// `run m as n` — a run, and every variable it held.
    Run {
        path: ModulePath,
        alias: Option<Spanned<SmolStr>>,
    },
    /// `import m` — the shared run of `m`, and every variable it held.
    Import { path: ModulePath },
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
    /// Mirrors `cambra::ccl::Branch`'s `pattern: Option<Pattern>`, which is
    /// the shape this lowers to: a tag-less branch in a scrutinee-`Case`.
    pub pattern: Option<MatchPattern>,
    pub body: Vec<Spanned<Stmt>>,
}

/// The tag a [`MatchArm`] matches, and what it says about that tag's payload.
#[derive(Debug, Clone, PartialEq)]
pub struct MatchPattern {
    pub tag: SmolStr,
    pub tag_span: Span,
    /// The module the tag belongs to, as in [`Expr::VariantCtor`]'s
    /// `tag_qualifier`.
    pub tag_qualifier: Vec<Spanned<SmolStr>>,
    pub payload: PayloadPattern,
}

/// What an arm's pattern says about the tag's payload.
///
/// The three spellings make **two** statements, and the split is the point:
/// declining to *read* a payload is not the same claim as there being none. ``
/// `some{Int} `` and `` `some `` are different types, so a pattern that names no
/// payload matches only the second — there is no silent conversion between them.
#[derive(Debug, Clone, PartialEq)]
pub enum PayloadPattern {
    /// `` case `tag(v): `` — the tag carries a payload, bound to `v` for the arm's
    /// body.
    Named(SmolStr),
    /// `` case `tag(_): `` — the tag carries a payload the arm does not read. `_` is
    /// the unused-binder spelling, in the same sense `case _:` uses it for an arm
    /// whose tag is not named; it is not a name, so the body cannot refer to it.
    Ignored,
    /// `` case `tag: `` — the tag carries **no** payload. A type statement, not an
    /// elision: this arm does not match a `` `tag `` that carries one.
    Absent,
}

/// A function parameter: a name with an optional type annotation.
#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: SmolStr,
    pub name_span: Span,
    pub annotation: Option<TypeAnnotation>,
}

/// A type parameter: a capitalized name, optionally with its kind, `T: K`, or its upper
/// bound, `T <: U`.
///
/// Spec: `docs/chl-spec.md`, "Type parameters".
#[derive(Debug, Clone, PartialEq)]
pub struct TypeParam {
    pub name: SmolStr,
    pub name_span: Span,
    pub annotation: Option<KindAnnotation>,
}

/// What a type parameter's annotation states (`docs/chl-spec.md`, "Kinds and bounds").
#[derive(Debug, Clone, PartialEq)]
pub enum KindAnnotation {
    /// `T: K` — the kind `K` itself.
    Kind(Spanned<Expr>),
    /// `T <: U` — the upper bound `U`, which is the kind `SubtypesOf(U)`.
    Bound(Spanned<Expr>),
}

/// One requirement of a `requires` clause: `Addable(A, B, Output=O)`, or a bare
/// name such as `Transaction`.
///
/// Spec: `docs/chl-spec.md`, "Trait requirements".
#[derive(Debug, Clone, PartialEq)]
pub struct Requirement {
    pub name: SmolStr,
    pub name_span: Span,
    /// The operand types, positionally.
    pub args: Vec<Spanned<Expr>>,
    /// The associated types, by name, written after the operands.
    pub assoc: Vec<AssocArg>,
}

/// A named argument of a requirement, `Output=O`.
#[derive(Debug, Clone, PartialEq)]
pub struct AssocArg {
    pub name: SmolStr,
    pub name_span: Span,
    pub value: Spanned<Expr>,
}

/// A user-written type annotation at a binder, and which of the two readings it
/// asks for.
///
/// The two spellings differ only in the mode; the type expression is parsed
/// identically. Lowering turns [`AnnotationMode::Bounded`] into a
/// `cambra::ccl::Type::BoundedHole` wrapper and leaves `Exact` bare.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeAnnotation {
    pub mode: AnnotationMode,
    pub ty: Spanned<Expr>,
}

/// Which reading a binder annotation asks for.
///
/// Spec: `docs/chl-spec.md`, "Two annotation forms: exact and bounded".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnnotationMode {
    /// `x: T` — the binder's type **is** `T`. The initializer (or argument) must
    /// be a subtype of `T`, and nothing downstream of the binder sees more than
    /// `T`.
    Exact,
    /// `x <: T` — the binder's type is *inferred*, with `T` as an upper bound.
    /// The value's own type flows through.
    Bounded,
}

/// Whether a binder's references may be discharged to its initializer.
///
/// Experimental, and so absent from `docs/chl-spec.md`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindingTransparency {
    /// `x = e` — the binder carries `e` as its definiens, so a type that
    /// mentions `x` outside the binder's scope reads `e` in its place.
    Transparent,
    /// `x ^= e` — the binder carries no definiens. `x` is bound at `e`'s type,
    /// refinements and all, and that type is everything a later type learns
    /// about it.
    Opaque,
}

/// The left-hand side of an assignment, augmented assignment, defer-define,
/// for-loop, or comprehension `for` clause — i.e. anywhere CHL binds names.
///
/// Restricted to bare names, (possibly-nested) tuple patterns, and a subscript.
/// Attribute targets (`obj.f = ...`) are not part of CHL today; if added later
/// they would extend this enum rather than reopening the `target: Expr` escape
/// hatch the previous AST allowed.
#[derive(Debug, Clone, PartialEq)]
pub enum AssignTarget {
    /// A bare identifier: `x = ...`.
    Name(SmolStr),
    /// A tuple destructuring pattern: `(a, b), c = ...`. May nest.
    Tuple(Vec<Spanned<AssignTarget>>),
    /// One key of a `Map`: `m[k] := v`.
    ///
    /// Not a binding position, unlike the other two: the collection is not being
    /// bound, one of its keys is being written. Only `:=` accepts it, a keyed write
    /// being a write to a mutable collection (`src/ccl/design/mutability.md`,
    /// "Surface-marker nodes: `For`, `MutWrite`, `Begin`, `Feed`"); every other
    /// statement form rejects it at lowering, where the message can name the binder
    /// the form wanted. The checked spelling `m[k]? := v` is refused earlier, in
    /// [`expr_to_assign_target`](crate::parser), because it is not a
    /// target this enum can hold rather than a target used in the wrong statement.
    ///
    /// The target is an arbitrary expression rather than a name so that a write
    /// through a path (`a.b[k] := v`) has somewhere to land; lowering accepts only
    /// the shapes it can resolve a mutable variable from.
    Subscript {
        target: Box<Spanned<Expr>>,
        index: Box<Spanned<Expr>>,
    },
    /// A variable of another module or run, `c::count := v`
    /// (`docs/chl-spec.md`, "9.6 Qualified references").
    Qualified(QualifiedName),
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
    /// `` `tag{…} `` — the tag's payload **type**, in a type position.
    ///
    /// A tag's braces are the payload type's own braces, elided, so this holds
    /// the payload type as the parser resolved it: the braced type itself for
    /// `` `pair{Int, Bool} `` (an [`Expr::BraceGroup`]) or `` `pair{a: Int} ``
    /// (an [`Expr::BraceRecord`]), and the bare inner type for `` `some{Int} ``,
    /// whose braces belong to the tag because a lone comma-free `{T}` is not a
    /// product (§2.4).
    Fields(Box<Spanned<Expr>>),
}

/// A CHL expression.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// A literal value: integer, string, or bool.
    Lit(Lit),

    /// A bare identifier — variable or function name.
    Name(SmolStr),

    /// A qualified reference, `cart::total` or `shop::eu::stock`: a member
    /// reached through an import name, a run name, or a Module-typed parameter
    /// (`docs/chl-spec.md`, "9.6 Qualified references").
    Qualified(QualifiedName),

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
    /// `cambra::ccl::Type::Record` in annotation position and rejects it in
    /// value position (a record *value* is `(x=1, y=2)`, [`Expr::Record`]).
    BraceRecord(Vec<RecordField>),

    /// A colon-free brace group: `{T, U}` (no `key: value` entries).
    ///
    /// Term-level braces are reserved for structural **type** syntax (see
    /// `docs/chl-spec.md`): a tuple type `{T, U}`. Lowering interprets it as a
    /// `cambra::ccl::Type::Tuple` in annotation position and rejects it in
    /// value position.
    ///
    /// Braces in type position are always a *product*, never grouping, which
    /// fixes both ends of the arity range (`docs/chl-spec.md`, "2.4 Atoms"):
    ///
    /// - **One element** carries the trailing comma, `{T,}`, matching the
    ///   term-level `(e,)`/`(e)` split. A comma-free `{T}` is rejected by the
    ///   parser, so it never reaches this variant.
    /// - **Zero elements** — `{}` — is the **unit type**, not a zero-field
    ///   product (`docs/chl-spec.md`, "6.6 The empty product is unit"). Lowering
    ///   maps the empty group there; it does *not* build an empty
    ///   `cambra::ccl::Type::Tuple`, which is not a valid type.
    BraceGroup(Vec<Spanned<Expr>>),

    /// A refinement type `{ T where p }`: the base type `T`, the keyword
    /// `where`, and a predicate `p` over the anonymous subject `_`
    /// (`docs/chl-spec.md`, "6.4 Refinement syntax").
    ///
    /// Term-level braces are reserved for structural **type** syntax like
    /// [`Expr::BraceRecord`] / [`Expr::BraceGroup`], so this too is only
    /// meaningful in annotation position: lowering reads it as a
    /// `cambra::ccl::Type::Refinement` and rejects it in value position.
    ///
    /// `base` is a single colon-free type expression (the parser rejects a
    /// multi-item or `field: T` base before this variant is built). `predicate`
    /// is an ordinary CHL `Bool` expression in which `_` denotes the value being
    /// refined; lowering maps that `_` to the reserved refinement binder
    /// (`cambra::ccl::REFINEMENT_BINDER`).
    BraceRefinement {
        base: Box<Spanned<Expr>>,
        predicate: Box<Spanned<Expr>>,
    },

    /// A function type `T => U`: a domain type, the `=>` arrow, and a codomain
    /// type (`docs/chl-spec.md`, "4.1 `def` — function definition" and "6. Types
    /// (informal sketch)").
    ///
    /// Like [`Expr::BraceRefinement`], this is structural **type** syntax,
    /// meaningful only in annotation position: lowering reads it as a
    /// `cambra::ccl::Type::Fun` (a compute function, `⇒`) and rejects it in
    /// value position. It is right-associative — `A => B => C` parses as
    /// `A => (B => C)` — because the parser takes the whole expression to the
    /// right of `=>` as the codomain.
    FunctionType {
        domain: Box<Spanned<Expr>>,
        codomain: Box<Spanned<Expr>>,
    },

    /// Subscript: `target[index]`, or the **checked** form `target[index]?` —
    /// **collection lookup only**. Projecting a product is a different operation and
    /// has its own spelling, [`Expr::Attribute`].
    ///
    /// The two subscript forms are one syntactic form because they are one operation —
    /// evaluate a finite function at a point — differing only in what happens when the
    /// point may be absent. `checked` yields `Option(V)` and always type-checks; the
    /// plain form yields `V` and requires the index's presence to be *provable*
    /// (`docs/chl-spec.md`, "3.9 Subscript and attribute access").
    Subscript {
        target: Box<Spanned<Expr>>,
        index: Box<Spanned<Expr>>,
        checked: bool,
    },

    /// Attribute access: `target.attr` — a record field by **name** (`r.age`) or a
    /// tuple position by **index** (`t.0`, whose digits are held here verbatim).
    ///
    /// One node for both because they are one operation, projecting a field; what
    /// differs is only how the field is keyed, which
    /// `cambra::ccl::ProjKey` already models. Lowering resolves the key once,
    /// so the distinction is stated where projection is built rather than a third time
    /// here. An identifier cannot begin with a digit, so the forms never collide.
    Attribute {
        target: Box<Spanned<Expr>>,
        attr: SmolStr,
        attr_span: Span,
        /// The module the label belongs to, `mod2` in `r.mod2::f1`, as in
        /// [`RecordField::qualifier`]. Empty for the current module's label, and
        /// always empty for a positional key.
        attr_qualifier: Vec<Spanned<SmolStr>>,
    },

    /// A backtick-introduced variant arm: `` `tag(payload) `` in a term,
    /// `` `tag{fields} `` in a type, and bare `` `tag `` for a tag that carries
    /// nothing.
    ///
    /// The backtick is what distinguishes a tag from a name, in every position:
    /// without it `some(1)` would be a [`Expr::Call`] to a function named
    /// `some`, and `` {some{Int}} `` a type application. Tags need no
    /// declaration — `cambra::ccl::Type::Variant` is structural, so
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
        /// The module the tag belongs to, `mod2` in `` mod2::`tag ``. Empty for
        /// the current module's tag (`docs/chl-spec.md`, "9.12 Field labels and
        /// tags belong to a module").
        tag_qualifier: Vec<Spanned<SmolStr>>,
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

    /// Polymorphic type: `forall (T, U <: B) V requires …`
    /// (`docs/chl-spec.md`, "Polymorphic type annotations").
    Forall {
        type_params: Vec<TypeParam>,
        body: Box<Spanned<Expr>>,
        requires: Vec<Spanned<Requirement>>,
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

    /// A block statement in value position: an `if`/`match` on the right of an
    /// assignment, or a one-line `match` inside a bracket.
    ///
    /// The block's value is its last statement's, by the same rule that gives a
    /// function body its value (`docs/chl-spec.md`, "4.5 `if` / `elif` /
    /// `else`"). The indented and one-line arm layouts differ in how an arm
    /// body is parsed, so both build the same statement here and lowering
    /// routes both through `lower_final_stmt`.
    ///
    /// **Invariant:** the statement is a [`Stmt::If`] or a [`Stmt::Match`].
    /// Lowering asserts it.
    Block(Box<Spanned<Stmt>>),

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

impl Expr {
    /// Whether this expression in type position reads as variant **arms**: a
    /// backticked tag, or a `|`-chain whose every leaf is one.
    ///
    /// `|` lexes as the logical-or operator, so a chain arrives as nested
    /// [`Expr::BinOp`] nodes. This is what tells a variant type from the tuple
    /// type it shares a bracket with, and the backtick is the whole test: the
    /// two readings never collide, because in *type* position there is no
    /// boolean to disjoin. So the arm count carries no syntactic weight —
    /// `` {`a} `` is a one-arm variant with no comma, while the one-element
    /// tuple type needs the `{T,}` that says so.
    ///
    /// Requiring *every* leaf to be a tag (rather than any) keeps a mixed
    /// `` {`a | Int} `` out of the variant path, so it fails as the tuple-type
    /// element it looks like rather than as a malformed arm.
    pub fn is_variant_arms(&self) -> bool {
        match self {
            Expr::VariantCtor { .. } => true,
            Expr::BinOp {
                left,
                op: BinOp::LogicalOr,
                right,
            } => left.node.is_variant_arms() && right.node.is_variant_arms(),
            _ => false,
        }
    }
}

/// A literal value.
#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    Int(i64),
    /// String literal with escapes already processed.
    String(String),
    Bool(bool),
}

/// A named field: `name=value` in an [`Expr::Record`] value, or `name: T` in
/// an [`Expr::BraceRecord`] record type.
#[derive(Debug, Clone, PartialEq)]
pub struct RecordField {
    pub name: SmolStr,
    pub name_span: Span,
    /// The module the label belongs to, `catalog` in `catalog::price=25`. Empty
    /// for the current module's label.
    pub qualifier: Vec<Spanned<SmolStr>>,
    pub value: Spanned<Expr>,
}

/// A name with a non-empty `::` qualifier, `cart::total` (an [`Expr::Qualified`]).
///
/// The qualifier's first segment may be `this`, which names the current module
/// (`docs/chl-spec.md`, "9.12 Field labels and tags belong to a module"). `this`
/// is a keyword, so no binder can take that spelling. The parser accepts it
/// wherever a qualifier stands; what each qualifier may name is a question for
/// name resolution.
#[derive(Debug, Clone, PartialEq)]
pub struct QualifiedName {
    pub qualifier: Vec<Spanned<SmolStr>>,
    pub name: Spanned<SmolStr>,
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
/// Notably absent vs. Python: `/` (true division), `%` (modulo), `>>` (right
/// shift). CHL's lowering does not implement these and the parser rejects them
/// at the syntactic level.
///
/// CHL reuses several Python tokens with different semantics: `&`, `|`, `^`
/// denote logical (not bitwise) and/or/xor. `++` denotes collection union
/// (CHL has no string-concatenation operator — `+` on strings handles that).
/// The variant names below reflect CHL's semantics rather than the source
/// token spellings.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    /// `^+` — addition whose result type records the sum. Same arithmetic as
    /// [`Add`](Self::Add), a different trait (`src/ccl/ops.rs`, `ArithmeticKind`).
    AddRefined,
    Sub,
    Mul,
    FloorDiv,
    /// `**` — exponentiation. Right-associative, and tighter than the unary minus
    /// on its left, so `-2 ** 2` is `-(2 ** 2)` (`docs/chl-spec.md`,
    /// "2.3 Expression precedence").
    Pow,
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
