//! Scalar primitives shared across the CCL pipeline: base types, literal
//! constants, the binary / unary operator kinds, the [`Builtin`] combinator
//! enum, projection keys, and the cross-phase [`TypeError`].

use std::fmt;

use crate::ccl::AggregateKind;

/// Primitive base types shared between the CCL type system and the interpreter.
///
/// Defined here (in `ccl`) and re-exported by the interpreter so that
/// `ccl` does not depend upward on `interpreter`. See `interpreter/types/`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BaseType {
    /// Signed 64-bit integer.
    Int,
    /// Unsigned 64-bit integer.
    UInt,
    /// Unicode string.
    String,
    /// Boolean value.
    Bool,
    /// The unit type (equivalent to Python `None`).
    Unit,
}

/// Errors about types that can be used by any phase of compilation
pub enum TypeError {
    /// Generic type error
    Unsupported(String),
}

/// A literal constant value.
///
/// Covers the subset of [`crate::interpreter::Value`] that can appear as
/// compile-time constants.
///
/// Named `Lit` to avoid shadowing `crate::interpreter::Literal`, which is
/// an unrelated operator struct.
#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    /// An integer constant.
    Int(i64),
    /// A string constant.
    String(String),
    /// A boolean constant.
    Bool(bool),
    /// The unit (null/None) constant.
    Unit,
}

/// Arithmetic sub-operations for [`BinOpKind::Arithmetic`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArithmeticKind {
    /// Integer addition (`+`).
    Add,
    /// Integer subtraction (`-`).
    Sub,
    /// Integer multiplication (`*`).
    Mul,
    /// Floor division (`//`).
    FloorDiv,
}

/// Comparison sub-operations for [`BinOpKind::Compare`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CompareKind {
    /// Equality (`==`).
    Equals,
    /// Inequality (`!=`).
    NotEquals,
    /// Less than (`<`).
    Less,
    /// Less than or equal (`<=`).
    LessOrEq,
    /// Greater than (`>`).
    Greater,
    /// Greater than or equal (`>=`).
    GreaterOrEq,
}

/// Boolean logic sub-operations for [`BinOpKind::BoolLogic`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LogicKind {
    /// Logical AND.
    And,
    /// Logical NAND.
    Nand,
    /// Logical OR.
    Or,
    /// Logical NOR.
    Nor,
    /// Logical XOR.
    Xor,
    /// Logical XNOR.
    Xnor,
}

/// Binary operation kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOpKind {
    /// An arithmetic operation (add, sub, mul, floor-div).
    Arithmetic(ArithmeticKind),
    /// A boolean logic operation (and, or, xor, …).
    BoolLogic(LogicKind),
    /// String concatenation (`+` on strings).
    Concat,
    /// A comparison that produces a boolean result.
    Compare(CompareKind),
}

impl BinOpKind {
    /// Returns the canonical infix symbol for this operator (e.g. `"+"`, `"and"`, `"<="`).
    ///
    /// Used by formatters such as the symbolic printer and the pretty-tree
    /// printer so that the mapping lives once on the type rather than being
    /// duplicated in each formatter.
    pub fn sym(&self) -> &'static str {
        match self {
            Self::Arithmetic(ArithmeticKind::Add) => "+",
            Self::Arithmetic(ArithmeticKind::Sub) => "-",
            Self::Arithmetic(ArithmeticKind::Mul) => "*",
            Self::Arithmetic(ArithmeticKind::FloorDiv) => "//",
            Self::Concat => "++",
            Self::Compare(CompareKind::Less) => "<",
            Self::Compare(CompareKind::LessOrEq) => "<=",
            Self::Compare(CompareKind::Greater) => ">",
            Self::Compare(CompareKind::GreaterOrEq) => ">=",
            Self::Compare(CompareKind::Equals) => "==",
            Self::Compare(CompareKind::NotEquals) => "!=",
            Self::BoolLogic(LogicKind::And) => "and",
            Self::BoolLogic(LogicKind::Nand) => "nand",
            Self::BoolLogic(LogicKind::Or) => "or",
            Self::BoolLogic(LogicKind::Nor) => "nor",
            Self::BoolLogic(LogicKind::Xor) => "xor",
            Self::BoolLogic(LogicKind::Xnor) => "xnor",
        }
    }

    /// Returns the function-style name used when this operator is referenced as
    /// a built-in primitive (e.g. `"add"`, `"lt"`, `"concat"`).
    ///
    /// Lambda elimination desugars `a op b` into
    /// `Apply(Tuple([a, b]), Builtin(BinOp(op)))`; this is the printable name
    /// of that built-in, used by [`Builtin::name`] and by the symbolic /
    /// pretty printers.
    pub fn fn_name(&self) -> &'static str {
        match self {
            Self::Arithmetic(ArithmeticKind::Add) => "add",
            Self::Arithmetic(ArithmeticKind::Sub) => "sub",
            Self::Arithmetic(ArithmeticKind::Mul) => "mul",
            Self::Arithmetic(ArithmeticKind::FloorDiv) => "floor_div",
            Self::Concat => "concat",
            Self::Compare(CompareKind::Equals) => "eq",
            Self::Compare(CompareKind::NotEquals) => "neq",
            Self::Compare(CompareKind::Less) => "lt",
            Self::Compare(CompareKind::LessOrEq) => "le",
            Self::Compare(CompareKind::Greater) => "gt",
            Self::Compare(CompareKind::GreaterOrEq) => "ge",
            Self::BoolLogic(LogicKind::And) => "and",
            Self::BoolLogic(LogicKind::Nand) => "nand",
            Self::BoolLogic(LogicKind::Or) => "or",
            Self::BoolLogic(LogicKind::Nor) => "nor",
            Self::BoolLogic(LogicKind::Xor) => "xor",
            Self::BoolLogic(LogicKind::Xnor) => "xnor",
        }
    }
}

/// Unary operation kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryOpKind {
    /// Arithmetic negation (`-x`).
    Neg,
    /// Boolean negation (`not x`).
    Not,
}

/// Built-in primitive functions used by the lowered point-free CCL.
///
/// These are the named combinators that earlier passes used to refer to via
/// [`TypedExprNode::Var`](crate::ccl::TypedExprNode::Var) with hard-coded magic
/// strings.  Representing them as a dedicated enum makes it cheap and type-safe
/// for downstream passes (simplify, planning, operator_conversion, …) to
/// recognise primitives without string matching.
///
/// Built-in nodes are produced by [`crate::ccl::lambda_elim`] and
/// [`crate::ccl::planning`]; they never appear in source-lowered CCL prior
/// to lambda elimination, so type inference does not need to reason about
/// them — types are stamped onto the surrounding
/// [`TypedExpr`](crate::ccl::TypedExpr) at the point each built-in is emitted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Builtin {
    // Categorical combinators (introduced by lambda elimination).
    /// `id : A → A` — identity morphism.
    Id,
    /// `curry : ((A, B) → C) → (A → (B → C))`.
    Curry,
    /// `const : A → (B → A)` — lift a value to a constant function.
    Const,
    /// `zip : ((A → B), (A → C)) → (A → (B, C))` — point-free product/fanout.
    Zip,
    /// `apply : (B, B → C) → C` — function application as a morphism.
    Apply,
    /// `map : (B → C) → ((A → B) → (A → C))` — post-composition.
    Map,
    /// `map_domain : (A → B) → (A → A)` — domain-to-domain identity stream.
    MapDomain,
    /// `compose : ((A → B), (B → C)) → (A → C)` — composition as a morphism.
    Compose,
    /// `converse : (A → K) → (K → (A → A))` — group-by-key combinator.
    Converse,
    /// `uncurry : (A → (B → C)) → ((A, B) → C)`.
    Uncurry,
    /// `restrict : (D ⇒ Bool) ⇒ (D ⇒ T) ⇒ ({d: D | p(d)} ⇒ T)` —
    /// mid-chain filter step.
    ///
    /// `restrict` is a *codomain-parametric function transformer*: it
    /// narrows the domain of an upstream value-producer `D ⇒ T` to the
    /// subset satisfying `p`, passing the values `T` through unchanged.
    /// So the refinement lands on the **domain** and `T` is preserved on
    /// the codomain — not the unsound `D ⇒ {d: D | p(d)}` (which would
    /// claim every `d : D` satisfies `p`).  The transformer
    /// `Apply(p, Restrict)` is therefore **applied to** its upstream
    /// (`Apply(upstream, Apply(p, Restrict))`), not composed with it —
    /// its domain is a function type, so it cannot be a morphism in a CCC
    /// `Compose` chain.
    ///
    /// Op-conversion compiles the application via the generic
    /// applied-combinator arm: `upstream` is converted with `input=None`,
    /// then this `Restrict` arm consumes it as `input=Some(_)`, compiles
    /// the predicate against it, and wraps it in a `Restrict` tile.
    /// Emitted by [`crate::ccl::planning`] for every downstream filter —
    /// the outer layers of a nested-refinement iteration site, the
    /// residual predicate of `JoinPlan::Loop`, and the residual predicate
    /// of `JoinPlan::Hash`.  Chain-head iteration is the separate
    /// `Iterate` variant.  See [`crate::ccl::ccl_utils::make_restrict`].
    Restrict,
    /// `iterate : (D ⇒ Bool) ⇒ ({d: D | p(d)} ⇒ {d: D | p(d)})` —
    /// chain-head iteration source.
    ///
    /// `Apply(p, Iterate)` requires `input=None`; op-conversion compiles
    /// it to an `IterateExtent` over `D` (plus a `Restrict` filter when
    /// `p` is non-trivial).  Emitted by [`crate::ccl::planning`] at the
    /// head of every iteration site: aggregate arguments, top-level
    /// program results, sink-bound fields, mutation-loop sources, and
    /// `JoinPlan::Loop` / `JoinPlan::Hash` arm leaves.  Mid-chain
    /// filtering is the separate `Restrict` variant.
    ///
    /// Planning is the sole emitter; lambda elimination never produces
    /// `Iterate`.  The trivially-true predicate `Apply(Lit::Bool(true), Const)`
    /// marks unrefined sites — op-conversion recognises it and emits
    /// just `IterateExtent` (no filter).
    Iterate,
    /// `permute_domain` — reorder positions in a tuple-typed domain.
    PermuteDomain,
    /// `flatten_domain` — flatten selected nested-tuple positions in a domain.
    FlattenDomain,

    /// A binary scalar operation lifted to a function on a 2-tuple
    /// (`(a, b) ▷ BinOp(op)`).
    ///
    /// Covers all arithmetic / string / comparison / boolean-logic operators;
    /// the inner [`BinOpKind`] is the single source of truth for which one.
    /// Lambda elimination desugars `a op b` into this form.
    BinOp(BinOpKind),

    // Unary scalar ops.
    /// `neg : Int → Int`.
    Neg,
    /// `not_fn : Bool → Bool` — boolean negation as a morphism.
    NotFn,

    // Aggregations (codomain of a function-typed input → scalar).
    /// `sum`.
    Sum,
    /// `max`.
    Max,
    /// `last_or_default : Tuple(Fun(D, T), T) → T` — extract the
    /// codomain value at the final position of an iteration stream, or
    /// fall back to the default scalar when the stream's domain is
    /// empty.  Compiles directly to the `ExtractLast` tile operator
    /// (which receives both the stream and the default operator); not
    /// an aggregate fold (no identity element), so it does not
    /// participate in `AggregateKind`.
    ///
    /// Used by `lower_mutation_loop` to expose the scalar final
    /// accumulator of a Record-bodied loop, whose external type is
    /// `Fun(D, Record({step, to_<defer>*}))`: the after-loop scalar acc is
    /// `(acc_stream ▷ Proj("step"), init) ▷ FinalOrDefault`.  The
    /// default is the pre-loop accumulator binding, so an
    /// empty-source loop (`for i in []: x += 1; x`) yields `init`
    /// rather than panicking or returning empty.
    ///
    /// TODO: Make the ordering requirement on this explicit.  Right now
    /// all of our types can be implicitly ordered, but that might not
    /// hold forever, and the implicit ordering might be wrong.  Tracked
    /// jointly with the `.rev().find(…)` in `ExtractLastProducer` —
    /// both assume the source's last position by emission order, not
    /// by sorted domain value.
    FinalOrDefault,

    /// `get_prev_seq : Tuple(Fun(I, V), I, V) → V` — the history value at
    /// the *predecessor* of the given position, or the default at the first
    /// position.
    ///
    /// Applied as a tupled argument, same convention as [`Self::FinalOrDefault`]:
    /// `Apply(Tuple([history, position, default]), Builtin(GetPrevSeq))`.
    /// The polymorphic scheme `∀ι ν. ((ι ⇒ ν), ι, ν) ⇒ ν` lives in
    /// [`crate::ccl::infer::OperatorSchemes`] (shared variables
    /// across positions, like `FinalOrDefault`).
    ///
    /// This is the **guard accessor** for induction-domain recursion in a
    /// [`crate::ccl::TypedExprNode::LetRec`]: a binding whose self-reference
    /// is consumed only as the history argument of `get_prev_seq` depends
    /// only on strictly earlier positions, which is what makes the group
    /// well-founded (see `src/ccl/design/mutability.md`, "The model" /
    /// "New builtins", and [`crate::ccl::letrec::check_letrec_causal`]).
    ///
    /// Op-conversion never compiles this builtin directly: letrec pattern
    /// recognition consumes it (the causal self-cycle becomes the `Recurse`
    /// engine), so its op-conversion arm is a deliberate error, like
    /// `LetRec`'s.
    GetPrevSeq,

    /// `get_prev_txn : Tuple(Fun(Txn, {time: Txn, write: V}), Txn, V) → V` —
    /// the write carried by the latest commit in the history stream *strictly
    /// before* the given time, or the default if none.
    ///
    /// Applied as a tupled argument, same convention as [`Self::GetPrevSeq`]:
    /// `Apply(Tuple([history, time, default]), Builtin(GetPrevTxn))`. Its
    /// polymorphic scheme `∀ν. ((Txn ⇒ {time: Txn, write: ν}), Txn, ν) ⇒ ν`
    /// lives in [`crate::ccl::infer::OperatorSchemes`].
    ///
    /// This is the **transaction-domain guard accessor** for a
    /// [`crate::ccl::TypedExprNode::LetRec`]: a binding whose reference to a
    /// commit-record binding is consumed only as the history argument depends
    /// only on strictly earlier commit times, which is what makes the
    /// `store ↔ commits` cycle well-founded (see
    /// `src/ccl/design/mutability.md`, "New builtins", and
    /// [`crate::ccl::letrec::check_letrec_causal`]).
    ///
    /// Op-conversion never compiles this builtin directly — like
    /// [`Self::GetPrevSeq`], letrec pattern recognition (the commit-operator
    /// complex) consumes it, so its op-conversion arm is a deliberate error.
    GetPrevTxn,

    /// `begin_<site> : 𝐼 ⇒ Txn` — the commit-time **oracle** for one `with
    /// begin():` site: where the site's iteration `𝑟` lands in the global
    /// commit order. Applied as `begin(r)` (`Apply(Var(r), Builtin(BeginTxn))`)
    /// inside a commit-record binding, it produces the transaction's commit time
    /// `t`, at which that writer's store snapshots are read (`store(t)`).
    ///
    /// Minted by [`crate::ccl::transact_phase`] — one application per site,
    /// *after* inference, so it carries no scheme in
    /// [`crate::ccl::infer::OperatorSchemes`]; its type `𝐼 ⇒ Txn` is
    /// stamped on the node at emission and the post-phase CHECK-mode `typecheck`
    /// (which trusts a builtin's recorded type) validates it directly. Opaque
    /// and consumed by [`crate::ccl::planning::plan_loops`], which reads the
    /// writer's source and body off the commit-record binding and discards the
    /// `begin`/`store(t)` plumbing. Like [`Self::GetPrevSeq`] /
    /// [`Self::GetPrevTxn`] it never reaches op-conversion, so its op-conversion
    /// arm is a deliberate error. A single shared builtin serves every site: the
    /// site identity recognition needs (the source stream + iteration domain)
    /// lives in the commit-record binding, not in the oracle.
    BeginTxn,

    /// `collection_union : (Fun(A, B), Fun(C, D)) → Fun(Union(A, C), dedup(B, D))`
    ///
    /// Merges two function-typed (collection) values into a single collection whose
    /// domain is the discriminated union of both input domains and whose codomain is
    /// the deduplicated union of both input codomains.  Lowered from Python `a @ b`.
    CollectionUnion,

    /// `as_of : Tuple(Fun(B, _), Fun(Txn, V)) → Fun(B, V)` — the **as-of
    /// (temporal) join**, the live cross-endpoint read. Applied as a tupled
    /// argument `Apply(Tuple([trigger, source]), Builtin(AsOf))`: for each
    /// `trigger` (request-loop) position, latch `source`'s (a transactional
    /// store's running render, `Fun(Txn, V)`) latest-decided value as of that
    /// position. The reply is indexed by the *trigger* (the enclosing request
    /// loop), not the commit clock — an outer-indexed read.
    ///
    /// Born in [`crate::ccl::transact_phase`]'s `rewrite_live_reads`, run
    /// **pre-lambda-elim** (after `channelize`): it recognizes a read-only
    /// reply — a chain of live-store reads `let k₁ = last_or_default((store.f₁, _))
    /// in … in trigger ≫ (λ r → e)` — and rewrites it, dropping the never-resolving
    /// `last_or_default`s. Reading **one** register → `as_of((trigger, store.f)) ≫
    /// (λ k → e)`; reading **several** → `as_of((trigger, store)) ≫ (λ snap → e[kᵢ
    /// ↦ snap.fᵢ])`, a single snapshot record folded at one commit frontier so the
    /// registers are read atomically (§I-c). Running before lambda elimination
    /// keeps a computed reply (`e = k + 1`) a lambda the elim pass point-frees,
    /// rather than a point-free `const` that could only be broadcast. Compiles to
    /// the [`crate::interpreter::commit_operator`] `AsOf` tile operator (scalar- or
    /// record-valued). It carries its **own recorded type** (no inference scheme):
    /// op-conversion and every post-phase `typecheck` read `.ty` directly, and
    /// planning treats it as an iteration-bearing source (it stages the trigger
    /// inside its tuple rather than prepending an `iterate`).
    AsOf,
}

impl Builtin {
    /// Stable, source-style display name for this built-in, used by
    /// [`crate::ccl::symbolic`] and the pretty-printer when rendering
    /// applied primitives.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Id => "id",
            Self::Curry => "curry",
            Self::Const => "const",
            Self::Zip => "zip",
            Self::Apply => "apply",
            Self::Map => "map",
            Self::MapDomain => "map_domain",
            Self::Compose => "compose",
            Self::Converse => "converse",
            Self::Uncurry => "uncurry",
            Self::Restrict => "restrict",
            Self::Iterate => "iterate",
            Self::PermuteDomain => "permute_domain",
            Self::FlattenDomain => "flatten_domain",
            Self::BinOp(op) => op.fn_name(),
            Self::Neg => "neg",
            Self::NotFn => "not_fn",
            Self::Sum => "sum",
            Self::Max => "max",
            Self::FinalOrDefault => "final_or_default",
            Self::GetPrevSeq => "get_prev_seq",
            Self::GetPrevTxn => "get_prev_txn",
            Self::BeginTxn => "begin",
            Self::CollectionUnion => "collection_union",
            Self::AsOf => "as_of",
        }
    }

    /// Built-in name for a unary [`UnaryOpKind`].
    pub fn for_unaryop(op: UnaryOpKind) -> Self {
        match op {
            UnaryOpKind::Neg => Self::Neg,
            UnaryOpKind::Not => Self::NotFn,
        }
    }

    /// Built-in name for an [`AggregateKind`].
    pub fn for_aggregate(kind: AggregateKind) -> Self {
        match kind {
            AggregateKind::Sum => Self::Sum,
            AggregateKind::Max => Self::Max,
        }
    }

    /// Op-conversion's `Apply { argument, function: Builtin(self) }` arm
    /// compiles `argument` (or, for tuple-shaped arguments, its
    /// iteration-source sub-parts) with `input=None`, treating it as a
    /// function-typed iteration source.  This is op-conversion's
    /// "input-internalising" group.
    ///
    /// Consulted by two helpers in [`crate::ccl::planning`]:
    ///
    /// - `is_internalising_builtin_function` — at `Apply { function }`
    ///   positions during the iteration-site walk, decides which
    ///   builtins' arguments to wrap with `iterate(_)`.  `CollectionUnion`
    ///   and `FinalOrDefault` are in this list because they self-iterate
    ///   from sub-parts of their tuple argument, but the walk's
    ///   per-shape match arms handle them before the catch-all that
    ///   consults this metho — so the per-element wrapping fires first
    ///   and the catch-all isd never reached for them.
    /// - `is_iteration_bearing` — at chain heads, decides which builtins
    ///   already provide their own iteration (and so should not be
    ///   wrapped with another `iterate(_)`).  Scalar-result builtins
    ///   (`Sum`, `Max`, `FinalOrDefault`) are in the list too; the
    ///   caller's `expr.ty.domain()` check filters them out at chain
    ///   heads independently.
    ///
    /// `Iterate` is NOT in this list — it is an iteration source, but
    /// it does not iterate *from* its argument (the argument is the
    /// predicate, threaded with `input=Some`).  `is_iteration_bearing`
    /// handles `Iterate` separately.  `Restrict` is also excluded: it
    /// threads its input through to the predicate (`input=Some`),
    /// neither iterating from arg nor providing its own iteration.
    ///
    /// Keep in sync with the corresponding arms in operator_conversion.rs.
    pub fn iterates_arg(self) -> bool {
        matches!(
            self,
            Self::Sum
                | Self::Max
                | Self::Converse
                | Self::MapDomain
                | Self::Uncurry
                | Self::PermuteDomain
                | Self::FlattenDomain
                | Self::CollectionUnion
                // `GetPrevSeq`/`GetPrevTxn` share `FinalOrDefault`'s
                // classification (a scalar-result builtin over a tuple whose
                // stream sub-part self-iterates), but op-conversion never sees
                // them: letrec pattern recognition consumes them first, and the
                // op-conv arm errors deliberately (see the variant docs).
                | Self::FinalOrDefault
                | Self::GetPrevSeq
                | Self::GetPrevTxn
        )
    }
}

impl From<BinOpKind> for Builtin {
    fn from(op: BinOpKind) -> Self {
        Self::BinOp(op)
    }
}

impl fmt::Display for Builtin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// The key identifying which field a [`TypedExprNode::Proj`](crate::ccl::TypedExprNode::Proj) projects.
///
/// Supports both positional tuple fields (`.0`, `.1`, …) and named record
/// fields (`.name`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProjKey {
    /// Integer-indexed tuple projection: `.0`, `.1`, …
    Index(usize),
    /// Named record-field projection: `.fieldname`.
    Field(String),
}
