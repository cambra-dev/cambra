//! The CCL expression AST: [`TypedExpr`] / [`TypedExprNode`], the
//! [`TypedBinding`] binding-site struct, the structural traversal helpers, and
//! the [`Branch`] / [`Pattern`] / [`TransactKey`] / [`TransactWriter`] support
//! types.

use crate::ccl::{AggregateKind, BinOpKind, Builtin, Lit, Name, ProjKey, Type, UnaryOpKind};

/// The `commit` field of a [`TransactWriter`] decision record — the boolean
/// grant/deny gating the whole (atomic) write set. Always `true` for the
/// induction (`mut`-loop) case.
pub const F_COMMIT: &str = "commit";
/// The `writes` field of a [`TransactWriter`] decision record — the positional
/// tuple of proposed per-key new values (`writes.i` for `write_keys[i]`), one
/// element even for a single-key write set.
pub const F_WRITES: &str = "writes";

/// A typed binding site: a named variable together with its type.
///
/// Used in [`TypedExprNode::Lambda`] and [`TypedExprNode::Let`] to carry
/// both the inferred type and any user-written annotation at each binding site.
///
/// `ty` starts as [`Type::Hole`] (lowering placeholder) and is converted to a
/// registered [`Type::Infer`] variable at inference entry, then filled in with
/// the concrete type by [`crate::ccl::infer::infer`].
/// `user_annotation` is set at construction time by lowering when the source
/// Python carries an explicit type cast; the inference pass checks that the
/// inferred type is compatible with it.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedBinding {
    /// The bound variable name. Carries the binder's identity (`uid`) under
    /// the Barendregt convention; see [`Name`].
    pub name: Name,
    /// The variable's type, filled in by type inference.
    ///
    /// Starts as [`Type::Hole`] (lowering placeholder); converted to [`Type::Infer`]
    /// at inference entry and written to a concrete type by [`crate::ccl::infer::infer`].
    pub ty: Type,
    /// User-written type annotation, if any.
    ///
    /// Set by lowering when the source Python carries an explicit type annotation
    /// (e.g. `x: int = expr`). The inference pass checks that the inferred type is
    /// compatible with it and raises [`crate::ccl::infer::InferError::AnnotationMismatch`] on conflict.
    pub user_annotation: Option<Type>,
}

impl TypedBinding {
    /// Create an unannotated binding with a [`Type::Hole`] placeholder.
    ///
    /// Use this at lowering time when no type is yet known. The inference pass
    /// converts the `Hole` to a registered inference variable before type-checking.
    pub fn new_unannotated(name: impl Into<Name>) -> Self {
        TypedBinding {
            name: name.into(),
            ty: Type::Hole,
            user_annotation: None,
        }
    }

    /// Create an annotated binding with a [`Type::Hole`] placeholder and a user annotation.
    ///
    /// Use this at lowering time when the source Python carries an explicit type annotation
    /// (e.g. `x: int = expr`). `ty` is still [`Type::Hole`] — the inference pass fills it in.
    pub fn new_annotated(name: impl Into<Name>, annotation: Type) -> Self {
        TypedBinding {
            name: name.into(),
            ty: Type::Hole,
            user_annotation: Some(annotation),
        }
    }
}

/// The expression kind enum for CCL expressions.
///
/// This is the central type of the CCL AST node hierarchy. Every program is a [`TypedExpr`]
/// whose `node` field holds one of these variants.
///
/// Application is curried: `f(x, y)` is `Apply(Apply(f, x), y)`. Compound
/// expressions may appear inline as arguments — [`TypedExprNode::Let`] bindings are
/// optional (unlike strict ANF).
///
/// # Purity invariant
///
/// **Every variant must denote a pure value.**  No variant may carry runtime
/// behaviour that is executed by the CCL pipeline (type inference, lambda
/// elimination, join planning, simplification).  Effects such as I/O or sink
/// dispatch are modelled as data-source/sink registrations in
/// [`crate::ccl::lower::LoweringContext`] and assembled at the program boundary
/// in [`crate::ccl::context::compile_program`], not as AST nodes.
///
/// If you are considering a variant that "does something" rather than
/// representing a value to be computed, model the effect at the boundary
/// instead.  See `src/ccl/CLAUDE.md` for the full rationale.
#[derive(Debug, Clone, PartialEq)]
pub enum TypedExprNode {
    /// A literal constant.
    Lit(Lit),

    /// A variable reference by name.
    Var(Name),

    /// A reference to a built-in primitive function.
    ///
    /// Introduced by [`crate::ccl::lambda_elim`] (and [`crate::ccl::planning`])
    /// to refer to combinators such as `id`, `zip`, `curry`, `apply`, the
    /// arithmetic / comparison / logic operators, the unary operators, and the
    /// aggregations.  Replaces the earlier convention of using
    /// [`TypedExprNode::Var`] with magic strings.  The wrapping
    /// [`TypedExpr::ty`] holds the (typically polymorphic, instantiated at the
    /// emission site) function type of the primitive — analogous to how
    /// `Var(name)` carried its type before.
    Builtin(Builtin),

    /// Curried function application: `f(x)` written `x ▷ f` in pipeline style.
    ///
    /// Multi-argument calls nest left: `f(x)(y)` becomes
    /// `Apply(Apply(Var("f"), x), y)`.
    ///
    /// Note: `crate::interpreter::Apply` is an unrelated operator struct.
    Apply {
        /// The function being applied.
        function: Box<TypedExpr>,
        /// The argument passed to the function.
        argument: Box<TypedExpr>,
    },

    /// Pure type-level assertion that re-views `value` under `target`.
    ///
    /// `cast(value, target)` does not change `value`'s runtime data — it
    /// asserts that `value` may be viewed at `target`.  Today the only
    /// `target` shape lowering emits is `Fun(Refinement(_, _), _)`: a
    /// function type whose domain carries a refinement predicate, so the
    /// cast attaches a refinement to a function's domain.  Lowering emits
    /// it for list-comprehension filters, for-loop `if`-guards, and
    /// `groupby` (see [`crate::ccl::ccl_utils::make_cast`]).
    ///
    /// `Cast` is an **upcast**: its whole typing rule is the single subtype
    /// obligation `value_ty <: target`.  For the domain refinement lowering
    /// emits, that holds by contravariance — `(𝐷 ⇒ 𝑉) <: ({𝐷 | 𝑝} ⇒ 𝑉)`
    /// because `{𝐷 | 𝑝} <: 𝐷` — so viewing an unrefined-domain collection
    /// function at a refined-domain type is sound.  The
    /// refinement-aware solver ([`crate::ccl::infer::solver::constrain_subtype`])
    /// flows the witness onto the fresh target-domain variable, *stacking* it
    /// onto any witnesses the value already carries, so nested casts compose
    /// (nested list comprehensions).  `target`'s predicate is inferred by the
    /// same `emit_annotation_predicates` / `coalesce_type_predicates` path as
    /// any refinement-bearing type.  A *covariant* refinement (e.g. casting
    /// `Int` to `{Int | p}`) correctly fails the subtype check — acquiring a
    /// value-level refinement is a runtime/SMT-checked narrowing, not an
    /// upcast.
    ///
    /// `target` is the lowering-time *specification* (its domain/codomain
    /// are typically `Type::Hole`, carrying only the refinement); the
    /// resolved cast type lands on [`TypedExpr::ty`] after inference — the
    /// same split as [`TypedExpr::user_annotation`] vs `ty` elsewhere.
    ///
    /// `Cast` denotes a pure value (it re-views another value), so it
    /// satisfies the CCL purity invariant.  At runtime it is a no-op:
    /// op-conversion compiles `value` and discards the wrapper, because the
    /// refinement on the type has already been consumed by planning.
    ///
    /// TODO: the name `Cast` is more general than the current
    /// implementation, which only honours `Fun(Refinement(_, _), _)`
    /// targets.  Either generalize to the full `𝑈 ⇒ 𝑇` semantics or
    /// rename narrower (`Refine`, `AssertDomain`).  See
    /// `src/ccl/design/type-inference.md` for the migration plan.
    Cast {
        /// The value being re-viewed under `target`.
        value: Box<TypedExpr>,
        /// The target type to view `value` at — a `Fun(Refinement(_, _), _)`
        /// carrying the domain refinement to acquire.
        target: Type,
    },

    /// A binary operation.
    BinOp {
        /// The left-hand operand.
        left: Box<TypedExpr>,
        /// The operation kind.
        op: BinOpKind,
        /// The right-hand operand.
        right: Box<TypedExpr>,
    },

    /// A unary operation.
    UnaryOp(UnaryOpKind, Box<TypedExpr>),

    /// A lambda abstraction.
    ///
    /// The bound parameter and its type are carried by a [`TypedBinding`].
    /// `param.ty` starts as [`Type::Hole`] on unannotated lambdas from
    /// lowering; [`crate::ccl::infer::infer`] (via Cambra's inference algorithm) fills it with the
    /// inferred concrete type or a `Type::Infer` variable before
    /// compilation.
    ///
    /// Note: `crate::interpreter::Lambda` is an unrelated operator struct.
    Lambda {
        /// The bound parameter, with its name and inferred/annotated type.
        param: TypedBinding,
        /// The lambda body.
        body: Box<TypedExpr>,
    },

    /// An aggregation over a function (including, and usually being, a collection)
    /// Computes the aggregate over the codomain of the function, which in the case of
    /// a collection is the elements of the collection.
    Aggregate {
        /// Expression being aggregated over.  Must be of type `Fun`
        input: Box<TypedExpr>,
        /// The type of aggregation to do (e.g. sum, max)
        kind: AggregateKind,
    },

    /// A let binding: `let name = value in body`.
    ///
    /// Binds `name` to `value` within `body`. Unlike strict ANF, `value`
    /// may be any `TypedExpr`, not only an atomic term.
    Let {
        /// The bound name and its type.
        ///
        /// `binding.ty` mirrors `bound_expr.ty` after inference and is filled
        /// in by [`crate::ccl::infer::infer`]. `binding.user_annotation` carries any
        /// user-written type annotation on the binding site (e.g. `x: Int = expr`),
        /// which inference checks for compatibility with the inferred expression type.
        binding: TypedBinding,
        /// The expression being bound.
        bound_expr: Box<TypedExpr>,
        /// The expression in which `binding.name` is in scope.
        body: Box<TypedExpr>,
    },

    /// A list literal: `[e0, e1, ...]`.
    ///
    /// Represents Python list syntax directly in the CCL tree. Elements may be
    /// arbitrary expressions (not restricted to [`Lit`]).
    ///
    /// Distinct from [`TypedExprNode::Tuple`] (unnamed product type) and from the
    /// function-encoding of lists used at the operator-graph level.
    List(Vec<TypedExpr>),

    /// Multi-way conditional branching on boolean guards.
    ///
    /// Multi-way dispatch — the single construct for both **logical**
    /// (guard-based) and **structural** (variant-tag) branching, and for
    /// combinations of the two.
    ///
    /// Each [`Branch`] carries an optional structural [`Pattern`] (match a
    /// variant tag of `scrutinee`, binding its payload) and an optional
    /// boolean `guard`. Branches are evaluated top-to-bottom; the first
    /// whose pattern matches *and* whose guard is `true` wins. A branch may
    /// have both a pattern and a guard — that is "match on structure and
    /// logic at the same time".
    ///
    /// - **Pure `if`/`elif`/`else`:** `scrutinee` is `None` and every branch
    ///   is guard-only (`pattern: None`). Guards are constrained to
    ///   [`Type::Base`]`(`[`BaseType::Bool`](crate::ccl::BaseType::Bool)`)`.
    /// - **Pattern match:** `scrutinee` is `Some(_)`; each pattern branch
    ///   constrains the scrutinee to a [`Type::Variant`] whose tags are the
    ///   branch tags, binding each payload at the per-tag narrowed type.
    ///
    /// NOTE: All branch bodies must currently infer the **same** type.
    /// Mismatched body types are a hard
    /// [`crate::ccl::infer::InferError::TypeMismatch`] rather than producing
    /// a sum type ([`Type::Variant`]).
    Case {
        /// Optional scrutinee whose variant tag the structural branches
        /// match. `None` for pure guard-based dispatch (the classic
        /// `if`/`elif` chain).
        scrutinee: Option<Box<TypedExpr>>,
        /// Ordered list of branches.
        branches: Vec<Branch>,
    },

    /// Tagged variant constructor: `.Tag(payload)`.
    ///
    /// Produces a [`Type::Variant`] containing a single tag whose payload type
    /// is inferred from `payload`. Width-subtyping then lets the resulting
    /// singleton variant flow into any consumer expecting a superset of tags.
    VariantCtor {
        /// Tag name; arbitrary identifier.
        tag: String,
        /// Payload expression.
        payload: Box<TypedExpr>,
    },

    /// A mutable store: a set of scalar-register **keys** sharing one
    /// sequencing domain, driven by a **writer** that reads the shared store and
    /// proposes per-position writes.
    ///
    /// The **domain-parameterized recurrence carrier**, born in
    /// [`crate::ccl::letrec_phase::recognize`] and consumed at operator
    /// conversion. It denotes a pure value — the store **record** `{key:
    /// ⟦key⟧}`, each field a key's history `Fun(domain, V)` — so a variable
    /// read is the record projection `__store.key` (an `Apply` of `Proj(field)`
    /// to the `__store` binder). Serialization and the store↔writer cycle are
    /// the *operator's* runtime behaviour (a cyclic `FanOut`), not the node's
    /// denotation — exactly as `Recurse` realizes the recurrence.
    ///
    /// Op-conversion dispatches on [`domain`](Self::Transact::domain): a
    /// concrete iteration extent → the sequential `Recurse` (the induction case
    /// — one always-commit writer over a `mut` loop). This is the only shape the
    /// pipeline produces today; the node keeps its multi-writer / general-domain
    /// structure so a concurrent commit engine can be reintroduced on it.
    Transact {
        /// The store's keys — one per scalar register sharing this store's
        /// sequencing domain. Each carries its position-0 `init` (the seed,
        /// evaluated once outside every writer's parameter scope). The node
        /// denotes the store **record** `{key.field_key(): Fun(domain, V)}`; a
        /// variable read is a projection `__store.key`. A single-key store is
        /// the one-accumulator case.
        keys: Vec<TransactKey>,
        /// The writers, in declaration order. Each reads/writes a footprint of
        /// keys (its read-set / write-set) and proposes a per-position decision
        /// record. An induction-domain store has exactly one writer (a `mut`
        /// loop, whose footprint is all its accumulators).
        writers: Vec<TransactWriter>,
        /// The store's **sequencing domain** — the index of every key's history
        /// `Fun(domain, V)`. A concrete iteration extent for a `mut`
        /// accumulator (the loop's induction domain). Op-conversion dispatches
        /// the engine on it.
        domain: Type,
    },

    /// A mutually recursive definition group:
    /// `letrec b₁ = e₁; …; bₙ = eₙ in body`.
    ///
    /// Every binding's name is in scope in **every** binding's body and in
    /// `body` — mutual recursion.  Well-formedness requires the recursion to
    /// be *guarded*: on every cycle of the group's reference graph at least
    /// one reference must go through a "previous value" accessor
    /// ([`Builtin::GetPrevSeq`]), so values at any position of the sequencing
    /// domain depend only on strictly earlier positions.
    /// [`crate::ccl::letrec::check_letrec_guarded`] enforces this; see
    /// `src/ccl/design/mutability.md` ("The model" / "`LetRec`").
    ///
    /// This is the general node for loops and future recursive definitions: the
    /// unified phase (design doc, "The unified phase") rewrites every mutable
    /// variable's history and feed output into one letrec, and operator
    /// conversion *recognizes patterns* in the group (a `get_prev_seq`-guarded
    /// self-cycle is a fold) to pick the engine. `letrec_phase` emits it for
    /// every mutation loop as a guarded group, then `letrec_phase::recognize`
    /// lowers every recognized group onto the domain-parameterized
    /// [`Transact`](Self::Transact) carrier before `desugar_defers`, so a
    /// `LetRec` does not survive to the later passes — those that would need
    /// pattern knowledge it doesn't carry treat a surviving group as unreachable
    /// rather than guessing.
    ///
    /// The node denotes a pure value (the unique solution of the guarded
    /// group, by induction along the domain order), so it satisfies the CCL
    /// purity invariant.
    LetRec {
        /// The mutually recursive definition group. Every binding's name is
        /// in scope in every binding's body (and in `body`). Each binding
        /// carries its full type (generated concretely by the unified phase).
        bindings: Vec<(TypedBinding, TypedExpr)>,
        /// The continuation, with the whole group in scope.
        body: Box<TypedExpr>,
    },

    /// A statement `for` loop, mirroring the CHL construct directly:
    /// `for target in iter: body`. Value `Unit`.
    ///
    /// A **pre-phase surface-structure node** in the same transient class as
    /// [`TypedExprNode::Defer`]: a pure placeholder no pass executes,
    /// eliminated wholesale by the unified letrec phase
    /// (src/ccl/design/mutability.md, "The unified phase"). Lowering emits
    /// it for mutation loops whose bodies carry no feeds or yields; the
    /// phase rewrites it — with the [`TypedExprNode::MutWrite`]s inside —
    /// into a guarded [`TypedExprNode::LetRec`]. No pass downstream of the
    /// phase may observe it; operator conversion rejects it explicitly.
    For {
        /// The iteration binder, bound in `body` to each source element.
        target: TypedBinding,
        /// The iteration source — a `Fun(D, T)` whose domain drives the loop.
        iter: Box<TypedExpr>,
        /// The per-iteration statement chain (`Let`s / `ExprStmt`-sequenced
        /// `MutWrite`s), value `Unit`. Reads of mutable variables are bare
        /// `Var`s — read-your-writes shadowing is the phase's job, not
        /// lowering's.
        body: Box<TypedExpr>,
    },

    /// One write to a `Mut`-declared variable: `name = value` inside a
    /// [`TypedExprNode::For`] body. Value `Unit`.
    ///
    /// `name` is a *reference* to the enclosing plain-`let` binding that
    /// introduced the variable (not a binder): uniquify and substitution
    /// treat it exactly like a `Var` use. Bare `Var(name)` reads inside
    /// `value` are ordinary reads of that binding — the value *before* this
    /// write.
    ///
    /// Same transient class as [`TypedExprNode::For`] — eliminated by the
    /// unified phase, which threads the write through the letrec recurrence.
    MutWrite {
        /// The mutable variable being written.
        name: Name,
        /// The written value; must be a subtype of the variable's type.
        value: Box<TypedExpr>,
    },

    /// A tuple constructor: `(e0, e1, ...)`.
    ///
    /// Compiles to a [`crate::interpreter::tile_operators::FanIn`] record with fields
    /// named `_0`, `_1`, … (via [`crate::interpreter::tuple_field`]).
    Tuple(Vec<TypedExpr>),

    /// A first-class projection morphism `.n` (tuple) or `.name` (record).
    ///
    /// `Proj(k)` represents the morphism `λ t → t.k` in point-free form.
    /// Tuple index access `t[n]` is lowered as `Apply(Proj(Index(n)), t)`.
    /// Introduced by lowering; absent in the higher-level design.
    Proj(ProjKey),

    /// A record constructor: `{field: expr, ...}`.
    ///
    /// Lowered from Python dict literals with bare identifier keys.
    /// Field access `r.field` lowers to `Apply(r, Proj(ProjKey::Field("field")))`.
    Record(Vec<(String, TypedExpr)>),

    /// A reference to an externally-registered data source, identified by name.
    ///
    /// Emitted by [`crate::ccl::lower`] when a zero-argument call is recognised
    /// as a registered source (e.g. `testsource1()` or `__stdinvalues()`).
    /// [`crate::ccl::infer`] resolves it to a `Fun(DataSource(name), output_type)`
    /// via the source registry; [`crate::interpreter::operator_conversion`] compiles it to
    /// the appropriate reader operator.
    Source(String),

    /// N-ary point-free function composition: `f₀ ≫ f₁ ≫ … ≫ fₙ₋₁`.
    ///
    /// Introduced by [`crate::ccl::lambda_elim`]; always contains at least
    /// two morphisms. [`crate::ccl::simplify`] flattens nested two-element
    /// `Compose` nodes into longer chains.
    ///
    /// Semantics: element `i` is applied before element `i+1`, so
    /// `Compose([f, g])` means "apply `f`, then pipe the result to `g`".
    Compose(Vec<TypedExpr>),

    /// N-ary collection union: `c0 ++ c1 ++ … ++ c{n-1}`.
    ///
    /// Each operand must have a function (collection) type
    /// `Fun(D_i, C_i)`; the result type is
    /// `Fun(Union(D_0, …, D_{n-1}), dedup_union(C_0, …, C_{n-1}))` —
    /// the domain union is never deduplicated, the codomain union is.
    ///
    /// Lowered from the CHL `++` operator.  The parser produces
    /// pairwise nesting; [`TypedExpr::collection_union`] flattens at
    /// construction time so every `CollectionUnion` node in the tree
    /// satisfies the invariant **"no operand is itself a
    /// `CollectionUnion`"**.  Inference, lambda elimination, and
    /// operator conversion all rely on this — they never need to look
    /// through nested `CollectionUnion` AST nodes.  (Type-level
    /// nesting via `Var` references to let-bound unions is a separate
    /// concern, preserved by design: the runtime `UnionOperator` has
    /// one input per operand, so a `Var(y)` whose type is itself
    /// `Fun(Union(...), …)` correctly becomes one nested-tagged
    /// variant of the outer union.)
    ///
    /// **Position invariant.** This node represents a *value* — the
    /// merged collection — and only appears where collections appear:
    /// in let bindings, as elements of a `Compose` chain (source
    /// position), as a program output, etc.  Inside a lambda body
    /// where the operands reference the surrounding parameter,
    /// [`crate::ccl::lambda_elim`] rewrites it to
    /// `Apply(Tuple(ops), Builtin::CollectionUnion)` so the function
    /// can be lifted out point-free.  After lambda elimination, both
    /// shapes (this node and the `Builtin` form) may appear and both
    /// compile to the same `UnionOperator`.
    CollectionUnion(Vec<TypedExpr>),

    /// A plan expression, followed by another statement
    ExprStmt {
        expr: Box<TypedExpr>,
        body: Box<TypedExpr>,
    },

    /// Feed a value into a deferred output: `x << value`.
    /// Lowers from the `<<` (LShift) binary operator when the LHS names a defer.
    /// Has type `Unit`; the value is collected by [`crate::ccl::desugar_defers`]
    /// and unioned into the source channel that resolves the defer.
    Feed { name: Name, value: Box<Expr> },

    /// Define a deferred output to a specific value: `x <<= value`.
    /// Lowers from the `<<=` (AugAssign LShift) statement when the LHS names a defer.
    /// Has type `Unit`; the value is collected by [`crate::ccl::desugar_defers`]
    /// and replaces the surrounding `Defer` binding.
    Define { name: Name, value: Box<Expr> },

    /// Placeholder for an output accumulator introduced by `x = defer()`.
    /// The bound name is resolved by the surrounding `Let` binding.
    /// Eliminated by [`crate::ccl::desugar_defers`] before type inference.
    Defer,

    /// Recovery placeholder inserted by lowering when a sub-expression or
    /// statement could not be lowered (either because it came from a parser
    /// recovery hole — [`crate::chl_parser::ast::Expr::Error`] /
    /// [`crate::chl_parser::ast::Stmt::Error`] — or because lowering itself
    /// failed with a [`crate::ccl::lower::LoweringError`]).
    ///
    /// **Contract.** This variant exists *only* while there are pending
    /// [`crate::ccl::lower::LoweringError`]s in the `LoweringResult`. Callers
    /// must inspect `errors` before consuming the lowered tree and abort the
    /// pipeline (no inference, no operator conversion) if non-empty.
    /// Downstream passes treat this variant as unreachable.
    Error,
}

/// A CCL expression with a type slot on every node.
///
/// Every node starts with `ty: Type::Hole`; the inference pass
/// ([`crate::ccl::infer::infer`]) converts it to a registered [`Type::Infer`] variable,
/// then fills it with the concrete type before compilation.
///
/// `user_annotation` carries an explicit type annotation written by the user
/// (e.g. from a Python `cast(T, expr)` or an annotated binding site). The
/// inference pass checks that the inferred type is compatible with it.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedExpr {
    /// The inferred type of this expression.
    ///
    /// Starts as [`Type::Hole`] (lowering placeholder); converted to [`Type::Infer`]
    /// at inference entry and written to a concrete type by [`crate::ccl::infer::infer`].
    pub ty: Type,
    /// The expression kind.
    pub node: TypedExprNode,
    /// User-written type annotation, if any.
    ///
    /// Checked against the inferred type by [`crate::ccl::infer::infer`]; `None` for all
    /// nodes produced by the current lowering pass.
    pub user_annotation: Option<Type>,
}

/// Type alias for backward compatibility. `Expr` is now [`TypedExpr`].
pub type Expr = TypedExpr;

impl TypedExpr {
    /// Construct a new [`TypedExpr`] with a [`Type::Hole`] placeholder and no user annotation.
    ///
    /// `Hole` is the lowering-phase placeholder. The inference pass converts it to a
    /// registered [`Type::Infer`] variable before type-checking begins.
    pub fn new(node: TypedExprNode) -> Self {
        TypedExpr {
            node,
            ty: Type::Hole,
            user_annotation: None,
        }
    }

    /// Set the inferred type on this expression, consuming and returning it.
    ///
    /// Used to pre-fill the type in tests or when the type is known at construction time.
    pub fn with_ty(self, ty: Type) -> Self {
        TypedExpr { ty, ..self }
    }

    /// Set the user annotation on this expression, consuming and returning it.
    ///
    /// Used to attach a user-written type annotation in tests.
    pub fn with_user_annotation(self, annotation: Type) -> Self {
        TypedExpr {
            user_annotation: Some(annotation),
            ..self
        }
    }

    /// Construct a literal expression.
    pub fn lit(l: Lit) -> Self {
        Self::new(TypedExprNode::Lit(l))
    }

    /// Construct a variable reference expression.
    pub fn var(name: impl Into<Name>) -> Self {
        Self::new(TypedExprNode::Var(name.into()))
    }

    /// Construct a [`TypedExprNode::Builtin`] reference.
    ///
    /// Callers are responsible for stamping the appropriate function type via
    /// [`TypedExpr::with_ty`]; the constructor itself leaves [`TypedExpr::ty`]
    /// as [`Type::Hole`], matching how the previous magic-string `Var`-based
    /// emission worked.
    pub fn builtin(b: Builtin) -> Self {
        Self::new(TypedExprNode::Builtin(b))
    }

    /// Construct a list literal expression.
    pub fn list(elts: Vec<Self>) -> Self {
        Self::new(TypedExprNode::List(elts))
    }

    /// Construct an aggregate expression.
    pub fn aggregate(input: Self, kind: AggregateKind) -> Self {
        Self::new(TypedExprNode::Aggregate {
            input: Box::new(input),
            kind,
        })
    }

    /// Construct an ExprStmt expression.
    pub fn expr_stmt(expr: Self, body: Self) -> Self {
        Self::new(TypedExprNode::ExprStmt {
            expr: Box::new(expr),
            body: Box::new(body),
        })
    }

    /// Construct a feed expression.
    pub fn mut_write(name: impl Into<Name>, value: Self) -> Self {
        Self::new(TypedExprNode::MutWrite {
            name: name.into(),
            value: Box::new(value),
        })
    }

    pub fn feed(name: impl Into<Name>, value: Self) -> Self {
        Self::new(TypedExprNode::Feed {
            name: name.into(),
            value: Box::new(value),
        })
    }

    /// Construct a define expression.
    pub fn define(name: impl Into<Name>, value: Self) -> Self {
        Self::new(TypedExprNode::Define {
            name: name.into(),
            value: Box::new(value),
        })
    }

    /// Construct a lowering-error placeholder.
    ///
    /// Used by [`crate::ccl::lower`] to fill in slots where a sub-expression
    /// could not be produced (parse-recovery hole or local lowering failure)
    /// while letting the surrounding tree keep being lowered. The placeholder
    /// is only valid while the accompanying error list is non-empty; see the
    /// [`TypedExprNode::Error`] doc for the contract.
    pub fn error() -> Self {
        Self::new(TypedExprNode::Error)
    }

    /// Construct a for-loop expression.
    ///
    /// Desugars directly to `Compose([source, Lambda(iter_var, body)])`.
    /// This is the canonical CCL representation for iteration: the source
    /// morphism feeds elements to the per-element lambda, which is then
    /// eliminated by lambda elimination into point-free form.
    pub fn for_loop(iter_var: impl Into<Name>, source: Self, body: Self) -> Self {
        let lambda = Self::lambda(iter_var, Type::Hole, body);
        Self::compose(vec![source, lambda])
    }

    /// Construct a let binding expression.
    ///
    /// `binding.ty` mirrors `bound_expr.ty` at construction time so that callers
    /// who pre-set the expression type via [`TypedExpr::with_ty`] (e.g. tests that
    /// bypass inference) do not need to set the binding type separately. After
    /// inference both fields hold the same type; [`crate::ccl::context::compile_program`] reads
    /// `binding.ty` as the authoritative slot. In normal lowering both start as
    /// [`Type::Infer`] and inference fills them together.
    pub fn let_bind(name: impl Into<Name>, bound_expr: Self, body: Self) -> Self {
        let ty = bound_expr.ty.clone();
        Self::new(TypedExprNode::Let {
            binding: TypedBinding {
                name: name.into(),
                ty,
                user_annotation: None,
            },
            bound_expr: Box::new(bound_expr),
            body: Box::new(body),
        })
    }

    /// Construct an annotated let binding expression.
    ///
    /// Like [`Self::let_bind`] but sets [`TypedBinding::user_annotation`] to `annotation`.
    /// Inference validates that the inferred type of `bound_expr` is compatible with
    /// `annotation` and raises [`crate::ccl::infer::InferError::AnnotationMismatch`] on conflict.
    pub fn let_bind_annotated(
        name: impl Into<Name>,
        bound_expr: Self,
        body: Self,
        annotation: Type,
    ) -> Self {
        Self::new(TypedExprNode::Let {
            binding: TypedBinding::new_annotated(name, annotation),
            bound_expr: Box::new(bound_expr),
            body: Box::new(body),
        })
    }

    /// Construct a [`TypedExprNode::LetRec`] group.
    ///
    /// Every binding's name is in scope in every binding's body and in
    /// `body` (mutual recursion); the caller is responsible for the
    /// guardedness well-formedness condition
    /// ([`crate::ccl::letrec::check_letrec_guarded`]).
    pub fn letrec(bindings: Vec<(TypedBinding, Self)>, body: Self) -> Self {
        Self::new(TypedExprNode::LetRec {
            bindings,
            body: Box::new(body),
        })
    }

    /// Construct a tuple expression.
    pub fn tuple(elts: Vec<Self>) -> Self {
        Self::new(TypedExprNode::Tuple(elts))
    }

    /// Construct a first-class projection morphism node.
    ///
    /// `Proj(Field(f))` acts as the function `λ t → t.f`.
    pub fn proj_field(field: impl Into<String>) -> Self {
        Self::new(TypedExprNode::Proj(ProjKey::Field(field.into())))
    }

    /// Construct a first-class projection morphism node.
    ///
    /// `Proj(Index(n))` acts as the function `λ t → t.n`. Tuple subscript `t[n]`
    /// is lowered as `Expr::apply(t, Expr::proj_index(n))`.
    pub fn proj_index(i: usize) -> Self {
        Self::new(TypedExprNode::Proj(ProjKey::Index(i)))
    }

    /// Construct a unary operation expression.
    pub fn unary(op: UnaryOpKind, operand: Self) -> Self {
        Self::new(TypedExprNode::UnaryOp(op, Box::new(operand)))
    }

    /// Construct an n-ary composition expression.
    ///
    /// `exprs` must contain at least two morphisms. The composition is
    /// left-to-right: `exprs[0]` is applied first, `exprs[1]` second, and so
    /// on.
    pub fn compose(exprs: Vec<Self>) -> Self {
        debug_assert!(exprs.len() >= 2, "Compose requires at least two morphisms");
        Self::new(TypedExprNode::Compose(exprs))
    }

    /// Construct an n-ary [`TypedExprNode::CollectionUnion`] expression.
    ///
    /// `operands` must contain at least two collections.  Any operand
    /// that is itself a [`TypedExprNode::CollectionUnion`] is spliced
    /// in-place — this is the **construction-time flattening**
    /// that makes `(a ++ b) ++ c` and `a ++ (b ++ c)` and `a ++ b ++ c`
    /// all produce the same flat 3-ary node, which inference and every
    /// downstream pass then see as canonical.
    ///
    /// The splicing drops the inner wrapper's `ty` / `user_annotation`
    /// fields.  That is safe because the constructor is only used in
    /// positions where either (a) inference has not yet run, so types
    /// are still [`Type::Hole`], or (b) the input is already flat by
    /// invariant (lambda elimination doesn't introduce nesting; it
    /// either preserves a top-level node or rewrites the whole thing
    /// to the point-free `Apply(Tuple, Builtin)` form).
    pub fn collection_union(operands: Vec<Self>) -> Self {
        let flat: Vec<Self> = operands
            .into_iter()
            .flat_map(|op| match op.node {
                TypedExprNode::CollectionUnion(inner) => inner,
                _ => vec![op],
            })
            .collect();
        debug_assert!(
            flat.len() >= 2,
            "CollectionUnion requires at least two operands after flattening",
        );
        Self::new(TypedExprNode::CollectionUnion(flat))
    }

    /// Construct a binary operation expression.
    pub fn binop(left: Self, op: BinOpKind, right: Self) -> Self {
        Self::new(TypedExprNode::BinOp {
            left: Box::new(left),
            op,
            right: Box::new(right),
        })
    }

    /// Construct a curried function application.
    ///
    /// `argument` is first, `function` is second, mirroring the pipeline style.
    pub fn apply(argument: TypedExpr, function: TypedExpr) -> Self {
        Self::new(TypedExprNode::Apply {
            argument: Box::new(argument),
            function: Box::new(function),
        })
    }

    /// Construct a [`TypedExprNode::Cast`] re-viewing `value` under `target`.
    ///
    /// Prefer [`crate::ccl::ccl_utils::make_cast`], which enforces the
    /// `target` shape contract; this is the bare constructor it builds on.
    pub fn cast(value: TypedExpr, target: Type) -> Self {
        Self::new(TypedExprNode::Cast {
            value: Box::new(value),
            target,
        })
    }

    /// Build an unannotated or pre-annotated [`TypedExprNode::Lambda`].
    ///
    /// Pass [`Type::Hole`] for `param_ty` when the parameter type is not yet
    /// known (lowering phase); pass the concrete type when it is already known.
    /// Do not pass `Type::Infer(fresh_infer_var())` from lowering — `Hole` is
    /// the correct lowering placeholder.
    pub fn lambda(param: impl Into<Name>, param_ty: Type, body: TypedExpr) -> Self {
        let result_ty = Type::fun(param_ty.clone(), body.ty.clone());
        Self::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: param.into(),
                ty: param_ty,
                user_annotation: None,
            },
            body: Box::new(body),
        })
        .with_ty(result_ty)
    }

    /// Construct a [`TypedExprNode::VariantCtor`] node.
    ///
    /// Produces a singleton variant value at the inference layer. Width-
    /// subtyping flows it into any consumer expecting a superset of tags.
    pub fn variant_ctor(tag: impl Into<String>, payload: TypedExpr) -> Self {
        Self::new(TypedExprNode::VariantCtor {
            tag: tag.into(),
            payload: Box::new(payload),
        })
    }

    /// Construct a pattern-matching [`TypedExprNode::Case`] node — a `Case`
    /// with a scrutinee whose branches carry structural [`Pattern`]s.
    pub fn match_expr(scrutinee: TypedExpr, branches: Vec<Branch>) -> Self {
        Self::new(TypedExprNode::Case {
            scrutinee: Some(Box::new(scrutinee)),
            branches,
        })
    }
}

// ---------------------------------------------------------------------------
// Structural traversal helpers
// ---------------------------------------------------------------------------

impl TypedExpr {
    /// Invoke `f` on each direct child [`TypedExpr`] of this node.
    ///
    /// "Direct child" means an Expr reachable through this node's value fields
    /// — `function`/`argument`, `left`/`right`, `Case` branch guard/body,
    /// `Lambda` body, `Let` `bound_expr`/`body`, list/tuple/record/compose
    /// elements, and so on.  It does **not** descend through type refinement
    /// predicates or any expression reachable only through [`Type`]; passes
    /// that need those (e.g. [`crate::ccl::ccl_utils::is_free`]) must visit
    /// them explicitly.
    ///
    /// Use this to write structural recursion over the tree without
    /// enumerating every variant.  Binder-aware passes that need to handle
    /// shadowing (e.g. stopping at a [`TypedExprNode::Lambda`] whose param
    /// matches a target name) must still handle the binder variants
    /// explicitly rather than relying on this method.
    pub fn walk_children(&self, mut f: impl FnMut(&TypedExpr)) {
        match &self.node {
            TypedExprNode::Lit(_)
            | TypedExprNode::Var(_)
            | TypedExprNode::Builtin(_)
            | TypedExprNode::Proj(_)
            | TypedExprNode::Source(_)
            | TypedExprNode::Defer
            | TypedExprNode::Error => {}
            TypedExprNode::Apply { function, argument } => {
                f(function);
                f(argument);
            }
            // Only `value` is an expression child; `target` is a type (its
            // refinement predicate is reached via type walks, not here).
            TypedExprNode::Cast { value, .. } => f(value),
            TypedExprNode::BinOp { left, right, .. } => {
                f(left);
                f(right);
            }
            TypedExprNode::UnaryOp(_, inner) => f(inner),
            TypedExprNode::Lambda { body, .. } => f(body),
            TypedExprNode::Aggregate { input, .. } => f(input),
            TypedExprNode::Let {
                bound_expr, body, ..
            } => {
                f(bound_expr);
                f(body);
            }
            TypedExprNode::List(elts)
            | TypedExprNode::Tuple(elts)
            | TypedExprNode::Compose(elts)
            | TypedExprNode::CollectionUnion(elts) => {
                for e in elts {
                    f(e);
                }
            }
            TypedExprNode::Case {
                scrutinee,
                branches,
            } => {
                if let Some(s) = scrutinee {
                    f(s);
                }
                for b in branches {
                    f(&b.guard);
                    f(&b.body);
                }
            }
            TypedExprNode::VariantCtor { payload, .. } => f(payload),
            TypedExprNode::Record(fields) => {
                for (_, e) in fields {
                    f(e);
                }
            }
            // `domain` is a `Type`, not an `Expr` child, so the expr-walker
            // skips it (its type residue is reached via `expr.ty` walks).
            TypedExprNode::Transact { keys, writers, .. } => {
                for k in keys {
                    f(&k.init);
                }
                for w in writers {
                    f(&w.source);
                    f(&w.body);
                }
            }
            TypedExprNode::LetRec { bindings, body } => {
                for (_, def) in bindings {
                    f(def);
                }
                f(body);
            }
            TypedExprNode::For { iter, body, .. } => {
                f(iter);
                f(body);
            }
            TypedExprNode::ExprStmt { expr, body } => {
                f(expr);
                f(body);
            }
            TypedExprNode::Feed { value, .. }
            | TypedExprNode::Define { value, .. }
            | TypedExprNode::MutWrite { value, .. } => f(value),
        }
    }

    /// Return `true` if `f` returns `true` for any direct child Expr.
    ///
    /// Short-circuits the recursive predicate cheaply: once a match is found,
    /// `walk_children` still finishes iterating remaining siblings but does
    /// not invoke `f` on them.
    pub fn any_child(&self, mut f: impl FnMut(&TypedExpr) -> bool) -> bool {
        let mut found = false;
        self.walk_children(|e| {
            if !found && f(e) {
                found = true;
            }
        });
        found
    }

    /// Return `true` if `f` returns `true` for every direct child Expr.  Vacuously true at leaves.
    pub fn all_children(&self, mut f: impl FnMut(&TypedExpr) -> bool) -> bool {
        let mut all = true;
        self.walk_children(|e| {
            if all && !f(e) {
                all = false;
            }
        });
        all
    }

    /// Fold `f` left-to-right over the direct child Exprs, starting from `init`.
    ///
    /// Useful for value-returning recursions that combine per-child results —
    /// counts, max-depth, set unions, `Option<&Expr>` finders.  For a recursive
    /// helper that returns `T`, the call pattern is:
    ///
    /// ```ignore
    /// fn count_foo(e: &Expr) -> usize {
    ///     let here = if is_foo(e) { 1 } else { 0 };
    ///     here + e.fold_children(0, |acc, child| acc + count_foo(child))
    /// }
    /// ```
    ///
    /// Short-circuit is possible by making `f` skip work when the accumulator
    /// already represents a "done" state (e.g. `acc.or_else(|| find(child))`
    /// for an `Option<&Expr>` finder).  The closure is only invoked for direct
    /// children of the current node; structural recursion is the caller's job.
    pub fn fold_children<T>(&self, init: T, mut f: impl FnMut(T, &TypedExpr) -> T) -> T {
        // Threaded via `Option` so we can move `acc` through a `FnMut` closure
        // without requiring `T: Default`.  Both `take`/`expect` pairs are safe:
        // `walk_children` calls the closure synchronously and `acc` is always
        // refilled before returning from it.
        let mut acc = Some(init);
        self.walk_children(|e| {
            let val = acc
                .take()
                .expect("fold_children: closure invoked re-entrantly");
            acc = Some(f(val, e));
        });
        acc.expect("fold_children: walk_children dropped accumulator")
    }

    /// Mutable analog of [`walk_children`](Self::walk_children).
    ///
    /// Invokes `f` on each direct child Expr by mutable reference, in the same
    /// order as `walk_children`.  Same caveats apply: does not descend through
    /// type refinement predicates and does not visit binder name/type fields.
    /// Pure-mutator passes that need to mutate `Lambda.param.ty`,
    /// `Let.binding.ty`, or the refinement predicate must handle those
    /// explicitly before (or after) calling this method.
    pub fn walk_children_mut(&mut self, mut f: impl FnMut(&mut TypedExpr)) {
        match &mut self.node {
            TypedExprNode::Lit(_)
            | TypedExprNode::Var(_)
            | TypedExprNode::Builtin(_)
            | TypedExprNode::Proj(_)
            | TypedExprNode::Source(_)
            | TypedExprNode::Defer
            | TypedExprNode::Error => {}
            TypedExprNode::Apply { function, argument } => {
                f(function);
                f(argument);
            }
            // Only `value` is an expression child; `target` is a type (its
            // refinement predicate is reached via type walks, not here).
            TypedExprNode::Cast { value, .. } => f(value),
            TypedExprNode::BinOp { left, right, .. } => {
                f(left);
                f(right);
            }
            TypedExprNode::UnaryOp(_, inner) => f(inner),
            TypedExprNode::Lambda { body, .. } => f(body),
            TypedExprNode::Aggregate { input, .. } => f(input),
            TypedExprNode::Let {
                bound_expr, body, ..
            } => {
                f(bound_expr);
                f(body);
            }
            TypedExprNode::List(elts)
            | TypedExprNode::Tuple(elts)
            | TypedExprNode::Compose(elts)
            | TypedExprNode::CollectionUnion(elts) => {
                for e in elts {
                    f(e);
                }
            }
            TypedExprNode::Case {
                scrutinee,
                branches,
            } => {
                if let Some(s) = scrutinee {
                    f(s);
                }
                for b in branches {
                    f(&mut b.guard);
                    f(&mut b.body);
                }
            }
            TypedExprNode::VariantCtor { payload, .. } => f(payload),
            TypedExprNode::Record(fields) => {
                for (_, e) in fields {
                    f(e);
                }
            }
            TypedExprNode::Transact { keys, writers, .. } => {
                for k in keys {
                    f(&mut k.init);
                }
                for w in writers {
                    f(&mut w.source);
                    f(&mut w.body);
                }
            }
            TypedExprNode::LetRec { bindings, body } => {
                for (_, def) in bindings {
                    f(def);
                }
                f(body);
            }
            TypedExprNode::For { iter, body, .. } => {
                f(iter);
                f(body);
            }
            TypedExprNode::ExprStmt { expr, body } => {
                f(expr);
                f(body);
            }
            TypedExprNode::Feed { value, .. }
            | TypedExprNode::Define { value, .. }
            | TypedExprNode::MutWrite { value, .. } => f(value),
        }
    }

    /// Mutable analog of [`fold_children`](Self::fold_children).
    ///
    /// Threads `init` through `f` while visiting each direct child by mutable
    /// reference.  Useful for bottom-up rewrites that want to OR a "changed"
    /// flag across children:
    ///
    /// ```ignore
    /// let changed = expr.fold_children_mut(false, |c, e| c | rewrite_once(e));
    /// ```
    pub fn fold_children_mut<T>(
        &mut self,
        init: T,
        mut f: impl FnMut(T, &mut TypedExpr) -> T,
    ) -> T {
        let mut acc = Some(init);
        self.walk_children_mut(|e| {
            let val = acc
                .take()
                .expect("fold_children_mut: closure invoked re-entrantly");
            acc = Some(f(val, e));
        });
        acc.expect("fold_children_mut: walk_children_mut dropped accumulator")
    }

    /// By-value transform of each direct child Expr.
    ///
    /// Moves each child out via [`std::mem::take`], passes it to `f`, and
    /// stores the returned value back in its slot.  Useful as the structural
    /// recursion step in by-value transformers like
    /// [`crate::ccl::lambda_elim::substitute`] — the caller writes
    /// `expr.map_children(|c| transform(c, args))` instead of plumbing
    /// `mem::take` and `walk_children_mut` by hand.
    pub fn map_children(&mut self, mut f: impl FnMut(TypedExpr) -> TypedExpr) {
        self.walk_children_mut(|child| {
            *child = f(std::mem::take(child));
        });
    }

    /// Fallible by-value transform of each direct child Expr.
    ///
    /// Like [`map_children`](Self::map_children), but `f` may return `Err`.
    /// On the first `Err`, the walk stops invoking `f` (remaining siblings
    /// still pass through `walk_children_mut`, but cheaply — just an `is_ok`
    /// check), and the error is returned from this method.  Children
    /// transformed before the failure remain in place.
    pub fn try_map_children<E>(
        &mut self,
        mut f: impl FnMut(TypedExpr) -> Result<TypedExpr, E>,
    ) -> Result<(), E> {
        let mut err: Result<(), E> = Ok(());
        self.walk_children_mut(|child| {
            if err.is_err() {
                return;
            }
            match f(std::mem::take(child)) {
                Ok(new) => *child = new,
                Err(e) => err = Err(e),
            }
        });
        err
    }
}

// Implement Default so that we can use std::mem::take out of Exprs.
impl Default for TypedExpr {
    fn default() -> Self {
        Self::new(TypedExprNode::Lit(Lit::Int(0)))
    }
}

/// One key of a [`TypedExprNode::Transact`] — a single scalar register sharing
/// the store's sequencing domain.
#[derive(Debug, Clone, PartialEq)]
pub struct TransactKey {
    /// The key — the (α-uniquified) `Name` of the register. A read of the
    /// variable projects [`Name::field_key`] of the store record (`__store.k`).
    pub name: Name,
    /// The position-0 initial value (the scalar seed), evaluated once outside
    /// every writer's scope. The key's history is `Fun(domain, V)`; a read is
    /// its latest value `V` (`last_or_default(history, init)`, defaulting to
    /// `init` when the store ran zero positions).
    pub init: TypedExpr,
}

/// One writer of a [`TypedExprNode::Transact`] — loop-shaped, mirroring a
/// mutation-loop accumulator arm but reading the *shared* store rather than a
/// private accumulator.
#[derive(Debug, Clone, PartialEq)]
pub struct TransactWriter {
    /// The writer's **read-set**: the store keys whose snapshot value the body
    /// reads, in body-parameter order. The body is fed `(snap_{k₀}, …,
    /// snap_{k_{r-1}}, item)` — each `read_keys[i]` bound as position `i` — so
    /// an in-body read of a store variable resolves to its snapshot by lexical
    /// shadowing (the accumulator pattern, generalized to several keys).
    pub read_keys: Vec<Name>,
    /// The writer's **write-set**: the store keys the body proposes new values
    /// for, in the order of the decision's `writes` tuple (`writes.i` is the
    /// new value for `write_keys[i]`).
    pub write_keys: Vec<Name>,
    /// Iteration source — a `Fun(D, item)` whose domain drives this writer and
    /// whose codomain elements are passed to [`Self::body`]. Sits *outside* the
    /// snapshot-parameter scope.
    pub source: TypedExpr,
    /// The per-position decision — `Fun(Tuple(snap…, item), {commit: Bool,
    /// writes: Tuple(new…), to_<defer>*})`: reads the store snapshot, returns a
    /// grant/deny (`commit`) with the proposed per-key write set (`writes`) and
    /// any per-position `to_<defer>` feed taps. `commit` is always `true` for
    /// the induction (`mut`-loop) case.
    pub body: TypedExpr,
}

/// Rebuild a [`TypedExprNode::Transact`] applying `recurse` to every child
/// expression — each key's `init` and each writer's `source`/`body`. The
/// single source of truth for the Transact structural-recursion rule, so the
/// substitute / inline / desugar / lambda-elim passes delegate here. The
/// writer body's snapshot binders (`let kᵢ = p.i`) are ordinary `let`s inside
/// `body`, so `recurse` handles their shadowing through its own `Let`
/// traversal; `read_keys`/`write_keys`/`domain` are labels, not binders, and
/// pass through untouched.
pub fn walk_transact<F>(
    keys: Vec<TransactKey>,
    writers: Vec<TransactWriter>,
    domain: Type,
    mut recurse: F,
) -> TypedExprNode
where
    F: FnMut(TypedExpr) -> TypedExpr,
{
    TypedExprNode::Transact {
        keys: keys
            .into_iter()
            .map(|k| TransactKey {
                init: recurse(k.init),
                ..k
            })
            .collect(),
        writers: writers
            .into_iter()
            .map(|w| TransactWriter {
                read_keys: w.read_keys,
                write_keys: w.write_keys,
                source: recurse(w.source),
                body: recurse(w.body),
            })
            .collect(),
        domain,
    }
}

/// Fallible variant of [`walk_transact`] for passes whose recursion returns a
/// `Result`.
pub fn try_walk_transact<F, E>(
    keys: Vec<TransactKey>,
    writers: Vec<TransactWriter>,
    domain: Type,
    mut recurse: F,
) -> Result<TypedExprNode, E>
where
    F: FnMut(TypedExpr) -> Result<TypedExpr, E>,
{
    let mut new_keys = Vec::with_capacity(keys.len());
    for k in keys {
        new_keys.push(TransactKey {
            init: recurse(k.init)?,
            ..k
        });
    }
    let mut new_writers = Vec::with_capacity(writers.len());
    for w in writers {
        new_writers.push(TransactWriter {
            read_keys: w.read_keys,
            write_keys: w.write_keys,
            source: recurse(w.source)?,
            body: recurse(w.body)?,
        });
    }
    Ok(TypedExprNode::Transact {
        keys: new_keys,
        writers: new_writers,
        domain,
    })
}

/// A single branch in a [`TypedExprNode::Case`] expression.
///
/// A branch carries an optional structural [`Pattern`] (match a variant tag
/// of the enclosing `Case`'s scrutinee, binding its payload) and an optional
/// boolean `guard`. The branch wins when its pattern matches *and* its guard
/// is `true`; `body` is then evaluated in scope of any pattern binding.
///
/// Branch kinds:
/// - guard only (`pattern: None`) — a classic `if`/`elif` condition;
/// - pattern only — a bare `case .Tag(x):` arm; its `guard` is the literal
///   `true` (the structural match alone decides the branch);
/// - both — `case .Tag(x) if x > 0:`, matching structure and logic at once.
#[derive(Debug, Clone, PartialEq)]
pub struct Branch {
    /// Optional structural pattern. Requires the enclosing `Case` to have a
    /// scrutinee; `None` for a purely logical branch.
    pub pattern: Option<Pattern>,
    /// Boolean guard; constrained to
    /// [`Type::Base`]`(`[`BaseType::Bool`](crate::ccl::BaseType::Bool)`)` during inference. A pattern
    /// branch with no secondary filter carries a literal `true` guard, so
    /// the "first branch whose guard holds" rule is uniform.
    pub guard: TypedExpr,
    /// Value expression; evaluated when the branch wins.
    pub body: TypedExpr,
}

/// The structural part of a [`Branch`]: a variant tag plus the binding that
/// receives its payload.
///
/// Matches one tag of the enclosing [`TypedExprNode::Case`]'s scrutinee and
/// binds the payload to `binding.name`; `binding.ty` is filled in by
/// inference to the per-tag narrowed payload type.
#[derive(Debug, Clone, PartialEq)]
pub struct Pattern {
    /// Tag this branch matches; must agree with one of the scrutinee
    /// variant's keys.
    pub tag: String,
    /// Payload binding, in scope for the branch's `guard` and `body`.
    pub binding: TypedBinding,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(name: &str) -> TypedExpr {
        TypedExpr::var(name)
    }

    /// `CollectionUnion([a, b])` with no nested operands is preserved as-is.
    #[test]
    fn collection_union_flat_input_is_unchanged() {
        let result = TypedExpr::collection_union(vec![leaf("a"), leaf("b")]);
        let TypedExprNode::CollectionUnion(ops) = result.node else {
            panic!("expected CollectionUnion node");
        };
        assert_eq!(ops.len(), 2);
        assert!(
            !ops.iter()
                .any(|e| matches!(&e.node, TypedExprNode::CollectionUnion(_))),
            "operands must be flat"
        );
    }

    /// `((a ++ b) ++ c)` (left-nested) flattens to a flat 3-ary node.
    #[test]
    fn collection_union_flattens_left_nested() {
        let ab = TypedExpr::collection_union(vec![leaf("a"), leaf("b")]);
        let abc = TypedExpr::collection_union(vec![ab, leaf("c")]);
        let TypedExprNode::CollectionUnion(ops) = abc.node else {
            panic!("expected CollectionUnion node");
        };
        assert_eq!(ops.len(), 3);
        assert!(
            !ops.iter()
                .any(|e| matches!(&e.node, TypedExprNode::CollectionUnion(_))),
            "operands must be flat"
        );
        let names: Vec<&str> = ops
            .iter()
            .map(|e| match &e.node {
                TypedExprNode::Var(n) => n.base(),
                _ => panic!("expected Var operand"),
            })
            .collect();
        assert_eq!(names, vec!["a", "b", "c"]);
    }

    /// `(a ++ (b ++ c))` (right-nested) flattens to a flat 3-ary node.
    #[test]
    fn collection_union_flattens_right_nested() {
        let bc = TypedExpr::collection_union(vec![leaf("b"), leaf("c")]);
        let abc = TypedExpr::collection_union(vec![leaf("a"), bc]);
        let TypedExprNode::CollectionUnion(ops) = abc.node else {
            panic!("expected CollectionUnion node");
        };
        assert_eq!(ops.len(), 3);
        let names: Vec<&str> = ops
            .iter()
            .map(|e| match &e.node {
                TypedExprNode::Var(n) => n.base(),
                _ => panic!("expected Var operand"),
            })
            .collect();
        assert_eq!(names, vec!["a", "b", "c"]);
    }

    /// `(((a ++ b) ++ c) ++ d)` (two levels of left nesting) flattens to 4.
    #[test]
    fn collection_union_flattens_double_nested() {
        let ab = TypedExpr::collection_union(vec![leaf("a"), leaf("b")]);
        let abc = TypedExpr::collection_union(vec![ab, leaf("c")]);
        let abcd = TypedExpr::collection_union(vec![abc, leaf("d")]);
        let TypedExprNode::CollectionUnion(ops) = abcd.node else {
            panic!("expected CollectionUnion node");
        };
        assert_eq!(ops.len(), 4);
        assert!(
            !ops.iter()
                .any(|e| matches!(&e.node, TypedExprNode::CollectionUnion(_))),
        );
    }
}
