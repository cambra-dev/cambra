//! The CCL expression AST: [`TypedExpr`] / [`TypedExprNode`], the
//! [`TypedBinding`] binding-site struct, the structural traversal helpers, and
//! the [`Branch`] / [`Pattern`] / [`TransactKey`] / [`WriterSite`] support
//! types.

use crate::ccl::provenance::NodeId;
use crate::ccl::{AggregateKind, BinOpKind, Builtin, Lit, Name, ProjKey, Type, UnaryOpKind};

/// The `commit` tag of a writer **decision variant** —
/// `` {`commit{𝑃} | `abort} ``. `𝑃` is the (dense) write/reply payload record
/// (`{writes, to_<defer>*}`); a committing position carries it. Both the
/// transaction writer and the induction writer build the same variant through
/// [`crate::ccl::ccl_utils::wrap_decision_variant`], and the runtime
/// (`body_decision_at`) decodes the tag: `commit` proposes the payload's writes,
/// `abort` denies (carry, no proposal).
pub const V_COMMIT: &str = "commit";
/// The `abort` tag of a writer **decision variant** — the nullary
/// whole-transaction deny (nothing fired). See [`V_COMMIT`].
pub const V_ABORT: &str = "abort";
/// The `writes` field of a [`WriterSite`] decision record — the positional
/// tuple of proposed per-key new values (`writes.i` for `write_keys[i]`), one
/// element even for a single-key write set.
pub const F_WRITES: &str = "writes";
/// Suffix of a **per-tap fire field** on a decision record. A reply tap
/// `to_<defer>_k` fed under one arm of cross-key *routing* (its control-flow
/// path is narrower than the transaction's overall `commit`) carries a companion
/// `to_<defer>_k__fire : Bool` field — its own path condition. The commit engine
/// appends the tap's value to the durable log only when the transaction commits
/// **and** the tap's fire field holds, so a feed under one route does not
/// over-fire on a sibling route's commit. Omitted when the tap's path *is* the
/// commit (a single-guard or spine feed always fires with its transaction), so
/// unconditional/single-guard programs keep their fire-field-free shape.
pub const F_FIRE_SUFFIX: &str = "__fire";

// Field names of a **commit-record** binding — the intermediate representation
// [`crate::ccl::transact_phase`] emits and [`crate::ccl::planning::plan_loops`]
// consumes. A commit-record binding `commits : 𝐼 ⇒ {time, write_targets, decision}`
// per `with begin():` site carries: the commit time `begin(r)` (`time`), the
// history bindings of the write-set keys (`write_targets`, so recognition can
// recover the writer's `write_keys` without a per-key merge), and the writer's
// verbatim `` {`commit{writes, to_<defer>*} | `abort} `` decision variant applied to
// the mutable variable snapshot at that time (`decision`). Only `write_targets`/`decision`
// reach recognition; `time` records the commit clock for the model's honesty.
/// The `time` field of a commit-record binding — the transaction's commit time
/// `begin(r)`, at which the writer's mutable variable snapshots are read.
pub const F_TIME: &str = "time";
/// The `write_targets` field of a commit-record binding — a positional tuple of
/// the write-set keys' history bindings (`write_targets.i` is the history of
/// `write_keys[i]`), the encoding recognition reads a site's `write_keys` off.
pub const F_WRITE_TARGETS: &str = "write_targets";
/// The `decision` field of a commit-record binding — the writer's verbatim
/// `` {`commit{writes, to_<defer>*} | `abort} `` decision variant, applied to the
/// mutable variable snapshot at the commit time. Recognition lifts the writer body out of it.
pub const F_DECISION: &str = "decision";
/// The `write` field of a **per-key commit view** — the single value a site's
/// commit proposes for one mutable variable key (`decision ▷ variant_project(`commit) ▷
/// .writes.i`, re-projected). A key's history binding searches the `⧺`-merged
/// per-key views of every site writing it: `{time, write}` per *committing*
/// transaction (the ``variant_project(`commit)`` eliminator drops `` `abort ``
/// positions), the exact record shape the design doc gives `get_prev_txn`'s
/// history argument.
pub const F_WRITE: &str = "write";

/// A typed binding site: a named variable together with its type.
///
/// Used in [`TypedExprNode::Lambda`] and [`TypedExprNode::Let`] to carry
/// both the inferred type and any user-written annotation at each binding site.
///
/// `ty` starts as [`Type::Hole`] (lowering placeholder) and is converted to a
/// registered [`Type::Infer`] variable at inference entry; inference then writes
/// **the type the binder is bound at** into it. `user_annotation` is a
/// *pre-inference input only* — lowering writes the source annotation there,
/// inference reconciles it and clears the slot, and no pass downstream may
/// observe one (`infer::api::debug_assert_annotations_cleared`). What survives the
/// clearing is nothing: mutability is answered by
/// [`TypedExprNode::MutDecl`] being the node that binds one.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedBinding {
    /// The bound variable name. Carries the binder's identity (`uid`) under
    /// the Barendregt convention; see [`Name`].
    pub name: Name,
    /// The type the binder is bound at.
    ///
    /// Starts as [`Type::Hole`] (lowering placeholder); converted to [`Type::Infer`]
    /// at inference entry and written to a concrete type by [`crate::ccl::infer::infer`].
    ///
    /// This is the type *references to the binder* have, which for an annotated
    /// binder is not necessarily its initializer's type: a deref-copy
    /// (`y: Int = x` off a mutable variable `x`) binds `y` at the value type, and a
    /// mutable variable introduction (`x: Mut(V) := init`) binds `x` at the history.
    /// Recording the initializer's type here instead is what forced the
    /// mutability checks to consult `user_annotation` as a proxy.
    pub ty: Type,
    /// User-written type annotation, if any — **cleared at the end of inference**.
    ///
    /// Set by lowering when the source carries an explicit type annotation
    /// (e.g. `x: Int = expr`). A `:=` introduction does *not* use this slot — its
    /// history rides the binder's `ty`, because [`TypedExprNode::MutDecl`] is a
    /// mutable variable introduction by construction. Inference reconciles the inferred type against it,
    /// raising [`crate::ccl::infer::InferError::AnnotationMismatch`] on conflict,
    /// then clears it — a retained annotation is a pre-inference marker that
    /// later passes can only misread.
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
    /// Use this at lowering time when the source carries an explicit type annotation
    /// (e.g. `x: Int = expr`). `ty` is still [`Type::Hole`] — the inference pass fills it in.
    pub fn new_annotated(name: impl Into<Name>, annotation: Type) -> Self {
        TypedBinding {
            name: name.into(),
            ty: Type::Hole,
            user_annotation: Some(annotation),
        }
    }

    /// Attach a user annotation to an already-constructed binding.
    pub fn declare(&mut self, annotation: Type) {
        self.user_annotation = Some(annotation);
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
    /// asserts that `value` may be viewed at `target`.  Every `target` lowering
    /// emits today is `Fun(Refinement(_, _), _)`: a function type whose domain
    /// carries a refinement predicate, so the cast attaches a refinement to a
    /// function's domain.  Lowering emits it for list-comprehension filters,
    /// for-loop `if`-guards, and `groupby` (see
    /// [`crate::ccl::ccl_utils::make_cast`]).  That is a fact about today's
    /// lowerings, not a contract: the one arm that *requires* the shape asserts
    /// it where it needs it ([`crate::ccl::lambda_elim`]'s cast-wrapped lambda).
    ///
    /// `Cast` is an **upcast**: the refined-domain function it produces is a
    /// supertype of `value`.  The refinement is attached *constructively* —
    /// inference's `emit_cast` decomposes `value`'s type and re-wraps its
    /// domain — rather than discharged as a `value_ty <: target`
    /// edge, because no such edge exists: the refinement lattice is strict
    /// (`unrefined ⊀ refined`), and the target lowering emits for a
    /// comprehension is a **data** function, whose domain is invariant rather
    /// than contravariant.  Re-wrapping stacks the refinement onto any the
    /// value already carries, so nested casts compose (nested list
    /// comprehensions).  `target`'s predicate is inferred by the
    /// same `emit_annotation_predicates` / `coalesce_type_predicates` path as
    /// any refinement-bearing type.  A *covariant* refinement (e.g. casting
    /// `Int` to `{Int | p}`) has no such construction and is rejected —
    /// acquiring a value-level refinement is a runtime/SMT-checked narrowing,
    /// not an upcast.
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
    /// Pure type-level assertion that `value` is the **executable realization** of a term
    /// typed `target` — a re-view the type system cannot prove, and is not asked to.
    ///
    /// Distinct from [`Cast`](Self::Cast), and the distinction is the whole point. A cast
    /// is an **upcast**: its typing rule is the subtype obligation `value_ty <: target`,
    /// discharged by the ordinary rules. This asserts an **isomorphism the rules cannot
    /// see**. Planning's realization of a conditional collection is the case: a `Case`
    /// typed `Σ (𝐷 : 𝐾). 𝐷 ⤇ 𝑉` becomes a gated union typed
    /// `Variant({𝑖: {𝐷ᵢ | π̂ᵢ}}) ⤇ 𝑉`, and those are genuinely different types — the sum
    /// picks one branch, the tagged union has rows from every leg. Only the gates make them
    /// agree, and no typing rule can check a gate. Routing that through `Cast` would mean
    /// claiming a subtype relation that does not hold.
    ///
    /// **Why it exists rather than rewriting the types above it.** Realization changes a
    /// subterm's type, and every enclosing mention of that type would otherwise have to
    /// follow — a chain that does not terminate, because the mentions are not all sums and
    /// not all reachable by one rule. Asserting the *original* type here means nothing
    /// above has to change at all.
    ///
    /// **What it does not cover.** A mention op-conversion *reads* — a comprehension's
    /// binder domain, which becomes the iteration extent — needs the realized type for
    /// real, not a re-view of the old one. This node is for mentions that are type-level
    /// only.
    ///
    /// Born after the type system is done (planning), so nothing infers it, and it carries
    /// **no target field**: the type it asserts is the node's own `ty`. A separate copy
    /// would be a second thing to keep in sync, and planning normalizes predicates in
    /// `ty` — a `Cast`'s `target` needs threading through exactly that walk, and this
    /// sidesteps it by not having one. At runtime it is a no-op: op-conversion compiles
    /// `value` and discards the wrapper.
    Realize(Box<TypedExpr>),

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

    /// Tagged variant constructor: `` `Tag(payload) ``.
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

    /// A transactional mutable variable: a set of scalar-variable **keys** sharing one
    /// sequencing domain, driven by concurrent **writers** that read the
    /// shared mutable variables and propose per-position writes.
    ///
    /// The **domain-parameterized recurrence carrier**, born in
    /// [`crate::ccl::planning::plan_loops`] and consumed at operator
    /// conversion. It denotes a pure value — the mutable variable **record** `{key:
    /// ⟦key⟧}`, each field a key's history `Fun(domain, V)` — so a variable
    /// read is the record projection `__hist.key` (an `Apply` of `Proj(field)`
    /// to the `__hist` binder). Serialization and the mutable variable↔writer cycle are
    /// the *operator's* runtime behaviour (a cyclic `FanOut`), not the node's
    /// denotation — exactly as the induction/commit store realizes the recurrence.
    ///
    /// Op-conversion dispatches on [`domain`](Self::Transact::domain): a
    /// concrete iteration domain → the position-driven `InductionStore` changelog
    /// (the induction case — one carry-complete, commit-gated writer, the
    /// no-conflict dual of the commit store); [`Type::Txn`] → the concurrent
    /// commit operator (multiple writers, serialize + retry).
    Transact {
        /// The mutable variable keys — one per scalar mutable variable sharing this carrier's
        /// sequencing domain. Each carries its position-0 `init` (the seed,
        /// evaluated once outside every writer's parameter scope). The node
        /// denotes the mutable variable **record** `{key.field_key(): Fun(domain, V)}`; a
        /// variable read is a projection `__hist.key`. A single-key carrier is
        /// the one-accumulator case.
        keys: Vec<TransactKey>,
        /// The writers, in declaration order. Each reads/writes a footprint of
        /// keys (its read-set / write-set) and proposes a per-position decision
        /// record. An induction-domain carrier has exactly one writer (a `mut`
        /// loop, whose footprint is all its accumulators).
        writers: Vec<WriterSite>,
        /// The carrier's **sequencing domain** — the index of every key's history
        /// `Fun(domain, V)`. A concrete iteration domain for a `mut`
        /// accumulator (the loop's induction domain); [`Type::Txn`] for a
        /// transactional commit clock (later increment). Op-conversion
        /// dispatches the engine on it.
        domain: Type,
    },

    /// A mutually recursive definition group:
    /// `letrec b₁ = e₁; …; bₙ = eₙ in body`.
    ///
    /// Every binding's name is in scope in **every** binding's body and in
    /// `body` — mutual recursion.  Well-formedness requires the recursion to
    /// be *guarded*: on every cycle of the group's reference graph at least
    /// one reference must go through a "previous value" accessor
    /// ([`Builtin::GetPrevSeq`], and later `get_prev_txn`), so values at any
    /// position of the sequencing domain depend only on strictly earlier
    /// positions.  [`crate::ccl::letrec::check_letrec_causal`] enforces
    /// this; see `src/ccl/design/mutability.md` ("The model: histories and causal recursion" / "`LetRec`").
    ///
    /// This is the general node for loops, transactions, and future
    /// recursive definitions: the unified phase (design doc, "The unified
    /// phase") rewrites every mutable variable's history, commit-record
    /// stream, and feed output into one letrec, and operator conversion
    /// *recognizes patterns* in the group (a `get_prev_seq`-guarded
    /// self-cycle is a fold; a commit-record binding read through
    /// `get_prev_txn` is a transactional mutable variable) to pick the engine.
    /// The induction `mut_elim` emits it for every mutation loop, and
    /// `transact_phase` emits it for every `Mut(V, Txn)` transaction block, both
    /// as causal groups. The group then travels — bodies point-freed — through
    /// `channelize` and `lambda_elim`; `planning::plan_loops` runs *after*
    /// `lambda_elim` on the point-free normal form and lowers every recognized
    /// group onto the domain-parameterized [`Transact`](Self::Transact) carrier.
    /// A `LetRec` therefore does not survive to planning — a group reaching
    /// op-conversion unrecognized is treated as unreachable rather than guessed.
    ///
    /// The node denotes a pure value (the unique solution of the causal
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
    /// (src/ccl/design/mutability.md, "mut_elim: eliminating overwrite mutability"). Lowering emits
    /// it for mutation loops whose bodies carry no feeds or yields; the
    /// phase rewrites it — with the [`TypedExprNode::MutWrite`]s inside —
    /// into a causal [`TypedExprNode::LetRec`]. No pass downstream of the
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

    /// A mutable variable's **introduction**: `x := init` (or `x: Mut(V, D) := init`),
    /// binding `x` as a mutable variable over `body`.
    ///
    /// The surface marker for the `:=` operator's *declaring* half, paired with
    /// [`TypedExprNode::MutWrite`] for its *writing* half. Both are eliminated by
    /// the unified phase (`transact_phase` / `mut_elim`), which turns the pair into
    /// one `letrec` recurrence (a loop-carried accumulator) or a chain of shadowing
    /// `Let`s (the degenerate sequential domain).
    ///
    /// **This is the only node that binds a mutable variable.** That is the point: it makes
    /// "is this binder mutable?" a question about the *node* rather than about a
    /// type that happened to survive inference. A [`TypedExprNode::Let`] cannot bind
    /// one — an initializer that is a mutable variable *reads* there (derefs), exactly as a
    /// mutable variable read does in any other value position — so no discipline rule is
    /// needed to reject the alias `b = a` would otherwise create. Before this node
    /// existed, an introduction was a `Let` carrying a `Mut` annotation, and every
    /// pass that needed to recognize one consulted that annotation as a proxy for
    /// the declaration.
    ///
    /// A `Lambda` param *can* still bind a mutable variable: that is pass-by-reference,
    /// where the mutable variable genuinely crosses a function boundary.
    MutDecl {
        /// The mutable variable's binder. Its `ty` is the history `Mut(V, D)`.
        binding: TypedBinding,
        /// The seed — the mutable variable's value at the first position of its domain.
        /// One *contribution* to `V`, not its definition: the value type is the
        /// join over the seed and every write.
        init: Box<TypedExpr>,
        /// The expression over which `binding.name` is a live mutable variable.
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
        /// The key written, for a write to one key of a mutable collection
        /// (`m[k] := v`); [`None`] for a whole-variable write (`x := v`).
        ///
        /// A scalar register's key is its variable name, which `name` already
        /// carries, so the two write forms differ in whether a *second* key sits
        /// below that one — which is what this option says. The store the write
        /// eliminates to is keyed either way.
        key: Option<Box<TypedExpr>>,
        /// The written value. For a whole-variable write it must be a subtype of
        /// the variable's type; for a keyed write, of the collection's codomain.
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
    /// pairwise nesting; [`TypedExpr::copair`] flattens at
    /// construction time so every `Copair` node in the tree
    /// satisfies the invariant **"no operand is itself a
    /// `Copair`"**.  Inference, lambda elimination, and
    /// operator conversion all rely on this — they never need to look
    /// through nested `Copair` AST nodes.  (Type-level
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
    /// `Apply(Tuple(ops), Builtin::Copair)` so the function
    /// can be lifted out point-free.  After lambda elimination, both
    /// shapes (this node and the `Builtin` form) may appear and both
    /// compile to the same `UnionOperator`.
    Copair(Vec<TypedExpr>),

    /// The **disjoint join** of collections that share one domain: `⊔ᵢ cᵢ`.
    ///
    /// A different operation from [`Self::Copair`], not a mode of it.
    /// Copairing takes collections to one over their *coproduct* —
    /// `(A ⤇ V) × (B ⤇ V) → (A + B) ⤇ V`, the universal property of the sum, always
    /// defined because the tags keep the operands apart. What distinguishes the two
    /// is the **result** domain, not whether the operand domains coincide: `x ++ x`
    /// is a copairing onto `A + A`, which is not `A`. A disjoint join
    /// takes collections that are *partial maps over the same* domain to one over
    /// that domain — `(D ⇀ V) × (D ⇀ V) → (D ⇀ V)` — and is defined **only when
    /// their domains are disjoint** (the join in the partial-function order, which
    /// exists iff the operands are compatible; separation logic's `*` on heaps is
    /// the same operation).
    ///
    /// So the two differ in signature, in result domain, and in definedness. The
    /// disjointness precondition is the whole content of this one, and is checked at
    /// the boundary that relies on it (`flat_merge`).
    ///
    /// Born **post-inference**, by the `Case` fan-outs in
    /// [`crate::ccl::lambda_elim`]: the arms of one `Case` restrict the *same* fed
    /// domain — by a first-match guard, or by tag — so their results must land back
    /// on it rather than on a coproduct. A writer decision, for instance, has to
    /// co-iterate with the sibling `commit` field of its own record.
    DisjointJoin(Vec<TypedExpr>),

    /// A plan expression, followed by another statement
    ExprStmt {
        expr: Box<TypedExpr>,
        body: Box<TypedExpr>,
    },

    /// Feed a value into a deferred output: `x << value`.
    /// Lowers from the `<<` (LShift) binary operator when the LHS names a defer.
    /// Has type `Unit`; the value is collected by [`crate::ccl::channelize`]
    /// and unioned into the source channel that resolves the defer.
    Feed { name: Name, value: Box<Expr> },

    /// Define a deferred output to a specific value: `x <<= value`.
    /// Lowers from the `<<=` (AugAssign LShift) statement when the LHS names a defer.
    /// Has type `Unit`; the value is collected by [`crate::ccl::channelize`]
    /// and replaces the surrounding `Defer` binding.
    Define { name: Name, value: Box<Expr> },

    /// Placeholder for an output accumulator introduced by `x = defer()`.
    /// The bound name is resolved by the surrounding `Let` binding.
    /// Eliminated by [`crate::ccl::channelize`] before type inference.
    Defer,

    /// A `with begin():` transaction block, as **one statement** (value `Unit`).
    /// `body` is the per-transaction statement chain lowering builds (a
    /// `Let`/`MutWrite`/`Case`/`Feed` chain ending in `Unit`) — the block's
    /// atomic writes, reads, guards, and per-commit feeds.
    ///
    /// A pre-phase surface marker in the same transient class as
    /// [`For`](TypedExprNode::For)/[`Feed`](TypedExprNode::Feed)/
    /// [`Defer`](TypedExprNode::Defer): it binds no name and carries no runtime
    /// behaviour. [`crate::ccl::transact_phase`] eliminates it wholesale —
    /// stripping each `Begin` (keyed on the enclosing loop) into a commit-record
    /// site — so it never reaches lambda elimination, recognition, or planning.
    /// Making the block a statement (rather than *being* the whole `For` body)
    /// is what lets one loop body mix a transaction with sibling induction
    /// writes and feeds.
    Begin { body: Box<TypedExpr> },

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

impl TypedExprNode {
    /// The variant's name as a stable, allocation-free string — for provenance /
    /// invariant diagnostics (e.g. the node-id uniqueness tripwire) that name a
    /// node by kind without dumping its contents. Exhaustive on purpose so a new
    /// variant forces an entry here.
    // Consumed by the id-uniqueness tripwires that land with pass adoption.
    #[allow(dead_code)]
    pub(crate) fn kind_name(&self) -> &'static str {
        match self {
            TypedExprNode::Lit(_) => "Lit",
            TypedExprNode::Var(_) => "Var",
            TypedExprNode::Builtin(_) => "Builtin",
            TypedExprNode::Apply { .. } => "Apply",
            TypedExprNode::Cast { .. } => "Cast",
            TypedExprNode::Realize(_) => "Realize",
            TypedExprNode::BinOp { .. } => "BinOp",
            TypedExprNode::UnaryOp { .. } => "UnaryOp",
            TypedExprNode::Lambda { .. } => "Lambda",
            TypedExprNode::Aggregate { .. } => "Aggregate",
            TypedExprNode::Let { .. } => "Let",
            TypedExprNode::MutDecl { .. } => "MutDecl",
            TypedExprNode::List(_) => "List",
            TypedExprNode::Case { .. } => "Case",
            TypedExprNode::VariantCtor { .. } => "VariantCtor",
            TypedExprNode::Transact { .. } => "Transact",
            TypedExprNode::LetRec { .. } => "LetRec",
            TypedExprNode::For { .. } => "For",
            TypedExprNode::MutWrite { .. } => "MutWrite",
            TypedExprNode::Tuple(_) => "Tuple",
            TypedExprNode::Proj(_) => "Proj",
            TypedExprNode::Record(_) => "Record",
            TypedExprNode::Source(_) => "Source",
            TypedExprNode::Compose(_) => "Compose",
            TypedExprNode::Copair(_) => "Copair",
            TypedExprNode::DisjointJoin(_) => "DisjointJoin",
            TypedExprNode::ExprStmt { .. } => "ExprStmt",
            TypedExprNode::Feed { .. } => "Feed",
            TypedExprNode::Define { .. } => "Define",
            TypedExprNode::Begin { .. } => "Begin",
            TypedExprNode::Defer => "Defer",
            TypedExprNode::Error => "Error",
        }
    }
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
/// `PartialEq` is hand-written (see the `impl` below) rather than derived: it
/// deliberately ignores `node_id`. Provenance is metadata, not part of a node's
/// value, so two structurally-equal nodes must compare equal even with distinct
/// ids.
#[derive(Debug)]
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
    /// Stable provenance identity for this node, minted fresh at construction
    /// (see [`crate::ccl::provenance`]). Excluded from [`PartialEq`] because
    /// provenance is metadata, not part of the node's value.
    ///
    /// **`Clone` freshens** (see the [`Clone`] impl below), so reaching a
    /// duplicated id takes writing one deliberately, through
    /// [`preserve`](Self::preserve).
    ///
    /// # What is forbidden is a mint, not a write
    ///
    /// `pub(super)` (visible within `crate::ccl`) so a pass can carry the id
    /// through a field-wise rebuild — see [`preserve`](Self::preserve) on why such
    /// a rebuild stays a struct literal. That is safe by construction: **a literal
    /// mints nothing**, so it cannot record a birth for an id no node carries.
    ///
    /// The hazard the constructors close is the *phantom birth* — minting an id
    /// and then overwriting it, so `on_mint` fires for an id that ends up on no
    /// node. That is now unrepresentable: `with_node_id` is deleted,
    /// [`freshen_node_id`](Self::freshen_node_id) is fresh-only, and there is no
    /// `set_node_id(arbitrary)`.
    ///
    /// So the thing to grep for is not a write to this field but
    /// `node_id: NodeId::fresh()` inside a literal — a *mint* that bypasses
    /// [`new`](Self::new) and therefore `on_mint`, giving a node an identity with
    /// no recorded birth. That is the exact dual of the phantom, and it is what
    /// makes the id-preserving literals worth reading carefully.
    pub(super) node_id: NodeId,
}

/// Type alias for backward compatibility. `Expr` is now [`TypedExpr`].
pub type Expr = TypedExpr;

/// Hand-written so that **a clone is a sibling, not the same node**: every node
/// it copies gets a freshly-minted [`NodeId`], and every `(origin, fresh)` pair
/// is reported to the ambient provenance recorder via
/// [`on_copy`](crate::ccl::provenance::on_copy).
///
/// A derived `Clone` would copy `node_id`, making every duplication site decide
/// whether to keep the id or freshen it. Freshening here removes the decision;
/// `src/ccl/design/provenance.md`, "Node identity" has what a wrong decision
/// costs.
///
/// **The named id-sharing paths.** Sharing an id takes writing one through
/// [`TypedExpr::preserve`] (one node at an id already in hand),
/// [`TypedExpr::clone_at`] (a subtree whose root carries a caller-supplied id
/// and whose interior freshens), [`TypedExpr::clone_preserving_ids`] (a subtree
/// at its source's ids), the
/// [`preserving_ids`](crate::ccl::provenance::preserving_ids) scope that backs
/// it — called directly by `PredMemo`'s rebuilds in `crate::ccl::ccl_utils` — or
/// the `*_preserving` constructors
/// ([`expr_stmt_preserving`](TypedExpr::expr_stmt_preserving),
/// [`let_in_preserving`](TypedExpr::let_in_preserving)), which are `preserve` in
/// convenience form. [`crate::ccl::subst`]'s `as_expr_preserving` reaches two of
/// them, landing a substituted occurrence's id on the replacement's root.
///
/// The freshen is deep by construction: `node.clone()` clones the children, and
/// each child is a `TypedExpr` reaching this same impl.
///
/// **Type slots are not freshened, and that is the rule, not an omission.** A
/// [`Type`] carries no identity: the only [`NodeId`]s reachable through one are
/// the `TypedExpr`s inside a `Refinement.predicate`, which is an
/// `Rc<TypedExpr>` — so `ty.clone()` bumps a refcount and reaches this impl not
/// at all. That is load-bearing twice over: a copy shares its source's predicate
/// terms, which is what `assert_unique_node_ids`' predicate walk dedups by `Rc`
/// to admit, and planning's compile memo is keyed on `Rc` identity, so splitting
/// the sharing would compile one predicate once per copy.
///
/// **`NodeId::PLACEHOLDER` is not preserved.** A [`throwaway`](TypedExpr::throwaway)
/// node is built to be rendered into a panic message, never cloned into a tree;
/// cloning one mints a real id, and `on_copy` drops the pair because its origin
/// is the sentinel. Nothing is recorded and nothing reaches a checked tree.
impl Clone for TypedExpr {
    fn clone(&self) -> Self {
        let node_id = crate::ccl::provenance::copy_id(self.node_id);
        TypedExpr {
            ty: self.ty.clone(),
            node: self.node.clone(),
            user_annotation: self.user_annotation.clone(),
            node_id,
        }
    }
}

/// Hand-written to **exclude `node_id`** from equality.
///
/// `node_id` is provenance metadata, not part of a node's value: two nodes that
/// are structurally equal as values must compare equal even when they carry
/// different ids. A derived `PartialEq` would instead make every freshly-minted
/// node compare unequal, breaking value-comparison in tests and pass logic.
/// Only `ty`, `node`, and `user_annotation` participate.
impl PartialEq for TypedExpr {
    fn eq(&self, other: &Self) -> bool {
        self.ty == other.ty
            && self.node == other.node
            && self.user_annotation == other.user_annotation
    }
}

impl TypedExpr {
    /// Construct a new [`TypedExpr`] with a [`Type::Hole`] placeholder and no user annotation.
    ///
    /// `Hole` is the lowering-phase placeholder. The inference pass converts it to a
    /// registered [`Type::Infer`] variable before type-checking begins.
    pub fn new(node: TypedExprNode) -> Self {
        let node_id = NodeId::fresh();
        crate::ccl::provenance::on_mint(node_id);
        TypedExpr {
            node,
            ty: Type::Hole,
            user_annotation: None,
            node_id,
        }
    }

    /// Construct a node at an **already-minted** identity: a *preserve*, the dual
    /// of [`new`](Self::new)'s mint.
    ///
    /// A pass that rebuilds a node — reparenting it, renaming a slot, moving it
    /// along a spine — is producing the same logical node at a new position, so
    /// its `NodeId` must carry over for its span and provenance to survive as a
    /// self-edge. Minting and then overwriting the id cannot express that: the
    /// mint fires [`on_mint`](crate::ccl::provenance::on_mint), so the log records a
    /// birth for an id that ends up on no node — a claim the fold cannot check,
    /// because its leak classes enumerate from the tree (see
    /// `design/provenance.md`, "The fold"). Entering the id at construction
    /// makes that unrepresentable rather than merely detectable.
    ///
    /// These are the only two ways to build a node, and the recorder sees exactly
    /// the difference: `new` mints and records a birth, `preserve` does neither.
    ///
    /// # Three shapes build a node at an existing id; only one of them is this
    ///
    /// **Reaching into another node for its id** — `node_id: src.node_id`, where
    /// `src` is some *other* node — is this constructor's shape, and the one where
    /// a stray `node_id: NodeId::fresh()` hides: a preserve and a mint differ by
    /// one token in otherwise identical five-line literals. Those sites are marked
    /// `TODO(preserve)` and are greppable: thirteen across five files —
    /// `channelize` (eight), `mut_elim` (two), and one each in `transact_phase`,
    /// `subst`, and `lambda_elim`. Eleven are this reach-for-another-id shape; the
    /// two in `subst` and `lambda_elim` ask a different question, whether their
    /// rebuild should mint or preserve at all.
    ///
    /// **A field-wise rebuild** — `let TypedExpr { node, ty, user_annotation,
    /// node_id } = expr;` then rebuilding with one child swapped — is *not* this
    /// shape and deliberately stays a struct literal. Nothing is reached for; the
    /// literal says "the same node, new child" in one expression, and its
    /// exhaustive field check is load-bearing: omit a field and it fails to
    /// compile, where `preserve(id, node).with_ty(…)` would silently default `ty`
    /// to [`Type::Hole`] — a type residue that surfaces, if at all, as a runtime
    /// assertion far away. Roughly three dozen such rebuilds live in
    /// `transact_phase`, `inline`, and `channelize`; converting them would trade a
    /// compile-time guarantee for a runtime one, once per site.
    ///
    /// **A copy at an id the tree already holds** — a subtree cloned, its root
    /// taking a caller-supplied id — is neither, and has its own primitive:
    /// [`clone_at`](Self::clone_at), whose one caller is
    /// [`crate::ccl::subst`]'s `as_expr_preserving`.
    pub(crate) fn preserve(node_id: NodeId, node: TypedExprNode) -> Self {
        TypedExpr {
            node,
            ty: Type::Hole,
            user_annotation: None,
            node_id,
        }
    }

    /// Construct a node that will **never enter a tree** — one built only to be
    /// rendered, typically inside a panic message or a `debug_assert!` probe.
    ///
    /// It carries [`NodeId::PLACEHOLDER`], the reserved throwaway identity, so it
    /// consumes no id and records no birth: a diagnostic must not perturb the
    /// provenance record it may be reporting on. `assert_unique_node_ids` backstops that
    /// a placeholder never reaches a checked tree.
    pub(crate) fn throwaway(node: TypedExprNode) -> Self {
        Self::preserve(NodeId::PLACEHOLDER, node)
    }

    /// The stable provenance id of this node (see [`crate::ccl::provenance`]).
    pub fn node_id(&self) -> NodeId {
        self.node_id
    }

    /// A deep copy at the **same identities** — the opt-out from the freshening
    /// [`Clone`], and the subtree analogue of [`preserve`](Self::preserve).
    ///
    /// Discouraged, and narrow: five shapes call it, each one a copy that
    /// denotes the same node as its source. Anywhere else a copy that duplicates
    /// ids is a bug an id-uniqueness assert will find later, and the fix is to
    /// **record** the freshened copy rather than to suppress the freshen —
    /// including when the symptom is a `Leak::Unrecorded` or a
    /// `Leak::DanglingParent`, which mean a copy was made with nothing recording
    /// or against an origin the table never recorded. Freshening everywhere and
    /// recording it costs no compile time and no meaningful memory, so the fix is
    /// at the copy site. See the vault's `freshening-clone-report`.
    ///
    /// # 1. A `Subst` discharge template
    ///
    /// A [`Subst`](crate::ccl::subst::Subst) discharge payload is never a tree
    /// node. Every read of it materializes a copy with its own identity —
    /// `Mapping::as_expr` a wholly fresh node-set, `as_expr_preserving` a fresh
    /// interior under the occurrence's own root — so copying the template itself
    /// must mint nothing, or each read strands the generation it copied from.
    /// Every site of this shape is either the argument to `Subst::discharge` or
    /// `Mapping`'s own `Clone` propagating one.
    ///
    /// # 2. A retained pane snapshot
    ///
    /// The three trees the inspector displays — `pre_inference_ir`,
    /// `post_inference_ir`, `post_channelize_ir` — are taken at their phase
    /// boundaries and kept. A pane exists to be joined to its neighbour by shared
    /// id, so freshening one would leave the fold nothing to join on. Source and
    /// copy are both live here and separately rooted, so neither is reachable
    /// from the other's tree and `assert_unique_node_ids` holds on each.
    ///
    /// # 3. A snapshot taken for rollback or comparison
    ///
    /// A copy the normal path discards, kept only so a failure or a later
    /// comparison has something to look at: lowering's per-statement rollback
    /// copy of the accumulated continuation (`lower_stmts_recovering`) and the
    /// post-inference type check's scratch tree (`infer::check::check`).
    /// Freshening them would mint whole trees for values nothing reads —
    /// quadratic in both cases; each site carries a `TODO` saying so, and the fix
    /// at both is to stop needing the copy at all.
    ///
    /// # 4. A test comparing trees across a phase
    ///
    /// A test that runs a phase over a copy and compares against the original
    /// needs the two to be the same nodes, or it is not testing the phase. See
    /// `uniquify`'s idempotence and id-stability tests.
    ///
    /// # 5. A move out of a borrow
    ///
    /// Where Rust forces a copy to get a value out of a map or a slice and the
    /// source is then dropped, the copy is the node it came from:
    /// `transact_phase`'s key-init stash, whose rewritten seed replaces the entry
    /// it was copied from, and its carrier binding list, borrowed from a plan
    /// that is placed exactly once. The discriminator is whether the source stays
    /// reachable, not whether the copy reaches the output — a copy that reaches
    /// the output beside a surviving source is a sibling and freshens.
    ///
    /// # Why this is sound
    ///
    /// In no shape are the source and the copy both reachable from one tree, so
    /// nothing ever observes two live nodes at one identity. A template is not a
    /// tree node; a pane is its own root; a rollback or test snapshot sits outside
    /// the tree the pipeline goes on rewriting; a move leaves nothing behind.
    pub(crate) fn clone_preserving_ids(&self) -> Self {
        let _preserving = crate::ccl::provenance::preserve_ids();
        self.clone()
    }

    /// A copy whose **root carries `node_id`** and whose interior is freshened —
    /// the root-carry primitive.
    ///
    /// The substitution engine's compound-replacement arm is the caller: the
    /// replacement for a `Var(𝑥)` occurrence denotes what the occurrence denoted
    /// — the value of 𝑥 *at that position* — so the occurrence keeps its own id,
    /// inheriting its span and attribution, while the interior becomes a fresh
    /// node-set. N reads give N distinct roots.
    ///
    /// The root is built directly at `node_id` rather than minted and then
    /// overwritten, so nothing is minted for it: a mint fires
    /// [`on_mint`](crate::ccl::provenance::on_mint), and an id no node ends up
    /// carrying is a phantom birth in the provenance record.
    ///
    /// The interior still freshens, because `node.clone()` reaches each child's
    /// own [`Clone`], so each child is a sibling of the template's and records as
    /// one.
    pub(crate) fn clone_at(&self, node_id: NodeId) -> Self {
        TypedExpr {
            ty: self.ty.clone(),
            node: self.node.clone(),
            user_annotation: self.user_annotation.clone(),
            node_id,
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

    /// Construct an ExprStmt expression — `expr; body`.
    ///
    /// The sequencing node's type **is** its body's, by construction: the
    /// statement's value is whatever the continuation evaluates to. Carrying it
    /// here holds that invariant in the module that defines the node, so a pass
    /// rebuilding a spine does not have to re-derive it. During lowering
    /// `body.ty` is [`Type::Hole`] and the carry is the identity; after inference
    /// it is the real type.
    pub fn expr_stmt(expr: Self, body: Self) -> Self {
        let ty = body.ty.clone();
        Self::new(TypedExprNode::ExprStmt {
            expr: Box::new(expr),
            body: Box::new(body),
        })
        .with_ty(ty)
    }

    /// [`expr_stmt`](Self::expr_stmt) at a **preserved** identity: the same
    /// logical statement rebuilt at a new spine position, carrying `node_id`
    /// rather than minting. See [`preserve`](Self::preserve).
    pub(crate) fn expr_stmt_preserving(node_id: NodeId, expr: Self, body: Self) -> Self {
        let ty = body.ty.clone();
        Self::preserve(
            node_id,
            TypedExprNode::ExprStmt {
                expr: Box::new(expr),
                body: Box::new(body),
            },
        )
        .with_ty(ty)
    }

    /// Construct a whole-variable write, `x := value`.
    pub fn mut_write(name: impl Into<Name>, value: Self) -> Self {
        Self::new(TypedExprNode::MutWrite {
            name: name.into(),
            key: None,
            value: Box::new(value),
        })
    }

    /// Construct a keyed write, `name[key] := value`.
    pub fn mut_write_keyed(name: impl Into<Name>, key: Self, value: Self) -> Self {
        Self::new(TypedExprNode::MutWrite {
            name: name.into(),
            key: Some(Box::new(key)),
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

    /// Construct a `with begin():` transaction-block marker over `body`.
    pub fn begin(body: Self) -> Self {
        Self::new(TypedExprNode::Begin {
            body: Box::new(body),
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

    /// `let binding = def in body`, typed as `body` — the pre-built-binding form
    /// of [`let_bind`](Self::let_bind), for passes that already hold a
    /// [`TypedBinding`] (a synthesized mutable variable, a rebuilt spine slot).
    ///
    /// As with [`expr_stmt`](Self::expr_stmt), the node's type is its body's: a
    /// `let` evaluates to its continuation.
    pub fn let_in(binding: TypedBinding, def: Self, body: Self) -> Self {
        let ty = body.ty.clone();
        Self::new(TypedExprNode::Let {
            binding,
            bound_expr: Box::new(def),
            body: Box::new(body),
        })
        .with_ty(ty)
    }

    /// [`let_in`](Self::let_in) at a **preserved** identity: the same logical
    /// binding rebuilt at a new spine position, carrying `node_id` rather than
    /// minting. See [`preserve`](Self::preserve).
    pub fn let_in_preserving(
        node_id: NodeId,
        binding: TypedBinding,
        def: Self,
        body: Self,
    ) -> Self {
        let ty = body.ty.clone();
        Self::preserve(
            node_id,
            TypedExprNode::Let {
                binding,
                bound_expr: Box::new(def),
                body: Box::new(body),
            },
        )
        .with_ty(ty)
    }

    /// Construct a [`TypedExprNode::MutDecl`] — a mutable variable introduction `x := init`.
    ///
    /// `history` is the binder's `Mut(V, D)` type: `V` the declared value type (a
    /// [`Type::Hole`] when it is to be inferred) and `D` the sequencing domain
    /// (`Txn` for a transactional mutable variable, a `Hole` for an induction accumulator
    /// whose domain the unified phase resolves).
    pub fn mut_decl(name: impl Into<Name>, history: Type, init: Self, body: Self) -> Self {
        Self::new(TypedExprNode::MutDecl {
            binding: TypedBinding {
                name: name.into(),
                ty: history,
                user_annotation: None,
            },
            init: Box::new(init),
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
    /// causality well-formedness condition
    /// ([`crate::ccl::letrec::check_letrec_causal`]).
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

    /// Construct an n-ary [`TypedExprNode::DisjointJoin`] expression.
    ///
    /// Unlike [`Self::copair`] this does **not** splice nested joins: a
    /// join of joins is not automatically one flat join, because flattening would
    /// silently merge two separately-established disjointness claims into one
    /// unchecked claim over the whole set.
    pub fn disjoint_join(operands: Vec<TypedExpr>) -> Self {
        assert!(
            !operands.is_empty(),
            "DisjointJoin requires at least one operand"
        );
        Self::new(TypedExprNode::DisjointJoin(operands))
    }

    /// Construct an n-ary [`TypedExprNode::Copair`] expression.
    ///
    /// `operands` must contain at least two collections.  Any operand
    /// that is itself a [`TypedExprNode::Copair`] is spliced
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
    pub fn copair(operands: Vec<Self>) -> Self {
        let flat: Vec<Self> = operands
            .into_iter()
            .flat_map(|op| match op.node {
                TypedExprNode::Copair(inner) => inner,
                _ => vec![op],
            })
            .collect();
        debug_assert!(
            flat.len() >= 2,
            "Copair requires at least two operands after flattening",
        );
        Self::new(TypedExprNode::Copair(flat))
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
    /// Lowering goes through [`crate::ccl::ccl_utils::make_cast`]; this is the
    /// bare constructor it builds on.
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
    /// Invoke `f` on each direct child [`TypedExpr`] of this node, in child
    /// order.
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
    ///
    /// This is the single immutable child-structure definition —
    /// [`child_exprs`](Self::child_exprs), [`any_child`](Self::any_child),
    /// [`all_children`](Self::all_children), and
    /// [`fold_children`](Self::fold_children) all route through it, so they
    /// cannot drift out of sync — and it allocates nothing, which is why it is
    /// the form the compile-path walks use.
    ///
    /// `f` receives each child borrowed for `&self`'s full lifetime rather than a
    /// shorter reborrow, so a child borrow may **escape** the closure into an
    /// enclosing binding. That is what lets a value-returning recursion (a
    /// find-by-id that yields `Option<&TypedExpr>`) go through this form instead
    /// of needing the allocating one.
    pub fn walk_children<'a>(&'a self, mut f: impl FnMut(&'a TypedExpr)) {
        match &self.node {
            TypedExprNode::Lit(_)
            | TypedExprNode::Var(_)
            | TypedExprNode::Builtin(_)
            | TypedExprNode::Proj(_)
            | TypedExprNode::Source(_)
            | TypedExprNode::Defer
            | TypedExprNode::Error => {}
            TypedExprNode::Apply { function, argument } => {
                f(function.as_ref());
                f(argument.as_ref());
            }
            TypedExprNode::Cast { value, .. } | TypedExprNode::Realize(value) => f(value.as_ref()),
            TypedExprNode::BinOp { left, right, .. } => {
                f(left.as_ref());
                f(right.as_ref());
            }
            TypedExprNode::UnaryOp(_, inner) => f(inner.as_ref()),
            TypedExprNode::Lambda { body, .. } => f(body.as_ref()),
            TypedExprNode::Aggregate { input, .. } => f(input.as_ref()),
            TypedExprNode::Let {
                bound_expr, body, ..
            } => {
                f(bound_expr.as_ref());
                f(body.as_ref());
            }
            TypedExprNode::MutDecl { init, body, .. } => {
                f(init.as_ref());
                f(body.as_ref());
            }
            TypedExprNode::List(elts)
            | TypedExprNode::Tuple(elts)
            | TypedExprNode::Compose(elts)
            | TypedExprNode::Copair(elts)
            | TypedExprNode::DisjointJoin(elts) => {
                for e in elts {
                    f(e);
                }
            }
            TypedExprNode::Case {
                scrutinee,
                branches,
            } => {
                if let Some(s) = scrutinee {
                    f(s.as_ref());
                }
                for b in branches {
                    f(&b.guard);
                    f(&b.body);
                }
            }
            TypedExprNode::VariantCtor { payload, .. } => f(payload.as_ref()),
            TypedExprNode::Record(fields) => fields.iter().for_each(|(_, e)| f(e)),
            // `domain` is a `Type`, not an `Expr` child, so the expr-walker
            // skips it (its type residue is reached via `expr.ty` walks). Child
            // order mirrors `walk_transact`: each key's init, then each writer's
            // source and body.
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
                f(body.as_ref());
            }
            TypedExprNode::For { iter, body, .. } => {
                f(iter.as_ref());
                f(body.as_ref());
            }
            TypedExprNode::ExprStmt { expr, body } => {
                f(expr.as_ref());
                f(body.as_ref());
            }
            TypedExprNode::Feed { value, .. } | TypedExprNode::Define { value, .. } => {
                f(value.as_ref())
            }
            // The key is a child like the value: it is an ordinary expression the
            // write evaluates, so every walk has to reach it or its nodes go
            // unvisited by uniquify, substitution, and the provenance fold.
            TypedExprNode::MutWrite { key, value, .. } => {
                if let Some(k) = key {
                    f(k.as_ref());
                }
                f(value.as_ref());
            }
            TypedExprNode::Begin { body } => f(body.as_ref()),
        }
    }

    /// Collect borrows of the direct child expressions, in
    /// [`walk_children`](Self::walk_children) order.
    ///
    /// Derived from `walk_children`, for the callers that want the children as a
    /// slice — to index them, enumerate them, or hand them to iterator
    /// combinators. It heap-allocates once per internal node, so prefer
    /// `walk_children` anywhere on the compile path; this form is for cold
    /// consumers (the inspector's snapshot queries).
    pub fn child_exprs(&self) -> Vec<&TypedExpr> {
        // Most nodes have ≤ 2 children; the few n-ary variants grow from there.
        let mut out = Vec::with_capacity(2);
        self.walk_children(|c| out.push(c));
        out
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

    /// Mutable analog of [`walk_children`](Self::walk_children): invoke `f` on
    /// each direct child Expr by mutable reference, in the same child order.
    ///
    /// The single mutable child-structure definition —
    /// [`fold_children_mut`](Self::fold_children_mut),
    /// [`map_children`](Self::map_children), and
    /// [`try_map_children`](Self::try_map_children) all route through it, and it
    /// allocates nothing. The immutable and mutable walkers are necessarily
    /// separate match arms (Rust's borrow rules forbid one `&`/`&mut`-generic
    /// body), so these two matches are the irreducible statement of the node's
    /// child structure, short of a codegen macro; a new child-bearing variant
    /// must appear in both.
    ///
    /// Same caveats as `walk_children`: does not descend through type refinement
    /// predicates and does not visit binder name/type fields. Pure-mutator passes
    /// that need to mutate `Lambda.param.ty`, `Let.binding.ty`, or the refinement
    /// predicate must handle those explicitly before (or after) calling this
    /// method.
    pub fn walk_children_mut<'a>(&'a mut self, mut f: impl FnMut(&'a mut TypedExpr)) {
        match &mut self.node {
            TypedExprNode::Lit(_)
            | TypedExprNode::Var(_)
            | TypedExprNode::Builtin(_)
            | TypedExprNode::Proj(_)
            | TypedExprNode::Source(_)
            | TypedExprNode::Defer
            | TypedExprNode::Error => {}
            TypedExprNode::Apply { function, argument } => {
                f(function.as_mut());
                f(argument.as_mut());
            }
            // Only `value` is an expression child; `target` is a type (its
            // refinement predicate is reached via type walks, not here).
            TypedExprNode::Cast { value, .. } | TypedExprNode::Realize(value) => f(value.as_mut()),
            TypedExprNode::BinOp { left, right, .. } => {
                f(left.as_mut());
                f(right.as_mut());
            }
            TypedExprNode::UnaryOp(_, inner) => f(inner.as_mut()),
            TypedExprNode::Lambda { body, .. } => f(body.as_mut()),
            TypedExprNode::Aggregate { input, .. } => f(input.as_mut()),
            TypedExprNode::Let {
                bound_expr, body, ..
            } => {
                f(bound_expr.as_mut());
                f(body.as_mut());
            }
            TypedExprNode::MutDecl { init, body, .. } => {
                f(init.as_mut());
                f(body.as_mut());
            }
            TypedExprNode::List(elts)
            | TypedExprNode::Tuple(elts)
            | TypedExprNode::Compose(elts)
            | TypedExprNode::Copair(elts)
            | TypedExprNode::DisjointJoin(elts) => {
                for e in elts {
                    f(e);
                }
            }
            TypedExprNode::Case {
                scrutinee,
                branches,
            } => {
                if let Some(s) = scrutinee {
                    f(s.as_mut());
                }
                for b in branches {
                    f(&mut b.guard);
                    f(&mut b.body);
                }
            }
            TypedExprNode::VariantCtor { payload, .. } => f(payload.as_mut()),
            TypedExprNode::Record(fields) => fields.iter_mut().for_each(|(_, e)| f(e)),
            // `domain` is a `Type`, not an `Expr` child (see `walk_children`).
            // Child order mirrors `walk_transact`.
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
                f(body.as_mut());
            }
            TypedExprNode::For { iter, body, .. } => {
                f(iter.as_mut());
                f(body.as_mut());
            }
            TypedExprNode::ExprStmt { expr, body } => {
                f(expr.as_mut());
                f(body.as_mut());
            }
            TypedExprNode::Feed { value, .. } | TypedExprNode::Define { value, .. } => {
                f(value.as_mut())
            }
            TypedExprNode::MutWrite { key, value, .. } => {
                if let Some(k) = key {
                    f(k.as_mut());
                }
                f(value.as_mut());
            }
            TypedExprNode::Begin { body } => f(body.as_mut()),
        }
    }

    /// Invoke `f` on each [`TypedBinding`] this node introduces directly — the
    /// binder slots [`walk_children_mut`](Self::walk_children_mut) deliberately
    /// does **not** visit: a `Lambda`/`Let`/`For` binder, each `LetRec` group
    /// binder, and each `Case` branch's pattern binder. Does not recurse into
    /// child expressions.
    ///
    /// This is the single source of truth for "which nodes bind names", so a
    /// pass that must cover every binder's slot (a type-erasing pass, an
    /// α-renamer, `uniquify`'s post-pass mint check) enumerates them here rather
    /// than re-deriving the set. The match is **exhaustive with no wildcard
    /// arm**, deliberately and for the same reason
    /// [`crate::ccl::scope::for_each_scoped_item`] is: a `_ => {}` catch-all
    /// would make a newly-added binding form silently invisible to every such
    /// pass, which is exactly the failure mode both walks exist to prevent.
    /// Whether the two agree on the declaration set is a test in
    /// `crate::ccl::scope`.
    ///
    /// Immutable analog of [`walk_binders_mut`](Self::walk_binders_mut), which
    /// is kept in lockstep — a new binder-bearing variant appears in both.
    pub fn walk_binders<'a>(&'a self, mut f: impl FnMut(&'a TypedBinding)) {
        match &self.node {
            TypedExprNode::Lambda { param, .. }
            | TypedExprNode::Let { binding: param, .. }
            | TypedExprNode::MutDecl { binding: param, .. }
            | TypedExprNode::For { target: param, .. } => f(param),
            TypedExprNode::LetRec { bindings, .. } => {
                bindings.iter().for_each(|(b, _)| f(b));
            }
            TypedExprNode::Case { branches, .. } => {
                for b in branches {
                    if let Some(p) = &b.pattern {
                        f(&p.binding);
                    }
                }
            }
            // Declares no binder. Enumerated rather than wildcarded — see above.
            TypedExprNode::Lit(_)
            | TypedExprNode::Var(_)
            | TypedExprNode::Builtin(_)
            | TypedExprNode::Proj(_)
            | TypedExprNode::Source(_)
            | TypedExprNode::Defer
            | TypedExprNode::Error
            | TypedExprNode::Apply { .. }
            | TypedExprNode::Cast { .. }
            | TypedExprNode::Realize(_)
            | TypedExprNode::BinOp { .. }
            | TypedExprNode::UnaryOp(..)
            | TypedExprNode::Aggregate { .. }
            | TypedExprNode::VariantCtor { .. }
            | TypedExprNode::List(_)
            | TypedExprNode::Tuple(_)
            | TypedExprNode::Record(_)
            | TypedExprNode::Compose(_)
            | TypedExprNode::Copair(_)
            | TypedExprNode::DisjointJoin(_)
            | TypedExprNode::ExprStmt { .. }
            | TypedExprNode::Begin { .. }
            | TypedExprNode::Feed { .. }
            | TypedExprNode::Define { .. }
            | TypedExprNode::MutWrite { .. }
            | TypedExprNode::Transact { .. } => {}
        }
    }

    /// Mutable analog of [`walk_binders`](Self::walk_binders) — same
    /// declaration set, same deliberate exhaustiveness.
    pub fn walk_binders_mut(&mut self, mut f: impl FnMut(&mut TypedBinding)) {
        match &mut self.node {
            TypedExprNode::Lambda { param, .. }
            | TypedExprNode::Let { binding: param, .. }
            | TypedExprNode::MutDecl { binding: param, .. }
            | TypedExprNode::For { target: param, .. } => f(param),
            TypedExprNode::LetRec { bindings, .. } => {
                bindings.iter_mut().for_each(|(b, _)| f(b));
            }
            TypedExprNode::Case { branches, .. } => {
                for b in branches {
                    if let Some(p) = &mut b.pattern {
                        f(&mut p.binding);
                    }
                }
            }
            // Declares no binder. Enumerated rather than wildcarded — see
            // [`walk_binders`](Self::walk_binders).
            TypedExprNode::Lit(_)
            | TypedExprNode::Var(_)
            | TypedExprNode::Builtin(_)
            | TypedExprNode::Proj(_)
            | TypedExprNode::Source(_)
            | TypedExprNode::Defer
            | TypedExprNode::Error
            | TypedExprNode::Apply { .. }
            | TypedExprNode::Cast { .. }
            | TypedExprNode::Realize(_)
            | TypedExprNode::BinOp { .. }
            | TypedExprNode::UnaryOp(..)
            | TypedExprNode::Aggregate { .. }
            | TypedExprNode::VariantCtor { .. }
            | TypedExprNode::List(_)
            | TypedExprNode::Tuple(_)
            | TypedExprNode::Record(_)
            | TypedExprNode::Compose(_)
            | TypedExprNode::Copair(_)
            | TypedExprNode::DisjointJoin(_)
            | TypedExprNode::ExprStmt { .. }
            | TypedExprNode::Begin { .. }
            | TypedExprNode::Feed { .. }
            | TypedExprNode::Define { .. }
            | TypedExprNode::MutWrite { .. }
            | TypedExprNode::Transact { .. } => {}
        }
    }

    /// Invoke `f` on every [`Type`] slot this node carries **directly**: its own
    /// `ty`, its `user_annotation`, a [`TypedExprNode::Cast`]'s `target`, a
    /// [`TypedExprNode::Transact`]'s `domain`, and — for every binder it introduces
    /// ([`walk_binders`](Self::walk_binders)) — both that binder's `ty` **and** its
    /// `user_annotation`. Does not recurse into child expressions.
    ///
    /// This is the single source of truth for "which type slots a node carries",
    /// and it exists because those slots are **independent** values: a refinement
    /// riding a lambda's domain also rides `param.ty`, and a cast's refinement
    /// rides both `ty` and `target`, but each slot holds its *own* immutable
    /// predicate `Rc`. So a pass that rewrites or measures predicates must reach
    /// all of them — `ty` alone silently misses the slot a comprehension filter's
    /// predicate actually lives in (`Cast.target`, which downstream
    /// `lambda_elim` and operator conversion read). Enumerate here rather than
    /// re-deriving the set per pass: a new type-slot-bearing variant then updates
    /// one place instead of every such pass, and a pass cannot acquire a blind
    /// spot by omission.
    ///
    /// **A binder's annotation is a slot, not decoration**, even though it is a
    /// short-lived one: lowering writes the user's declared type there and
    /// inference clears it ([`TypedBinding::user_annotation`]). Any pass that runs
    /// *before* inference completes — and lowering's own rewrites — therefore has a
    /// binder annotation to reach, and a walk that visits only `b.ty` misses every
    /// predicate riding one.
    ///
    /// **Coverage is exact — every variant, no exceptions**, including a
    /// [`TypedExprNode::Transact`]'s `domain`. A `Transact` is born by
    /// `planning::plan_loops` and its sequencing domain is the extent of the source
    /// it iterates, refinements and all, so a `mut` accumulator over a filtered
    /// collection carries that filter's predicate there as well as on every other
    /// slot the same extent reaches. `planning::compile_refinement_predicates`
    /// rewrites predicates through this walk, and the post-planning `typecheck`
    /// compares refinements by structural equality, so a domain this walk skipped
    /// would hold the bare predicate while its siblings hold the compiled one and
    /// the carrier's own type would contradict its `domain`. The exhaustiveness
    /// this claims is checked, not asserted:
    /// `walk_type_slots_covers_every_carried_type_slot`.
    ///
    /// Callers that also need slots reachable *through* a type (a `Fun` domain, a
    /// refinement predicate's own type slots) compose this with
    /// [`Type::walk_children`] — see
    /// [`crate::ccl::ccl_utils::distinct_predicate_rcs`].
    pub fn walk_type_slots<'a>(&'a self, mut f: impl FnMut(&'a Type)) {
        f(&self.ty);
        if let Some(annotation) = &self.user_annotation {
            f(annotation);
        }
        if let TypedExprNode::Cast { target, .. } = &self.node {
            f(target);
        }
        if let TypedExprNode::Transact { domain, .. } = &self.node {
            f(domain);
        }
        self.walk_binders(|b| {
            f(&b.ty);
            if let Some(annotation) = &b.user_annotation {
                f(annotation);
            }
        });
    }

    /// Mutable analog of [`walk_type_slots`](Self::walk_type_slots), for passes
    /// that rewrite type slots in place. Kept in lockstep with it — any new
    /// type-slot-bearing variant must appear in both.
    pub fn walk_type_slots_mut(&mut self, mut f: impl FnMut(&mut Type)) {
        f(&mut self.ty);
        if let Some(annotation) = &mut self.user_annotation {
            f(annotation);
        }
        if let TypedExprNode::Cast { target, .. } = &mut self.node {
            f(target);
        }
        if let TypedExprNode::Transact { domain, .. } = &mut self.node {
            f(domain);
        }
        self.walk_binders_mut(|b| {
            f(&mut b.ty);
            if let Some(annotation) = &mut b.user_annotation {
                f(annotation);
            }
        });
    }

    /// Does this node declare any binder? The cheap half of
    /// [`walk_binders`](Self::walk_binders), for callers that only need to know
    /// whether a node opens a scope at all (see
    /// [`crate::ccl::scope::for_each_scoped_item_mut`], which skips its
    /// scope-collection pass entirely for the overwhelmingly common node that
    /// binds nothing).
    pub fn binds_any(&self) -> bool {
        let mut binds = false;
        self.walk_binders(|_| binds = true);
        binds
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
        // Built *literally*, not via `Self::new`: a `mem::take` throwaway must
        // not fire `on_mint` and pollute an open recording. It carries the
        // reserved `PLACEHOLDER` id (never minted, ignored by `on_mint`) and is
        // always immediately overwritten, so it never reaches a checked tree.
        // Every default node shares this id, so two defaults compare equal (as
        // they already did — `node_id` is excluded from `PartialEq`).
        TypedExpr {
            node: TypedExprNode::Lit(Lit::Int(0)),
            ty: Type::Hole,
            user_annotation: None,
            node_id: NodeId::PLACEHOLDER,
        }
    }
}

/// One key of a [`TypedExprNode::Transact`] — a single scalar mutable variable sharing
/// the mutable variable's sequencing domain.
#[derive(Debug, Clone, PartialEq)]
pub struct TransactKey {
    /// The key — the (α-uniquified) `Name` of the mutable variable. A read of the
    /// variable projects [`Name::field_key`] of the history record (`__hist.k`).
    pub name: Name,
    /// The position-0 initial value (the scalar seed), evaluated once outside
    /// every writer's scope. The key's history is `Fun(domain, V)`; a read is
    /// its latest value `V` (`final_or_default(history, init)`, defaulting to
    /// `init` when the mutable variable ran zero positions).
    pub init: TypedExpr,
}

/// One writer of a [`TypedExprNode::Transact`] — loop-shaped, mirroring a
/// mutation-loop accumulator arm but reading the *shared* mutable variables rather than a
/// private accumulator.
#[derive(Debug, Clone, PartialEq)]
pub struct WriterSite {
    /// The writer's **read-set**: the mutable variable keys whose snapshot value the body
    /// reads, in body-parameter order. The body is fed `(snap_{k₀}, …,
    /// snap_{k_{r-1}}, item)` — each `read_keys[i]` bound as position `i` — so
    /// an in-body read of a mutable variable resolves to its snapshot by lexical
    /// shadowing (the accumulator pattern, generalized to several keys).
    pub read_keys: Vec<Name>,
    /// The writer's **write-set**: the mutable variable keys the body proposes new values
    /// for, in the order of the decision's `writes` tuple (`writes.i` is the
    /// new value for `write_keys[i]`).
    pub write_keys: Vec<Name>,
    /// Iteration source — a `Fun(D, item)` whose domain drives this writer and
    /// whose codomain elements are passed to [`Self::body`]. Sits *outside* the
    /// snapshot-parameter scope.
    pub source: TypedExpr,
    /// The per-position decision — ``Fun(Tuple(snap…, item), {`commit{writes: Tuple(new…), to_<defer>*} | `abort})``: reads the mutable variable snapshot and returns
    /// a grant/deny variant — `` `commit `` carries the (dense) per-key write set and
    /// any per-position `to_<defer>` feed taps; `` `abort `` is the whole-transaction
    /// deny (carry, no proposal). An induction (`mut`-loop) position `` `commit ``s
    /// unless every branch carries (a full non-writing position `` `abort ``s).
    pub body: TypedExpr,
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
/// receives its payload — `` `Tag(binder) ``, the destructuring form mirroring
/// [`TypedExprNode::VariantCtor`]'s construction.
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
    ///
    /// Always present, including for an arm whose source named no payload: the name is
    /// then a reserved spelling nothing can refer to. [`Self::empty_payload`] carries
    /// what the source said about the payload's type; the presence of this does not.
    pub binding: TypedBinding,
    /// Whether the arm asserts the tag carries **nothing**: the surface `` case
    /// `tag: ``, as against `` case `tag(_): ``, which has a payload it does not read.
    ///
    /// The claim is about the type, so it is a constraint rather than a formality.
    /// `` `some{Int} `` and `` `some `` are different types, and an arm that names no
    /// payload does not match the first. `emit_case` records it as `payload <: Unit` on
    /// that arm alone, which lets the rejection name the arm.
    pub empty_payload: bool,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(name: &str) -> TypedExpr {
        TypedExpr::var(name)
    }

    /// `Copair([a, b])` with no nested operands is preserved as-is.
    #[test]
    fn copair_flat_input_is_unchanged() {
        let result = TypedExpr::copair(vec![leaf("a"), leaf("b")]);
        let TypedExprNode::Copair(ops) = result.node else {
            panic!("expected Copair node");
        };
        assert_eq!(ops.len(), 2);
        assert!(
            !ops.iter()
                .any(|e| matches!(&e.node, TypedExprNode::Copair(_))),
            "operands must be flat"
        );
    }

    /// `((a ++ b) ++ c)` (left-nested) flattens to a flat 3-ary node.
    #[test]
    fn copair_flattens_left_nested() {
        let ab = TypedExpr::copair(vec![leaf("a"), leaf("b")]);
        let abc = TypedExpr::copair(vec![ab, leaf("c")]);
        let TypedExprNode::Copair(ops) = abc.node else {
            panic!("expected Copair node");
        };
        assert_eq!(ops.len(), 3);
        assert!(
            !ops.iter()
                .any(|e| matches!(&e.node, TypedExprNode::Copair(_))),
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
    fn copair_flattens_right_nested() {
        let bc = TypedExpr::copair(vec![leaf("b"), leaf("c")]);
        let abc = TypedExpr::copair(vec![leaf("a"), bc]);
        let TypedExprNode::Copair(ops) = abc.node else {
            panic!("expected Copair node");
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
    fn copair_flattens_double_nested() {
        let ab = TypedExpr::copair(vec![leaf("a"), leaf("b")]);
        let abc = TypedExpr::copair(vec![ab, leaf("c")]);
        let abcd = TypedExpr::copair(vec![abc, leaf("d")]);
        let TypedExprNode::Copair(ops) = abcd.node else {
            panic!("expected Copair node");
        };
        assert_eq!(ops.len(), 4);
        assert!(
            !ops.iter()
                .any(|e| matches!(&e.node, TypedExprNode::Copair(_))),
        );
    }

    /// Every `Type` a node carries *directly* is reached by
    /// [`TypedExpr::walk_type_slots`] — or is a named, justified exception.
    ///
    /// Stamps a distinct `Type::DataSource` marker into each slot and asserts the
    /// walk reports exactly the expected set. A marker is used rather than a real
    /// type because the point is slot *reachability*, not type content.
    ///
    /// The full inventory of directly-carried `Type`s in the AST: `TypedExpr.ty`,
    /// `TypedExpr.user_annotation`, `TypedBinding.ty`, `TypedBinding.user_annotation`,
    /// `TypedExprNode::Cast.target`, and `TypedExprNode::Transact.domain`. The walk
    /// covers all six.
    #[test]
    fn walk_type_slots_covers_every_carried_type_slot() {
        fn marker(name: &str) -> Type {
            Type::DataSource(name.into())
        }
        fn reached(e: &TypedExpr) -> Vec<String> {
            let mut seen = Vec::new();
            e.walk_type_slots(|ty| {
                if let Type::DataSource(n) = ty {
                    seen.push(n.to_string());
                }
            });
            seen.sort();
            seen
        }

        // A binder-bearing node: node type + annotation, binder type + annotation.
        let mut lam = TypedExpr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "x".into(),
                ty: marker("param_ty"),
                user_annotation: Some(marker("param_annotation")),
            },
            body: Box::new(TypedExpr::lit(Lit::Unit)),
        });
        lam.ty = marker("node_ty");
        lam.user_annotation = Some(marker("node_annotation"));
        assert_eq!(
            reached(&lam),
            vec!["node_annotation", "node_ty", "param_annotation", "param_ty"],
            "a binder's annotation carries a mutable variable's history — see \
             `walk_type_slots`"
        );

        // `Cast` carries a target beyond its own type.
        let mut cast = TypedExpr::cast(TypedExpr::lit(Lit::Unit), marker("cast_target"));
        cast.ty = marker("node_ty");
        assert_eq!(reached(&cast), vec!["cast_target", "node_ty"]);

        // A `Transact` carries its sequencing domain beyond its own type, and that
        // domain holds the iterated source's refinements — the predicates
        // `planning::compile_refinement_predicates` rewrites through this walk.
        let mut txn = TypedExpr::new(TypedExprNode::Transact {
            keys: Vec::new(),
            writers: Vec::new(),
            domain: marker("transact_domain"),
        });
        txn.ty = marker("node_ty");
        assert_eq!(reached(&txn), vec!["node_ty", "transact_domain"]);
    }
}
