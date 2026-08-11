# CCL IR — the typed AST

The intermediate representation between CHL source and the dataflow operator graph: the `TypedExpr`/`Type` node vocabulary, the invariants every pass relies on, and the design rationale behind the node set. For where the IR sits in the pipeline, see the [hub](README.md); for the passes that produce and consume it, see [lowering.md](lowering.md), [type-inference.md](type-inference.md), and [optimization.md](optimization.md).

CCL is a λ-calculus–based IR: CHL source is lowered into CCL, where it is type-inferred and optimized, then compiled to the operator graph for execution.

---

## Key design decisions

### Purity invariant: CCL is a pure value language

**Every `TypedExprNode` variant must denote a pure value.  Effects belong at the program boundary, not inside the AST.**

No `TypedExprNode` variant may carry runtime behaviour executed by the CCL pipeline (type inference, lambda elimination, planning, simplification).  Side-effecting operations — I/O, network calls, sink dispatch — are modelled as data-source/sink registrations in `LoweringContext` and assembled at the boundary by `compile_program` in `ccl/context.rs`.

For example, an effectful `Sink` node embedding an I/O dispatch would let optimization passes duplicate or reorder it — silently skipping or double-firing responses. Sink dispatch is instead modelled as a pure `Defer` placeholder plus an out-of-band sink-binding registry in `LoweringContext`, with `compile_program` assembling the `SinkConsumer` at the boundary after the pipeline runs.

If you find yourself adding a variant that "does something" rather than representing a value, model the effect at the boundary instead.

### Less normalized than ANF

CCL is a λ-calculus IR, not strict A-Normal Form. In ANF every intermediate result must be named with a `Let` binding; in CCL compound expressions may appear inline. For example, `Apply(f, BinOp(x, Add, y))` is valid without an intermediate binding for `x + y`.

`Let` bindings are available for naming intermediate results (required by the type checker and useful for debugging), but are not mandatory.

Rationale: strict ANF over-normalizes the tree, destroying structural information needed for optimization passes (reordering, equivalency checks, fusion).

### Structured names and α-uniquification (Barendregt convention)

Binder and variable names are a structured `Name` enum (`ccl/names.rs`), not a bare string. The four ways a name comes to exist are four variants, so the case a site handles is a `match` arm rather than a magic-value check:

- **`Raw(String)`** — what lowering builds; identity is contextual by scope (two source binders can share a spelling).
- **`Unique { base, uid }`** — a uniquified *source* binder; identity is the globally-fresh `uid`, `base` is the source spelling kept as display metadata. Minted at uniquification for every source binding site.
- **`Synthetic { kind, uid }`** — a *compiler-introduced* binder (`kind ∈ {Pair, Mono, FloatedDefer, SolverArg}`); it carries its own globally-fresh `uid` for identity (only the `Mono` kind additionally carries a nested `Name` as provenance). Operationally identical to `Unique` (globally distinct, capture-free) — it differs only in *provenance*: minted by a pass, not written by the user. That keeps `Unique`'s invariant exact ("after uniquification every binder is `Unique`" — a `Synthetic` there is a pass minting too early) and `Unique.base` trustworthy as a real identifier. The solver's dependent-application binder (`__arg`) is a `SolverArg` synthetic, not a `Unique`.
- **`Reserved(ReservedName)`** — a name with custom semantics; the only one is the refinement element binder `__elem`, the single shared name every refinement binds (which is what makes refinement equality plain structural equality of bare predicates).

Symbolic output prints `Name::base()` for every variant; `Debug` surfaces the `uid` for `Unique`. Identity decisions are `match`es on the variant, never string comparison (e.g. `n.is_elem()`, not `n.base() == "__elem"`).

Lowering itself does not rename: CHL reassignment of the same variable (`x = 1; x = 2`) produces nested `Let` bindings that shadow each other, with both binders spelled `x`. Immediately after lowering, the **uniquify pass** (`ccl/uniquify.rs`) mints a globally fresh uid at every binding site and resolves each bound reference to the binder that lexically binds it:

```
let x#1 = 1
in let x#2 = 2   ← same spelling, its own binder identity
in x#2
```

After uniquification, shadowing ceases to exist for every downstream pass: plain structural equality on terms coincides with α-equivalence, so refinement-predicate comparisons need no scope analysis. The convention is *unique binding sites at lowering; copying preserves uids; no pass mints fresh uids on an equality-mediated path* — passes that duplicate terms (discharges, monomorphization splices, lowering's own clone of comprehension generator sources into the loop-join predicate) copy minted names verbatim, so copies compare equal by construction. Two *independently lowered* α-equivalent terms do **not** compare equal; the one place lowering needed that (the loop-join source clone), it pre-mints the subtree before cloning (see `ccl/uniquify.rs` module docs, "mint before copy").

Renaming happens at the name level only — the tree shape is untouched, so this does not over-normalize the way strict ANF or SSA conversion would.

### Binding structure lives in one place

Which children a node's binders scope over is stated once, in `ccl/scope.rs`'s `for_each_scoped_item`: it visits each direct child paired with the binders in scope for it, plus the name *occurrences* the node makes itself. Every scope-aware walk in the crate is a fold over it — free-occurrence counting (`ccl_utils`'s `count_free`, `count_free_in_value`), free-variable collection (`subst`'s `collect_expr_fv`), and capture-avoiding substitution (`Subst::rewrite_expr`, via the `for_each_scoped_item_mut` adapter).

The rules themselves:

- `Lambda` — `param` scopes over `body`.
- `Let` — `binding` scopes over `body` only; `bound_expr` is outside it (CCL's `let` is non-recursive).
- `LetRec` — every group binder scopes over every binding's definition and over `body`.
- `For` — `target` scopes over `body`; `iter` is outside.
- `Case` — each branch's `pattern.binding` scopes over that branch's `guard` and `body`, and nothing else.
- `Feed` / `Define` / `MutWrite` — the `name` field is a *use* of the binder it names, not a binder.
- `Transact` — introduces no binder; its keys are labels of the register record the node denotes, so they are surfaced as a distinct occurrence kind that free-*variable* analyses skip while an identity-sensitive consumer still folds them in.

Every `match` that decides one of these rules is exhaustive with **no wildcard arm**, deliberately: before this existed, the walkers ended in `_ => walk_children(..)`, so a new binding form compiled clean in all of them and silently got the wrong scope in every one. Now it is a compile error until the new form declares its scope. That covers three matches, each closing the same failure mode at a different layer:

- `for_each_scoped_item` — which children each binder scopes over.
- `for_each_scoped_item_mut`'s name half — which names a node mentions of its own, so that a rename retargets a new node's name reference instead of walking past it. Its agreement with the immutable walk is a corpus test.
- `TypedExpr::walk_binders` — the enumeration of binding *slots*, which the scoped walk is checked against and which `uniquify`'s post-pass mint assertion runs on. A wildcard here would let a new binding form be invisible to the assertion that is supposed to catch a forgotten mint.

Two passes stay outside the fold and say why in their own docs: `ccl/uniquify.rs` *mints* binders rather than observing them, and substitution's transport mode (`Subst::apply_expr_inner`) rebuilds nodes rather than walking them.

A scope is a type, `Binders`, not a collected list of binder references: it borrows the node's binder slots in place, so the walk allocates nothing even for a `LetRec` group — which matters because it sits under `is_free`, and substitution consults that once per mapped binder per node. `Binders` also owns `shadows`, the question every consumer actually asks, so "does this scope shadow this name" is answered once rather than at each fold.

Consumers may rely on three properties of the walk, each asserted in `scope.rs`'s tests: the `Child` items come in `walk_children` order (so the `&mut` walk can pair scopes with children positionally), the binders it declares are exactly `walk_binders`', and a scope's children are consecutive with a binder-introducing scope entered only once. The last is what lets a consumer build per-scope state once per scope rather than once per child, and the `&mut` walk hands it the change point directly, as a `Scope` item ahead of the run of children it covers. Substitution needs both halves of that: restricting the substitution across the scope (`Subst::shadow_all`, which borrows instead of cloning whenever the scope names nothing the substitution acts on) and the Barendregt no-capture check, which is release-active and walks every replacement term — so a `LetRec` group of *n* binders owes *n* checks, and paying per child instead would cost *n*(*n*+1).

### Application shape

Function application is a single `Apply(Box<Expr>, Box<Expr>)` node. Single-argument CHL calls `f(a)` lower to `Apply(a, Var(f))` directly. Multi-argument CHL calls `f(a, b, ...)` lower to `Apply(Tuple([a, b, ...]), Var(f))` — the arguments are tupled so the call shape matches how multi-arg CHL lambdas are uncurried at lowering time (see [lowering.md](lowering.md)).

Partial / curried application in CCL itself is still represented by chained `Apply` nodes — `f(x)(y)` in source writes the curry explicitly and lowers to `Apply(y, Apply(x, Var(f)))`. This path is not currently supported past operator conversion (no `curry` combinator case yet) and is tracked as follow-up work; in normal CHL source, chained applications only arise when users nest lambdas explicitly.

Rationale: keeping application a single-argument node preserves the uniform λ-calculus basis, while the tupled-lowering convention lets the common multi-arg case compile cleanly through `lambda_elim` and operator conversion without threading a curry/uncurry combinator through every pass.

### Lambda/Apply encoding of collection iteration

Collection iteration (list comprehensions) is encoded with the existing `Lambda` and `Apply` nodes rather than a dedicated iteration node: `[f(x) for x in xs]` lowers to the map-lambda applied to the collection (`xs ▷ (λ x → f(x))`), with the parameter `x` ranging over the collection's extent. Reusing `Lambda`/`Apply` preserves the uniform λ-calculus basis — whether a lambda maps over a collection or simply receives one argument is a property of what it is applied to, not a mode stored on the node.

Lambdas do not survive to the dataflow graph: [lambda elimination](optimization.md#lambda-elimination-ccllambda_elimrs) rewrites the applied map-lambda to point-free combinators, which [operator conversion](optimization.md#compilation) then turns into extent-iterating tile operators. See also [/docs/operational-semantics/lowering.md](/docs/operational-semantics/lowering.md).

### `MutDecl` — the register introduction

`x := init` lowers to `MutDecl { binding, init, body }`, the surface marker for the
declaring half of `:=` (`MutWrite` is its writing half). Both are erased by the
unified phase, which turns the pair into one `letrec` recurrence or a chain of
shadowing `Let`s.

It is a node rather than a flag on `Let` because the two have different lifetimes:
`Let` survives the whole pipeline, while a register introduction is compiled away.
And it is the **only** node that binds a register — a `Let` cannot, because
`emit_let` derefs a register-typed initializer, so `b = a` binds `b` at `a`'s value.
That is what makes register-ness structural: a pass asks which node it is looking
at, not whether a type or an annotation survived inference.

### `Cast` — explicit refinement acquisition

`Cast { value, target }` is a type conversion that re-views `value` as the type `target`. It is a node (not a `Builtin`) because it has its own typing rule and its own structural shape — modelling it as `Apply(value, Cast)` with the target hidden on `user_annotation` forced every traversal to special-case the `Apply`-with-Cast-head pattern and read the target out of a side field. The node makes both the value child and the target type first-class.

Lowering ([`ccl_utils::make_cast`]) emits it for list-comprehension filters, for-loop `if`-guards, and `groupby`. The only `target` shape lowering produces today is `Fun(Refinement(_, 𝑝), _)`: a function type whose domain carries the predicate `𝑝`, so the cast attaches a refinement to a collection function's domain. `target` is the lowering-time *specification* (its domain/codomain are typically `Type::Hole`, carrying only the refinement); the resolved cast type lands on `expr.ty` after inference — the same `user_annotation`-vs-`ty` split used elsewhere.

`Cast` is an **upcast**: its whole typing rule is the single subtype obligation `value_ty <: target`. For the domain refinement lowering emits, that holds by contravariance — `(𝐷 ⇒ 𝑉) <: ({𝐷 | 𝑝} ⇒ 𝑉)` because `{𝐷 | 𝑝} <: 𝐷` — so viewing an unrefined-domain collection function at a refined-domain type is sound. A *covariant* refinement (casting `Int` to `{Int | 𝑝}`) correctly *fails* the check — acquiring a value-level refinement is a runtime/SMT-checked narrowing, not an upcast. How the solver discharges the refinement obligation — flowing the demanded refinement onto the target-domain variable and stacking it so chained casts compose — is covered in [type-inference.md](type-inference.md#45-dependent-refinements-via-pi-types).

`lambda_elim`, planning, and operator conversion carry the domain refinement through to a runtime `Restrict`: a `Cast` around a group-by lambda becomes a **Pi-const** form whose refinement planning's pointful group-by recognizer reads off the predicate, while a `Cast` wrapping point-free filter/guard code survives lambda elimination unchanged and is consumed as a domain refinement at planning — see [optimization.md](optimization.md). The current `Cast` only honours domain-refinement targets; the direction for a general `𝑈 ⇒ 𝑇` cast is in [type-inference.md](type-inference.md#6-future-work).

### `Case` only — no `IfThenElse`

CHL `if/else`, `elif` chains, and ternary `if` expressions are all lowered to `Case` during CHL → CCL lowering. There is no `IfThenElse` node in the CCL AST. `Case` subsumes all multi-way branching.

`Case { scrutinee: Option<Box<TypedExpr>>, branches: Vec<Branch> }` holds an ordered list of `Branch { pattern: Option<Pattern>, guard, body }` values; guards are arbitrary `TypedExpr` nodes constrained to `Bool` at inference time, and the first truthy guard wins. The `if`/`elif` path is the degenerate case — `scrutinee: None` with `pattern: None` on every branch. `elif` chains arrive **already flattened**: the CHL parser stores an `if`/`elif`/`else` chain as a single `Stmt::If { branches, else_body }` (one entry per `if`/`elif`, no nested `orelse`), and `lower_if` walks that flat branch list, emitting one guard-only `Branch` per entry plus a final `true`-guarded else — so `if c1: … elif c2: … else: …` produces `{ c1 → …; c2 → …; true → … }`. Structural pattern decomposition is represented as `Let` bindings in arm bodies; literal matching is an equality guard expression.

CHL `match` statements (planned) will desugar entirely at lowering time: the scrutinee is bound with a fresh `Let(__scrut)` node, then each arm produces a guard (`__scrut == lit` for literal patterns, `Lit(true)` for wildcard/structural) and a body (with `Let` bindings for any captured variable names). No IR changes are needed for `match` support.

### `Transact` — the domain-parameterized recurrence carrier

CHL mutation-accumulation `for` loops **and** `with begin():` transactions share one carrier node, `Transact`, rather than recursive `Lambda`/`Let` combinations or a dedicated fold node. (For the lowering mechanics and the operator-graph realization, see [lowering.md](lowering.md#mutation-accumulation-loops) and [mutability.md](mutability.md).)

`Transact { keys, writers, domain }` denotes a **transactional register**: a set of scalar-register `keys` sharing one sequencing `domain`, driven by concurrent `writers` that read the shared registers and propose per-position writes. It denotes a *pure value* — the register record `{key: Fun(domain, V)}`, each field a key's history — so a variable read is the projection `__reg.key`; the register↔writer cycle is the operator's runtime behaviour, not the node's denotation (exactly as the induction/commit store realizes a recurrence). Each key carries its position-0 `init` (evaluated once outside every writer's parameter scope); an induction-domain carrier has exactly one writer (a `mut` loop, whose footprint is all its accumulators).

`Transact` is **born in `planning::plan_loops`** (from the causal `LetRec` the mutability phase emits — see below) and consumed at operator conversion, which **dispatches on `domain`**: a concrete iteration domain → the position-driven `InductionStore` changelog (the induction case — one always-commit or commit-gated writer, whose footprint is all its accumulators); `Type::Txn` → the concurrent commit operator (the transactional slice — multiple writers, serialize + retry). Loop planning runs **after `lambda_elim`**, on the group's point-free normal form — it anchors on the causal accessors (`get_prev_seq` / `get_prev_txn` / `begin_<site>`), which survive elimination, so one `LetRec` travels from the mutability phase through `channelize` and `lambda_elim` and is planned point-free; `Transact` is then loop planning's *output* carrier from there to op-conversion (op-conversion is lambda-free, and planning stages the carrier's writer sources). There is no `Jump` node: `while` loops with explicit restart/break are future work.

Rationale: planning post-elim retires the old pointful/point-free double representation (one `LetRec`, not a pointful group re-derived into a point-free one); the `Transact` carrier makes the register structure available to planning and op-conversion, and unifying loops and transactions on one node lets both domains share the one planning→conversion path.

### `LetRec` — causal mutually recursive definition groups

`LetRec { bindings: Vec<(TypedBinding, TypedExpr)>, body }` is a mutually recursive definition group: every binding's name is in scope in **every** binding's body and in `body`. It is the node the mutability/transactions/feeds redesign targets — a mutable variable's history becomes an ordinary letrec binding whose recurrence reads *strictly earlier* positions through a guard accessor (`get_prev_seq` for an induction domain; `get_prev_txn` for the transaction domain). The full model is [mutability.md](mutability.md); the essentials for the AST reference:

- **The unified letrec phase** (`ccl/mut_elim.rs` for induction, `ccl/transact_phase.rs` for `Txn`; after inlining, before `channelize`) emits one `LetRec` per mutation loop / transaction: the accumulators (or per-key histories) become a history binding `𝐷 ⇒ {step, to_<feed>*}` made causal by `get_prev_seq` (induction) or `get_prev_txn` (`Txn`), trailing reads become `final_or_default`, and each in-loop feed is hoisted to an ordinary `Feed(defer, __hist ▷ .to_<feed>)`. `planning::plan_loops` then lowers each group onto the `Transact` carrier above, so planning and op-conversion run unchanged.
- **Well-formedness is causality** (`ccl/letrec.rs`): on every cycle of the group's reference graph at least one edge must sit in a `get_prev_*` accessor's history slot. Op-conversion errors on a raw `LetRec` or an applied `GetPrevSeq` — loop planning consumes them; a non-causal group is a compile error, never a silent fallback.
- **Scoping** is mutual throughout: uniquify mints all group binders before walking any body, and substitution/freeness treat a matching group binder as shadowing everywhere inside the group.

Symbolic rendering: `letrec 𝑏₁ = 𝑒₁; …; 𝑏ₙ = 𝑒ₙ in body`.

### `TypedExpr` — type slot on every node

Every CCL expression is wrapped in `TypedExpr { node: TypedExprNode, ty: Type, user_annotation: Option<Type> }`.

- `node` holds the expression kind (the `TypedExprNode` enum).
- `ty` starts as `Type::Hole` (stamped by `TypedExpr::new()`); the inference pass converts it to a registered `Type::Infer` variable then fills it with the concrete type before compilation.
- `user_annotation` carries an explicit annotation from the source (e.g. a `cast` call). It is a **pre-inference input**: inference reconciles the inferred type against it, records the outcome in `ty`, and then clears the slot, so no pass downstream observes one. A binder additionally carries `declared` — the one fact about its annotation that outlives it. See `src/ccl/design/type-inference.md`, "The binder slot, and why annotations do not outlive inference".

### `Type::Hole`, `Type::Infer`, `Type::History`, and `Type::ChanDom` — the transient variants

The type system uses distinct transient placeholders with strict ownership:

| Variant | Owner | Meaning | Eliminated by |
|---|---|---|---|
| `Type::Hole` | Lowering | "This slot needs a type; not yet known" | Constraint emission  |
| `Type::Infer(id)` | Type checker only | "Inference variable N, produced by the solver" | Constraint solution |
| `Type::History { value, domain, kind }` | Type checker only | The unified history handle: a function `domain ⇒ value` plus a `HistoryKind` marker (`Overwrite` = mutable variable, displayed `Mut(value, domain)`; `Feed` = deferred-output channel, displayed `feed(domain ⇒ value)`) | `Overwrite` by mut_elim (overwrite) / `transact_phase` (Txn); `Feed` by `channelize` — both erased to a bare `Type::Fun` before `operator_conversion` |
| `Type::ChanDom(d)` | Type checker only | A defer channel's *rigid nominal domain*, minted per `let d = defer()`, so channel reads type concretely at inference with no `Infer` residue | `channelize` (`erase_chan_domains` substitutes the assembled channel domain) |

**`Type::Hole`** is stamped by `TypedExpr::new()` and `TypedBinding::new_unannotated()`. It is a structural placeholder that carries no identity. The inference pass eliminates all `Hole` placeholders and replaces them with concrete types or `Type::Infer` variables. `fresh_infer_var_id()` must not be called from lowering code; use `Type::Hole` instead.

**`Type::Infer(id)`** is produced by the inference pass (`ccl/infer/`) when a type cannot yet be determined. Any `Infer` remaining after inference represents an ambiguous type. Inference is the sole creator of `Infer` variables; lowering always uses `Type::Hole`. A defer channel's domain is *not* an `Infer` — it is a rigid `Type::ChanDom` typed at inference (see below), so no re-typing pass is needed to resolve it.

**`Type::History`** collapses what were once two separate variants (`Type::Mut` and `Type::Feed`) into one `domain ⇒ value` function distinguished only by a two-valued `HistoryKind` (`Overwrite | Feed`) — see [`Mut` is a CCL type](mutability.md#mut-is-a-ccl-type) and [`Feed` is a CCL type](mutability.md#feed-is-a-ccl-type). A mutable variable derefs on read to the scalar `value` (carry-forward terminal, scalar-last read); a feed reads as its whole stream `domain ⇒ value`. Both are erased before `operator_conversion`, so no history type survives to planning.

**`Type::ChanDom`** carries its introduction level (an identity-transparent `ChanLevel`) and freshens like a quantified variable, so a defer minted inside a generalized generator names a distinct channel per specialization. `channelize` closes the tree by the pure whole-tree substitution `erase_chan_domains` — the feed-side analog of the mutable-elimination phase's `erase_mut`.

This separation makes test expression construction straightforward: tests that build expressions without running inference use `Type::Hole` (via `TypedExpr::new()`) and never need to synthesize `InferVarId` values.
---

## Temporary Hacks
The following are temporary simplifications that we implemented for expediency, but expect to clean up later.

### `Aggregate` — first-class aggregation node

CHL aggregate calls (`sum(xs)`, `max(xs)`) are lowered directly to `Expr::Aggregate` rather than kept as `Apply(Var("sum"), xs)`. This makes aggregate operations structurally distinct from ordinary function calls, which simplifies:

- Type inference: each variant has a full operator scheme in `OperatorSchemes` that captures its element-vs-output-type relationship — `Sum : ∀α. (α ⇒ Int) ⇒ Int` (requires an `Int` codomain, returns `Int`) and `Max : ∀α γ. (α ⇒ γ) ⇒ γ` (returns the codomain unchanged). `emit_aggregate` infers the input type and applies the scheme directly to it via `apply_unary_scheme`; the scheme's own domain shape `(α ⇒ γ)` enforces that the input is a function and folds its codomain, so no separate "input must be a function" check is needed.
- Compilation: the compiler dispatches on `Expr::Aggregate` and emits the appropriate aggregate operator without scanning call-site variable names.

`AggregateKind` enumerates the supported operations; each variant's typing rule is the operator scheme selected by `OperatorSchemes::aggregate`. New variants (`Count : ∀α. (α ⇒ γ) ⇒ Int`, …) add a scheme there without touching the `Aggregate` inference branch.

---

## Source injection

Sources need to be available to all stages of compilation, so they are tracked in a `GlobalContext` struct which produces references to the other types of contexts.

Each phase of compilation needs different information about the sources: lowering needs just the names, inference needs the types, and compilation needs to track the materialized extents so that they are shared across references to the same source.
