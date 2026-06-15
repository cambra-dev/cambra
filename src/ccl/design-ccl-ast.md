# CCL AST Design

Design decisions for the Cambra Core Language (CCL) abstract syntax tree — the intermediate representation between CHL source and the dataflow operator graph.

---

## Overview

CCL is a λ-calculus–based IR. CHL source is lowered into CCL, where it is type-inferred and optimized, then compiled to the operator graph for execution.

```
CHL source
  → parse          (chl_parser)
  → lower          (ccl/lower.rs: CHL AST → CCL AST, structural only)
  → desugar_defers (ccl/desugar_defers.rs: eliminate Defer/Feed/Define nodes; see §Defer)
  → infer          (ccl/infer.rs: type inference via simple-sub; delegates to ccl/infer_simple_sub.rs)
  → inline         (ccl/inline.rs::inline_non_iterable_lambdas: inline UDF Let bindings with non-iterable domains; beta-reduce at call sites)
  → lambda_elim    (ccl/lambda_elim.rs: Lambda → point-free combinators)
  → optimize       (tree rewrites on CCL AST, currently just planning.rs)
  → convert        (interpreter/operator_conversion.rs: CCL AST → tile operators)
  → subscribe()
  → producer/consumer dataflow
```

---

## Key Design Decisions

### Purity invariant: CCL is a pure value language

**Every `TypedExprNode` variant must denote a pure value.  Effects belong at the program boundary, not inside the AST.**

No `TypedExprNode` variant may carry runtime behaviour executed by the CCL pipeline (type inference, lambda elimination, planning, simplification).  Side-effecting operations — I/O, network calls, sink dispatch — are modelled as data-source/sink registrations in `LoweringContext` and assembled at the boundary by `compile_program` in `ccl/context.rs`.

Historical violation: `TypedExprNode::Sink(String)` embedded an I/O dispatch operation in the AST.  Optimization passes could duplicate or reorder the node, silently skipping or double-firing responses.  The fix was to remove `Sink` and replace the pattern with a `Defer` placeholder (pure) plus an out-of-band sink-binding registry in `LoweringContext`.  `compile_program` extracts the sink expression after the full pipeline runs and wires up the `SinkConsumer` at the boundary.

If you find yourself adding a variant that "does something" rather than representing a value, model the effect at the boundary instead.

### Less normalized than ANF

CCL is a λ-calculus IR, not strict A-Normal Form. In ANF every intermediate result must be named with a `Let` binding; in CCL compound expressions may appear inline. For example, `Apply(f, BinOp(x, Add, y))` is valid without an intermediate binding for `x + y`.

`Let` bindings are available for naming intermediate results (required by the type checker and useful for debugging), but are not mandatory.

Rationale: strict ANF over-normalizes the tree, destroying structural information needed for optimization passes (reordering, equivalency checks, fusion).

### Structured names and α-uniquification (Barendregt convention)

Binder and variable names are a structured `Name` enum (`ccl/names.rs`), not a bare string. The four ways a name comes to exist are four variants, so the case a site handles is a `match` arm rather than a magic-value check:

- **`Raw(String)`** — what lowering builds; identity is the string (two source binders can share a spelling).
- **`Unique { base, uid }`** — a uniquified *source* binder; identity is the globally-fresh `uid`, `base` is the source spelling kept as display metadata. Minted at uniquification for every source binding site.
- **`Synthetic { kind, name }`** — a *compiler-introduced* binder (`kind ∈ {Pair, Mono, ShadowRename, FloatedDefer, SolverArg}`); identity is the mangled `name`. Operationally identical to `Unique` (globally distinct, capture-free) — it differs only in *provenance*: minted by a pass, not written by the user. That keeps `Unique`'s invariant exact ("after uniquification every binder is `Unique`" — a `Synthetic` there is a pass minting too early) and `Unique.base` trustworthy as a real identifier. The solver's dependent-application binder (`__arg`) is a `SolverArg` synthetic, not a `Unique`.
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

### Application shape

Function application is a single `Apply(Box<Expr>, Box<Expr>)` node. Single-argument CHL calls `f(a)` lower to `Apply(a, Var(f))` directly. Multi-argument CHL calls `f(a, b, ...)` lower to `Apply(Tuple([a, b, ...]), Var(f))` — the arguments are tupled so the call shape matches how multi-arg CHL lambdas are uncurried at lowering time (see "CHL `lambda` expressions" below).

Partial / curried application in CCL itself is still represented by chained `Apply` nodes — `f(x)(y)` in source writes the curry explicitly and lowers to `Apply(Apply(Var(f), x), y)`. This path remains unsupported past operator conversion (no `curry` combinator case yet) and is tracked as follow-up work; in normal CHL source, chained applications only arise when users nest lambdas explicitly.

Rationale: keeping application a single-argument node preserves the uniform λ-calculus basis, while the tupled-lowering convention lets the common multi-arg case compile cleanly through `lambda_elim` and operator conversion without threading a curry/uncurry combinator through every pass.

### Lambda/Apply encoding of collection iteration

Collection iteration (list comprehensions) is encoded using the existing `Lambda` and `Apply` nodes.

The operator graph's Iteration/Argument mode distinction is captured by the way the graph is constructed:

- `Lambda::subscribe()` (no binding) → `VarSource::Iteration` — variable iterates over its extent
- `Lambda::subscribe_to_application(binding)` → `VarSource::Argument` — variable receives from a binding
- `Apply::subscribe()` always calls `subscribe_to_application`, forcing Argument mode

The same distinction applies in CCL:

| CCL node | Compilation path | Operator graph |
|----------|-----------------|---------------|
| Standalone `Lambda` (not inside `Apply`) | `subscribe()` (if execution is forced)| `VarSource::Iteration` |
| `Apply(lambda, collection)` | `subscribe_to_application(collection)` | `VarSource::Argument` |
| `Aggregate { input: xs, kind: Sum }` | `compile_aggregate` | aggregate operator |

### `Aggregate` — first-class aggregation node

CHL aggregate calls (`sum(xs)`, `max(xs)`) are lowered directly to `Expr::Aggregate` rather than kept as `Apply(Var("sum"), xs)`. This makes aggregate operations structurally distinct from ordinary function calls, which simplifies:

- Type inference: each variant has a full operator scheme in `OperatorSchemes` that captures its element-vs-output-type relationship — `Sum : ∀α. (α ⇒ Int) ⇒ Int` (requires an `Int` codomain, returns `Int`) and `Max : ∀α γ. (α ⇒ γ) ⇒ γ` (returns the codomain unchanged). `emit_aggregate` infers the input type and applies the scheme directly to it via `apply_unary_scheme`; the scheme's own domain shape `(α ⇒ γ)` enforces that the input is a function and folds its codomain, so no separate "input must be a function" check is needed.
- Compilation: the compiler dispatches on `Expr::Aggregate` and emits the appropriate aggregate operator without scanning call-site variable names.

`AggregateKind` enumerates the supported operations; each variant's typing rule is the operator scheme selected by `OperatorSchemes::aggregate`. New variants (`Count : ∀α. (α ⇒ γ) ⇒ Int`, `Mean : ∀α. (α ⇒ Int) ⇒ Float`, …) add a scheme there without touching the `Aggregate` inference branch.

### CHL `lambda` expressions — single `Expr::Lambda` (tupled when multi-arg)

CHL `lambda` expressions lower to a single `Expr::Lambda`. A single-parameter `lambda x: body` becomes `λ x → body`. A multi-parameter `lambda x, y, ...: body` is **uncurried at lowering**: it becomes `λ __arg_tuple_N → body[x := __arg_tuple_N.0, y := __arg_tuple_N.1, ...]`, a single-parameter lambda whose parameter is a synthetic tuple and whose body has each named argument replaced in-place by a projection of that tuple. `param.ty` starts as `Type::Hole`; inference resolves it (including the tuple arity for the multi-arg case) from the body's projection constraints and the call-site argument type.

Each multi-arg lambda mints a fresh `N` from a counter on `LoweringContext`, so nested multi-arg lambdas (e.g. `lambda x, y: lambda a, b: x + a`) receive distinct tuple-parameter names. Without the unique suffix, an outer substitution that inserts `Var("__arg_tuple")` into an inner lambda's body would be captured by the inner binder; the fresh suffix plus the reserved `__arg_tuple_` prefix (user code cannot bind double-underscore names here) keeps the in-place substitution non-capture-avoiding yet correct.

Rationale for uncurrying: a curried `λ x → λ y → body` lowering would trigger `lambda_elim`'s nested-lambda rule and produce `curry(body)`, which operator conversion cannot compile. Uncurrying at lowering pairs with the tupled call lowering above so that syntactic multi-arg functions compile without any `curry` combinator appearing in the tree. Users who want genuine partial application still write `lambda x: lambda y: ...` or `curry(f)` explicitly — those produce curried types and are tracked as follow-up work.

In-place substitution (rather than wrapping the body in `let xi = __arg_tuple_N.i`) avoids introducing function-typed `Let` nodes that `lambda_elim`'s Let rule would lift to `ParamTy ⇒ T` and compile into zip-of-projections morphisms that current simplification cannot reduce back to a bare morphism.

Restrictions not yet supported (lowering raises `LoweringError::Unsupported`): `*args`, `**kwargs`, keyword-only arguments, and default values.

### Function definitions — `Let` + single `Expr::Lambda` (tupled when multi-arg)

CHL `def` statements are lowered to `Let` bindings whose value is a single `Expr::Lambda`, mirroring the `lambda`-expression shape above. `def f(x): body` becomes `let f = λ x → lower(body) in ...`; `def f(x, y, ...): body` uncurries to `let f = λ __arg_pair → lower(body)[x := __arg_pair.0, y := __arg_pair.1, ...] in ...`. The function name is bound via `Expr::let_bind`, and the body is lowered via `lower_stmts` (supporting assignments, nested function definitions, and a final expression).

Pairing the definition shape with `lower_call`'s tupled multi-arg shape keeps the common multi-arg `def` path free of the curried-lambda chain that `lambda_elim` would fold into an unsupported `curry(body)`.

### Generator functions — `Compose+Lambda` with `defer`/`feed` desugaring

Generator functions (functions whose body ends in a `for` loop containing `yield`) are lowered directly to `Compose([source, Lambda(x, body)])`, combined with the existing `defer`/`feed` operators. There is no separate `For` AST node — for-loops are desugared at lowering time to the same `Compose+Lambda` shape already used by list comprehensions and generator expressions.

**Yield desugaring** (lowering, `lower_generator_for`): a `yield expr` terminal is replaced with `feed(__result, expr)` and the whole loop is wrapped:
```text
def f(params):
    for x in iter:
        yield expr
```
becomes:
```text
let f = λ params →
    let __result = defer
    in (iter ≫ λx → feed(__result, expr)); __result
```

**`<<` feeds inside for-loops** (no `yield`): a `for` whose body ends in `x << expr` lowers to a bare `Compose([source, Lambda(x, body)])` with `Unit` type — no `defer` wrapper is needed because the caller already holds the defer binding.

**Nested `for` loops** produce nested `Compose+Lambda` pairs. Lambda elimination converts each Lambda outward-in to a composition chain.

**Mutation accumulation loops** (`x = 0; for i in src: x += i; x`) are detected in `lower.rs` and lowered to a [`TypedExprNode::Loop`] node rather than a `For` node.  `lower_middle_stmt` calls `find_mutation_loop_vars` (which scans the body for *every* outer-scope name that gets mutated, in first-mention order — handles `x = x + i; o << x` shapes and multi-accumulator bodies like `y = y + i; x = x * i`), then `lower_mutation_loop` builds:

```text
let x = Loop {
  params: [x],
  init_args: [Var(x)],          // outer x's pre-loop value
  source: <iteration source>,
  loop_body: λ p → let x = p ▷ Proj(0) in
                   let i = p ▷ Proj(1) in
                   step,
} in body
```

`lower_mutation_loop_body` walks the for-body sequentially, building a flat let-chain of every assignment and snapshotting each `<<` feed value with the let-chain that preceded it.  Feeds anywhere in the body are supported — pre-mutation, between mutations, or post-mutation — and each captures exactly the SSA-style scope its Python source intended.  See "Record-bodied loops with feeds" below for how feeds are surfaced.

Operator conversion realises the loop as a `Recurse` operator wrapped in a `FanOut`.  All dataflow stays in `Tile`s — no shared cache is exposed across operator boundaries.

```text
              ┌──────────────────────────────────────────────────────────┐
              │                                                          │
init ──┐      ▼                                                          │
        ├──→ Recurse ──→ FanOut ──┬──→ FanIn ──→ body ──→ FanOut(Memo) ──┤
domain ─┘                         │                  │                   │
                                  │   source ────────┘                   │
                                  │                                      │
                                  └── (acc_var reads from this branch)   │
                                                                         │
                                            .step ◀────────── (cycle) ───┘
                                                                         │
                                       external Record stream ◀──────────┘
                                       ((Proj("step"), init) ▷ LastOrDefault
                                        + Proj("to_<defer>*"))
```

- **Inputs**: `init` carries the accumulator's starting value (scalar for one param, packed `Record({_i: Scalar(T_i)})` via `ScalarFanIn` for multi-var); `domain` is an `IterateExtent` over the source's domain; `recursive_input` is the body fan-out's `.step` branch back into the cycle, wired in by `recursive_input_setter` after body compilation.
- **`Recurse` output**: emits the accumulator *shifted forward by one in the domain* — `init` at position 0, `recursive_input[i-1]` at position `i > 0`.  Wrapped in a `FanOut` so that the body's tuple input (the first arm of a `fan_in(prev_acc, source)`) and the loop's external output can share the stream.
- **Loop body** is compiled with `Some(fan_in([prev_acc_fan.branch(), source_op]))` as its input — a `SealedFunction(D, Record{_0: AccType, _1: item_ty})` matching the body's CCL type `Fun(Tuple(AccType, item_ty), Record({step, to_<defer>*}))`.  The body's lambda projects `acc_var` and `iter_var` out of the input record.  Its codomain is always `Record({step: <step_shape>, to_<defer>*: T_*})` (with the `to_<defer>` fields possibly empty).  The body's output is wrapped in `FanOut(Memo(…))`: one branch is projected to `.step` and closes the cycle via `recursive_input_setter`, the other is the Loop's external output exposed directly as the body Record stream.
- **External output**: the body fan-out's external branch is exposed directly as the body Record stream.  Downstream lowering picks each accumulator off via `(Proj("step") [▷ Proj(i)], init_arg) ▷ LastOrDefault` (so an empty source yields `init_arg`, not a panic) and each per-iteration channel via `Proj("to_<defer>")`.

#### Record body shape

`lower_mutation_loop` emits one Loop whose body terminates in a Record carrying the recurrence value, with feeds left as `ExprStmt(Feed(d, V), …)` wrappers around the Record:

```text
let acc_stream = Loop {
  params: [acc_name],
  init_args: [Var(acc_name)],   // pre-loop value
  loop_body: λp →
    let acc = p ▷ Proj(0) in
    let i = p ▷ Proj(1) in
    ExprStmt(Feed(defer_0, <feed_value_0>),
    ExprStmt(Feed(defer_1, <feed_value_1>),
      Record({ step: <full let-chain> Var(acc_name) }))),
} in
let acc_name = (acc_stream ▷ Proj("step"), Var(acc_name)) ▷ LastOrDefault in
continuation
```

`desugar_defers` then absorbs each `Feed(defer_k, V)` into a `to_<defer_k>` field on the body's terminal Record, drops the `ExprStmt` wrappers, and binds the per-iteration channel via `let defer_k = Var(acc_stream) ▷ Proj("to_<defer_k>")` in the surrounding cluster.  No `body_taps` field is needed — the Record's field set is the source of truth.

- **`step`**'s type is the scalar accumulator type for a single param, or a positional `Tuple(T_0, …, T_{n-1})` for multi-var.  Multi-var lowering finishes each accumulator's chain with an extra `▷ Proj(i)` before the `LastOrDefault` pair.
- **`Builtin::LastOrDefault`** is the explicit stream-to-scalar primitive (`Tuple(Fun(D, T), T) → T`) used for the post-loop accumulator extraction.  Compiles directly to `ExtractLast`, which receives both the stream and the default operator and falls back to the default when the source domain is empty (the loop body ran zero times).  The default at each accumulator's call site is the pre-loop binding `Var(acc_name)`, which resolves to the outer scope because the surrounding `let acc_name = …` shadows it only inside its own body.  It is *not* an `AggregateKind` because there is no fold / identity element; lambda-elim handles it via the polymorphic-builtin Apply rule, mirroring `Zip`.
- **Op-conversion**: the Loop arm always projects `.step` from a fan-out branch of the body's output before feeding to `recursive_input_setter` so the cycle carries only the recurrence value; the full Record stream is exposed as the Loop's external output.

This shape compiles to **exactly one `Recurse`** per source-level mutation loop, regardless of how many feeds the body contains or whether the after-loop scalar accumulator is also consumed.  Multiple sequential mutation loops sharing one defer still build up a Union-domain `SealedFunction` via `CollectionUnion` — `desugar_defers` collects every `Feed(defer_k, …)` for a given defer and unions their stream values at the defer's resolution site.  Because the desugaring runs pre-inference, the `let acc_stream = Loop` binding stays as a plain shared `Let` and gets normal scope-sharing via inference and lambda-elim, with no per-pass duplication-preservation machinery.

Each feed's value lives inside the body's lambda scope, so its references to `acc` and `iter_var` resolve against the body's per-iteration projections — exactly what the original `o << e` meant.  Pre-mutation feeds capture the empty let-chain (acc = `p.0`, the prev-iteration value); post-mutation feeds capture the chain up to the mutation.

**Generators with loop-carried state** (brainstorm §4b's `running_totals`: `total = 0; for x in xs: total += x; yield total`) reuse this same `Loop` lowering — `yield e` is just `<<` against a synthesised generator defer.  `lower_generator_or_mutation_loop` allocates `__result_N = Defer` outside the loop, passes its name into `lower_mutation_loop_body` as `yield_defer`, and each `yield e` is emitted as a raw `Feed(__result_N, …)` inline at the yield site with the same let-chain snapshotting as an explicit `<<`.  `desugar_defers` then absorbs every such feed into a `to_<defer>` field on the body Record.  The surrounding generator-function context already wraps the loop in `let __result_N = Defer in …` so the collected yields surface as the function's stream return value.  Both `lower_generator_for` (final-statement path) and `lower_middle_stmt` (middle-statement path) detect mutation independently of `yield` and dispatch through this same helper — they only differ in what continuation is passed in (`Var(__result_N)` for the final-statement case, the surrounding `body` for the middle case).

**Let-bindings in generator bodies** (`y = f(x); yield y`) lower to nested `Let` nodes inside the Lambda body, evaluated once per iteration of the enclosing loop.

**Pre-loop lets** (assignments before the outer `for` in a function body) are handled by `lower_stmts` — they wrap the generator expression in `Let` nodes. The `for` lowering itself (`lower_generator_for`) only handles the loop and its body.

**Mutation rule**: an assignment inside a for-loop body is a let-binding (allowed) iff the target name is fresh in the current frame or was introduced by the same `for`-body (including the iter-variable). Assignments to names from enclosing frames, function arguments, or pre-loop lets are rejected as mutation. Function definitions inside for-loop bodies are treated identically to assignments.

Generator expressions `(expr for x in xs)` are lowered via `lower_list_comp` to the same `Compose+Lambda` encoding as generator functions.

### `GroupBy` — first-class grouping node

`groupby(collection, key)` calls are lowered directly to `Expr::GroupBy` rather than kept as a nested `Apply`. This makes the grouping operation structurally distinct from ordinary calls, which simplifies:

- **Type inference**: `infer` can propagate the collection's element type onto the key lambda's `param_ty` without needing built-in name resolution.
- **Compilation**: the compiler can dispatch on `Expr::GroupBy` and emit the appropriate group operator without inspecting call-site variable names.

The result type is `Fun(K, Fun(UInt, V))` where `K` is the key type and `V` is the element type. The outer function maps a key to a group; the inner function maps an unsigned index to an element within that group — the same encoding used for lists (`Fun(UIntRange(n), V)`), but with an unbounded `UInt` domain since group sizes are not known statically.

### `Cast` — explicit refinement acquisition

`Cast { value, target }` is a pure type-level assertion that re-views `value` under `target`. It is a node (not a `Builtin`) because it has its own typing rule and its own structural shape — modelling it as `Apply(value, Cast)` with the target hidden on `user_annotation` forced every traversal to special-case the `Apply`-with-Cast-head pattern and read the target out of a side field. The node makes both the value child and the target type first-class.

Lowering ([`ccl_utils::make_cast`]) emits it for list-comprehension filters, for-loop `if`-guards, and `groupby`. The only `target` shape lowering produces today is `Fun(Refinement(_, 𝑝), _)`: a function type whose domain carries the predicate `𝑝`, so the cast attaches a refinement to a collection function's domain. `target` is the lowering-time *specification* (its domain/codomain are typically `Type::Hole`, carrying only the refinement); the resolved cast type lands on `expr.ty` after inference — the same `user_annotation`-vs-`ty` split used elsewhere.

`Cast` is an **upcast**: its whole typing rule is the single subtype obligation `value_ty <: target`. For the domain refinement lowering emits, that holds by contravariance — `(𝐷 ⇒ 𝑉) <: ({𝐷 | 𝑝} ⇒ 𝑉)` because `{𝐷 | 𝑝} <: 𝐷` — so viewing an unrefined-domain collection function at a refined-domain type is sound. The refinement-aware solver (`simple_sub::constrain_subtype`'s refinement arm) flows the demanded tag onto the *fresh* target-domain variable, *stacking* it onto any tags the value already carries, so chained casts (nested list comprehensions: `{𝐷|𝑝} ⇒ 𝑉 <: {?a|𝑞} ⇒ 𝑉`) compose. The result is `target`; coalesce pins its fresh vars from `value` (the domain var, in negative position, takes `value`'s domain as an upper bound; the codomain var takes `value`'s codomain as a lower bound). `target`'s predicate is inferred and coalesced by the same `emit_annotation_predicates` / `coalesce_type_predicates` path as any refinement-bearing type. A *covariant* refinement (casting `Int` to `{Int | 𝑝}`) correctly *fails* the subtype check — acquiring a value-level refinement is a runtime/SMT-checked narrowing, not an upcast.

This relies on the solver flowing a demanded refinement tag onto a *variable base* under a refinement layer (`{?a | 𝑞} <: {𝐷 | 𝑝}` records `?a <: {𝐷 | 𝑝}` rather than rejecting on `{𝑝} ⊄ {𝑞}`). An earlier implementation worked around the solver lacking this by *constructing* the refined result type from the value plus `target`'s tag; once the refinement arm learned to flow the deficit onto a variable base (the refinement analog of how the record/function arms thread structure through variables), the cast collapsed to the plain upcast above.

`lambda_elim` recognises `Cast { value: Lambda, .. }` as the body of an outer lambda whose binder is free only in the cast's *refinement* (the group-by shape) and emits the **Pi-const** form `const(cast(<point-free inner>))` typed as a Pi `(param) ⇒ ({D | p} ⇒ V)`: the binder-dependence rides the refinement and is materialized as a `Restrict` at iteration (the dependent-application model), and planning's pointful group-by recognizer (`convert_groupby_pointful`) reads the binder off the predicate. (This replaced the former correlated-refinement uncurrying that reconstructed a `Lambda { refinement }`.) Casts that are not a lambda body — top-level filter / for-loop guards wrapping point-free code — survive `lambda_elim` (the standard structural recursion descends into `value` and keeps the wrapper) and propagate through to op-conversion, which compiles them as a pure pass-through: the refinement lives on `expr.ty` and is consumed by planning (`operator_conversion::iterate_type` turns a domain refinement into a `Restrict`) before reaching the tile graph. The migration plan toward a general `𝑈 ⇒ 𝑇` cast is in `docs/refinement-types-design.md`.

### `Case` only — no `IfThenElse`

CHL `if/else`, `elif` chains, and ternary `if` expressions are all lowered to `Case` during CHL → CCL lowering. There is no `IfThenElse` node in the CCL AST. `Case` subsumes all multi-way branching.

`Case` holds an ordered list of `Branch { guard, body }` values. Guards are arbitrary `TypedExpr` nodes constrained to `Bool` at inference time; the first truthy guard wins. `elif` chains are **flattened** into a single `Case`: when `lower_if` recurses into the `orelse` block and the result is itself a `Case`, its branches are extended directly rather than nested, so `if c1: … elif c2: … else: …` produces `{ c1 → …; c2 → …; true → … }`. Structural pattern decomposition is represented as `Let` bindings in arm bodies; literal matching is an equality guard expression.

CHL `match` statements (planned) will desugar entirely at lowering time: the scrutinee is bound with a fresh `Let(__scrut)` node, then each arm produces a guard (`__scrut == lit` for literal patterns, `Lit(true)` for wildcard/structural) and a body (with `Let` bindings for any captured variable names). No IR changes are needed for `match` support.

### `Loop` for mutation-accumulation iteration

CHL mutation-accumulation `for` loops are lowered to an explicit `Loop` node rather than recursive `Lambda`/`Let` combinations or a dedicated fold node.

`Loop` is a bounded iteration with explicit loop-carried accumulators: `params` lists the accumulator slots (one or more), `init_args` supplies their starting values in declaration order, `source` drives the iteration, and `loop_body` computes each new accumulator value from `(prev_acc_0, …, prev_acc_{n-1}, item)`.  The accumulator slots are only in scope inside `loop_body`; `init_args` is evaluated outside the loop's param scope.  There is no `Jump` node: the loop has a single entry (`init_args`) and the runtime iterates the body until the source is exhausted, so labelled tail-calls aren't needed.  `continue`-style "skip the rest of this iteration" semantics fall out as conditional `Case`-on-old-vs-new in the body, again without an AST extension.  General `while` loops with explicit restart/break would need a richer encoding (a body-tail-call form for `continue`, runtime support in `Recurse` for `break`), but those are future work.

The mutation-loop pattern emitted by `lower_mutation_loop` (see "Mutation accumulation loops" above) is currently the only `Loop` shape consumed end-to-end: `infer.rs::infer_mutation_loop` and `operator_conversion`'s `Loop` arm both pattern-match on `Loop { params: [acc_0…], init_args: [init_0…], source: Fun(D, item_ty), loop_body: Lambda(p, …) }` with `params.len() == init_args.len()`, and reject anything else.  Any combination of accumulator count and per-iteration channel count is supported: single- or multi-accumulator, with or without feeds (the body Record's field set is the source of truth).  Future work (general `while` loops, generators with internal mutable state) will extend these passes to handle additional shapes.

Rationale: encoding loops as recursive lambdas requires detecting recursive bindings by scanning the tree for forward references. `Loop` makes the loop structure explicit, simplifying both the lowering pass and optimization passes targeting iterate/feedback operators.

### Shared literal and operator types

`Literal` and `BinOpKind` are defined in a shared module, not in the interpreter. The CCL IR must not depend on interpreter internals.

### Typed binding sites — `TypedBinding`

All binding sites — `Lambda`, `Loop`, and `Let` — use `TypedBinding { name, ty, user_annotation }` rather than separate `name: String` / type fields.

- `ty` starts as `Type::Hole` (lowering placeholder); the inference pass converts it to a registered `Type::Infer` variable at inference entry and fills in the concrete type before compilation.
- `user_annotation` carries an optional user-written type annotation (e.g. from a CHL `cast` expression). Inference validates the inferred type against it; if the body provides no usable constraint the annotation is used directly as the param type.

`Type::Hole` and `Type::Infer(_)` have no runtime equivalents — all types must be resolved to concrete types before operator-graph compilation.

### `TypedExpr` — type slot on every node

Every CCL expression is wrapped in `TypedExpr { node: TypedExprNode, ty: Type, user_annotation: Option<Type> }`.

- `node` holds the expression kind (`TypedExprNode` enum, formerly `Expr`).
- `ty` starts as `Type::Hole` (stamped by `TypedExpr::new()`); the inference pass converts it to a registered `Type::Infer` variable then fills it with the concrete type before compilation.
- `user_annotation` carries an explicit annotation from the source (e.g. a `cast` call). Inference checks it for compatibility with the inferred type and uses it as the final type if present.

`TypeAnnotation` no longer exists as a node variant; annotations are carried uniformly by `TypedExpr.user_annotation` instead.

### `Type::Hole` and `Type::Infer` — the two-way split

The type system uses two distinct pre-/post-inference placeholders with strict ownership:

| Variant | Owner | Meaning | Must be eliminated by |
|---|---|---|---|
| `Type::Hole` | Lowering | "This slot needs a type; not yet known" | End of inference (debug assertion if survives) |
| `Type::Infer(id)` | Type checker only | "Inference variable N, produced by simple-sub" | End of inference (ambiguous type if survives) |

**`Type::Hole`** is stamped by `TypedExpr::new()` and `TypedBinding::new_unannotated()`. It is a structural placeholder that carries no identity. The simple-sub inference pass (`infer_simple_sub`) eliminates all `Hole` placeholders and replaces them with concrete types or `Type::Infer` variables. `fresh_infer_var_id()` must not be called from lowering code; use `Type::Hole` instead.

**`Type::Infer(id)`** is produced by the simple-sub pass (`ccl/infer_simple_sub.rs`) when a type cannot yet be determined. Any `Infer` remaining after inference represents an ambiguous type. The simple-sub pass is the sole creator of `Infer` variables during inference; lowering always uses `Type::Hole`.

This separation makes test expression construction straightforward: tests that build expressions without running inference use `Type::Hole` (via `TypedExpr::new()`) and never need to synthesize `InferVarId` values.

---

## Node Definitions

```rust
// --- Shared module (no dependency on interpreter) ---

enum Literal {
    Int(i64),
    String(String),
    Bool(bool),
    Unit,
}

enum ArithmeticKind { Add, Sub, Mul, FloorDiv }

enum CompareKind { Equals, NotEquals, Less, LessOrEq, Greater, GreaterOrEq }

enum LogicKind { And, Nand, Or, Nor, Xor, Xnor }

enum BinOpKind {
    Arithmetic(ArithmeticKind),
    BoolLogic(LogicKind),
    Concat,
    Compare(CompareKind),
    /// Left-to-right function composition: `f ≫ g` means "apply f, then g".
    /// Introduced by `lambda_elim`; absent in source-level CCL.
    Compose,
}

// Collection union is a *value-level* construct, not a binary op — it has
// its own top-level node `TypedExprNode::CollectionUnion(Vec<TypedExpr>)`
// (N-ary natively, rendered `c₀ ⊎ c₁ ⊎ …` by `symbolic`). Lowered from
// CHL `a ++ b`; lambda elimination preserves the top-level node when
// recursing into operands and falls back to
// `Apply(Tuple([a, b]), Builtin(CollectionUnion))` only when the operands
// reference a surrounding lambda parameter. Both shapes compile to a
// `UnionOperator` tile.

enum UnaryOpKind {
    Neg,  // unary -
    Not,  // boolean not
}

enum AggregateKind {
    Sum,  // sum of elements (Int input → Int output)
    Max,  // maximum element (any base type input → same base type output)
}

// --- CCL AST ---

/// Every program is a TypedExpr. `node` holds the expression kind; `ty` is
/// filled in by infer::infer; `user_annotation` carries an explicit cast/annotation.
struct TypedExpr {
    node: TypedExprNode,
    ty: Type,                        // Infer(id) until inference fills it; Error on inference failure
    user_annotation: Option<Type>,   // checked against ty by infer; None for lowered nodes
}

/// Type alias for call-site convenience: `Expr` == `TypedExpr`.
type Expr = TypedExpr;

/// Key for a first-class projection morphism. Identifies which field is projected.
enum ProjKey {
    Index(usize),   // tuple field: .0, .1, …
    Field(String),  // record field: .fieldname
}

enum TypedExprNode {
    Lit(Literal),
    Var(String),
    /// Reference to a built-in primitive function (id, curry, zip, apply,
    /// map, converse, the binops, the unary ops, sum/max, …). Introduced
    /// post-inference by lambda elimination and planning; matched on
    /// directly by simplify, planning, and operator_conversion.
    Builtin(Builtin),
    Proj(ProjKey),
    Apply{
      function: Box<TypedExpr>,
      argument: Box<TypedExpr>
    },         // unary application: f(x) == x ▷ f
    Cast {
        value: Box<TypedExpr>,   // the value being re-viewed
        target: Type,            // Fun(Refinement(_, _), _): the type to view it at
    },         // pure type-level assertion; see "Cast — explicit refinement acquisition" below
    BinOp{
      left: Box<TypedExpr>,
      op: BinOpKind,
      right: Box<TypedExpr>,
    },
    UnaryOp(UnaryOpKind, Box<TypedExpr>),
    Lambda {
        param: TypedBinding,    // name + ty (Unknown until inferred) + user_annotation
        body: Box<TypedExpr>,
        // A refined parameter (filtered / joined comprehension, groupby) carries
        // its predicate on `param.ty` as a `Type::Refinement`, introduced by
        // `cast` (`ccl_utils::make_cast`) — not on a dedicated AST field.
    },
    Let {
        binding: TypedBinding,  // name + ty mirrors bound_expr.ty after inference
        bound_expr: Box<TypedExpr>,
        body: Box<TypedExpr>,
    },
    List(Vec<TypedExpr>),                     // list literal [e0, e1, ...]; elements may be arbitrary exprs of the same type
    Aggregate {
        input: Box<TypedExpr>,                // expression being aggregated (must be of type Fun)
        kind: AggregateKind,                  // the aggregation operation (Sum, Max, …)
    },
    /// Multi-way conditional branching. Evaluates each `Branch` in order;
    /// the first branch whose guard evaluates to `true` wins. Guards must
    /// have type `Bool`. CHL `if/else`, `elif` chains (flattened), and
    /// ternary `if` are all lowered to this node.
    Case {
        branches: Vec<Branch>,  // Branch { guard: TypedExpr, body: TypedExpr }
    },
    Loop {
        params: Vec<TypedBinding>,            // loop-carried accumulator slots
        init_args: Vec<TypedExpr>,            // one init per param, evaluated outside the loop
        source: Box<TypedExpr>,               // iteration source: Fun(D, item_ty)
        loop_body: Box<TypedExpr>,            // per-iteration step: Fun(Tuple(params…, item), Record{step, to_<defer>*})
    },
    GroupBy {
        collection: Box<TypedExpr>,           // the collection (function) whose elements are grouped
        key: Box<TypedExpr>,                  // key extraction function: element → key
    },
    // Construction — lowering stubbed, deferred
    Tuple(Vec<TypedExpr>),
    Proj(ProjKey),                            // first-class projection morphism: .n or .name
    Record(Vec<(String, TypedExpr)>),
    // Built-in data source
    Source(String),

    // --- Output operators (defer/feed/define) ---
    // See §Defer for semantics and the desugar_defers pass.

    /// Placeholder for an output accumulator introduced by `x = defer()`.
    /// The bound name is resolved by the surrounding `Let` binding.
    /// Eliminated by `desugar_defers::run` before type inference.
    Defer,

    /// Feed a value into a deferred output: `x << value`.
    /// Lowers from the `<<` (LShift) binary operator when the LHS names a defer.
    /// Has type `Unit`; the value is collected by `desugar_defers` and unioned
    /// into the source channel that resolves the defer.
    Feed {
        name: String,         // name of the defer binding being fed into
        value: Box<Expr>,
    },

    /// Define a deferred output to a specific value: `x <<= value`.
    /// Lowers from the `<<=` (AugAssign LShift) statement when the LHS names a defer.
    /// Has type `Unit`; the value is collected by `desugar_defers` and replaces
    /// the surrounding `Defer` binding.
    Define {
        name: String,         // name of the defer binding being defined
        value: Box<Expr>,
    },

    /// A bare expression used as a statement, followed by the rest of the block.
    /// `ExprStmt { expr, body }` evaluates `expr` for its side effects (e.g. a `Feed`
    /// or `Define`), then continues to `body`. Introduced by `lower_middle_stmt` for
    /// non-assignment, non-final statements. Dropped by `simplify` once any contained
    /// `Feed`/`Define` nodes have been removed.
    ExprStmt {
        expr: Box<TypedExpr>,
        body: Box<TypedExpr>,
    },
}

enum Type {
    Base(BaseType),
    UIntRange(usize),                    // finite index range [0, n); domain of list types
    Fun { name: Option<String>, domain, codomain }, // T ⇒ U, or Pi (x: T) ⇒ U when named
    Tuple(Vec<Type>),
    Record(Vec<(String, Type)>),
    PartialTuple(Vec<(usize, Type)>),    // partial tuple: only listed indices constrained; domain of Proj(Index(n))
    PartialRecord(Vec<(String, Type)>),  // partial record: only listed fields constrained; domain of Proj(Field("x"))
    Union(Vec<Type>),
    Hole,                                // lowering placeholder; converted to Infer at inference entry
    Infer(InferVarId),                   // residual type variable after simple-sub coalesce
    Error,                               // inference already failed here; suppresses cascades
    Refinement(Box<Type>, Refinement),   // refined base type; `Refinement.predicate` is the restriction
    DataSource(String),                  // opaque domain type of a source
}

// `Fun.name` is the **Pi binder**: when `Some(x)`, `x` is bound in `codomain`
// and may be referenced by refinement predicates nested within it — the
// dependent-function type `(x: domain) ⇒ codomain`. Inference (`emit_lambda`)
// always names the binder from the lambda parameter; coalesce keeps the name
// only when the codomain's predicates reference it and strips it otherwise, so
// an ordinary arrow stays `name: None`. See the dependent-refinements section
// of `design-simple-sub.md`.

/// Carries the restriction predicate for a refined domain (i.e. a filtered/joined comprehension).
/// Equality is type-blind structural equality of the predicate term (pointer-equal
/// cells short-circuit); traversals needing occurrence identity key on the
/// predicate cell's address (`PredicateCellId`).
struct Refinement {
    /// A **bare** boolean predicate (not a lambda) in which the single reserved
    /// implicit binder `REFINEMENT_BINDER` ("__elem") is free — the element the
    /// refinement ranges over. Every refinement shares that one binder; nested
    /// refinements shadow it. (A predicate *function* `D ⇒ Bool` is stored bare
    /// as `__elem ▷ p`.)
    predicate: Rc<RefCell<TypedExpr>>,
}
```

---

## Source injection

Sources need to be available to all stages of compilation, so they are tracked in a `GlobalContext` struct
which produces references to the other types of contexts.

Each phase of compilation needs different information about the sources: lowering needs just the names, inference needs the types, and compilation needs to track the materialized extents so that they are shared across references to the
same source.

## Type inference

`ccl::infer` runs simple-sub algebraic subtyping (Parreaux 2020, ICFP). The
full algorithm description — motivation, data structures, constraint rules,
polarity, let-polymorphism, the coalesce pipeline — lives in
[`design-simple-sub.md`](./design-simple-sub.md). This section covers only the
CCL-specific wiring.

### Pass structure

```
Lowering → TypedExpr (all nodes carry Type::Hole)
                │
          emit_node (src/ccl/infer_simple_sub.rs)
                │  walks the AST, calling constrain() for each structural rule
                ▼
          SimpleType constraint graph (VarState.lower/upper bound lists)
                │
          coalesce_pass   (compact_type → coalesce_compact per node)
                │  turns the constraint graph back into ccl::Type values, and
                │  in the same walk fills the binder slots that aren't any
                │  node's expr.ty (Lambda param, Let binding, Case/Loop slots).
                │  Var uses need no scope — they share the binder's var.
                │  Compose/Proj domains are reconstructed earlier, in the solver
                │  (emit_compose's reverse adjacency). Refinements ride the
                │  lattice — see design-simple-sub.md §4.
                ▼
          TypedExpr (fully typed; Type::Hole eliminated)
```

`Type::Infer(id)` after inference means the coalesce pass left a constraint
variable genuinely unconstrained (e.g. the parameter of an unapplied identity
lambda). It is not a UnificationTable entry — the old HM solver (`unify.rs`)
and its `UnificationTable` have been removed.

### `GroupBy` inference

When inferring `Expr::GroupBy { collection, key }`:

1. Infer the type of `collection`.
2. If the collection type has a codomain (i.e. it is a `Fun(_, elem_ty)`), write `elem_ty` into the key lambda's `param.ty` when `param.ty` is still `Type::Hole` or `Type::Infer(_)`. This mirrors the `Apply` rule where the argument type is pushed onto the lambda parameter.
3. Infer the type of `key` (now annotated); take its codomain as `key_output_ty`.
4. Return `Fun(key_output_ty, Fun(Base(UInt), elem_ty))`. Falls back to a fresh variable if either codomain cannot be determined.

### BinOp type rules

| Op kind | Operand constraint | Result type |
|---|---|---|
| `Arithmetic` | both operands constrained equal | operand type |
| `Concat` | both operands constrained to `String` | `String` |
| `Compare` | both operands constrained equal | `Bool` |
| `BoolLogic` | both operands constrained to `Bool` | `Bool` |

**Note**: String + String → `Concat` rewriting is performed at **compile time**
(in `lambda_elim.rs`), not at inference time. The inference
pass only constrains both operands to `String` and returns `String` as the result type.

### UnaryOp type rules

| Op kind | Operand constraint | Result type |
|---|---|---|
| `Neg` | operand constrained to `Int` | `Int` |
| `Not` | operand constrained to `Bool` | `Bool` |

### `Case` inference

For each `Branch { guard, body }`: the guard is constrained to `Type::Base(BaseType::Bool)`; body types across all branches are unified via `constrain_equal`. The overall `Case` type is the unified body type. A 0-branch `Case` is a malformed AST (lowering never produces one) and returns `InferError::EmptyCase`.

### Record literals and field access

CHL record literals use Python dict syntax with **bare identifier keys**:

```python
r = {x: 1, y: "hello"}   # Record([("x", 1), ("y", "hello")])
r.x                        # Apply(r, Proj(ProjKey::Field("x"))) → 1
```

**Lowering:**
- `{k: v, ...}` (all keys must be bare `Name` nodes) → `TypedExprNode::Record([(k, v), ...])`.
  Dict literals with non-identifier keys (e.g. string constants) are rejected with `LoweringError::Unsupported`.
- `expr.field` (Python `Attribute`) → `Apply(lower(expr), Proj(ProjKey::Field("field")))`.

**Type inference:** `Record([(k, e), ...])` infers to `Type::Record([(k, T), ...])` where each `T` is
the inferred type of the corresponding value expression — identical in structure to `Tuple` inference.

**Lambda elimination:** `Record(fields)` inside a lambda body is treated identically to `Tuple`:
each field expression is recursively eliminated, producing `Apply(Record([…elim fields…]), Zip)`.
The inner `Record` node carries type `Record([(k, Fun(D,T)), …])` — a record of morphisms — and
the outer `Zip` application fuses them via a shared `FanOut`, producing a morphism to a record.
This ensures `typecheck` invariants hold: a `Record` node always has a `Record` type.

**Operator conversion:** At the `Apply(Record([…]), Zip)` node, the `Zip` handler dispatches on
the argument shape. For a `Record` argument it uses `fan_in_named`, which selects `FanIn::new_named`
(function-tiling inputs) or `ScalarFanIn::new_named` (scalar inputs) and preserves the declared
field names in the output `Tile::Record`. `Proj(ProjKey::Field(name))` compiles to a
`MapResult` using `FunctionDef::RecordField(name)`, extracting the named field from the upstream
record tile — identical in mechanism to `Proj(ProjKey::Index(n))` for tuples.

### `Proj` inference — `PartialTuple` / `PartialRecord` domain types

A bare `Proj(key)` node — i.e. the projection morphism, not an application of it — is
inferred as a function type whose domain is a **partial** structural type:

| Key | Inferred type |
|---|---|
| `Proj(Index(n))` | `PartialTuple([(n, ?a)]) ⇒ ?a` |
| `Proj(Field("x"))` | `PartialRecord([("x", ?a)]) ⇒ ?a` |

`PartialTuple([(n, ?a)])` means "a tuple whose index `n` has type `?a`; all other
positions are unconstrained." This correctly unifies with any concrete `Tuple` of
length ≥ n+1, constraining `?a` to the element type at that index.

`PartialRecord([("x", ?a)])` means "a record that has at least field `"x"` of type
`?a`; all other fields are unconstrained."

**Unification rules** (in `constrain_equal`):

- `PartialTuple ↔ Tuple`: constrain `?a` against `Tuple[n]`. Out-of-bounds index is a `TypeMismatch`.
- `PartialTuple ↔ PartialTuple`: constrain overlapping indices. Non-overlapping entries are left unconstrained (PR 2 will merge them via `set`).
- `PartialRecord ↔ Record`: constrain `?a` against `Record["x"]`. Missing field is a `TypeMismatch`.
- `PartialRecord ↔ PartialRecord`: constrain overlapping fields only.

**Multi-projection accumulation**: `UnificationTable::set` merges `PartialTuple`/`PartialRecord`
entries when called on a variable that is already solved to one of those types. Overlapping
indices/fields are validated via `constrain_equal`; non-overlapping entries are appended.
Multiple projections of the same parameter (e.g. `x[0]` and `x[1]`) each call `set`, which
merges the `PartialTuple` entries, so the final `probe()` returns the complete tuple structure.

### `Compose` inference

N-ary `Compose([f₀, f₁, …, fₙ₋₁])` is inferred by chaining: each morphism's codomain is constrained as a **subtype** of the next morphism's domain (`constrain_subtype(prev_codomain, d_i)`). This allows a refined codomain (e.g. `Refinement(T, pred)`) to feed into a base-typed domain (`T`) without a type error. The overall type is `Fun(domain(f₀), codomain(fₙ₋₁))`. This case arises when `infer` is run over output from `simplify`, which can produce `Compose` nodes.

### Variant (sum) semantic equality

The post-inference structural checks decide type equality via the solver's
`constrain_subtype` (bidirectionally, in `typecheck_compatible`), which compares
`Type::Variant` tag sets structurally. Nested sums never reach this comparison:
`TypedExpr::collection_union` flattens at construction (next section), so a
`Var(y)` referencing a let-bound sum still contributes a single flat variant.

### Union flattening (construction-time)

`a ++ b ++ c` in CHL parses to right- or left-associated binary AST nodes. **`TypedExpr::collection_union` flattens at construction time**: any operand that is itself a `TypedExprNode::CollectionUnion` is spliced into the outer operand list, so the constructor always returns a flat N-ary node. This makes the invariant **"no operand of a `CollectionUnion` is itself a `CollectionUnion`"** hold from lowering onward — inference, lambda elimination, and operator conversion never need to look through nested AST. The flat AST flows naturally into a flat `Type::Union` domain (each operand contributes one variant; type-level nesting only arises from indirect-through-`Var` references to let-bound unions, which the runtime models exactly). `operator_conversion` compiles the N-ary node directly to a single `UnionOperator` with N inputs.

### `check_fully_typed` validation

After `resolve`, `infer` calls `check_fully_typed(expr)` to assert that every `ty` and every `TypedBinding::ty` in the tree is a concrete type — no `Type::Hole` or `Type::Infer(_)` anywhere, including inside compound types like `Fun` or `Tuple`. Returns `InferError::UnresolvedHole` or `InferError::UnresolvedInfer(id)` on failure, with the symbolic representation of the offending expression for debugging.

### TODOs

- Infer `Let.ty` from the type of `value` (required before `Let` nodes can be compiled; see §Compilation).
- CHL `match` statement lowering: desugar at lowering time using `Let(__scrut)` + guard expressions (no IR changes needed).

---

## Defer / Feed / Define — Deferred Collection Operators (`ccl/desugar_defers.rs`)

`defer()`, `<<`, and `<<=` are CHL-level operators that let a block accumulate a result value progressively. They are reified as three CCL AST nodes (`Defer`, `Feed`, `Define`) during lowering, then **eliminated** before type inference by `desugar_defers::run`.

TODO: `x = defer()` should be replaced with `deferred x` once we implement a custom parser and aren't stuck with CHL parsing rules.

### CHL syntax

| CHL | Meaning |
|---|---|
| `x = defer()` | Declare `x` as a deferred accumulator |
| `x << value` | Feed `value` into `x` (used in expression position; any number of feeds) |
| `x <<= value` | Define `x` to be exactly `value` (used as a statement; exactly one define) |

A `defer` binding supports **either** feeds or exactly one define — mixing both is an error.

Both the feed and define expressions evaluate to Unit.

### Lowering

`x = defer()` lowers to `let x = Defer in …`.

`requests, responses = http_serve(port, method, path)` lowers to:
```
let requests = Source("__http_requests_N") in
let responses = Defer in
<user body>
```

The `DataSink` for responses (`HttpServerSharedState`) is registered in `LoweringContext::sink_bindings` keyed by the `responses` binding name.  After the full pipeline runs, `compile_program` extracts the responses binding expression via `extract_sink_bindings`, compiles it independently, and subscribes a `SinkConsumer` to it.  The main program output is replaced by a Unit placeholder; sink programs do not produce a primary output value.

`x << expr` in expression or statement position lowers to `Feed { name: "x", value: expr }`, wrapped in an `ExprStmt` when it appears as a non-final statement.

`x <<= expr` lowers to `Define { name: "x", value: expr }`, also wrapped in an `ExprStmt`.

The `ExprStmt { expr, body }` node chains a side-effecting statement before the rest of the block:
```
let x = defer
in ExprStmt(Define(x, 1), x)    # x <<= 1; x
```

### `desugar_defers::run` — the elimination pass

The pass runs **after** `lower` and **before** `infer`.  Because it runs
pre-inference, `Defer`/`Feed`/`Define`/`ExprStmt` nodes never reach any
later pass — those passes can treat the variants as `unreachable!`.

In broad strokes, for each cluster of consecutive `let d_i = Defer in …`
bindings the pass walks the cluster body to extract every `Feed(d_i, V)`
and the (at most one) `Define(d_i, V)`, combines the extracted values via
`++` (`TypedExprNode::CollectionUnion`), and emits the cluster's bindings
at the body's terminal in topological order so cross-defer references
(`x ≪= y; y ≪= …`) resolve without `letrec`.  Special handling exists
for per-iteration feeds (Compose/Apply with iteration lambda), Loop
bodies (per-iteration `to_<defer>` Record fields), filter-feed Cases,
defer-mediating UDF calls (`y = f(arg)` where `f` introduces or
manipulates a defer), and a handful of structural rewrites (defer-
returning let lift, alias inlining for defer handles).

The full mechanism — the two-phase structure (chain rewriter + cluster
walker), the smart-walker for defer-mediating UDF calls, the shadow-
renaming step, error modes, known gaps, and a navigation map for the
source — lives in **[design-desugar-defers.md](design-desugar-defers.md)**.

### Inference

Because `desugar_defers` runs first, the inference pass never sees
`Defer`/`Feed`/`Define` nodes.  Channel values appear as ordinary
expressions (Apply/Compose/Loop), and the resolved defer is just a
`Let` binding whose `bound_expr` is the assembled channel.  No special
`DeferredCollectionDomain` type or per-feed unification step is needed
— standard inference does the job.

Mutation-loop inference (`infer_mutation_loop`) leverages
`Type::PartialRecord` to learn the loop body's full Record codomain
from the body itself: the constraint
`body_codomain ≡ PartialRecord({step: <step_shape>})` pins the `step`
field while letting unification add whatever `to_<defer>` fields the
body's Record literal carries.  This is the right pattern for any
"shape with a known core plus an open set of additional fields" inference
goal — see `Type::PartialRecord` in the type table above.

---

## Planning (`ccl/planning.rs`)

`planning::run` runs after `lambda_elim` and produces the CCL that operator conversion will see.  The pass does general iteration-site planning — hash-join planning is just one *specialised* strategy folded in at a site, not the whole job (hence `planning`, not `join_plan`).  It performs two CCL-to-CCL rewrites and a final cleanup:

1. **Keyed-aggregate rewrite** (`recognize_groupby_sites` / `convert_groupby_pointful`) — recognises the **pointful** dependent-refinement source `const(cast(c)) : (k) ⇒ ({i | i ▷ c ▷ key == k} ⇒ V)` that lambda elimination emits for `[sum(g) for g in groupby(xs, key_fn)]` and folds the partition dispatch through `converse`.  (This replaced the former combinator recogniser that matched lambda-elim's correlated-refinement uncurrying.)
2. **Iteration-site materialization** (`insert_iterate_markers`) — a single walk that visits every position where op-conversion would compile with `input=None`.  At each site the pass picks the best implementation strategy:
   - **Hash join** (`try_hash_join_rewrite` → `convert_loop_join` → `plan_loop_join` → `join_plan_to_expr`) when the site's domain is a refined tuple whose predicate decomposes into equality join conditions.  The emitted chain is itself iteration-bearing at its leaves (each `JoinPlan::Loop` emits `Apply(true ▷ const, Iterate)`), so no further marker is added.
   - **Iterate-then-restricts chain** (`wrap_with_iterate`'s fallback) — build the iteration source by *applying* one `restrict(p)` per refinement layer (innermost first) to a chain-head `Apply(true ▷ const, Iterate)`, then compose the value-producing body onto it, when the hash-join recogniser doesn't match.  `restrict` is a function transformer `(𝐷 ⇒ 𝑇) ⇒ ({𝑑: 𝐷 \| 𝑝(𝑑)} ⇒ 𝑇)` — applied, not composed — so each layer narrows the domain while preserving the value `𝑇`, and the chain stays well-typed (its honest second-order type would make a morphism-`Compose` ill-typed; `typecheck` now rejects that).

Hash-join planning is the *specialised* strategy at an iteration site; the uniform iterate-then-restricts chain is the default.

The full pipeline inside `run`:

```
recognize_groupby_sites(&mut expr);
let expr = simplify(expr);
insert_iterate_markers(&mut expr);
simplify(expr)
```

`simplify` brackets the marker pass on both sides — the same marker-aware pass, not two modes:

- The **pre-marker `simplify`** runs on an iterate-free AST, canonicalising the value-level combinators before marker insertion; with no markers present, every rule fires.  (The join/group-by recognizers match the *pointful* predicate carried in the type, which `simplify` does not touch — see §6.5.)
- The **post-marker `simplify`** absorbs the `id` leaves and nested `Compose` boilerplate that `replace_tuple_project_with_id` produces while planning a hash join.  Safety here is a property of the *nodes*, not of pass timing: `simplify`'s structural-discard rules (`try_const_reduce`, `try_product_beta_fst`/`_snd`, `try_literal_tuple_projection`, `try_ccc_universal`, `try_exponential_eta`, …) self-guard on an iteration-freeness check — `simplify_once` accumulates "this sub-tree contains an `iterate` source" bottom-up (OR-ing `is_iteration` over the node and its children) and the discard rules refuse to fire whenever it holds, because an `Apply(_, Iterate)` at a chain head *is* the iteration source for everything downstream, so dropping it strands the chain.  Only `iterate` needs guarding: a `restrict` filter is always applied to an iterate-bearing upstream, so it is never separable from its source and the same guard protects it transitively.  Reductions of fully iteration-free sub-trees remain sound (they are pure CCC morphisms), so no separate iterate-safe mode is needed.

### Hash Joins

Loop join patterns — where a predicate filters a cartesian product of two or more collections — are converted to hash-join strategies via `try_hash_join_rewrite`, called from `wrap_with_iterate` at every iteration site whose domain has a `Type::Refinement`.

#### Recognised pattern

The recognizer matches the **pointful** predicate form (design §6.5) — the lambda the refinement carries, not a compiled combinator chain. The predicate has the shape `λ rec → rec.0 ▷ l0 ▷ (λ v0 → … rec.k ▷ lk ▷ (λ vk → <bool>))`, where each `rec.i ▷ li` binds the element `vi` of arm `i` and the innermost boolean is a conjunction of:
- equalities `vi == vj` (the join conditions), and
- residual predicates over the element binders.

`split_join_conditions` builds the `vi ↦ rec.i ▷ li` environment, decomposes the boolean (`and` / `==` / residual), and for each side substitutes the environment and runs lambda-elim to recover the combinator morphism over `rec`. Each equality side must then depend on a *single* arm, identified by `is_function_of_single_tuple_arm`.

#### 2-way join

For two arms the transformation is straightforward:
1. **Build side**: group by the build key using `converse` — yielding `key → (build_type → build_type)`
2. **Probe side**: compose the probe key with the build side lookup — yielding `probe_type → (build_type → build_type)`
3. **Materialise**: `▷ uncurry ▷ map_domain` flattens the curried result back to `(probe_type, build_type) → (probe_type, build_type)`, which is the same as what would have come out of the loop join.

#### N-way join planning

For `n ≥ 3` arms `plan_loop_join` constructs a left-deep binary hash-join tree using a five-step algorithm:

1. **Split conditions** (`split_join_conditions`): decompose the pointful predicate (above) into equality join conditions — each side compiled to a combinator morphism over the tuple domain, where each key depends on exactly one arm — and *other predicates* that aren't equalities.  For each equality condition, `replace_tuple_project_with_id` strips the tuple projection, leaving a function of just the arm's own type.  Each non-equality predicate is paired with the set of arm indices it references (`collect_arms_used`), so it can be pushed to the right level later.

2. **Build spanning tree** (`spanning_tree_children`): treat each equality condition as an undirected edge `(arm_a, arm_b)` and run BFS from arm 0 over this graph.  Returns `children: Vec<Vec<usize>>` — the BFS spanning tree as an adjacency list — or `None` if the graph is disconnected (some arm has no join path to arm 0).

3. **Build left-deep plan with predicate pushdown** (`build_join_plan`): walk the BFS children recursively, starting from arm 0.  For each child subtree, find a condition that *straddles* the accumulated probe side and the child's subtree, orient it probe/build, and fold it into a `JoinPlan::Hash`.  Any remaining straddling equality conditions become residual predicates at that node.  Non-equality predicates are pushed down greedily: predicates whose required arms are entirely within a child subtree are forwarded into that child's recursive call; predicates whose required arms span the current probe side are applied at the first join node where all required arms are present, after reindexing (`reindex_for_domain`) to match the flat output domain of the current node.  Single-arm predicates that depend only on a leaf arm are pushed all the way into the `JoinPlan::Loop` node's `predicate` field.  Returns `(JoinPlan, arm_order)` where `arm_order[i]` is the canonical arm index at output position `i`.

4. **Emit CCL** (`join_plan_to_expr`): convert the `JoinPlan` tree to a CCL expression bottom-up.
   - `Loop { arms }` → `id` on the tuple type of those arms (or the single arm type)
   - `Hash { probe, build, … }` → the probe/build `converse`/`uncurry`/`map_domain` chain described above.  Additionally, for nested hash joins, we need to convert from the nested 2-tuple structure generated by the join tree back to a flat n-tuple structure, so a new `flatten_domain` combinator is inserted before the `map_domain` as needed.  `flatten_domain` allows for flattening up specific positions of a tuple of tuples.

5. **Restore canonical order**: because BFS visit order depends on the order equality conditions appear in the AND expression, `arm_order` may not be `[0, 1, …, n-1]`.  When it differs, `convert_loop_join` appends `▷ ([perm] ▷ permute_domain) ▷ map_domain`, where `perm[j]` = the position of canonical arm `j` in `arm_order`.  This rewrites the domain from the BFS-induced tuple order back to the original `(T_0, T_1, …, T_{n-1})` order that the rest of the expression expects.

For example, a three way join might end up looking like
```
(arm1 ≫ ((arm3 ≫ arm2 ▷ converse) ▷ uncurry ▷ map_domain ≫ .0 ≫ arm3) ▷ converse) ▷ uncurry ▷ ([1] ▷ flatten_domain) ▷ map_domain ▷ ([0, 2, 1] ▷ permute_domain) ▷ map_domain ≫ join_body
```

#### `JoinPlan` structure

```
JoinPlan::Loop  { arms, predicate }
JoinPlan::Hash  { probe, build,
                  probe_key_idx,  // None if probe is a single-arm leaf
                  probe_key_expr,
                  build_key_idx,  // None if build is a single-arm leaf
                  build_key_expr,
                  predicate }
```

`probe_key_idx` / `build_key_idx` are indices *into the output type of that side's sub-plan*, not into the original tuple.  They are `None` when the respective side is a single-arm `Loop` (no projection needed).  When `Some(i)`, a `Proj(i)` step is inserted before the key expression.

The `predicate` fields correspond to extra predicates that aren't expressable as hash join conditions; planning emits these as a downstream `iterate(predicate)` step on the joined output (op-conversion compiles that to a `Restrict` filter tile).

Future work:
1. Support loop joins inside hash joins (today the Loop nodes are always single-arm)
2. Support hash joins inside loop joins.  This will require a new CartesianProduct operator, as currently the only thing that can
do a cartesian product is iterating a type, and this needs to be downstream of nontrivial operators.
3. Bloom filters to optimize joins.  Instead of doing traditional join ordering, we'll do runtime bloom-filter passing as described in https://dl.acm.org/doi/pdf/10.1145/3725283

### Keyed Aggregates

Keyed aggregates are patterns like `sum(x) for x in groupby(xs, key_fn)` where:
- A collection is grouped by a key function
- An aggregation operation is applied to each group
- The pattern iterates first over the key, then over elements within that key's group

### The Optimization

The pass identifies constructs where a `curry` operator is applied to a function whose **domain**
carries a predicate refinement (`{(key, value) | …} ⇒ A` — the placement `lambda_elim` uses for the
correlated partition predicate; see `design-simple-sub.md` §4).
The refinement expresses equality with a key: elements are partitioned when the key function applied
to them equals a particular value. This pattern is rewritten to:

1. Swap the iteration order: instead of iterating both the collection and key together,
   iterate the collection and compute the key for each element
2. Use the `"converse"` combinator to group elements by their key values
3. Apply the aggregation operator to each group

This transformation reduces the domain iteration complexity and allows the runtime to optimize
group-by-key operations using dedicated grouping operators instead of generic iteration.

### Iteration-Site Marking (`insert_iterate_markers`)

`insert_iterate_markers` is the final step of planning.  It walks the CCL and inserts an explicit `Apply(predicate, Builtin::Iterate)` term at every position where operator conversion would compile with `input=None` and the expression is function-typed.  Refinement layers beyond the innermost are reified as a chain of `Apply(predicate, Builtin::Restrict)` mid-chain filters.  After the pass, op-conversion is a context-free dispatch on AST shape: it never inspects refinement structure to decide whether to start an iteration, and every iteration source it ever emits comes from exactly one CCL primitive.

For the full description of the input-policy split that this pass mirrors, see the [Operator Conversion section in `interpreter/design-operators.md`](/src/interpreter/design-operators.md#operator-conversion-interpreteroperator_conversionrs).  The short version:

- **Input-internalising arms** in op-conversion (`Sum`, `Max`, `Converse`, `MapDomain`, `Uncurry`, `FlattenDomain`, `PermuteDomain`, `CollectionUnion`, `LastOrDefault` stream side, `Loop` source, value-position `Record` fields, the catch-all `Apply`) compile their argument with `input=None`.  Each such argument is an iteration site and gets a chain-head `Apply(true ▷ const, Iterate)` as its source, with one `restrict(p)` *applied* per refinement layer.
- **Input-threading arms** (`Const`, `Zip`, `Map`, `Restrict` itself, and the `Var` / `Let` / `Compose` infrastructure) accept `input=Some(upstream)` and pass it through, so their children inherit the surrounding iteration and are not iteration sites.
- **The program root** and each function-typed field of a trailing sink-bound `Record` are iteration sites by *subscription*: the user-supplied consumer (or `SinkConsumer`) subscribes to the result, expecting an iterated stream.
- **Each function-typed bound expression in the top-level `Let` chain** is *also* wrapped, but not for that reason — the consumer subscribes to the program result, not to intermediate bindings.  The real reason is mechanical: op-conversion's `Let` arm compiles `bound_expr` *unconditionally* (`operator_conversion.rs`, `let bound_op = convert_impl(bound_expr, …)?`), whether or not `body` references the binding.  A function-typed bound expr that isn't iteration-bearing would then reach an `input=None` arm and error (e.g. the `List` arm's "list literal reached op-conversion without an input").  So the wrap is forced by eager compilation, not by subscription.  A consequence is that bindings are *not* inert: a dead iterable binding (`let x = [1, 2, 3] in 42`) is dropped by nothing today — it is eagerly compiled and iterate-wrapped (materialised) rather than eliminated.  Making iteration use-driven so the wrap becomes unnecessary is tracked by [#232](https://github.com/cambra-dev/Cambra/issues/232).

At each iteration site, `wrap_with_iterate` first tries the specialised hash-join rewrite (`try_hash_join_rewrite`); the iterate-then-restricts chain is the default when hash join doesn't match.  See [Hash Joins](#hash-joins) below for the recognised shapes and the join-plan tree.

When the hash-join rewrite doesn't fire, the chain that `wrap_with_iterate` emits is:
- A single chain-head `Apply(true ▷ const, Iterate)` over the unrefined base domain — op-conversion compiles this to a bare `IterateExtent` (no filter tile, since the predicate is trivially true).
- One `restrict(p)` *applied* per refinement layer, innermost-first.  Each `restrict` is a function transformer applied to the source it narrows — not a morphism composed with it — so `make_restrict` keeps the term well-typed (its honest second-order type makes a morphism-`Compose` ill-typed; `typecheck` now rejects that).  Op-conversion compiles each applied `restrict` to a `Restrict` tile fed the previous step's tile as `input=Some(_)`.
- The value-producing body is then composed onto that source (`source ≫ body`) as a genuine CCC morphism.

For an unrefined site, the source is just the chain-head iterate.  For a refined site `{D | p}`, it's `iterate ▷ (p ▷ restrict)`.  For nested `{{D | p_inner} | p_outer}`, it's `iterate ▷ (p_inner ▷ restrict) ▷ (p_outer ▷ restrict)` — matching the goldens (`tests/compilation_pipeline.rs:2296`, `:2388`).

`Apply(p, Iterate)` is rendered as `p ▷ iterate` in symbolic form, or as just `iterate` when `p` is the trivially-true predicate (a shortcut in `symbolic.rs` to keep program dumps readable; the underlying AST always carries the predicate).  `Apply(p, Restrict)` renders as `p ▷ restrict`.

#### Skip cases (`is_iteration_bearing`)

A chain head is left alone when wrapping it with iterate would either be redundant or break op-conversion:

- **Already iterate-led** — `Apply(_, Iterate)` at head.
- **Restrict-led** — `Apply(_, Apply(_, Restrict))` at head, i.e. the outer `restrict` filter of a refined site.  A `restrict` application always sits on an iteration source by construction (`make_restrict` only ever wraps an iteration-bearing upstream), so a refined site is iteration-bearing just as its unrefined `iterate`-led counterpart is.  Recognising it keeps the pass idempotent on refined sites — without it, a second marker walk would re-enter `wrap_with_iterate` on the still-refined domain and stack a second iteration source.
- **Provides its own iteration** — `Apply(_, MapDomain | Uncurry | Converse | CollectionUnion)` and the nested `PermuteDomain` / `FlattenDomain` applies.  These arms construct iteration internally from their argument, so prepending iterate would feed them an unwanted upstream stream.
- **Rejects `input=Some`** — value-position `Tuple` / `Record` literals (op-conversion's `Tuple` / `Record` arms assert `input.is_none()`) and the catch-all `Apply` with a non-builtin function (`Proj`, `Var`, curried `Apply`).
- **Function-typed `Var`** — the bound op was already iterate-wrapped at its let-bind site, so returning the `FanOut` branch directly is correct; an outer iterate would create a redundant `MapResult` lookup.

#### Special cases beyond the uniform "wrap argument" pattern

Three op-conversion arms have child-input policies that don't fit the single-argument shape:

- **`Apply(Tuple | Record, Zip)`** — Zip fans the upstream input out to each tuple/record element.  Those elements receive `Some(fan_out_branch)`, so they are not iteration sites.  The pass walks into the elements (to reach deeper iteration sites) without triggering the value-position `Record` / `Tuple` wrap.
- **`Apply(Tuple([stream, default]), LastOrDefault)`** — the tuple's first element (`stream`) is iterated; the second (`default`) is a scalar fallback for empty iteration and needs no marker.
- **`CollectionUnion`** — both the value-form node (`CollectionUnion(operands)`) and the function-form `Apply(Tuple(ops), CollectionUnion)` need each operand wrapped independently; op-conversion compiles each with `input=None`.

#### `Let` recursion

A top-level `Let { bound_expr, body }` is compiled by op-conversion's `Let` arm with `input=None`, which then fans `None` into both children.  The marker pass therefore recurses into both — wrapping function-typed bound expressions and walking the body — without prepending iterate to the `Let` itself (which would mis-thread input through to `bound_expr` and `body`).  The bound-expression wrap is unconditional because the `Let` arm compiles `bound_expr` eagerly regardless of whether `body` uses it (see the iteration-site list above); [#232](https://github.com/cambra-dev/Cambra/issues/232) tracks making iteration use-driven so an unused binding can be dropped instead of materialised.

#### Joins emit an `iterate` source with `restrict` filters applied

`JoinPlan::Loop` and `JoinPlan::Hash` emissions in `join_plan_to_expr` use `Builtin::Iterate` as the iteration source and `Builtin::Restrict` for the residual filters, the latter built with `make_restrict` (a `restrict` *applied* to its upstream):

- A leaf `JoinPlan::Loop` without a predicate emits `Apply(true ▷ const, Iterate)` over the arm's type (replacing the bare `Builtin::Id` used previously).
- A `JoinPlan::Loop` with a predicate emits `make_restrict(predicate, base_iter)` = `Apply(base_iter, Apply(predicate, Restrict))`, i.e. `base_iter ▷ (predicate ▷ restrict)` — the iterate provides the source and the applied restrict filters it.
- A `JoinPlan::Hash` with a residual predicate emits `make_restrict(predicate, map_domain)` = `map_domain ▷ (predicate ▷ restrict)` — same shape, but the restrict filters the joined output.

This is *application*, not composition: the `restrict` transformer's domain is a function type, so it cannot sit as a morphism in a `Compose` chain (`typecheck` rejects that).  Op-conversion compiles the outer `Apply`'s argument (`base_iter` / `map_domain`) with `input=None` via the catch-all arm — the `MapDomain` / `IterateExtent` arm sees no upstream input as required — and the `Restrict` arm then consumes that tile as `input=Some(_)` and applies the filter.

---

## Lambda Elimination (`ccl/lambda_elim.rs`)

`lambda_elim::run` converts a fully type-inferred CCL expression containing
`Lambda` nodes into a point-free expression of primitive combinators, following
the Cartesian Closed Category (CCC) structure described in
`docs/operational-semantics/lowering.md`.

### Output nodes introduced

| Source form | CCL AST after `lambda_elim` |
|---|---|
| `f ≫ g` | `BinOp { left: f, op: Compose, right: g }` |
| `.n` (projection) | `Proj(ProjKey::Index(n))` |
| `.field` | `Proj(ProjKey::Field("field"))` |
| `a + b` (and other non-compose BinOps) | `Apply { argument: Tuple([a, b]), function: Builtin(BinOp(op)) }` |
| `-x`, `not x` (UnaryOps) | `Apply { argument: x, function: Builtin(Neg) }` |

Non-compose `BinOp` and `UnaryOp` nodes are desugared uniformly to function
application form so that operator conversion can treat all operations as
combinators.  This applies at all levels: inside lambda bodies (via
`elim_lambda`) and at the top level of a program (via `elim_lambdas`).

### Built-in combinators

The output references built-in primitives via the `Builtin` enum carried by
`TypedExprNode::Builtin`. Each variant has a stable display name (matched by
the symbolic printer and used in the historical `Var(...)` rendering):

| Variant | Name | Meaning |
|---|---|---|
| `Builtin::Id` | `id` | identity morphism |
| `Builtin::Apply` | `apply` | function application as a morphism |
| `Builtin::Curry` | `curry` | currying |
| `Builtin::Uncurry` | `uncurry` | uncurrying |
| `Builtin::Const` | `const` | constant lift: `const(c) = λ _ → c` |
| `Builtin::Zip` | `zip` | product/fanout: `zip(f, g) = λ x → (f(x), g(x))`, written `⟨f, g⟩` |
| `Builtin::Map` | `map` | post-composition: `map(g)` applied to a curried function |
| `Builtin::MapDomain` | `map_domain` | domain-to-domain identity stream |
| `Builtin::Compose` | `compose` | composition as a first-class morphism |
| `Builtin::Restrict` | `restrict` | planning-introduced mid-chain filter, a codomain-parametric function transformer: `restrict(p) : (𝐷 ⇒ Bool) ⇒ (𝐷 ⇒ 𝑇) ⇒ ({𝑑: 𝐷 \| 𝑝(𝑑)} ⇒ 𝑇)`. It narrows the **domain** of an upstream `𝐷 ⇒ 𝑇` to the subset satisfying `𝑝`, preserving the value `𝑇` on the codomain — *not* the unsound `𝐷 ⇒ {𝑑: 𝐷 \| 𝑝(𝑑)}`. Because its domain is a function type it is **applied to** its upstream (`upstream ▷ (𝑝 ▷ restrict)`), never composed as a CCC morphism. Emitted by `planning` for every downstream filter step — the outer layers of a nested-refinement iteration site, the residual predicate of `JoinPlan::Loop`, and the residual predicate of `JoinPlan::Hash`. Op-conversion compiles the application via the generic applied-combinator arm: `upstream` is converted with `input=None`, then the Restrict arm consumes it (`input=Some(_)`), compiles the predicate against it, and wraps it in a `Restrict` tile. Chain-head iteration is the separate `Iterate` variant. |
| `Builtin::Iterate` | `iterate` | planning-introduced chain-head iteration source: `iterate(p) : {𝑑: 𝐷 \| 𝑝(𝑑)} ⇒ {𝑑: 𝐷 \| 𝑝(𝑑)}` (or `𝐷 ⇒ 𝐷` when `p` is the trivially-true `true ▷ const` — the refinement would carry no information, so the wrapper is omitted; refinements are transparent under `typecheck_equal`, so the two forms compose interchangeably). `planning` emits one at the head of every iteration site (aggregate arguments, the stream side of `LastOrDefault`, top-level function-valued results, sink-bound record fields, mutation-loop sources, …). Op-conversion's Iterate arm requires `input=None`; it compiles `Apply(p, Iterate)` to an `IterateExtent` tile (plus a `Restrict` filter when `p` is non-trivial). Mid-chain filtering is the separate `Restrict` variant. |
| `Builtin::Converse` | `converse` | grouping by key |
| `Builtin::PermuteDomain`, `Builtin::FlattenDomain` | `permute_domain`, `flatten_domain` | hash-join domain massaging |
| `Builtin::BinOp(op)` for any `op: BinOpKind` | `add`, `sub`, `eq`, `lt`, `and`, `or`, `concat`, … | every arithmetic / compare / boolean-logic / string-concat binary op (one variant, parameterised by the existing `BinOpKind` so the operator enum has a single source of truth) |
| `Builtin::{Neg,NotFn}` | `neg`, `not_fn` | unary operations |
| `Builtin::{Sum,Max}` | `sum`, `max` | aggregations (fold/reduce) |
| `Builtin::CollectionUnion` | `collection_union` | point-free function form of N-ary collection union, emitted only by lambda elimination when an inside-a-lambda `TypedExprNode::CollectionUnion` needs to be lifted out: `Apply(Tuple([a, b]), Builtin(CollectionUnion))`. The value-form node (top-level `TypedExprNode::CollectionUnion`) is the canonical shape; both compile to a `UnionOperator` tile. Surface `a ++ b ++ c` lowers directly to a flat N-ary value-form node — see §Union flattening for the construction-time invariant. |

Earlier passes encoded these with `TypedExprNode::Var("name")` against magic
strings; downstream pattern matches (`simplify`, `planning`,
`operator_conversion`) now switch directly on the `Builtin` variant.

### `zip` encoding

`⟨f, g⟩` (pointwise function pairing) is encoded as:
```
Apply { argument: Tuple([f, g]), function: Builtin(Zip) }
```
There is no dedicated `Zip` AST node; it reuses the existing `Apply` + `Tuple`
+ `Builtin` nodes.

### For-loop filter pattern in lambda elimination

For-loops lower directly to `Compose([src, Lambda(x, body)])`. Lambda elimination handles them through the existing `Lambda` and `Compose` arms, with one special case for the filter pattern.

**Filter pattern** (`elim_lambdas`, detected at the `Compose` level): a `Compose` whose last element is a `Lambda(x, Case { [guard → action, true → unit] })` (a two-branch filter case) is rewritten as a filtered composition:
```text
Compose([src, Lambda(x, { guard(x) → action(x); true → unit })])
  ⟹  src_refined ≫ elim_lambda(x, action)
```
where `src_refined` is `src_elim` with its domain wrapped in `Type::Refinement` carrying `guard` as a `Predicate`. `planning`'s `insert_iterate_markers` pass then reifies that domain refinement into an explicit `Apply(guard, Iterate)` at the iteration site, which op-conversion compiles to an `IterateExtent` + `Restrict` filter pair (equivalent to the refinement-lambda path used by list comprehensions).

The filter check happens at the `Compose` level (rather than inside the `Lambda` arm) because the refinement must be attached to the source, which is only visible alongside the lambda at the compose level.

### `Let` nodes after rule 7

When the lambda-elimination rule 7 rewrites a `Let` inside a lambda body, the
bound variable changes type from `T` to `ParamTy ⇒ T`. The rewritten `Let` node
has `bound_ty: None` because the old annotation is stale and would be incorrect.

---

## Inlining Pass (`ccl/inline.rs`)

`inline_non_iterable_lambdas` runs **after `infer`** and **before `lambda_elim`**.
It performs two structural rewrites on `Let` bindings, in order:

1. **Alias inlining** — eliminate `let y = x` pure α-renamings.
2. **UDF inlining** — substitute call sites for functions over non-iterable domains.

### Motivation

**Scalar UDFs** (e.g. `Fun(Int, Int)`): operator conversion compiles `Let`-bound
expressions independently with `input = None`. For a function whose domain is
scalar, this causes the operator graph to insert an `IterateExtent` for the
domain — which panics at runtime ("Attempted to iterate on infinite Extent")
because base types have no finite enumerable extent.

**List-producing UDFs** (e.g. generator `def`s, `Fun(Fun(UIntRange, Int), Fun(UIntRange, Int))`):
these lower to `λ user_arg → λ __iter_record → body`. If that nested-lambda
shape reaches `lambda_elim` intact, the rule emits a `curry` combinator —
and `operator_conversion.rs` doesn't implement `curry`, so compilation fails
with `unrecognised Var(curry)`.

Inlining at the CCL level threads the call-site argument as `input`, and
beta-reducing the outer lambda strips the user-parameter layer, leaving a single
`__iter_record`-wrapping lambda that matches the list-comprehension shape
`lambda_elim` already handles.

### Alias inlining

When the right-hand side of a `Let` is a plain `Var(x)`, the binding is pure
α-renaming. It is eliminated unconditionally by substituting `x` for the bound
name throughout the body — *unless* `x` is rebound by an inner `let x = …`
node inside that body, which would cause variable capture.

Performing this before `lambda_elim` prevents the let-in-lambda rule from
hoisting such bindings into `const(x)` wrappers that would need to be
recognised and stripped by downstream passes.

### What is inlined (UDF step)

A `Let { binding, bound_expr, body }` is inlined when `should_inline(bound_expr.ty)` returns `true`:

- `bound_expr.ty` is `Fun(domain, codomain)`
- `domain` is **not** iterable — i.e. `is_iterable_domain(domain)` is `false`

`is_iterable_domain` returns `true` for:
- `UIntRange(_)`, `DataSource(_)` — finite, enumerable
- `Tuple(ts)` where **all** components are iterable
- `Record(fields)` where **all** fields are iterable
- `Refinement(inner, _)` inheriting the iterability of `inner`

And `false` for:
- `Base(_)` (Int, String, Bool, etc.) — no finite enumeration of all values
- `Fun(_, _)` as domain — there are infinitely many possible functions of any
  given function type, so it cannot be enumerated. This case covers
  list-producing UDFs whose domain is itself a list-shaped function type.

### Substitution and beta-reduction

At each call site, substitution is paired with beta-reduction of the outer
user-parameter lambda. Apply chains terminating in `Var(name)` participate in
beta-reduction; unrelated `Apply(arg, Lambda)` patterns elsewhere in the tree
are left intact so list-comprehension bodies and scalar BinOp desugaring keep
the structure `lambda_elim` + `simplify` expect.

Multi-arg call-site bodies contain `Apply(Tuple(…), Proj(Index(i)))` (from the
uncurried `__arg_pair.i` references). Those literal-tuple projections are
folded later by `simplify::try_literal_tuple_projection`; this pass leaves
them in place.

After beta-reducing a UDF call, `inline_impl` is re-applied to the result so
that any newly-created `Let` bindings (e.g. from a defer-returning argument)
are also processed by the alias-inlining and lift steps.

### Pipeline position

```
infer   →   inline_non_iterable_lambdas   →   lambda_elim   →   planning   →   operator_conversion
```

### Limitations

- **Explicitly curried UDFs used unapplied** (e.g. `let f = λ x → λ y → body in g(f)`):
  `f` is inlined because its domain is non-iterable, but with no call site to
  beta-reduce against the outer lambda survives, lambda-elim emits `curry`, and
  compilation fails with "unsupported Builtin(curry)". Fully-applied curried calls
  (`f(1)(2)`) are fine — beta-reduction collapses both layers. Wiring `curry` in
  `operator_conversion.rs` is the follow-up that closes this gap entirely.
- **Collection UDFs** (domain `UIntRange` or `DataSource`): not inlined; they compile
  correctly via `Memo + FanOut` and benefit from sharing.
- **Body duplication**: a UDF called N times has its body duplicated N times in the
  operator graph. Acceptable for now; only collection-typed UDFs warrant caching.
- **Recursive UDFs**: unsupported (already noted in `operator_conversion.rs`).

---

## Compilation

There are two compilation passes that translate CCL into tile-dataflow operators. 

`interpreter/operator_conversion.rs` converts the λ-free CCL produced by `lambda_elim` + `simplify` into `TileOperator`s.  This process is mostly
a 1:1 correspondence, with each type of object lifted up to apply within a chain of composed terms.

| CCL form | Operator |
|---|---|
| `Compose([f, g, …])` | sequential pipeline: output of each feeds next |
| `zip(f, g)` | `FanIn` over a shared `FanOut`-wrapped domain (via the `fan_in` factory) |
| `zip({k: f, …})` | `fan_in_named` — record-of-morphisms fused via `FanIn::new_named` or `ScalarFanIn::new_named` |
| `id` | identity (pass-through) |
| `const(c)` | `MapResultToConst` |
| `map(g)` | `MapResult` |
| `Proj(Index(n))` | `tuple_field(n)` projection |
| `add`, `sub`, … | `apply_binop` |
| `neg`, `not_fn` | `apply_unaryop` |
| `iterate(p)` | chain-head iteration source: `IterateExtent` (when `p` is `true ▷ const`) or `IterateExtent ≫ Restrict` (otherwise) |
| `restrict(p)` | mid-chain filter: `Restrict` over the upstream input |
| `Lit` | `Constant` scalar |
| `Tuple([…])` | `ScalarFanIn` |
| `List([…])` | `MapResult` over index stream |
| `Source(name)` | data-source operator |
| `Let { binding, … }` | `Memo`-wrapped `FanOut` bound in scope |

End-to-end pipeline tests live in `tests/compilation_pipeline.rs`.

### `Let` nodes compile to a dedicated `Let` operator

`Let` is compiled to a first-class `Let` operator rather than desugared to `Apply(Lambda, value)`.

The desugaring identity `let x = e1 in e2 ≡ (λx. e2)(e1)` is operationally correct, but
compiling through it loses binding provenance in the graph and introduces unnecessary indirection:
data flows `apply.argument → lambda.var → lambda.body → lambda_producer → apply_producer`,
and `Lambda` must support both `VarSource::Iteration` and `VarSource::Argument` modes even
though a let-binding is always `Argument`.

The `Let` operator stores `(variable: Var, definition: Operator, body: Operator, extent: Extent)`.
`LetProducer::get()` returns the body's output directly — no `FunctionBindings` wrapping.
The bound variable is subscribed to `definition` exactly once via a `VarProducer`, so multiple
`VarRef(name)` nodes in the body all resolve to the same producer and the value is computed once.

**Prerequisite**: `binding.ty` on the `Let` node's `TypedBinding` must be resolved to a concrete type before compilation — the type inference pass fills it from the inferred type of `bound_expr`.

