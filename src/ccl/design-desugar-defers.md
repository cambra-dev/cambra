# `desugar_defers` — design and implementation

This doc describes how `src/ccl/desugar_defers.rs` actually works, the
invariants it maintains, and the limitations it still carries.  Read
[design-ccl-ast.md §Defer](design-ccl-ast.md#defer--feed--define--deferred-collection-operators-cccldesugar_deferrs)
first for the surface-syntax background; this doc picks up where that
section ends.

## What the pass does

CHL has three deferred-collection operators — `x = defer()`, `x << v`,
and `x <<= v` — that lower to three CCL AST nodes
([`TypedExprNode::Defer`], [`TypedExprNode::Feed`], and
[`TypedExprNode::Define`]) plus [`TypedExprNode::ExprStmt`] for
statement sequencing.  Those four variants are *placeholders*: they
don't denote pure values, and the type system has no rules for them.

`desugar_defers::run` runs **after lowering and before inference** and
eliminates all four variants.  After it returns, no `Defer`/`Feed`/
`Define`/`ExprStmt` nodes remain anywhere in the tree, and every
downstream pass (`infer`, `inline`, `lambda_elim`, `simplify`,
`operator_conversion`) treats those variants as
`unreachable!`.

The output is a plain CCL expression in which:

- Each `let d = Defer in body` is replaced by `let d = <channel> in
  body'`, where `<channel>` is the assembled defer-handle value
  (typically `Fun(D, T)`) and `body'` is `body` with every `Feed(d,
  V)` / `Define(d, V)` extracted into the channel.
- Multiple `Feed`s for the same defer are combined via
  `TypedExprNode::CollectionUnion` (the surface `++` operator).
- Cross-defer references resolve through topological ordering of
  cluster bindings.
- Defer-mediating UDF calls (`y = f(x)` where `f` takes/returns a
  defer) are reduced at the call site **without inlining** the
  function body.  The function's body is rewritten at its binding
  site to return a `Record({to_<target>: contribs, …})`; each call
  site contributes `Apply(call_expr, Proj("to_<target>"))` to the
  surrounding cluster's channel.

## Two-phase structure

`run` is two passes over the tree:

```
run(expr) = expr
  |> rewrite_chains_in_scope      // Phase 1: defer-mediating UDF call rewriting
  |> desugar                      // Phase 2: cluster channelization
  |> drop_expr_stmts               // post-pass: ExprStmt cleanup
  |> assert_no_defer_residue       // invariant check
```

Phase 1 rewrites call chains that touch defer-mediating functions so
the cluster algorithm in Phase 2 can see uniform shapes.  Phase 2
walks each `let d = Defer in …` cluster and emits the channelized
form.

---

## Phase 1 — chain rewriter

### Lambda classification

A let-bound lambda is classified by its defer interaction
([`LambdaClass`]):

| Class               | Body shape (post-float for `DeferIntroducing`) | Example                                       |
|---------------------|------------------------------------------------|-----------------------------------------------|
| `VarBody`           | `λp → Var(name)`                               | `def f(x): return x`                          |
| `ParamAsTarget`     | `λp → body` where `body` has `Feed(p, …)`      | `def g(c): c << 100; c`                       |
| `DeferIntroducing`  | `λp → let x = Defer in body` (pre-float)       | `def f(n): x = defer(); x << n; x`            |
| `Plain`             | Anything else (no defer interaction)           | `def add(a, b): return a + b`                 |

Classification is done in order of structural specificity: `VarBody`
first, then `DeferIntroducing` (must float before treating as
anything else), then `ParamAsTarget`, then `Plain`.  See
[`classify_lambda`].

### The float transformation

A `DeferIntroducing` lambda is *floated* before any rewriting:

```text
λp → let x = Defer in body[x]
  ⟹  λp → λ__floated_x → body[x → __floated_x]
```

[`float_defer_in_lambda`] does this in place at the lambda's
definition site.  The internal `Defer` becomes a second explicit
parameter, named `__floated_<x>` (a breadcrumb of the original
name).  The class of the post-float lambda is still
`DeferIntroducing`, but now the body shape is `λp → λ__floated →
body` — recognisable by the classifier's "curried two-lambda"
arm.

### Chain wrapping

The chain rewriter walks the tree top-down, registering each
defer-mediating function in a lexically-scoped `HashMap` on
`DesugarCtx`.  When it finds an `Apply` chain that touches a registered
function ([`chain_has_di`] returns true), it rewrites the chain.

The structural rewrite: each direct call `Apply(arg, Var(f))` of a
floated `DeferIntroducing` function gets the missing second
application of a fresh defer handle:

```text
Apply { function: Var(f), argument: arg }
  ⟹  Apply { function: Apply { function: Var(f), argument: arg },
             argument: Var(<defer_name>) }
```

The reasoning: the user wrote `f(arg)` expecting a defer back, but
the floated `f` takes two args (`p` and `__floated`).  Inserting
`Var(<defer_name>)` as the second application supplies the missing
floated handle.

For the **outermost** DI call in a chain, `<defer_name>` is the
let-binding's name (the user's `y` in `let y = f(arg) in …`).  For
**inner** DI calls in composed chains, [`wrap_di_calls_in_chain`]
mints a fresh `FloatedDefer` synthetic name (`Name::floated()`, displayed
`__floated`) and returns it for the caller to allocate via
`let __floated = Defer in …`.

After wrapping, the let becomes:

```text
let <outermost_defer> = Defer in
let __floated = Defer in
…
ExprStmt(<wrapped chain>, <body>)
```

The wrapped chain is now in a shape Phase 2 can walk.

### What gets rewritten where

`rewrite_chains_in_scope` has two trigger paths:

1. **`let y = <chain>`** — if `<chain>` contains a DI call, use `y` as
   the outermost defer name and emit a `let y = Defer in …` prefix.
2. **`<chain>` at expression position** — not let-bound; allocate a
   fresh `FloatedDefer` synthetic (`Name::floated()`) and emit it as both
   the outermost defer and the chain's reduction target.

A `let f = lambda in body` where the lambda is defer-mediating
registers `f` in the function context, recurses into the body
(which may contain calls to `f`), and **keeps the `let f = …`
binding intact in the output** of this phase.  Phase 2 may drop it
later (see below).

---

## Phase 2 — cluster channelization

[`desugar`] walks the rewritten tree once.  Most arms recurse
structurally; the load-bearing arms are:

### `let d = Defer in body` — cluster detection

When the bound expression is `Defer`, peel off the entire cluster of
consecutive `let d_i = Defer in …` bindings.  This handles patterns
like

```chl
x = defer()
y = defer()
x << y
y << [0, 1]
```

where `x`'s channel references `y` and vice versa.  Processing one
defer at a time and stacking the bindings in walk order produces a
let-chain in the wrong dependency order for at least one such
program.

After collecting `defer_names`, recurse into the cluster body, then
call [`channelize_cluster`].

### `channelize_cluster`

For each defer in the cluster (innermost first):

1. Call [`extract_for_defer`] on the body, threading mutable `feeds:
   Vec<Expr>` and `define: Option<Expr>`.  This walks the body,
   collecting `Feed(d, V)` values into `feeds` and replacing them
   with `Lit::Unit`, and the at-most-one `Define(d, V)` into
   `define`.  Other defers' Feed/Define nodes are passed through.

2. Determine the channel:
   - If `feeds` is empty and `define` is `None`: `DeferError::NoFeedOrDefine`
   - If both are present: `DeferError::FeedsAndDefinesMixed`
   - If only `define`: the channel is the define value verbatim
   - If only `feeds`: combine via [`combine_feed_values`] (a single
     N-ary [`TypedExprNode::CollectionUnion`] for multiple feeds;
     pass-through for a single feed)

3. Stash the channel under `name` in a `HashMap<String, Expr>`.

After all defers have been processed, sort the cluster
topologically ([`topo_sort_cluster`]) using [`count_free`] to detect
cross-defer references.  A defer whose channel references another
cluster defer is bound *after* the referenced defer.  Cycles
(`x ≪= y; y ≪= x`) are reported as `DeferError::MutuallyRecursiveCycle`.

Finally, emit the cluster's bindings at the body's terminal via
[`rename_shadows_then_bind`].

### `rename_shadows_then_bind`

Walks the (already-processed) body through `Let`/`ExprStmt` chains
to its terminal, then prepends the cluster's let-bindings in
topological order.

Two complications along the way:

- **Shadow renaming.**  If the body contains `let n = … in inner`
  for some `n` that channel expressions reference, the channel's
  free `n` would resolve to the body's binding instead of the outer
  scope's.  [`compute_protected_set`] identifies these names; for
  each shadowing `Let`, the binding is α-renamed to a fresh
  `ShadowRename` synthetic (`Name::shadow_rename()`) and the inner
  body's references are substituted.

- **Cross-cluster references through intervening lets.**  Patterns
  like `let d_1 = Defer in let z = E in let d_2 = Defer in …` where
  `d_2`'s channel references `d_1` need `d_1` bound *before* the
  `let z`.  When `rename_shadows_then_bind` finds a `Let` whose
  `bound_expr` references any of the cluster's names, it emits the
  cluster bindings before that let rather than continuing to the
  terminal.

### `extract_for_defer` — the per-defer body walker

This is the hot path.  It walks `body` once for a given `defer_name`
and:

- Pulls `Feed(defer_name, V)` and `Define(defer_name, V)` into
  the caller's `feeds` / `define` accumulators.
- Lifts top-level scalar feeds to `Fun(Unit, T)` via `λ __unused :
  Unit → V` when `in_inner_scope == false`.  Per-iteration feeds
  (inside Lambda/Loop bodies) stay scalar and are wrapped by the
  surrounding iteration shape.
- Handles half a dozen specialized shapes (next subsection).
- For everything else, recurses structurally and returns the same
  shape with feeds extracted.

The function is large (~700 lines) because each specialized shape
needs its own case.

### Specialized extraction paths

#### Top-level scalar feed lift

For `Feed(d, V)` at `in_inner_scope == false`:

```text
Feed(d, V)  ⟹  feeds += [λ __unused : Unit → V];   replace with Unit
```

This makes the channel match the defer handle's expected `Fun(Unit,
T)` shape at the cluster bind site.

#### Compose/Apply with iteration lambda

For `Apply(prefix, Lambda(x, body))` where `body` contains feeds:

```text
Apply(prefix, Lambda(x, Feed(d, V)))
  ⟹  Apply(prefix, Lambda(x, V))  as a channel contribution
     +
     Apply(prefix, Lambda(x, Unit))  as the new tree
```

The channel is the *companion* `Apply(prefix, λx → V)` — same
iteration shape, yielding the feed value instead of `Unit`.

Same pattern for `Compose([prefix..., Lambda(x, body)])`.

#### Loop body absorption — `process_loop_for_defer`

For `let acc_stream = Loop {…} in body` where the loop body contains
feeds for `defer_name`:

- The body's terminal `Record({step, …})` is augmented with one
  `to_<defer>_<k>` field per feed site ([`augment_loop_body_record_multi`]).
- The outer channel contribution becomes `Var(acc_stream) ▷
  Proj("to_<defer>_<k>")`, unioned via `++` across `k`.

Without the let-binding wrap, the loop expression would have to be
cloned into each channel projection — duplicating the recurrence
cycle in the operator graph.  Using `Var(acc_stream)` lets all
projections share the single loop.

#### Filter-feed pattern — `try_extract_filter_feed`

For a 2-arm Case `λp → Case { guard → Feed(d, V); true → Unit }`:

```text
pred_on_source = source ≫ (λp → guard)
refined_source = source with user_annotation = Fun(Refinement(_, pred_on_source), _)
channel = refined_source ≫ (λp → V)
```

The original Lambda's body collapses to `Unit`.  Inference treats
the refinement-typed source as a filtered iteration; `planning`'s
`insert_iterate_markers` pass reifies the refinement into an explicit
`Apply(guard, Iterate)` at the iteration site, which op-conversion
compiles to an `IterateExtent` + `Restrict` filter pair.

#### Case-arm fan-out (multi-arm Case with feeds)

When a Case with 3+ arms has feeds in some-but-not-all arms (so
`try_extract_filter_feed` doesn't match), each arm's terminal is
wrapped in `Record({result, to_<d>})`:

- Feeding arm: `to_d` = combined feed values
- Empty arm: `to_d` = [`empty_channel()`] = `Lit::Unit`

This path is **known broken** — see [Future work](#known-gaps--future-work).
The realistic 2-arm shape uses `try_extract_filter_feed` and avoids
the issue.

#### Smart-walker for defer-mediating UDF calls — return-value design

A defer-mediating function `f` is registered in `DesugarCtx` along
with the set of defer targets its body feeds.  At its `let f = …`
binding site, [`rewrite_lambda_to_return_contributions`] replaces
the lambda's body with a `Record({to_<target_k>: contribs_k, …})`
(see [`build_contributions_record`]).  The function returns the
contributions Record, computed in terms of the function's own
params, rather than returning its defer-handle param.

At each call site of `f`, the smart walker
([`try_smart_walk_pat`] / [`try_smart_walk_di`]) fires.  Both share
[`smart_walk_synthesize_call_contributions`], which:

1. Looks up `f`'s [`FunctionInfo`] in `DesugarCtx` —
   `feed_targets` and `primary_target` are populated at Phase 2
   registration time.
2. Pushes `Apply(call_expr, Proj("to_<current_target>"))` into the
   surrounding cluster's `feeds` Vec.  At runtime this projects the
   primary target's contribution out of the call's Record return.
3. For every other target the function feeds (closure-captured
   defers — names cross the function boundary unchanged),
   synthesizes a `Feed(<other_target>, Apply(call_expr, Proj("to_<other_target>")))`
   at the call site.  Those Feed nodes get picked up by their own
   clusters' standard walks.
4. Returns the chain `ExprStmt(feed_0, ExprStmt(feed_1, …, Var(<defer_name>)))`
   as the call's residue.  The final `Var(<defer_name>)` is the
   call's reduction value (defer-handle returns of PaT/DI both
   reduce to the cluster's defer-handle variable).

The function is **not duplicated** at the call site: the call
expression itself stays in the output and is type-inferred normally.
Only the call's *projections* live in the cluster channels, and
they reference a single shared `call_expr` subtree per call site.
At runtime each `Apply(call_expr, Proj("to_X"))` evaluates the
function once and pulls out the requested field.

**`Var(<defer>)` substitution.**  The chain rewriter wraps every DI
call with `Var(<defer>)` as the second argument so the curried
`λp → λ__floated → body` reduces.  In the return-value design
`__floated` is unused inside the rewritten body — the body's feeds
contribute to Record fields rather than referencing `__floated`
directly.  Keeping the `Var(<defer>)` in the projection
expression would build a self-referential
`let <defer> = … Var(<defer>) … in …` binding (the channel
expression references the very binding it constructs), which CCL
doesn't support without letrec.  The synthesizer substitutes
`Var(<defer>) → Lit::Unit` inside the call expression before
projecting; the rewritten body discards that argument anyway.  Same
fix applies to PaT calls.

**Defer-introducing functions with no feeds.**  A function like
`def f(n): x = defer(); x` (DI, but the body never feeds `x`) has
an empty `feed_targets`.  Its rewritten body is `Record({})`,
which has no fields to project from.  The synthesizer detects
`feed_targets.is_empty()` and skips both the primary projection
and any closure-capture synthesis — the call contributes nothing,
and the surrounding cluster gathers its feeds from outside the
function (typical: `let y = f(10) in for i in src: y << i`).

#### Defer-returning let-lift — `try_lift_defer`

For `let y = (let x = Defer in body_x) in body_y` where `body_x`
ends in `Var(x)`:

```text
let y = (let x = Defer in body_x) in body_y
  ⟹  let y = Defer in body_x[x → y]    with terminal Var(y) replaced by body_y
```

`pre_infer_substitute` renames `Feed("x", …)` and `Define("x",
…)` target strings to `y` so the outer cluster picks them up.
Also handles an `ExprStmt` prefix on the outer `bound_expr`.

There's also a related "let-of-defer-returning-let collapse"
pattern: `let y = (let z = E in Var(z)) in body_y` becomes
`let z = E in body_y[y → z]`.  Surfaces deeper defers (inside `E`)
so a subsequent `try_lift_defer` pass can fire.

#### Alias inlining for defer handles

`let y = Var(x) in body` where the body contains
`Feed(y, …)`/`Define(y, …)` is α-renamed to `body[y → x]` (with
`pre_infer_substitute` retargeting the Feed/Define names to `x`).
Runs *before* defer channelization so the cluster walker sees the
real defer name.

Only fires when (1) the body uses `y` as a defer handle, and (2)
`x` isn't rebound by an inner Let inside the body (capture-safe).
Plain non-defer aliases are left for [`crate::ccl::inline`].

### Post-pass cleanup

`drop_expr_stmts` collapses every remaining `ExprStmt(e, b)` to
just `b`.  By this point every `e` is pure — `Feed`/`Define` sites
have been replaced with `Lit::Unit`, so the discarded value is
known-Unit and dropping it is value-preserving.

`assert_no_defer_residue` walks the tree to confirm no
`Defer`/`Feed`/`Define` nodes survived.  Any residue indicates a
shape the pass didn't recognise — reported as
`DeferError::UnboundDeferHandle`.

---

## Error modes

| Variant                              | Triggered by                                                                          |
|--------------------------------------|---------------------------------------------------------------------------------------|
| `NoFeedOrDefine(name)`               | `let d = Defer in body` where no `Feed(d, …)` or `Define(d, …)` exists in body        |
| `MultipleDefinitions(name)`          | Two or more `Define(d, …)` for the same defer                                         |
| `FeedsAndDefinesMixed(name)`         | A defer has both `Feed(d, …)` and `Define(d, …)` contributions                        |
| `NestedDefinition`                   | `Define(d, …)` inside a Loop body, Compose element, Case branch, or Lambda            |
| `UnboundDeferHandle(name)`           | `Feed`/`Define` references a name never bound by `let d = Defer`                      |
| `MutuallyRecursiveCycle(name)`       | Cluster defers reference each other cyclically (`x ≪= y; y ≪= x`)                     |

All variants are propagated to `CompileError::DesugarDefers` and
surfaced to the user via `CompileError::render`.

---

## Known gaps & future work

### 1. Filter-feed refinement doesn't reach `operator_conversion`

[`try_extract_filter_feed`] attaches a `Refinement` to the source's
`user_annotation` so the source is treated as filtered iteration.
With the return-value design, the filter-feed path runs *inside*
[`build_contributions_record`] when rewriting a function body, and
the refined source ends up inside the function's returned `Record`.
After inference, the refinement carries through to the
cluster-binding's type — but the value expression at the binding
site is now `Apply(call_expr, Proj("to_<target>"))`, which doesn't
expose the refinement on its own `expr.ty`.

`planning`'s `insert_iterate_markers` pass walks each function-typed
expression and reifies its domain refinement into a chain-head
`Apply(true ▷ const, Iterate)` source with one `restrict(p)` *applied*
per refinement layer (`iterate ▷ (p ▷ restrict) ▷ …`), which
op-conversion compiles to an `IterateExtent` plus one `Restrict` tile
per layer.  Today the pass reads the
refinement from the value-expression's type (the wrapped function
value); it does not look at any refinement attached to the surrounding
let-binding's type, so a refinement that only surfaces on the binding
(the cluster binding's type after inference) is silently dropped — and
end-to-end, the `test_generator_function::positives` case currently
produces the unfiltered list.

A known TODO is extending the planning walk to honour refinements
attached to let-binding types (the cluster binding's type carries
the refinement after inference; that's the right place to read it
from).  Once that lands:

- Drop the `if code.contains("def positives")` skip guard at the
  top of [`tests/compilation_pipeline.rs::test_generator_function`].
- No changes are needed to `desugar_defers` itself — the
  refinement is already in the right place; only the consumer
  needs updating.

### 2. Case-arm fan-out is broken (`empty_channel` limitation)

When a Case has 3+ arms with feeds in some-but-not-all, the
Case-arm fan-out path is taken: each arm publishes a
`Record({result, to_d})` where the no-feed arm's `to_d` is
[`empty_channel()`] = `Lit::Unit`.  Feeding arms publish a typed
scalar (e.g. `Var(x) : Int`).  Inference rejects the Case because
arm Record types don't unify.

Patching the type slot (e.g. via a `TypedExprNode::EmptyValue`
with fresh `Type::Infer`) was considered and rejected: it fixes
the typecheck error but trades it for a silent miscompile — the
Case fan-out would still produce a per-iteration `to_d` for every
iteration, including no-feed arms, leaking placeholder values
into the consumer's stream.

**Proper fix: refinement-based fan-out** (generalize
[`try_extract_filter_feed`] to N arms).  For each feeding arm
`i`, build a refined source with predicate `¬g_0 ∧ ¬g_1 ∧ … ∧
¬g_{i-1} ∧ g_i` (Case's "first matching guard wins" semantics)
and contribute `refined_source ≫ (λp → feed_value)` to the
cluster channel.  Arms without feeds contribute nothing — no
empty-channel placeholder needed.  Both the typecheck and
runtime gaps vanish together.

This path is unreachable from CHL today because lowering rejects
`elif` inside generator-for-loop bodies — the multi-arm Case
form never gets constructed from source.  Tracked end-to-end in
[`tests/compilation_pipeline.rs::multi_arm_case_with_some_feeding_branches_is_a_known_gap`].

### 3. Higher-order use of defer-mediating functions

In the return-value design, a defer-mediating function's body is
rewritten at its binding site to return `Record({to_<target>: …, …})`.
Direct calls of the form `Apply(arg, Var(f))` (or the DI two-step
shape) are handled by the smart walker, which projects the
relevant `to_<target>` field at each call site.

If `f` is referenced indirectly — passed as a value into `map`,
aliased through `let g = f`, anything outside the recognized call
shapes — the call doesn't go through the smart walker.  The
surviving call evaluates the rewritten function, which now
*returns a Record* instead of its original defer-handle param.
Callers expecting the original signature get a type mismatch at
inference time.

No test exercises this today; the gap is latent.  A real fix
would either:

- Detect higher-order use at the binding site (look for
  `count_free(f, body)` references that are *not* in an
  `Apply(_, Var(f))` chain) and synthesize a wrapper lambda that
  unpacks the contributions Record into per-target Feed sites at
  the call site.
- Reject higher-order use of defer-mediating functions at
  lowering with a clear diagnostic.

### 4. Non-trivial return values from defer-mediating UDFs

`try_smart_walk_pat` reduces a `ParamAsTarget` call to
`Var(<defer_name>)`, on the assumption that `g`'s body returns its
param.  For bodies like `def g(c): c << 100; c + 1` (returning a
non-param value), this is wrong — the call's value is the
substituted return expression.  The smart walker silently
discards the body's tail.

Not currently exercised by tests; tracked in the implementation
as a known limitation.  A real fix would have the smart walker
return the substituted body's terminal (with `Feed`/`Define`
already stripped) instead of `Var(<defer_name>)`.

### 5. `try_lift_defer` covers only a single nesting level

The lift handles `let y = (let x = Defer in body_x) in body_y`
and the let-of-defer-returning-let collapse, but deeper
nestings (UDF inlines that produce three or more lift sites)
would need multiple passes to fully unwind.  The current
implementation runs each pattern once per `desugar` recursion;
cascading lifts work because each pass surfaces the next
candidate, but pathological shapes could need more iterations.

Not currently exercised; flagged for awareness.

---

## Implementation map

For navigating the source ([src/ccl/desugar_defers.rs](desugar_defers.rs)):

| Concern                                    | Function                                              |
|--------------------------------------------|-------------------------------------------------------|
| Entry point                                | `run`                                                 |
| Phase 1 chain rewriter                     | `rewrite_chains_in_scope`                             |
| Phase 2 cluster walk                       | `desugar`                                             |
| Lambda classification                      | `classify_lambda`                                     |
| Defer float                                | `float_defer_in_lambda` + `extract_defer_binding`     |
| DI chain wrap                              | `wrap_di_calls_in_chain` + `wrap_di_calls_helper`     |
| DI chain detection                         | `chain_has_di`                                        |
| Per-defer feed extraction                  | `extract_for_defer`                                   |
| Lambda body rewrite (returns Record)       | `rewrite_lambda_to_return_contributions`              |
| Per-target contribution Record build       | `build_contributions_record`                          |
| Smart-walker for PaT calls                 | `try_smart_walk_pat`                                  |
| Smart-walker for DI calls                  | `try_smart_walk_di`                                   |
| Call-site contribution synthesis           | `smart_walk_synthesize_call_contributions`            |
| Filter-feed (2-arm Case)                   | `try_extract_filter_feed`                             |
| Defer-returning let lift                   | `try_lift_defer`                                      |
| Loop body absorption                       | `process_loop_for_defer` + `augment_loop_body_record_*` |
| Case-arm fan-out (broken)                  | `empty_channel` + `augment_terminal_with_channel`     |
| Cluster topo-sort                          | `topo_sort_cluster`                                   |
| Channel binding emission                   | `channelize_cluster` + `rename_shadows_then_bind`     |
| Shadow detection                           | `compute_protected_set` + `collect_free_vars`         |
| Substitution                               | `pre_infer_substitute`                                |
| Final cleanup                              | `drop_expr_stmts`                                     |
| Invariant check                            | `assert_no_defer_residue`                             |
