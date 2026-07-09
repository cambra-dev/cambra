# `desugar_defers` — design and implementation

This doc describes how `src/ccl/desugar_defers.rs` actually works, the
invariants it maintains, and the limitations it still carries.  Read
[lowering.md — deferred collection operators](lowering.md#deferred-collection-operators--defer----)
first for the surface-syntax background; this doc picks up where that
section ends.

## What the pass does

CHL has three deferred-collection operators — `x = defer()`, `x << v`,
and `x <<= v` — that lower to three CCL AST nodes
([`TypedExprNode::Defer`], [`TypedExprNode::Feed`], and
[`TypedExprNode::Define`]) plus [`TypedExprNode::ExprStmt`] for
statement sequencing.  Inference types them directly (`Defer` mints a
feed-handle type `Type::Feed(ρ)`, feeds/defines contribute into `ρ`,
reads discharge through the handle — see design-simple-sub.md §"Feed
handles"), so type errors are reported against the user's program
shape.

`desugar_defers::run` runs **after inference and after the induction
`letrec_phase`** (`compile_program`: parse → lower → infer → inline →
letrec_phase → recognize → desugar → strict typecheck → …) and eliminates
all four variants *and* their transient `Feed` / `Infer`-channel-
domain types.  Running after the phase means an in-loop feed has already
been hoisted to an ordinary feed of the loop's history, so desugar sees
only top-level defer chains.  After it returns, no
`Defer`/`Feed`/`Define`/`ExprStmt` nodes — and no `Feed`/`Hole`/`Infer`
types — remain anywhere in the tree, and every downstream pass
(`lambda_elim`, `simplify`, `operator_conversion`) treats those variants
as `unreachable!`.  (`inline` runs *before* desugar, not after, so it
still sees `Defer`/`Feed`/`Define` — see the `inline` module docs.)

**The pass is type-preserving.**  The input tree arrives fully typed;
desugar follows a small discipline — constructed nodes carry `Hole`,
filter-feed sources get their refined domain and (fully-typed) predicate
stamped directly (`refine_source_domain`) — and ends with
[`crate::ccl::infer_simple_sub::retype`], a solver-free bottom-up
synthesis that re-derives every residue type from the surviving
concrete types (iterated to a bounded fixpoint so call-site argument
types can resolve a monomorphized generator parameter's channel
domain).  The strict post-desugar `typecheck` in `compile_program` is
the release-visible enforcement of this contract; `run` additionally
asserts residue-freeness in debug builds.

(The pass also still supports untyped input — `run(expr, false)` — for
its own structural unit tests; in that legacy mode the type-synthesis
steps are skipped entirely.)

The output is a plain CCL expression in which:

- Each `let d = Defer in body` is replaced by `let d = <channel> in
  body'`, where `<channel>` is the assembled defer-handle value
  (typically `Fun(D, T)`) and `body'` is `body` with every `Feed(d,
  V)` / `Define(d, V)` extracted into the channel.
- Multiple `Feed`s for the same defer are combined via
  `TypedExprNode::CollectionUnion` (the surface `++` operator).
- Cross-defer references resolve through topological ordering of
  cluster bindings.

**A note on scope — the pass was slimmed to a single phase.**
`desugar_defers` used to carry a second phase: a chain rewriter that
reduced *defer-mediating UDF* calls (calls of a function that takes or
returns a `defer` handle) at their call sites, rewriting the function
body to return a contributions `Record` rather than inlining it.  That
machinery — lambda classification, the `Defer`-float transformation,
DI-chain wrapping, the return-`Record` body rewrite, and the call-site
"smart walker" — is **gone**.  [`crate::ccl::inline`] runs *before*
this pass and beta-reduces every defer-mediating UDF at its call site,
so by the time desugar runs there are no such calls left: it only ever
sees flattened `let d = Defer in …` chains.  What remains is a
**single-phase cluster channelizer**.

The broader goal is to retire this pass entirely — folding channel
assembly into the unified sequencing phase so feeds lower through the
same road as stores.  See [`mutability.md`](mutability.md) §4 "Retire
`desugar_defers`" for the target design and current status.

## Pipeline

`run` is a single structural pass over the tree (plus, on typed input,
the closing type synthesis):

```
run(expr, input_typed) = expr
  |> desugar                       // cluster channelization
  |> drop_expr_stmts               // post-pass: ExprStmt cleanup
  |> assert_no_defer_residue       // invariant check
  |> retype                        // typed order only: re-derive residue types
```

[`desugar`] walks each `let d = Defer in …` cluster and emits the
channelized form; the remaining steps drop the now-pure `ExprStmt`
residue, assert no defer nodes survived, and re-synthesize the types
the walk disturbed.

---

## Cluster channelization

[`desugar`] walks the tree once.  Most arms recurse
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
refined_source = source with ty = Fun(Refinement(D, pred_on_source), V)
channel = refined_source ≫ (λp → V)
```

The original Lambda's body collapses to `Unit`, and
[`refine_source_domain`] stamps the refined domain type directly off
the source's inferred `Fun(D, V)` (the legacy untyped order parks the
same refinement in `user_annotation` for inference to consume).
`planning`'s `insert_iterate_markers` pass reifies the refinement into
an explicit `Apply(guard, Iterate)` at the iteration site, which
op-conversion compiles to an `IterateExtent` + `Restrict` filter pair.

#### Multi-arm Case with feeds

A multi-arm `Case` that feeds the defer in some arm (so it is *not* the two-arm
filter shape `try_extract_filter_feed` handles) is rejected with
`DeferError::PartialFeedCaseUnsupported`. The former Record-based fan-out (each
arm publishing `Record({result, to_<d>})`, no-feed arms getting an ill-typed
`Unit` placeholder) is retired in favour of the N-arm refinement fan-out — not
yet built. See [Future work](#known-gaps--future-work). The realistic 2-arm
shape goes through `try_extract_filter_feed` (gap #1) and is unaffected.

#### Defer-returning let-lift — `try_lift_defer`

For `let y = (let x = Defer in body_x) in body_y` where `body_x`
ends in `Var(x)`:

```text
let y = (let x = Defer in body_x) in body_y
  ⟹  let y = Defer in body_x[x → y]    with terminal Var(y) replaced by body_y
```

`desugar_substitute` (a thin wrapper over the uniform engine,
`ccl::subst::Subst::rewrite_expr`) renames `Feed("x", …)` and
`Define("x", …)` target names to `y` so the outer cluster picks them
up — and, through the engine, also rewrites type-carried refinement
predicates that close over the renamed binder. Also handles an
`ExprStmt` prefix on the outer `bound_expr`.

There's also a related "let-of-defer-returning-let collapse"
pattern: `let y = (let z = E in Var(z)) in body_y` becomes
`let z = E in body_y[y → z]`.  Surfaces deeper defers (inside `E`)
so a subsequent `try_lift_defer` pass can fire.

#### Alias inlining for defer handles

`let y = Var(x) in body` where the body contains
`Feed(y, …)`/`Define(y, …)` is α-renamed to `body[y → x]` (with
`desugar_substitute` retargeting the Feed/Define names to `x`).
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
| `PartialFeedCaseUnsupported(name)`   | A multi-arm `Case` feeds `d` in some arms but not others (no typed empty channel yet) |

All variants are propagated to `CompileError::DesugarDefers` and
surfaced to the user via `CompileError::render`.  Because the pass runs
after inference, *type* errors surface first: a program with both a
type error and a structural defer error reports only the type error,
and a never-bound feed target now arrives as
`InferError::UnboundVariable` from the `Feed`/`Define` typing rules
(`UnboundDeferHandle` remains as the pass's own residue tripwire).  One
ordering nuance: a scalar `Define` mixed with `Feed`s on the same defer
collides in the feed-handle payload during inference
(`IncompatibleBounds`) before `FeedsAndDefinesMixed`'s clearer message
is reached.

---

## Known gaps & future work

### 1. Filter-feed refinement — resolved

The two-arm filter-feed (`if guard: d << v` in a loop / generator) now compiles
end-to-end. [`try_extract_filter_feed`] recognises the shape and the caller
builds the channel's refined source with the **bare element predicate**
`__elem ▷ source ▷ (λ p → guard)` — the same form a filtered comprehension
`[v for p in source if guard]` builds ([`crate::ccl::lower::comprehension`]) —
fully typed at construction, then [`refine_source_domain`] wraps the source's
domain in `Refinement(_, pred)`. `planning`'s `insert_iterate_markers` reifies
that domain refinement into a chain-head `Apply(true ▷ const, Iterate)` with one
`restrict(p)` per layer, which op-conversion compiles to an `IterateExtent` plus
a `Restrict` tile.

Two earlier bugs are corrected by this: (a) the predicate compose was left
`Hole`-typed, and — since a `Refinement` predicate is immutable, `retype` never
re-derives it — the `Hole` reached the strict post-desugar typecheck; (b) the
predicate was built in the point-free `source ≫ (λ p → guard)` form, which is
constant in `__elem`, so `planning::compile_refinement_predicates` η-collapsed it
to `const(_)` and dropped the per-element test. The element form
`__elem ▷ source ▷ (λ p → guard)` fixes both. `feed_with_if`,
`test_generator_function::positives`, and the `generator_pipeline` program are
un-`#[ignore]`d.

### 2. Multi-arm Case-with-feeds fan-out (N-arm) not yet supported

A multi-arm `Case` that feeds the defer in one or more arms is rejected up
front with `DeferError::PartialFeedCaseUnsupported`. The two-arm filter shape
`{guard → d << v; true → unit}` is *not* affected — it is handled earlier as a
refined-source channel (gap #1, `try_extract_filter_feed`); this covers only the
residual N-arm case.

The former Record-based fan-out (each arm published a `Record({result, to_d})`,
with no-feed arms getting an `empty_channel()` = `Lit::Unit`) has been
**retired**: that `Unit` placeholder didn't match the feeding arms' channel type
(an ill-typed fan-out, or — had the type slot been patched — a silent miscompile
leaking a placeholder into the consumer's stream every iteration). Rejecting is
strictly safer.

**Proper fix: extend the refinement fan-out of gap #1 to N arms.**  For each
feeding arm `i`, build a refined source with predicate
`¬g₀ ∧ ¬g₁ ∧ … ∧ ¬g_{i-1} ∧ gᵢ` (Case's "first matching guard wins") and
contribute `refined_source ≫ (λ p → feed_value)` to the cluster channel via
`++` — the same element-form predicate the two-arm case now builds, with no
empty-channel placeholder. Unreachable from CHL today: lowering rejects `elif`
inside generator-for-loop bodies, so a multi-arm feed `Case` never reaches this
pass. Tracked by
[`tests/compilation_pipeline.rs::multi_arm_case_with_some_feeding_branches_is_a_known_gap`].

### 3. `try_lift_defer` covers only a single nesting level

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
| Cluster walk                               | `desugar`                                             |
| Per-defer feed extraction                  | `extract_for_defer`                                   |
| Filter-feed (2-arm Case)                   | `try_extract_filter_feed` + `refine_source_domain`    |
| Defer-returning let lift                   | `try_lift_defer`                                      |
| Multi-arm Case feed (rejected, N-arm TODO) | `extract_for_defer` Case arm                          |
| Cluster topo-sort                          | `topo_sort_cluster`                                   |
| Channel binding emission                   | `channelize_cluster` + `rename_shadows_then_bind`     |
| Shadow detection                           | `compute_protected_set` + `collect_free_vars`         |
| Substitution                               | `desugar_substitute` (wraps `ccl::subst`)           |
| Final cleanup                              | `drop_expr_stmts`                                     |
| Invariant check                            | `assert_no_defer_residue`                             |
