# Lowering — CHL to CCL

How CHL source becomes CCL. Lowering (`ccl/lower/`) is structural — it does no type reasoning; it turns CHL AST into the `TypedExpr` node vocabulary of [ir.md](ir.md), stamping every node with `Type::Hole` for inference to fill. Immediately after, the uniquify pass (`ccl/uniquify.rs`) α-uniquifies binders (see [ir.md](ir.md#structured-names-and-α-uniquification-barendregt-convention)). This doc covers the non-obvious lowering *encodings*: how lambdas, function definitions, generators, mutation loops, and the deferred-collection operators become CCL shapes.

---

## CHL `lambda` expressions — single `Expr::Lambda` (tupled when multi-arg)

CHL `lambda` expressions lower to a single `Expr::Lambda`. A single-parameter `lambda x: body` becomes `λ x → body`. A multi-parameter `lambda x, y, ...: body` is **uncurried at lowering**: it becomes `λ __arg_tuple_N → body[x := __arg_tuple_N.0, y := __arg_tuple_N.1, ...]`, a single-parameter lambda whose parameter is a synthetic tuple and whose body has each named argument replaced in-place by a projection of that tuple. `param.ty` starts as `Type::Hole`; inference resolves it (including the tuple arity for the multi-arg case) from the body's projection constraints and the call-site argument type.

Each multi-arg lambda mints a fresh `N` from a counter on `LoweringContext`, so nested multi-arg lambdas (e.g. `lambda x, y: lambda a, b: x + a`) receive distinct tuple-parameter names. Without the unique suffix, an outer substitution that inserts `Var("__arg_tuple")` into an inner lambda's body would be captured by the inner binder; the fresh suffix plus the reserved `__arg_tuple_` prefix (user code cannot bind double-underscore names here) keeps the in-place substitution non-capture-avoiding yet correct.

Rationale for uncurrying: a curried `λ x → λ y → body` lowering would trigger `lambda_elim`'s nested-lambda rule and produce `curry(body)`, which operator conversion cannot compile. Uncurrying at lowering pairs with the tupled call lowering (see [ir.md](ir.md#application-shape)) so that syntactic multi-arg functions compile without any `curry` combinator appearing in the tree. Users who want genuine partial application still write `lambda x: lambda y: ...` or `curry(f)` explicitly — those produce curried types and are tracked as follow-up work.

In-place substitution (rather than wrapping the body in `let xi = __arg_tuple_N.i`) avoids introducing function-typed `Let` nodes that `lambda_elim`'s Let rule would lift to `ParamTy ⇒ T` and compile into zip-of-projections morphisms that current simplification cannot reduce back to a bare morphism.

Restrictions not yet supported (lowering raises `LoweringError::Unsupported`): `*args`, `**kwargs`, keyword-only arguments, and default values.

## Function definitions — `Let` + single `Expr::Lambda` (tupled when multi-arg)

CHL `def` statements are lowered to `Let` bindings whose value is a single `Expr::Lambda`, mirroring the `lambda`-expression shape above. `def f(x): body` becomes `let f = λ x → lower(body) in ...`; `def f(x, y, ...): body` uncurries to `let f = λ __arg_pair → lower(body)[x := __arg_pair.0, y := __arg_pair.1, ...] in ...`. The function name is bound via `Expr::let_bind`, and the body is lowered via `lower_stmts` (supporting assignments, nested function definitions, and a final expression).

Pairing the definition shape with `lower_call`'s tupled multi-arg shape keeps the common multi-arg `def` path free of the curried-lambda chain that `lambda_elim` would fold into an unsupported `curry(body)`.

## Generator functions — `Compose+Lambda` with `defer`/`feed` desugaring

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

### Mutation-accumulation loops

**Mutation accumulation loops** (`x = 0; for i in src: x += i; x`) are detected in `lower.rs` and lowered to a [`TypedExprNode::Loop`](ir.md#loop-for-mutation-accumulation-iteration) node rather than a `For` node.  `lower_middle_stmt` calls `find_mutation_loop_vars` (which scans the body for *every* outer-scope name that gets mutated, in first-mention order — handles `x = x + i; o << x` shapes and multi-accumulator bodies like `y = y + i; x = x * i`), then `lower_mutation_loop` builds:

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

`lower_mutation_loop_body` walks the for-body sequentially, building a flat let-chain of every assignment and snapshotting each `<<` feed value with the let-chain that preceded it.  Feeds anywhere in the body are supported — pre-mutation, between mutations, or post-mutation — and each captures exactly the SSA-style scope its Python source intended.  See "Record body shape" below for how feeds are surfaced.

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

**Generators with loop-carried state** (`running_totals`: `total = 0; for x in xs: total += x; yield total`; mutability design notes, §4b) reuse this same `Loop` lowering — `yield e` is just `<<` against a synthesised generator defer.  `lower_generator_or_mutation_loop` allocates `__result_N = Defer` outside the loop, passes its name into `lower_mutation_loop_body` as `yield_defer`, and each `yield e` is emitted as a raw `Feed(__result_N, …)` inline at the yield site with the same let-chain snapshotting as an explicit `<<`.  `desugar_defers` then absorbs every such feed into a `to_<defer>` field on the body Record.  The surrounding generator-function context already wraps the loop in `let __result_N = Defer in …` so the collected yields surface as the function's stream return value.  Both `lower_generator_for` (final-statement path) and `lower_middle_stmt` (middle-statement path) detect mutation independently of `yield` and dispatch through this same helper — they only differ in what continuation is passed in (`Var(__result_N)` for the final-statement case, the surrounding `body` for the middle case).

**Let-bindings in generator bodies** (`y = f(x); yield y`) lower to nested `Let` nodes inside the Lambda body, evaluated once per iteration of the enclosing loop.

**Pre-loop lets** (assignments before the outer `for` in a function body) are handled by `lower_stmts` — they wrap the generator expression in `Let` nodes. The `for` lowering itself (`lower_generator_for`) only handles the loop and its body.

**Mutation rule**: an assignment inside a for-loop body is a let-binding (allowed) iff the target name is fresh in the current frame or was introduced by the same `for`-body (including the iter-variable). Assignments to names from enclosing frames, function arguments, or pre-loop lets are rejected as mutation. Function definitions inside for-loop bodies are treated identically to assignments.

Generator expressions `(expr for x in xs)` are lowered via `lower_list_comp` to the same `Compose+Lambda` encoding as generator functions.

---

## Deferred collection operators — `defer` / `<<` / `<<=`

`defer()`, `<<`, and `<<=` are CHL-level operators that let a block accumulate a result value progressively. They are reified as three CCL AST nodes (`Defer`, `Feed`, `Define`) during lowering, then **eliminated** before type inference by `desugar_defers::run`.

> TODO: `x = defer()` should be replaced with `deferred x` once we implement a custom parser and aren't stuck with CHL parsing rules.

### CHL syntax

| CHL | Meaning |
|---|---|
| `x = defer()` | Declare `x` as a deferred accumulator |
| `x << value` | Feed `value` into `x` (used in expression position; any number of feeds) |
| `x <<= value` | Define `x` to be exactly `value` (used as a statement; exactly one define) |

A `defer` binding supports **either** feeds or exactly one define — mixing both is an error. Both the feed and define expressions evaluate to Unit.

### Lowering

`x = defer()` lowers to `let x = Defer in …`.

`requests, responses = http_serve(port, method, path)` lowers to:
```
let requests = Source("__http_requests_N") in
let responses = Defer in
<user body>
```

The `DataSink` for responses (`HttpServerSharedState`) is registered in `LoweringContext::sink_bindings` keyed by the `responses` binding name.  After the full pipeline runs, `compile_program` drains the registry via `ctx.lowering_ctx().take_sink_bindings()`, compiles each sink field's expression independently, and subscribes a `SinkConsumer` to it (the registration side is `register_sink_binding`).  The main program output is replaced by a Unit placeholder; sink programs do not produce a primary output value.

`x << expr` in expression or statement position lowers to `Feed { name: "x", value: expr }`, wrapped in an `ExprStmt` when it appears as a non-final statement. `x <<= expr` lowers to `Define { name: "x", value: expr }`, also wrapped in an `ExprStmt`. The `ExprStmt { expr, body }` node chains a side-effecting statement before the rest of the block:
```
let x = defer
in ExprStmt(Define(x, 1), x)    # x <<= 1; x
```

### The `desugar_defers` pass

The pass runs **after** `lower` and **before** `infer`.  Because it runs pre-inference, `Defer`/`Feed`/`Define`/`ExprStmt` nodes never reach any later pass — those passes can treat the variants as `unreachable!`.

In broad strokes, for each cluster of consecutive `let d_i = Defer in …` bindings the pass walks the cluster body to extract every `Feed(d_i, V)` and the (at most one) `Define(d_i, V)`, combines the extracted values via `++` (`TypedExprNode::CollectionUnion`), and emits the cluster's bindings at the body's terminal in topological order so cross-defer references (`x ≪= y; y ≪= …`) resolve without `letrec`.  Special handling exists for per-iteration feeds (Compose/Apply with iteration lambda), Loop bodies (per-iteration `to_<defer>` Record fields), filter-feed Cases, defer-mediating UDF calls (`y = f(arg)` where `f` introduces or manipulates a defer), and a handful of structural rewrites (defer-returning let lift, alias inlining for defer handles).

The full mechanism — the two-phase structure (chain rewriter + cluster walker), the smart-walker for defer-mediating UDF calls, the shadow-renaming step, error modes, known gaps, and a navigation map for the source — lives in **[desugar-defers.md](desugar-defers.md)**.

### Inference after desugaring

Because `desugar_defers` runs first, the inference pass never sees `Defer`/`Feed`/`Define` nodes.  Channel values appear as ordinary expressions (Apply/Compose/Loop), and the resolved defer is just a `Let` binding whose `bound_expr` is the assembled channel.  No special `DeferredCollectionDomain` type or per-feed unification step is needed — standard inference does the job.

Mutation-loop inference (`emit_loop`) learns the loop body's full Record codomain from the body itself via a one-way subtyping constraint: `require_sub(body_codomain, product({step: σ}))` pins the `step` field while width-subtyping lets the body's Record literal supply whatever `to_<defer>` fields it carries. This is the general pattern for "a known core plus an open set of additional fields" — an open record demanded by `require_sub`, not a dedicated partial-record type.
