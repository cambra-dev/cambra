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

A mutation-accumulation loop (`x := 0; for i in src: x += i; x`) lowers to the
**direct-mirror markers**, not a bespoke loop node: a `TypedExprNode::For` whose
body carries `TypedExprNode::MutWrite` mutable writes. `lower_middle_stmt` /
`lower_generator_or_mutation_loop` detect the loop-carried `:=` / `+=` writes
(`find_mutation_loop_vars`, which scans the body for every mutated outer-scope
name in first-mention order) and emit that `For`/`MutWrite` shape; mutability of
each write is checked post-inference, not at lowering, and a plain `=` to an
outer-scope name is a lowering error that points at `:=`.

The recurrence is **not** built at lowering. The unified `mut_elim` rewrites
every `For`+`MutWrite` loop into a guarded `LetRec` — the accumulators' history
over the loop's induction domain, guarded by `get_prev_seq`, with trailing reads
lowered to `final_or_default` — and `planning::plan_loops` lowers that onto the
domain-parameterized `Transact` carrier, which operator conversion compiles to a
position-driven `InductionStore` changelog. In-loop feeds (`<<`, and `yield` in a generator) are hoisted to
`Feed(defer, view)` and routed as ordinary channels by `channelize`, the
feed-routing step (channelize) of mutability elimination. A generator with loop-carried state
(`total := 0; for x in xs: total += x; yield total`) is the same shape — `yield e`
is a `<<` against a synthesized result defer.

The design of record for the recurrence construction and feed routing is
[The model: histories and causal recursion](mutability.md#the-model-histories-and-causal-recursion)
and [mut_elim: eliminating overwrite mutability](mutability.md#mut_elim-eliminating-overwrite-mutability); the
implementation lives in `src/ccl/mut_elim.rs` (the `For`/`MutWrite` → `LetRec`
→ `Transact` via loop planning) and `src/ccl/channelize.rs` (feed routing).

**Conditionals in loop bodies.** A mutation nested inside an `if` in a loop body
lowers via a `ChlStmt::If` arm in the direct-mirror loop-body lowering: each branch
body lowers through the same recursive statement-chain helper and is emitted as a
statement-position `Case` — a faithful mirror, no path computation at lowering
(mutability is a type-level fact lowering does not have). `find_mutation_loop_vars`
recurses into the branches so `for x in src: if p: total += x` classifies as a
mutation loop; the branch merge (the write leg and its carry) is compiled downstream
in `mut_elim` (`transform_chain`). A `for` or a `with begin():` nested inside an `if`
inside a loop body stays rejected.

**Let-bindings in generator bodies** (`y = f(x); yield y`) lower to nested `Let` nodes inside the Lambda body, evaluated once per iteration of the enclosing loop.

**Pre-loop lets** (assignments before the outer `for` in a function body) are handled by `lower_stmts` — they wrap the generator expression in `Let` nodes. The `for` lowering itself (`lower_generator_for`) only handles the loop and its body.

**Mutation rule**: an assignment inside a for-loop body is a let-binding (allowed) iff the target name is fresh in the current frame or was introduced by the same `for`-body (including the iter-variable). Assignments to names from enclosing frames, function arguments, or pre-loop lets are rejected as mutation. Function definitions inside for-loop bodies are treated identically to assignments.

Generator expressions `(expr for x in xs)` are lowered via `lower_list_comp` to the same `Compose+Lambda` encoding as generator functions.

---

## Deferred collection operators — `defer` / `<<` / `<<=`

`defer()`, `<<`, and `<<=` are CHL-level operators that let a block accumulate a result value progressively. They are reified as three CCL AST nodes (`Defer`, `Feed`, `Define`) during lowering, then **eliminated** — after type inference and mut_elim — by the feed-channelization step `channelize::run` ([The `channelize` step](#the-channelize-step-feed-channelization), below).

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

### The `channelize` step (feed channelization)

Feed channelization runs **after** `infer` and `mut_elim::run` (and after `inline`), but **before** `lambda_elim` and `planning::plan_loops` — loop planning consumes the point-free normal form post-elim, so both mutable-variable and channel letrec groups travel through channelization intact. It is the append-mutability half of the eliminator (mut_elim + channelize) and is **type-preserving by construction**: inference types the `Defer`/`Feed`/`Define` constructs directly (so type errors report against the user-shaped tree), and every channel node the step builds is stamped from its children's concrete types. The one residue construction cannot know up front — the channel *domains* — is named rigidly at inference (`Type::ChanDom`, minted per `let d = Defer`), so a defer read and every node that consumes it types concretely against the rigid name; closing the tree is then a pure whole-tree substitution (`ChanDom(d)` ↦ the assembled channel domain), *not* a re-typing pass. No pass *downstream* sees `Defer`/`Feed`/`Define`/`ExprStmt` — those can treat the variants as `unreachable!`. (See [type-inference.md](type-inference.md) for why inference runs before channelization.)

In broad strokes, for each cluster of consecutive `let d_i = Defer in …` bindings the step walks the cluster body to extract every `Feed(d_i, V)` and the (at most one) `Define(d_i, V)`, combines the extracted values via `++` (`TypedExprNode::CollectionUnion`), and emits the cluster as one **mutually-scoped `Feed`-kind `LetRec` group** — so cross-defer references (`x ≪= y; y ≪= …`) need no binding order, and a reference *cycle* among channels is rejected by the letrec guardedness rule (channels carry no guard). Recognition later flattens the acyclic group to dependency-ordered `let`s. Special handling exists for per-iteration feeds (Compose/Apply with iteration lambda), N-arm filter-feed Cases (`if`/`elif` fan-out to refined-source channels), and a handful of structural rewrites (defer-returning let lift, alias inlining for defer handles). Because `mut_elim` hoists every in-loop feed to a top-level `Feed(defer, view)` before this step runs, channelization is origin-agnostic — it never distinguishes an accumulator-loop feed from a feed-only-loop or scalar feed.

The design of record — where this step sits in mutability elimination and why `desugar_defers`/`retype` were retired — is **[mutability.md](mutability.md) §4**; the in-depth implementation notes (extraction paths, shadow-renaming, error modes, navigation map) live in the `ccl/channelize.rs` module rustdoc.

### Inference before desugaring

The inference pass types `Defer`/`Feed`/`Define` directly — `Defer : Feed(ChanDom(d) ⇒ V)`, `Feed`/`Define : Unit` with their contributions constrained into the channel (see [Feed handles as an invariant `History` constructor](type-inference.md#feed-handles-as-an-invariant-history-constructor-typehistory--kind-feed-)). `channelize` then rewrites each resolved defer cluster into a `Feed`-kind `LetRec` group of assembled channels, erasing the transient `Feed` histories and substituting each rigid `ChanDom(d)` domain for the concrete channel domain. No special `DeferredCollectionDomain` type is needed — standard inference does the job, every channel node is typed by construction, and reads type concretely via their `ChanDom` domains (no `retype` pass, no bounded read-type fixup).

Mutation-loop inference (`emit_loop`) learns the loop body's full Record codomain from the body itself via a one-way subtyping constraint: `require_sub(body_codomain, product({step: σ}))` pins the `step` field while width-subtyping lets the body's Record literal supply whatever `to_<defer>` fields it carries. This is the general pattern for "a known core plus an open set of additional fields" — an open record demanded by `require_sub`, not a dedicated partial-record type.
