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

## Variants and match

Surface variants ([chl-spec.md](../../../docs/chl-spec.md#315-variant-constructors) §3.15, [§4.10](../../../docs/chl-spec.md#410-match--tag-dispatch)) add **no IR node**. Both halves already existed for the conditionals stack, which is the point: `match` is not a new concept, it is the surface for one.

- `.tag(e)` lowers to `VariantCtor { tag, payload }`. The nullary `.tag` lowers to the same node with a `Lit(Unit)` payload, so there is one constructor shape rather than a nullary/unary pair.
- `match s: case tag(w): body …` lowers to `Case { scrutinee: Some(s), branches }`, one `Branch` per arm carrying a `Pattern { tag, binding }`. Every arm's guard is the literal `true`, which is what makes tag dispatch and the guarded `if`/`elif` chain the *same* first-match rule over one node. A binder-less `case tag:` still binds — to a minted `__match_payload_N` the body cannot spell — so downstream passes need no separate no-binder case.

`Option(T)` is a built-in *abbreviation* for the two-tag variant `{some: T, none: Unit}`, handled in `lower_type_application` beside `List(T)`. It is the only place the compiler mentions either tag spelling; nothing at the term level knows the names `some` or `none`, so `.some`/`.none` are ordinary constructors and `Option` is not a special case but a peer of its neighbours. `Type::option_of` lists its tags in **name order**, matching the name-ordered form the solver materializes a coalesced variant in, so an annotation compares equal to an inferred type structurally.

### Unreachable arms are kept, and cost nothing

Variant width subtyping constrains the scrutinee to a **subtype** of the arms' tag set (`emit_case`'s `require_sub`), so a `match` written for the full `Option` over a scrutinee inference has pinned to one tag is well-typed with a dead arm. Surplus arms are the normal case, not a user error.

Nothing prunes them. `variant_project` names the tag it reads, and a tag the column does not carry yields an empty restriction that contributes nothing to the union — so a dead arm is simply inert. The one thing it needs is a payload *type*: its variable never received a bound, so `coalesce_node` defaults an otherwise-unresolved pattern payload to `Unit`, an unobservable payload carrying no information.

Exhaustiveness is correspondingly **directional**, and `lambda_elim` asserts it that way: every tag the *scrutinee* can carry must be covered by some arm (otherwise the union re-totals to a domain with gaps), while arms beyond that are unconstrained. Two arms for one tag remains a violation — it would union two partitions onto the same domain positions.

An earlier version of this pass pruned unreachable arms at coalesce. That narrowed a `Case`'s arm set relative to the enclosing lambda's declared domain, which is what made `match` on a function parameter miscompile: specialization narrows a *read* to its lower bound while the parameter keeps the arms' union, so pruning against the read left a body handling fewer tags than the domain it claimed.

The fan-out a `match` inside a lambda produces is a **`DisjointJoin`**, not a `Copair`: its arms restrict the *same* fed domain and merge back onto it. See [ir.md](ir.md), "`Copair` and `DisjointJoin` — two collection-combining operations, not one".

### A scalar match is the C-form, gated by tag

`elim_lambda` compiles a scrutinee-`Case` *inside* a lambda to the union of tag-restricts `⧺ᵢ (𝑑 ▷ variant_project(cᵢ) ▷ (λ 𝑤ᵢ → 𝑒ᵢ))`. A `match` in value position with **no** enclosing lambda does not reuse that by applying it to the scrutinee; it takes the same C-form the scalar *guard*-`Case` takes, with the boolean gate replaced by the tag projection:

    guard:  ⧺ᵢ ( iterate ▷ restrict(π̂ᵢ)                  ≫ const(𝑒ᵢ) ) ▷ final_or_default(…, 𝑒ₙ)
    tag:    ⧺ᵢ ( iterate ▷ const(𝑠) ≫ variant_project(cᵢ) ≫ 𝑒ᵢ       ) ▷ final_or_default

Three things follow from lifting onto the synthetic one-shot driver rather than applying the arms to the scrutinee:

- **The scrutinee enters by `const`**, exactly as the guard form's arm *values* do. Planning prepends an `iterate` to the union — it is an iteration source — and that `iterate` takes **no input**. This is why the obvious-looking eta-expansion `𝑠 ▷ (λ __scrut → match __scrut { … })` cannot work: it makes the union's domain the *scrutinee's*, so the scrutinee has to be fed into an operator that accepts nothing. That shape appeared to work only while unreachable arms were being pruned, because a single-arm fan-out emits no union and so gets no `iterate`.
- **No first-match predicate is synthesised.** Disjointness is structural: `variant_project(cᵢ)` is empty at any position not carrying `cᵢ`, so the arms partition the driver with no gate at all. The guard form needs `π̂ᵢ = 𝑔ᵢ ∧ ¬⋁ⱼ<ᵢ 𝑔ⱼ`; the tag form needs nothing.
- **The collapse needs no default.** The arms cover every tag the scrutinee can carry, so exactly one position survives and `final_or_default` is applied to the **bare stream** rather than a `(stream, default)` tuple. `ExtractLast` carries an `Option` default for this and fails loudly on an empty source rather than inventing a value. The guard form's default is its trailing `true` arm's value; a tag partition has no such arm.

`VariantProject` takes its payload extent from the *node's* type, not from the scrutinee's extent, precisely because a width-subtype scrutinee may not carry the projected tag — there would be no arm to read the extent from, yet the empty result still needs describing.

The two scalar `Case` forms are therefore one shape — lift onto a one-shot driver, fan out over disjoint sub-domains, `⧺`, collapse — differing only in what disjoins the sub-domains. That is also the shape a *mixed* arm needs (`case tag(x) if p:`): the composition `variant_project(cᵢ) ≫ restrict(π̂ᵢ)`, with the first-match complement taken only over prior arms **sharing that tag** rather than over all prior arms.

**Known gap.** A *single-arm* `match` does not compile: the driver is made an iteration source by unioning the arms, and `CollectionUnion` requires at least two operands, so a lone arm leaves its leading `const` with nothing to lift over. Either one arm wants a driver-free shape (its partition is trivially total, so there is no sibling to share a domain with) or the driver wants materializing without a union. `tests/compilation_pipeline/variants.rs` carries it as an ignored test.

### The default arm

`case _:` lowers to a `Branch` with `pattern: None` inside the scrutinee-`Case` — the shape `Branch` already had — and needs **no runtime work at all**: it fires exactly when no tagged arm matched, which is precisely the empty-stream case `final_or_default` handles, so it becomes that operator's *default* rather than an arm of the union. The tagged arms form the union as before; the collapse switches from the bare-stream form to the `(stream, default)` tuple form. No tag-complement predicate is synthesised.

What it does need is an **inference** change, and it is the dual of exhaustiveness. Without a default arm the arms must cover everything the scrutinee can carry, so `scrut <: Variant({tagᵢ: αᵢ})` — the scrutinee's tags are *at most* the arms'. With one, the scrutinee may carry tags no arm names, so that constraint would make the default arm unreachable by construction: every scrutinee it could fire on is rejected first. `emit_case` instead relates both to a fresh variable *above* the arms' variant — `expected <: open` and `scrut <: open` — which drops the subset requirement without needing a row variable.

The consequence for elimination is that `arms_variant` becomes a **join**: the projections consume the arms' demand *unioned with the scrutinee's own tags*, since with a default arm the arms' tag set is no longer above the scrutinee. Without a default arm the join adds nothing, so the no-default path is unchanged.

`case _:` is special-cased in the parser rather than falling through as a tag, because `_` lexes as an ordinary identifier and would otherwise parse as a tag literally *named* `_` — silently unmatchable. The default arm must be last and unique; both are rejected at lowering.
