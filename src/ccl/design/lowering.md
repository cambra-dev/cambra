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

In broad strokes, for each cluster of consecutive `let d_i = Defer in …` bindings the step walks the cluster body to extract every `Feed(d_i, V)` and the (at most one) `Define(d_i, V)`, combines the extracted values via `++` (`TypedExprNode::Copair` — the channels have distinct index sets), and emits the cluster as one **mutually-scoped `Feed`-kind `LetRec` group** — so cross-defer references (`x ≪= y; y ≪= …`) need no binding order, and a reference *cycle* among channels is rejected by the letrec guardedness rule (channels carry no guard). Recognition later flattens the acyclic group to dependency-ordered `let`s. Special handling exists for per-iteration feeds (Compose/Apply with iteration lambda), N-arm filter-feed Cases (`if`/`elif` fan-out to refined-source channels), and a handful of structural rewrites (defer-returning let lift, alias inlining for defer handles). Because `mut_elim` hoists every in-loop feed to a top-level `Feed(defer, view)` before this step runs, channelization is origin-agnostic — it never distinguishes an accumulator-loop feed from a feed-only-loop or scalar feed.

The design of record — where this step sits in mutability elimination — is **[mutability.md](mutability.md)**; the in-depth implementation notes (extraction paths, shadow-renaming, error modes, navigation map) live in the `ccl/channelize.rs` module rustdoc.

### Inference before channelization

The inference pass types `Defer`/`Feed`/`Define` directly — `Defer : Feed(ChanDom(d) ⇒ V)`, `Feed`/`Define : Unit` with their contributions constrained into the channel (see [Feed handles as an invariant `History` constructor](type-inference.md#feed-handles-as-an-invariant-history-constructor-typehistory--kind-feed-)). `channelize` then rewrites each resolved defer cluster into a `Feed`-kind `LetRec` group of assembled channels, erasing the transient `Feed` histories and substituting each rigid `ChanDom(d)` domain for the concrete channel domain. No special `DeferredCollectionDomain` type is needed — standard inference does the job, every channel node is typed by construction, and reads type concretely via their `ChanDom` domains (no `retype` pass, no bounded read-type fixup).

Mutation-loop inference (`emit_loop`) learns the loop body's full Record codomain from the body itself via a one-way subtyping constraint: `require_sub(body_codomain, product({step: σ}))` pins the `step` field while width-subtyping lets the body's Record literal supply whatever `to_<defer>` fields it carries. This is the general pattern for "a known core plus an open set of additional fields" — an open record demanded by `require_sub`, not a dedicated partial-record type.

## `if` and `match` in value position

A block statement in value position — `x = if c: … else: …`, `x = match v: …`,
and the one-line `match` ([chl-spec.md](../../../docs/chl-spec.md#the-one-line-form),
"The one-line form") — reaches lowering as `ChlExpr::Block` wrapping the
`Stmt::If` or `Stmt::Match` it parsed to. Every spelling routes through
`lower_final_stmt`, so a block right-hand side lowers to the `Case` its
tail-position and ternary counterparts already produce and adds no IR node.

## Variants and match

Surface variants ([chl-spec.md](../../../docs/chl-spec.md#315-variant-constructors) §3.15, [§4.10](../../../docs/chl-spec.md#410-match--tag-dispatch)) add **no IR node**. Both halves already existed for the conditionals stack: `match` is the surface for a concept the IR already had.

- `` `tag(e) `` lowers to `VariantCtor { tag, payload }`. The bare `` `tag `` lowers to the same node with a `Lit(Unit)` payload, so there is one constructor shape rather than a nullary/unary pair — and `` `tag() `` reaches lowering as that same payload-less shape, the empty product being unit.
- **A tag's bracket is the payload's bracket, elided**, so neither level needs a bracket rule of its own: the parser hands the term payload to the ordinary `( … )` product production and the type payload to the ordinary `{ … }` one. A constructor therefore reads like a call (`` `pair(1, True) `` carries the tuple), and the one form the type side has to resolve is a lone comma-free `{T}` — a standalone parse error, hence free to mean "these braces are the tag's, and `T` is the payload type". Doubling the braces is rejected there, which is what leaves one spelling per type; the term level makes no such claim, since `( e )` is also grouping.
- ``match s: case `tag(w): body …`` lowers to `Case { scrutinee: Some(s), branches }`, one `Branch` per arm carrying a `Pattern { tag, binding, empty_payload }`. Every arm's guard is the literal `true`, which makes tag dispatch and the guarded `if`/`elif` chain one first-match rule over one node. An arm that names no payload — `` case `tag(_): `` or `` case `tag: `` — still binds, to a minted `__match_payload_N` the body cannot spell, so downstream passes need no separate no-binder case.
- `empty_payload` separates the two spellings, which make different claims. `` case `tag(_): `` says the arm does not read its payload and says nothing about its type. `` case `tag: `` says the tag carries nothing: `` `some{Int} `` and `` `some `` are different types, so that arm does not match a tag carrying a payload. `emit_case` records the second as `payload <: Unit` on that arm alone, after the scrutinee constraint. The order matters because the payload has flowed in by then, and the per-arm placement is what lets the rejection name the arm rather than read as a whole-scrutinee mismatch.

`Option(T)` is a built-in *abbreviation* for the two-tag variant `` {`some{T} | `none} ``, handled in `lower_type_application` beside `List(T)`. It is the only place the compiler mentions either tag spelling; nothing at the term level knows the names `some` or `none`, so `` `some ``/`` `none `` are ordinary constructors and `Option` is not a special case but a peer of its neighbours. `Type::option_of` lists its tags in **name order**, matching the name-ordered form the solver materializes a coalesced variant in, so an annotation compares equal to an inferred type structurally.

### Unreachable arms are kept, and cost nothing

Variant width subtyping constrains the scrutinee to a **subtype** of the arms' tag set (`emit_case`'s `require_sub`), so a `match` written for the full `Option` over a scrutinee inference has pinned to one tag is well-typed with a dead arm. Surplus arms are the normal case, not a user error.

Nothing prunes them. `variant_project` names the tag it reads, and a tag the column does not carry yields an empty restriction that contributes nothing to the union — so a dead arm is simply inert. It still needs a payload type, and no value reaches the position to supply one, so coalesce pins it (`pin_unobservable_arm_payload`): to the concrete type an upper bound requires the payload to flow into, else to a base every requirement the arm's body states accepts, else to `Unit`. The pin records its choice in both directions, which is what makes the arm's slot and the merge over the arms agree; a bound above the position does not participate in that merge. See [type-inference.md](type-inference.md), "An unobservable arm payload is pinned to what its uses require".

Exhaustiveness is correspondingly **directional**, and `lambda_elim` asserts it that way: every tag the *scrutinee* can carry must be covered by some arm (otherwise the union re-totals to a domain with gaps), while arms beyond that are unconstrained. Two arms for one tag remains a violation — it would union two partitions onto the same domain positions.

Pruning them at coalesce instead looks harmless and is not: it narrows a `Case`'s arm set relative to the enclosing lambda's declared domain, which miscompiles `match` on a function parameter. Specialization narrows a *read* to its lower bound while the parameter keeps the arms' union, so pruning against the read leaves a body handling fewer tags than the domain it claims.

The fan-out a `match` inside a lambda produces is a **`DisjointJoin`**, not a `Copair`: its arms restrict the *same* fed domain and merge back onto it. See [ir.md](ir.md), "`Copair` and `DisjointJoin` — two collection-combining operations, not one".

### A scalar match is the C-form, gated by tag

`elim_lambda` compiles a scrutinee-`Case` *inside* a lambda to the union of tag-restricts `⧺ᵢ (𝑑 ▷ variant_project(cᵢ) ▷ (λ 𝑤ᵢ → 𝑒ᵢ))`. A `match` in value position with **no** enclosing lambda does not reuse that by applying it to the scrutinee; it takes the same C-form the scalar *guard*-`Case` takes, with the boolean gate replaced by the tag projection:

    guard:  ⧺ᵢ ( iterate ▷ restrict(π̂ᵢ)                  ≫ const(𝑒ᵢ) ) ▷ final_or_default(…, 𝑒ₙ)
    tag:    ⧺ᵢ ( iterate ▷ const(𝑠) ≫ variant_project(cᵢ) ≫ 𝑒ᵢ       ) ▷ final_or_default

Three things follow from lifting onto the synthetic one-shot driver rather than applying the arms to the scrutinee:

- **The scrutinee enters by `const`**, exactly as the guard form's arm *values* do. Planning prepends an `iterate` to the union — it is an iteration source — and that `iterate` takes **no input**. The eta-expansion `𝑠 ▷ (λ __scrut → match __scrut { … })` therefore cannot work: it makes the union's domain the scrutinee's, so the scrutinee has to be fed into an operator that accepts nothing. It works for a single-arm `match`, which emits no union and so gets no `iterate` at all; keeping surplus arms (above) is what exposes the problem.
- **No first-match predicate is synthesised.** Disjointness is structural: `variant_project(cᵢ)` is empty at any position not carrying `cᵢ`, so the arms partition the driver with no gate at all. The guard form needs `π̂ᵢ = 𝑔ᵢ ∧ ¬⋁ⱼ<ᵢ 𝑔ⱼ`; the tag form needs nothing.
- **The collapse needs no default.** The arms cover every tag the scrutinee can carry, so exactly one position survives and `final_or_default` is applied to the **bare stream** rather than a `(stream, default)` tuple. `ExtractFinal` carries an `Option` default for this and fails loudly on an empty source rather than inventing a value. The guard form's default is its trailing `true` arm's value; a tag partition has no such arm.

`VariantProject` takes its payload extent from the node's type rather than from the scrutinee's extent, because a width-subtype scrutinee may not carry the projected tag — there would be no arm to read the extent from, yet the empty result still needs describing.

The two scalar `Case` forms are therefore one shape — lift onto a one-shot driver, fan out over disjoint sub-domains, `⧺`, collapse — differing only in what disjoins the sub-domains. That is also the shape a *mixed* arm needs (`` case `tag(x) if p: ``): the composition `variant_project(cᵢ) ≫ restrict(π̂ᵢ)`, with the first-match complement taken only over prior arms **sharing that tag** rather than over all prior arms.

A **single-arm** `match` needs no union: its partition is trivially total, so there is no sibling to share a domain with and the arm compiles on its own (a `DisjointJoin` needs at least two operands to be worth building, and none is built).

### The default arm

`case _:` lowers to a `Branch` with `pattern: None` inside the scrutinee-`Case` — the shape `Branch` already had — and needs no runtime work: it fires when no tagged arm matched, which is the empty-stream case `final_or_default` handles, so it becomes that operator's default rather than an arm of the union. The tagged arms form the union as before; the collapse switches from the bare-stream form to the `(stream, default)` tuple form. No tag-complement predicate is synthesised.

What it does need is an **inference** change, and it is the dual of exhaustiveness. `emit_case` emits one constraint either way — `scrut <: Variant({tagᵢ: αᵢ})`, the scrutinee flowing into the arms' variant — because that is what carries each tag's payload *into* its arm's binder slot `αᵢ`. The scrutinee sits on the **left**, so the width rule recurses `scrut.tagᵢ <: αᵢ` per shared tag.

A default arm changes only whether that arm set is **closed**. Closed, a tag the arms do not name is the `ExtraTag` error — that *is* the exhaustiveness check. Open ([`Openness`](../ty.rs)), the missing-tag rejection is dropped while every shared tag still constrains its payload, which is exactly what the default arm needs.

Relating both sides to a fresh variable *above* them instead — `expected <: open`, `scrut <: open` — looks like it should work and does not. A common supertype constrains neither of its subtypes against the other: both `αᵢ` and the scrutinee's payload become *lower bounds* of `open.tagᵢ`, information flows up into `open`, and nothing flows back down into `αᵢ`. The binder then takes no bound from the scrutinee at all and is decided by whatever else touches it — in practice the arms' join, i.e. the *default arm's* type. That costs both directions at once: a legitimate `match` mistypes its binder, and an arm body misusing its payload is no longer rejected, because the body's own use pins the binder unopposed.

The reason no placement of plain variables works: on the **tag** axis the scrutinee must be the supertype (it may carry tags the arms do not handle), while on the **payload** axis its payload must sit *below* the binder (payloads are covariant). One closed subtyping judgment cannot point both ways, which is what the openness marker resolves.

The consequence for elimination is that `arms_variant` becomes a **join**: the projections consume the arms' demand *unioned with the scrutinee's own tags*, since with a default arm the arms' tag set is no longer above the scrutinee. Without a default arm the join adds nothing, so the no-default path is unchanged.

`case _:` is special-cased in the parser rather than falling through as a tag, because `_` lexes as an ordinary identifier and would otherwise parse as a tag literally *named* `_` — silently unmatchable. The default arm must be last and unique; both are rejected at lowering.

A `match` whose **only** arm is the default lowers to that arm's body, not to a `Case`. A tag-less branch is a *fallback*, and with no tagged arm to fall back from there is nothing to dispatch: the value is the body's, whatever the scrutinee is. Everything below is defined over a non-empty arm set — `arms_variant` is the arms' tag set, the fan-out partitions the driver by tag, `final_or_default` collapses that partition — so an empty one has no meaning to give rather than a degenerate one. The scrutinee is kept as an `ExprStmt` head, which is what still *types* it (a `match` over an unbound name is an error here as anywhere) without letting it decide anything; `channelize` drops the `ExprStmt` with the rest. Nothing is demanded of its type either — a default-only `match` names no tag, so its scrutinee need not be a sum at all.

## Refinement type annotations — `{T where p}` → `Type::Refinement`

A refinement annotation `{T where p}` ([chl-spec.md](../../../docs/chl-spec.md), "6.4 Refinement syntax") lowers, in `lower_type_expr` (`ccl/lower/stmts.rs`), to `Type::Refinement(lower(T), Refinement::born(lower(p)))`. The base `T` lowers recursively like any other annotation; the predicate `p` lowers through the ordinary `lower_expr` path, so it is a bare `Bool`-valued `TypedExpr` — the same shape a literal singleton (`{Int | __elem == 5}`) or a `groupby` refinement carries.

Inside the predicate, `_` denotes the value being refined, which is the reserved refinement binder `__elem` (`REFINEMENT_BINDER`, `Name::elem()`). Lowering resolves it with a save/restored `LoweringContext::in_refinement_predicate` flag set only while lowering the predicate: with the flag set, a bare `_` in *term* position lowers to `Var(__elem)` rather than a variable named `_`. This keeps "`_` is the value being refined" a local rule of the predicate — the flag is off everywhere else, and `_` in *type* position stays the inference hole (`Type::Hole`), so the two uses of `_` never collide. Because the flag is threaded on the context, `lower_type_expr` (and `mut_annotation_parts`, which lowers a `Mut(V)`'s inner value type) take `&mut LoweringContext`.

## Function type annotations — `T => U` → `Type::Fun`

A function-type annotation `T => U` ([chl-spec.md](../../../docs/chl-spec.md), "6. Types (informal sketch)") lowers, in `lower_type_expr` (`ccl/lower/stmts.rs`), to `Type::fun(lower(T), lower(U))`. That helper builds the non-dependent compute function `Type::Fun { name: None, fun_kind: FunKind::Compute, .. }`. The kind is `Compute` because a `def` and a lambda both infer a compute function, so an annotated binding `f: (Int => Int) = \x -> …` checks against the lambda it binds; a data collection carries `FunKind::Data` and is written with its own constructor (`List(T)`, `Map(K, V)`), never with `=>`. The surface has no binder for the function, so the lowered type is never a Pi type, and a refinement in the codomain cannot reference the domain by name.

`T` and `U` lower recursively like any other annotation, so a refinement nested in either rides through `Type::Fun` to the post-inference wall — `emit_annotation_predicates` (`ccl/infer/emit.rs`) recurses into a function type's domain and codomain to type those predicates. In value position `T => U` is rejected (`lower_expr_inner`, `ccl/lower/mod.rs`): it names a type, not a value.
