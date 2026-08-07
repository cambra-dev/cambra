# Optimization & compilation passes

The passes that turn a fully type-inferred CCL tree into tile-dataflow operators. In pipeline order they run **inline → lambda_elim → planning → simplify → operator_conversion**; this doc is organized by pass. Inlining and lambda elimination remove `Lambda` nodes and UDF indirection; planning recognizes iteration sites (hash joins, keyed aggregates) and marks them; `operator_conversion` does the final λ-free CCL → `TileOperator` translation. For the AST these passes operate on, see [ir.md](ir.md); for the CCC theory behind lambda elimination, see [`docs/operational-semantics/lowering.md`](/docs/operational-semantics/lowering.md).

---

## Inlining Pass (`ccl/inline.rs`)

`inline_non_iterable_lambdas` runs **after `infer`** and **before `lambda_elim`**. It performs two structural rewrites on `Let` bindings, in order:

1. **Alias inlining** — eliminate `let y = x` pure α-renamings.
2. **UDF inlining** — substitute call sites for functions over non-iterable domains.

### Motivation

**Scalar UDFs** (e.g. `Fun(Int, Int)`): operator conversion compiles `Let`-bound expressions independently with `input = None`. For a function whose domain is scalar, this causes the operator graph to insert an `IterateExtent` for the domain — which panics at runtime ("Attempted to iterate on infinite Extent") because base types have no finite enumerable extent.

**List-producing UDFs** (e.g. generator `def`s, `Fun(Fun(UIntRange, Int), Fun(UIntRange, Int))`): these lower to `λ user_arg → λ __iter_record → body`. If that nested-lambda shape reaches `lambda_elim` intact, the rule emits a `curry` combinator — and `operator_conversion.rs` doesn't implement `curry`, so compilation fails with `unsupported Builtin(curry)`.

Inlining at the CCL level threads the call-site argument as `input`, and beta-reducing the outer lambda strips the user-parameter layer, leaving a single `__iter_record`-wrapping lambda that matches the list-comprehension shape `lambda_elim` already handles.

### Alias inlining

When the right-hand side of a `Let` is a plain `Var(x)`, the binding is pure α-renaming. It is eliminated unconditionally by substituting `x` for the bound name throughout the body — *unless* `x` is rebound by an inner `let x = …` node inside that body, which would cause variable capture.

Performing this before `lambda_elim` prevents the let-in-lambda rule from hoisting such bindings into `const(x)` wrappers that would need to be recognised and stripped by downstream passes.

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
- `Fun(_, _)` as domain — there are infinitely many possible functions of any given function type, so it cannot be enumerated. This case covers list-producing UDFs whose domain is itself a list-shaped function type.

### Substitution and beta-reduction

At each call site, substitution is paired with beta-reduction of the outer user-parameter lambda. Apply chains terminating in `Var(name)` participate in beta-reduction; unrelated `Apply(arg, Lambda)` patterns elsewhere in the tree are left intact so list-comprehension bodies and scalar BinOp desugaring keep the structure `lambda_elim` + `simplify` expect.

Multi-arg call-site bodies contain `Apply(Tuple(…), Proj(Index(i)))` (from the uncurried `__arg_pair.i` references). Those literal-tuple projections are folded later by `simplify::try_literal_tuple_projection`; this pass leaves them in place.

After beta-reducing a UDF call, `inline_impl` is re-applied to the result so that any newly-created `Let` bindings (e.g. from a defer-returning argument) are also processed by the alias-inlining and lift steps.

### Limitations

- **Explicitly curried UDFs used unapplied** (e.g. `let f = λ x → λ y → body in g(f)`): `f` is inlined because its domain is non-iterable, but with no call site to beta-reduce against the outer lambda survives, lambda-elim emits `curry`, and compilation fails with "unsupported Builtin(curry)". Fully-applied curried calls (`f(1)(2)`) are fine — beta-reduction collapses both layers. Wiring `curry` in `operator_conversion.rs` is the follow-up that closes this gap entirely.
- **Collection UDFs** (domain `UIntRange` or `DataSource`): not inlined; they compile correctly via `Memo + FanOut` and benefit from sharing.
- **Body duplication**: a UDF called N times has its body duplicated N times in the operator graph. Acceptable for now; only collection-typed UDFs warrant caching.
- **Recursive UDFs**: unsupported (already noted in `operator_conversion.rs`).

---

## Lambda Elimination (`ccl/lambda_elim.rs`)

`lambda_elim::run` converts a fully type-inferred CCL expression containing `Lambda` nodes into a point-free expression of primitive combinators, following the Cartesian Closed Category (CCC) structure described in [`docs/operational-semantics/lowering.md`](/docs/operational-semantics/lowering.md).

### Output nodes introduced

| Source form | CCL AST after `lambda_elim` |
|---|---|
| `f ≫ g` | `BinOp { left: f, op: Compose, right: g }` |
| `.n` (projection) | `Proj(ProjKey::Index(n))` |
| `.field` | `Proj(ProjKey::Field("field"))` |
| `a + b` (and other non-compose BinOps) | `Apply { argument: Tuple([a, b]), function: Builtin(BinOp(op)) }` |
| `-x` (UnaryOp) | `Apply { argument: x, function: Builtin(Neg) }` |
| `not x` (UnaryOp) | `Apply { argument: x, function: Builtin(NotFn) }` |

Non-compose `BinOp` and `UnaryOp` nodes are desugared uniformly to function application form so that operator conversion can treat all operations as combinators. This applies at all levels: inside lambda bodies (via `elim_lambda`) and at the top level of a program (via `elim_lambdas`).

### Built-in combinators

The output references built-in primitives via the `Builtin` enum carried by `TypedExprNode::Builtin`. Each variant has a stable display name (matched by the symbolic printer):

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
| `Builtin::Restrict` | `restrict` | planning-introduced mid-chain filter; a codomain-parametric function transformer: `restrict(p) : (𝐷 ⇒ Bool) ⇒ (𝐷 ⇒ 𝑇) ⇒ ({𝑑: 𝐷 \| 𝑝(𝑑)} ⇒ 𝑇)`. It narrows the **domain** of an upstream `𝐷 ⇒ 𝑇` to the subset satisfying `𝑝`, preserving the value `𝑇` on the codomain (*not* the unsound `𝐷 ⇒ {𝑑: 𝐷 \| 𝑝(𝑑)}`). Because its domain is a function type it is **applied to** its upstream (`upstream ▷ (𝑝 ▷ restrict)`), never composed as a CCC morphism. (Where planning emits it, and how op-conversion compiles the application, is covered under Planning below.) Chain-head iteration is the separate `Iterate` variant. |
| `Builtin::Iterate` | `iterate` | planning-introduced chain-head iteration source: `iterate(p) : {𝑑: 𝐷 \| 𝑝(𝑑)} ⇒ {𝑑: 𝐷 \| 𝑝(𝑑)}` (or `𝐷 ⇒ 𝐷` when `p` is the trivially-true `true ▷ const`). `planning` emits one at the head of every iteration site (aggregate arguments, the stream side of `FinalOrDefault`, top-level function-valued results, sink-bound record fields, mutation-loop sources, …). Op-conversion's Iterate arm requires `input=None`; it compiles `Apply(p, Iterate)` to an `IterateExtent` tile (plus a `Restrict` filter when `p` is non-trivial). Mid-chain filtering is the separate `Restrict` variant. |
| `Builtin::Converse` | `converse` | grouping by key |
| `Builtin::PermuteDomain`, `Builtin::FlattenDomain` | `permute_domain`, `flatten_domain` | hash-join domain massaging |
| `Builtin::BinOp(op)` for any `op: BinOpKind` | `add`, `sub`, `eq`, `lt`, `and`, `or`, `concat`, … | every arithmetic / compare / boolean-logic / string-concat binary op (one variant, parameterised by the existing `BinOpKind` so the operator enum has a single source of truth) |
| `Builtin::{Neg,NotFn}` | `neg`, `not_fn` | unary operations |
| `Builtin::{Sum,Max}` | `sum`, `max` | aggregations (fold/reduce) |
| `Builtin::Copair` | `copair` | point-free function form of the N-ary copairing, emitted only by lambda elimination when an inside-a-lambda `TypedExprNode::Copair` needs to be lifted out: `Apply(Tuple([a, b]), Builtin(Copair))`. The value-form node (top-level `TypedExprNode::Copair`) is the canonical shape; both compile to a `UnionOperator` tile. Surface `a ++ b ++ c` lowers directly to a flat N-ary value-form node — see [ir.md](ir.md) and [type-inference.md](type-inference.md#union-flattening-construction-time) for the construction-time invariant. |

Downstream passes (`simplify`, `planning`, `operator_conversion`) match directly on the `Builtin` variant.

### `zip` encoding

`⟨f, g⟩` (pointwise function pairing) is encoded as:
```
Apply { argument: Tuple([f, g]), function: Builtin(Zip) }
```
There is no dedicated `Zip` AST node; it reuses the existing `Apply` + `Tuple` + `Builtin` nodes.

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

When the lambda-elimination rule 7 rewrites a `Let` inside a lambda body, the bound variable changes type from `T` to `ParamTy ⇒ T`. The rewritten `Let` node has `bound_ty: None` because the old annotation is stale and would be incorrect.

---

## Planning (`ccl/planning/`)

`planning::run` runs after `lambda_elim` and produces the CCL that operator conversion will see.  The pass does general iteration-site planning — hash-join planning is just one *specialised* strategy folded in at a site, not the whole job (hence `planning`, not `join_plan`).  It performs two CCL-to-CCL rewrites and a final cleanup:

1. **Keyed-aggregate rewrite** (`recognize_groupby_sites` / `convert_groupby_pointful`) — recognises the **pointful** dependent-refinement source `const(cast(c)) : (k) ⇒ ({i | i ▷ c ▷ key == k} ⇒ V)` that lambda elimination emits for `[sum(g) for g in groupby(xs, key_fn)]` and folds the partition dispatch through `converse`.
2. **Iteration-site materialization** (`insert_iterate_markers`) — a single walk that visits every position where op-conversion would compile with `input=None`.  At each site the pass picks the best implementation strategy:
   - **Hash join** (`try_hash_join_rewrite` → `convert_loop_join` → `plan_loop_join` → `join_plan_to_expr`) when the site's domain is a refined tuple whose predicate decomposes into equality join conditions.  The emitted chain is itself iteration-bearing at its leaves (each `JoinPlan::Loop` emits `Apply(true ▷ const, Iterate)`), so no further marker is added.
   - **Iterate-then-restricts chain** (`wrap_with_iterate`'s fallback) — build the iteration source by *applying* one `restrict(p)` per refinement layer (innermost first) to a chain-head `Apply(true ▷ const, Iterate)`, then compose the value-producing body onto it, when the hash-join recogniser doesn't match.  `restrict` is a function transformer `(𝐷 ⇒ 𝑇) ⇒ ({𝑑: 𝐷 \| 𝑝(𝑑)} ⇒ 𝑇)` — applied, not composed — so each layer narrows the domain while preserving the value `𝑇`, and the chain stays well-typed (its honest second-order type would make a morphism-`Compose` ill-typed; `typecheck` rejects that).

Hash-join planning is the *specialised* strategy at an iteration site; the uniform iterate-then-restricts chain is the default.

The full pipeline inside `run`:

```
recognize_groupby_sites(&mut expr);
let expr = simplify(expr);
insert_iterate_markers(&mut expr);
simplify(expr)
```

`simplify` brackets the marker pass on both sides — the same marker-aware pass, not two modes:

- The **pre-marker `simplify`** runs on an iterate-free AST, canonicalising the value-level combinators before marker insertion; with no markers present, every rule fires.  (The join/group-by recognizers match the *pointful* predicate carried in the type, which `simplify` does not touch — see the dependent-refinements section of [type-inference.md](type-inference.md#45-dependent-refinements-via-pi-types).)
- The **post-marker `simplify`** absorbs the `id` leaves and nested `Compose` boilerplate that `replace_tuple_project_with_id` produces while planning a hash join.  Its structural-discard rules (`try_const_reduce`, `try_product_beta_fst`/`_snd`, `try_literal_tuple_projection`, `try_ccc_universal`, `try_exponential_eta`, …) **self-guard on an iteration-freeness check**, so safety is a property of the *nodes*, not of pass timing.  The guard is computed bottom-up: `simplify_once` OR-s `is_iteration` over each node and its children, marking any sub-tree that contains an `iterate` source, and the discard rules refuse to fire on such a sub-tree — an `Apply(_, Iterate)` at a chain head *is* the iteration source for everything downstream, so dropping it would strand the chain.  Only `iterate` needs the guard: a `restrict` filter always sits on an iterate-bearing upstream, so it is never separable from its source and the same guard protects it transitively.  Fully iteration-free sub-trees are pure CCC morphisms and reduce soundly, so no separate iterate-safe mode is needed.

### Hash Joins

Loop join patterns — where a predicate filters a cartesian product of two or more collections — are converted to hash-join strategies via `try_hash_join_rewrite`, called from `wrap_with_iterate` at every iteration site whose domain has a `Type::Refinement`.

#### Recognised pattern

The recognizer matches the **pointful** predicate form ([type-inference.md §4.5](type-inference.md#45-dependent-refinements-via-pi-types)) — the lambda the refinement carries, not a compiled combinator chain. The predicate has the shape `λ rec → rec.0 ▷ l0 ▷ (λ v0 → … rec.k ▷ lk ▷ (λ vk → <bool>))`, where each `rec.i ▷ li` binds the element `vi` of arm `i` and the innermost boolean is a conjunction of:
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

A `JoinPlan` is either a `Loop` (a leaf that iterates a set of `arms` with an optional residual `predicate`) or a `Hash` join of a `probe` sub-plan against a `build` sub-plan on key expressions, with an optional residual `predicate`.

`probe_key_idx` / `build_key_idx` are indices *into the output type of that side's sub-plan*, not into the original tuple.  They are `None` when the respective side is a single-arm `Loop` (no projection needed).  When `Some(i)`, a `Proj(i)` step is inserted before the key expression.

The `predicate` fields correspond to extra predicates that aren't expressable as hash join conditions; planning emits these as a downstream `iterate(predicate)` step on the joined output (op-conversion compiles that to a `Restrict` filter tile).

Future work:
1. Support loop joins inside hash joins (today the Loop nodes are always single-arm)
2. Support hash joins inside loop joins.  This will require a new CartesianProduct operator, as currently the only thing that can do a cartesian product is iterating a type, and this needs to be downstream of nontrivial operators.
3. Bloom filters to optimize joins.  Instead of doing traditional join ordering, we'll do runtime bloom-filter passing as described in https://dl.acm.org/doi/pdf/10.1145/3725283

### Keyed Aggregates

Keyed aggregates are patterns like `sum(x) for x in groupby(xs, key_fn)` where:
- A collection is grouped by a key function
- An aggregation operation is applied to each group
- The pattern iterates first over the key, then over elements within that key's group

The pass identifies constructs where a `curry` operator is applied to a function whose **domain** carries a predicate refinement (`{(key, value) | …} ⇒ A` — the placement `lambda_elim` uses for the correlated partition predicate; see [type-inference.md §4.5](type-inference.md#45-dependent-refinements-via-pi-types)). The refinement expresses equality with a key: elements are partitioned when the key function applied to them equals a particular value. This pattern is rewritten to:

1. Swap the iteration order: instead of iterating both the collection and key together, iterate the collection and compute the key for each element
2. Use the `"converse"` combinator to group elements by their key values
3. Apply the aggregation operator to each group

This transformation reduces the domain iteration complexity and allows the runtime to optimize group-by-key operations using dedicated grouping operators instead of generic iteration.

### Iteration-Site Marking (`insert_iterate_markers`)

`insert_iterate_markers` is the final step of planning.  It walks the CCL and inserts an explicit `Apply(predicate, Builtin::Iterate)` term at every position where operator conversion would compile with `input=None` and the expression is function-typed.  Refinement layers beyond the innermost are reified as a chain of `Apply(predicate, Builtin::Restrict)` mid-chain filters.  After the pass, op-conversion is a context-free dispatch on AST shape: it never inspects refinement structure to decide whether to start an iteration, and every iteration source it ever emits comes from exactly one CCL primitive.

For the full description of the input-policy split that this pass mirrors, see the [Operator Conversion section in `interpreter/design-operators.md`](/src/interpreter/design-operators.md#operator-conversion-interpreteroperator_conversionrs).  The short version:

- **Input-internalising arms** in op-conversion (`Sum`, `Max`, `Converse`, `MapDomain`, `Uncurry`, `FlattenDomain`, `PermuteDomain`, `Copair` / `DisjointJoin`, `FinalOrDefault` stream side, `Loop` source, value-position `Record` fields, the catch-all `Apply`) compile their argument with `input=None`.  Each such argument is an iteration site and gets a chain-head `Apply(true ▷ const, Iterate)` as its source, with one `restrict(p)` *applied* per refinement layer.
- **Input-threading arms** (`Const`, `Zip`, `Map`, `Restrict` itself, and the `Var` / `Let` / `Compose` infrastructure) accept `input=Some(upstream)` and pass it through, so their children inherit the surrounding iteration and are not iteration sites.
- **The program root** and each function-typed field of a trailing sink-bound `Record` are iteration sites by *subscription*: the user-supplied consumer (or `SinkConsumer`) subscribes to the result, expecting an iterated stream.
- **Each function-typed bound expression in the top-level `Let` chain** is wrapped because op-conversion's `Let` arm compiles `bound_expr` *unconditionally* (`operator_conversion.rs`, `let bound_op = convert_impl(bound_expr, …)?`), whether or not `body` references the binding — a non-iteration-bearing function-typed bound expr would otherwise reach an `input=None` arm and error (e.g. the `List` arm's "list literal reached op-conversion without an input").  This is a mechanical requirement of eager compilation, not subscription.  One consequence: a dead iterable binding (`let x = [1, 2, 3] in 42`) is eagerly compiled and iterate-wrapped rather than eliminated — making iteration use-driven so the wrap becomes unnecessary is tracked by [#232](https://github.com/cambra-dev/Cambra/issues/232).

At each iteration site, `wrap_with_iterate` first tries the specialised hash-join rewrite (`try_hash_join_rewrite`); the iterate-then-restricts chain is the default when hash join doesn't match.  See [Hash Joins](#hash-joins) above for the recognised shapes and the join-plan tree.

When the hash-join rewrite doesn't fire, the chain that `wrap_with_iterate` emits is:
- A single chain-head `Apply(true ▷ const, Iterate)` over the unrefined base domain — op-conversion compiles this to a bare `IterateExtent` (no filter tile, since the predicate is trivially true).
- One `restrict(p)` *applied* per refinement layer, innermost-first.  Each `restrict` is a function transformer applied to the source it narrows — not a morphism composed with it — so `make_restrict` keeps the term well-typed (its honest second-order type makes a morphism-`Compose` ill-typed; `typecheck` rejects that).  Op-conversion compiles each applied `restrict` to a `Restrict` tile fed the previous step's tile as `input=Some(_)`.
- The value-producing body is then composed onto that source (`source ≫ body`) as a genuine CCC morphism.

For an unrefined site, the source is just the chain-head iterate.  For a refined site `{D | p}`, it's `iterate ▷ (p ▷ restrict)`.  For nested `{{D | p_inner} | p_outer}`, it's `iterate ▷ (p_inner ▷ restrict) ▷ (p_outer ▷ restrict)` — matching the goldens in `tests/compilation_pipeline/`.

`Apply(p, Iterate)` is rendered as `p ▷ iterate` in symbolic form, or as just `iterate` when `p` is the trivially-true predicate (a shortcut in `symbolic.rs` to keep program dumps readable; the underlying AST always carries the predicate).  `Apply(p, Restrict)` renders as `p ▷ restrict`.

#### Skip cases (`is_iteration_bearing`)

A chain head is left alone when wrapping it with iterate would either be redundant or break op-conversion:

- **Already iterate-led** — `Apply(_, Iterate)` at head.
- **Restrict-led** — `Apply(_, Apply(_, Restrict))` at head, i.e. the outer `restrict` filter of a refined site.  A `restrict` application always sits on an iteration source by construction (`make_restrict` only ever wraps an iteration-bearing upstream), so a refined site is iteration-bearing just as its unrefined `iterate`-led counterpart is.  Recognising it keeps the pass idempotent on refined sites — without it, a second marker walk would re-enter `wrap_with_iterate` on the still-refined domain and stack a second iteration source.
- **Provides its own iteration** — `Apply(_, MapDomain | Uncurry | Converse | Copair)` and the nested `PermuteDomain` / `FlattenDomain` applies.  These arms construct iteration internally from their argument, so prepending iterate would feed them an unwanted upstream stream.
- **Rejects `input=Some`** — value-position `Tuple` / `Record` literals (op-conversion's `Tuple` / `Record` arms assert `input.is_none()`) and the catch-all `Apply` with a non-builtin function (`Proj`, `Var`, curried `Apply`).
- **Function-typed `Var`** — the bound op was already iterate-wrapped at its let-bind site, so returning the `FanOut` branch directly is correct; an outer iterate would create a redundant `MapResult` lookup.

#### Special cases beyond the uniform "wrap argument" pattern

Three op-conversion arms have child-input policies that don't fit the single-argument shape:

- **`Apply(Tuple | Record, Zip)`** — Zip fans the upstream input out to each tuple/record element.  Those elements receive `Some(fan_out_branch)`, so they are not iteration sites.  The pass walks into the elements (to reach deeper iteration sites) without triggering the value-position `Record` / `Tuple` wrap.
- **`Apply(Tuple([stream, default]), FinalOrDefault)`** — the tuple's first element (`stream`) is iterated; the second (`default`) is a scalar fallback for empty iteration and needs no marker.
- **`Copair` / `DisjointJoin`** — for `Copair`, both the value-form node (`Copair(operands)`) and the function-form `Apply(Tuple(ops), Copair)` need each operand wrapped independently; op-conversion compiles each with `input=None`. `DisjointJoin` is the sibling operation (see [ir.md](ir.md), "`Copair` and `DisjointJoin` — two collection-combining operations, not one") and behaves the same way here: its operands are compiled with `input=None` when nothing is fed, so each is its own iteration site.

#### `Let` recursion

A top-level `Let { bound_expr, body }` is compiled by op-conversion's `Let` arm with `input=None`, which then fans `None` into both children.  The marker pass therefore recurses into both — wrapping function-typed bound expressions and walking the body — without prepending iterate to the `Let` itself (which would mis-thread input through to `bound_expr` and `body`).  The bound-expression wrap is unconditional because the `Let` arm compiles `bound_expr` eagerly regardless of whether `body` uses it (see the iteration-site list above); [#232](https://github.com/cambra-dev/Cambra/issues/232) tracks making iteration use-driven so an unused binding can be dropped instead of materialised.

#### Joins emit an `iterate` source with `restrict` filters applied

`JoinPlan::Loop` and `JoinPlan::Hash` emissions in `join_plan_to_expr` use `Builtin::Iterate` as the iteration source and `Builtin::Restrict` for the residual filters, the latter built with `make_restrict` (a `restrict` *applied* to its upstream):

- A leaf `JoinPlan::Loop` without a predicate emits `Apply(true ▷ const, Iterate)` over the arm's type.
- A `JoinPlan::Loop` with a predicate emits `make_restrict(predicate, base_iter)` = `Apply(base_iter, Apply(predicate, Restrict))`, i.e. `base_iter ▷ (predicate ▷ restrict)` — the iterate provides the source and the applied restrict filters it.
- A `JoinPlan::Hash` with a residual predicate emits `make_restrict(predicate, map_domain)` = `map_domain ▷ (predicate ▷ restrict)` — same shape, but the restrict filters the joined output.

This is *application*, not composition: the `restrict` transformer's domain is a function type, so it cannot sit as a morphism in a `Compose` chain (`typecheck` rejects that).  Op-conversion compiles the outer `Apply`'s argument (`base_iter` / `map_domain`) with `input=None` via the catch-all arm — the `MapDomain` / `IterateExtent` arm sees no upstream input as required — and the `Restrict` arm then consumes that tile as `input=Some(_)` and applies the filter.

---

## Compilation

There are two compilation passes that translate CCL into tile-dataflow operators.

`interpreter/operator_conversion.rs` converts the λ-free CCL produced by `lambda_elim` + `simplify` into `TileOperator`s.  This process is mostly a 1:1 correspondence, with each type of object lifted up to apply within a chain of composed terms.

| CCL form | Operator |
|---|---|
| `Compose([f, g, …])` | sequential pipeline: output of each feeds next |
| `zip(f, g)` | `FanIn` over a shared `FanOut`-wrapped domain (via the `fan_in` factory) |
| `zip({k: f, …})` | `fan_in_named` — record-of-morphisms fused via `FanIn::new_named` or `ScalarFanIn::new_named` |
| `id` | identity (pass-through) |
| `const(c)` | `MapResultToConst` |
| `map(g)` | pass-through: compiles `g` with the upstream threaded in as input (emits no operator of its own) |
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

End-to-end pipeline tests live in `tests/compilation_pipeline/`.

### `Let` nodes compile to a shared binding, not `Apply(Lambda)`

A `Let` node is compiled directly rather than desugared to `Apply(Lambda, value)`.

The desugaring identity `let x = e1 in e2 ≡ (λx. e2)(e1)` is operationally correct, but compiling through it would lose binding provenance in the graph and introduce unnecessary indirection through an intermediate application.

Instead, the bound expression is converted to an operator, wrapped in a `Memo` (so its value is computed at most once) inside a `FanOut` (so every use in the body shares that one computation), and bound in scope. Each `Var` reference in the body resolves to the shared `FanOut` handle, so a value bound once and used many times is computed once and fanned out to all its uses.

**Prerequisite**: `binding.ty` on the `Let` node's `TypedBinding` must be resolved to a concrete type before compilation — the type inference pass fills it from the inferred type of `bound_expr`.
