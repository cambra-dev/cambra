# CCL Operator Specifications

Specifications for each CCL (Cambra Core Language) operator. For the underlying protocol and
progress algebra formalism, see [docs/operational-semantics/semantics.md](/docs/operational-semantics/semantics.md).

Each operator is **stateless** and corresponds to program syntax. Calling `subscribe()` on an
operator creates a runtime **producer/consumer** pair that manages actual execution state.

---

## Tilings and Tiles

Tilings and Tiles are the data model used by `TileOperator` and `TileProducer`. A `Tiling`
describes the *shape* of data a producer will emit — analogous to a type. A `Tile` is the
materialized data itself, shaped according to its `Tiling`.

### Extent

An `Extent` is the type-level view of a value: the set of all values a term can take on. Extents
are used in `Tiling` to describe domain and codomain shapes, and by producers to track which
values remain to be emitted or have already been released.

| Variant | Meaning |
|---------|---------|
| `Base(BaseType)` | A primitive type: `Int`, `UInt`, `String`, `Bool`, or `Unit`. |
| `Function { domain, codomain }` | A function type mapping one extent to another. |
| `Record(fields)` | A record type with named field extents. |
| `Union(variants)` | A union type: one of several possible extents. |
| `UIntRange(IntervalSet<usize>)` | A finite, mutable set of unsigned integer indices. Created from a CCL `UIntRange(n)` type as the full set `[0, n)`, and shrunk directly as individual elements or sub-intervals are released by `IterateExtentProducer`. Constructors: `Extent::uint_range(n)` for `[0, n)`, `Extent::uint_range_interval(start, end)` for arbitrary half-open ranges. |
| `DataSourceDomain(…)` | The domain of a streaming data source; polled externally for new elements. |
| `Restricted { base, restriction }` | A subset of `base` filtered by a `Restriction` handle; populated at runtime by `Filter` operators. |

At runtime, `Extent`s are responsible for tracking which elements are available and what has been released and forgotten.

### Tiling

Each `TileOperator` declares a `Tiling` that tells consumers what structure to expect:

| Variant | Meaning |
|---------|---------|
| `Scalar(Extent)` | A single value, possibly still unknown (represented as an empty `ColumnValue`). |
| `Record(fields)` | A named collection of sub-tilings, one per field. The tiles are records with fields that are the tiles of the sub-tilings |
| `SealedFunction { domain, codomain }` | A function mapping with structured codomain. Domain values accumulate incrementally; a `domain_predicate` on the tile signals when all have arrived. |
| `CurriedFunction { domain1, domain2, codomain }` | Logically, this tiling is equivalent to `SealedFunction(domain1, SealedFunction(domain2, codomain))`. It has a custom layout for efficiency, detailed in the `Tile` table below. |
| `Aggregation { accumulator }` | An ongoing aggregate with scalar accumulator type. |

`Tiling::extent()` converts a `Tiling` to the corresponding `Extent` (the type-level view).

`Tiling::empty_tile()` constructs the starting state for a tile — empty `ColumnValue`s and
`Predicate::False` domain predicates everywhere.

### Tile

A `Tile` holds the actual data. Its shape mirrors its `Tiling`:

| Variant | Contents |
|---------|----------|
| `Scalar(ColumnValue)` |  The two tiles in this tiling are `⊥` and the specific scalar of the tiling. `⊥` is represented as an empty `ColumnValue` and the scalar is represented as a `ColumnValue` of length 1 |
| `Record(fields)` | A Record of other `Tiles` |
| `SealedFunction { domain, codomain, domain_predicate }` | Each `Tile` is the set of known mappings of the function.  The `domain` is a `ColumnValue` of the domain elements, and the `codomain` is another `Tile`, which must be implicitly vectorized.  For example, a `Scalar` tiling is stored as a `ColumnValue` instead of a single element. |
| `CurriedFunction { domain1, offsets, domain2, codomain, domain_predicate }` | Each tile represents the known mappings of a curried function of type `domain1 → domain2 → codomain`. In the implementation, this is realized as sorted and aligned `ColumnValue`s of domain1 elements and offsets, where the offsets index into the codomain and domain2 `ColumnValue`. |
| `Aggregation { accumulator, terminal }` | Logically, this tiling knows the final number of inputs `N` that will be aggregated and the tiles are of form `(count, accumulator)`.  However, for making this feasible to compute, we instead store a terminal flag indicating `count == N`. |

`Tile::is_terminal()` returns true when a tile carries complete, final data. No larger tiles will ever be returned, although
equivalent tiles with some data released may.

`Tile`s also support `merge` to combine two tiles, `remove_guarded` to filter out data in a `Tile` matching a `TileGuard`, and `to_guard` to construct a `TileGuard` that corresponds to the data in a `Tile`

Tiles representing collections (`SealedFunction` and `CurriedFunction`) support logical deletes by storing a `BitSet` of deleted values.  These are set by filteriing operator like `Restrict` and compacted away by
stateful operators like `Memo` and aggregation.

### TileGuard

A `TileGuard` specifies a sub-tiling (a downward-closed, ⊕-closed subset of tiles) of interest. It drives
demand-directed computation and incremental release, mirroring the intent/yield guard system of
the previous version of the interpreter.

| Variant | Meaning |
|---------|---------|
| `Scalar(bool)` | `true` = interested, `false` = not interested. |
| `CurriedFunction(bool)` | All-or-nothing interest in the lookup table. |
| `Aggregation(bool)` | All-or-nothing interest in the aggregate result. |
| `Record(fields)` | Per-field `TileGuard`s, allowing fine-grained field demand. |
| `Function(FunctionGuard)` | Structured interest in a function tile (see below). |
| `Or(arms)` | Union of multiple guards; produced when two `Record` guards are unioned, because OR cannot be pushed through the AND semantics of a `Record` guard. Arms are always flat (no nested `Or`). |

`TileGuard::intersect()` computes the overlap between two guards (conjunction of interest
regions). `TileGuard::union()` computes the union; for `Record` guards this produces an `Or`
variant because the field-wise AND semantics prevent distributing OR through the conjunction.
`is_universal()` and `is_empty()` test the extremes.

TileGuards are also used to extract portions of a tile that a consumer is interested. This will be implemented
as a `split(guard: &TileGuard)` method on `Tile` in the future.

### FunctionGuard

Refines interest in a `SealedFunction` or `CurriedFunction` tiling:

| Variant | Meaning |
|---------|---------|
| `Domain(Predicate)` | Interested only in domain elements matching the predicate. |
| `Codomain(TileGuard)` | Interested only in codomain elements that are part of the subtiling specified by the guard. |

"Interested in everything" and "interested in nothing" are not separate variants — they are the trivial/degenerate guards, recognized via `is_universal()` / `is_empty()` (an empty guard is the annihilator under `intersect`).

### Predicate

A `Predicate` describes a subset of values within an extent. Used as a domain-completeness
signal in tiles and as a region specifier in guards.

| Variant | Meaning |
|---------|---------|
| `True` | All values. Universal predicate; identity under `intersect`. |
| `False` | No values. Empty predicate; annihilator under `intersect`. |
| `LessThanEq(Value)` | All values ≤ the given value (upper-bound streaming signal). |
| `Intervals(IntervalSet<Value>)` | Arbitrary union of intervals. |
| `Record(fields)` | Per-field predicates for record-typed extents. AND semantics: a value satisfies `Record(fields)` iff it satisfies every field predicate. |
| `Or(arms)` | Union of multiple predicates; produced when two `Record` predicates are unioned, because OR cannot be pushed through the AND-conjunction of a `Record`. Arms are always flat (no nested `Or`). |
| `Union(variants)` | Per-variant predicates for union-typed extents (`Extent::Union`). A value `Union { tag, inner }` satisfies `Union(variants)` iff `variants[tag].contains(inner)`. The length of `variants` must equal the number of union variants. Used as the domain predicate on tiles emitted by `UnionProducer`, and split by `UnionProducer::release_impl` to forward each per-variant predicate to the correct upstream input. |

`Predicate::intersect()` computes the conjunction of two predicates.
`Predicate::union()` computes the disjunction; for `Record` predicates this produces an `Or`
variant for the same reason as `TileGuard`.
`Predicate::as_bool()` short-circuits to `Some(true/false)` when the predicate is trivially
`True` or `False` (including uniform record predicates and `Or` predicates whose arms are all
`False`).
For `Union` predicates, `as_bool()` returns `Some(true)` when every variant predicate is `True`,
and `Some(false)` when every variant predicate is `False`; otherwise `None`. All set operations
(`intersect`, `minus`, `union`) are applied element-wise across the variant predicates.

### CCL types vs. tilings

CCL types and tilings describe a term at two different layers, and the relationship is one of the things that makes the tile pipeline tick.

The CCL type layer is **pointwise**: `mul : (Int, Int) → Int`, `zip(f, g) : A → (B, C)`. A type describes an element-wise function — "given one input of type A, produce one output of type B." It says nothing about how many `A`s will arrive, in what order, or whether the result will be materialised as a single value or streamed.

The tile layer chooses **how the runtime materialises that pointwise function**. The same pointwise morphism can be compiled to either:

- **A scalar-tiled operator** — evaluate the function on a single input value. One `A` in, one `B` out. Used when the morphism sits at a scalar call site (e.g. a literal tuple fed into a multi-arg UDF).
- **A function-tiled operator** (`SealedFunction` / `CurriedFunction`) — evaluate the function across a stream of inputs, essentially vectorising the pointwise definition. Used when the morphism sits downstream of an iteration or data source.

Both compiled forms satisfy the same CCL type; which one a specific call site gets is determined at op-conversion by the upstream `input`'s tiling, which flows in from whatever sits above the operator in the dataflow graph. This is what makes UDFs like `lambda x: x + 1` compile cleanly whether they're called once on a literal or mapped over a source — no duplication at the CCL level, the tile layer specialises automatically.

In practice this means tile operators need to be **tile-polymorphic in their inputs**: the same CCL-level combinator often needs two tile-level implementations, one per input tiling. The `MapResult` family handles this via `change_tiling_result`; fan-in is handled by [`fan_in`](./tile_operators/fan.rs), which dispatches to [`FanIn`] (function-tiled arms) or [`ScalarFanIn`] (scalar arms) based on what the compiled arms ended up with. New combinators should assume the same pattern: don't commit to one tiling when the upstream context picks it.

---

## The release contract

`release(𝑅)` says the data in 𝑅 is **never requested again, and never returned again** — the same promise from each end of the wire. It holds at every granularity: a consumed prefix, one arm of a union, a record field, or the whole tiling (the *universal* release, after which the only conforming tile is the empty one). This is what makes bounded execution possible — a producer may reclaim 𝑅, and every tile it emits afterwards lies outside its accumulated obsolete guard.

Every operator must obey it in both directions, because a violation yields **wrong results rather than an error**. A producer that returns released data hands its consumer values that consumer already took delivery of; a `Tile::Scalar`'s positions are implicit, so `merge` cannot tell "this position again" from "one more position" and appends, and one value silently becomes two, surfacing wherever it is later broadcast. An operator that fails to forward a release it could make strands upstream state instead — `FanOut` forwards the *intersection* of its branches' guards, so one branch that swallows a release blocks reclamation for all of them.

`TileProducer::get` checks the producer's half in debug builds: the returned tile must carry no live data inside the accumulated `obsolete_guard`. What an operator can forward depends on how it reads its input, so it is specified per operator below.

An operator must therefore **reject a guard it cannot honor rather than ignore it**. The guard accumulates in `obsolete_guard` whether or not `release_impl` acts on it, so dropping one silently leaves the operator free to re-emit that region — from its own state, or by re-reading an input it never passed the release to. Every `release_impl` is exhaustive; an operator with no sub-region to reclaim piecewise checks the guard with `TileGuard::expect_universal_or_empty`. Rejecting fires where the guard arrives, which does not depend on anything pulling afterwards — the `get` post-condition only fires if something does.

## Tile Operators

Each `TileOperator` is a static (compile-time) node in the dataflow graph. It knows its output
[`Tiling`] and can instantiate a live `TileProducer` via `subscribe`. Operators are constructed
during compilation; producers are created on demand at runtime.

| Operator | Input Tiling(s) | Output Tiling | Description |
|---|---|---|---|
| `Constant` | None | `Scalar` | Produces a fixed scalar `Value`. |
| `IterateExtent` | None | `SealedFunction(extent → Scalar(extent))` | Enumerates all values in an `Extent`, producing an identity-mapping sealed function (domain = codomain = extent) |
| `MapResultWithSource` | `SealedFunction(DataSourceDomain → Scalar(DataSourceDomain))` | `SealedFunction(DataSourceDomain → Scalar)` | Looks up each key of a data-source domain via `DataSourceDomainExtentImpl::get` to produce a sealed function from keys to their output values. |
| `FanIn` | `N` inputs of `SealedFunction(shared_extent → *)` tilings |  `SealedFunction(shared_domain → Record(_0, … _N))` | Merges N sealed-function operators that share a domain into one sealed function whose codomain is a Record Tiling of all their codomains. Prefer the free `fan_in` factory at op-conversion call sites: it dispatches to `FanIn` (function-tiled arms) or `ScalarFanIn` (scalar arms) based on the compiled arms' tilings, since the same CCL-level `zip` maps to either tile shape depending on upstream `input`. |
| `ScalarFanIn` | `N` inputs with `Scalar` tilings | `Record(_0, … _N)` | Packs N scalar inputs into a single `Record` tiling where each field is a `Scalar` tiling. The scalar counterpart of `FanIn`; reachable from op-conversion via the `fan_in` factory. Re-reads every operand on every pull, so the only release it can forward is the universal one. |
| `MapResult` | Function: any tiling of type `A → B`<br>Data: `SealedFunction(extent → Scalar(A))` | `SealedFunction(extent → Scalar(B))` | Applies a function element-wise over a sealed-function input, transforming each codomain value. The function input can have many different tilings; currently supports `Scalar(ComputableFunction)`, `Scalar(Function)`, `CurriedFunction`, and `SealedFunction` tilings. When the **data** input is itself a `CurriedFunction`, it maps the function over each codomain list, producing a `CurriedFunction` with the same domain and transformed values. A **`Scalar` data input against a `CurriedFunction` function** is the single-key lookup `groupby(c, k)(v)`: the same walk at one key, yielding that key's group as a `SealedFunction` — one currying level shallower, since the scalar consumes `domain1`. A key absent from a *settled* grouping is the empty group; absent from an unsettled one it is simply not answered yet, which the function's `domain_predicate` distinguishes. A `SealedFunction` function draws the same distinction: a row whose key it has not answered yet is withheld — dropped from the output, its domain position subtracted from the output's `domain_predicate` — and answered on a later pull. The **data** input tracks the consumer's release; the **function** operand is re-read whole on every pull, so it is released only on a universal release. |
| `MapResultToConst` | `SealedFunction(extent → *)` | `SealedFunction(extent → Scalar)` | Replaces every codomain value of a sealed-function input with the same constant (or zips it in, per its mode), preserving the domain. The constant must be present (terminal) before it can be broadcast — a still-absent constant (e.g. a scalar read from a sibling induction loop that has not yet converged) yields an empty, non-terminal output rather than fabricating a value for the unknown positions. |
| `ToScalar` | `SealedFunction(Unit → Scalar)` | `Scalar` | Unwraps a `SealedFunction` with `domain = Units(1)`, extracting and returning its single codomain element as a scalar tile. |
| `Converse` | `SealedFunction(domain → Scalar(codomain))` | `CurriedFunction(codomain → domain)` | Inverts a sealed-function operator: each codomain value maps to the list of domain values that produced it. |
| `Uncurry` | `CurriedFunction(A → B → C)` | `SealedFunction(Record(A, B) → Scalar(C))` | Flattens a curried function into a sealed function with a pair domain: transforms the nested lookup structure `A → B → C` into a flat pair-keyed structure `(A, B) → C`. |
| `MapDomain` | `SealedFunction(A → *)` | `SealedFunction(A → Scalar(A))` | Replaces the codomain of a sealed function with a copy of the domain values (identity codomain), producing an identity mapping from domain to itself. |
| `Filter` | Predicate: any tiling of type `A → bool` <br>Data: `SealedFunction(extent → Scalar(A))` | Same as input | Filters a sealed-function tile by a boolean predicate: keeps only domain elements where the predicate on the value evaluates to `true`. <br>TODO can probably remove this in favor of Restrict |
| `Restrict` | Predicate: any tiling of type `A → bool` <br>Data: `SealedFunction(A → *)` | Same as input | Filters a sealed-function tile by a boolean predicate: keeps only domain elements whose predicate evaluates to `true`. |
| `Aggregate` | `SealedFunction(* → Scalar)` | `Aggregation` | Reduces all codomain values of a `SealedFunction` input into a single running accumulator via an `AggregateKind` (e.g. Sum, Max). Currently, the aggregation is hardcoded in the graph, but we could add support for aggregate-kinds-as-data |
| `ExtractAggregate` | `Aggregation` | `Scalar` | Extracts the final value from an `Aggregation` tile. Constructed with an `only_terminal` flag: when `true` it emits only once the aggregation is marked terminal (the `only_terminal: false` path is currently `todo!()`). |
| `MapAggregate` | `CurriedFunction(domain → codomain)` | `SealedFunction(domain → Aggregation)` | Performs a per-key aggregation |
| `MapExtractAggregate` | `SealedFunction(extent → Aggregation)` | `SealedFunction(extent → Scalar)` | Extracts terminal per-key aggregation results from a `SealedFunction(D, Aggregation)`, producing `SealedFunction(D, Scalar)`. |
| `FanOut` | `*` | Same as input | Allows multiple operators to consume the output of the same operator. Each consumer subscribes via a `FanOut::branch()` handle; the fan-out forwards `get` requests and tracks the intersection of release guards across branches. Constructed via either `FanOut::new` (no cyclic-mode overhead — the common case) or `FanOut::new_cyclic` (for fan-outs whose branches feed back into their own input, e.g. a commit/induction store whose writer reads the store back before proposing, or a mutation-loop body whose other branch is wired to the cyclic prev-accumulator stream). Cyclic mode adds a per-pull tile-cache and a subscribe-in-progress flag so re-entrant subscribes / pulls skip redundant inner work and serve from the cached snapshot instead of re-entering the inner producer. |
| `Memo` | `*` | Same as input | Caches the output of an operator so it can be repeatedly read without recomputation. Releases each region as it takes delivery of it, so the input can clear its state; once the input is drained the cache is the sole source of the value. Only release builds then skip the upstream pull — a `Memo` sits above most scalar producers, so short-circuiting in debug would shield every one of them from the release-contract check. |
| `ExtractFinal` | two inputs: `source` (`SealedFunction(D → Scalar(T))`) and `default` (`Scalar(T')` for any `T'` that `T` includes) | `Scalar(T)` | Extracts the final codomain value of `source` once it signals terminal.  When `source` is terminal but emits zero values (e.g. a mutation loop whose body ran zero times because its iteration source was empty), emits the `default` scalar's value instead — keeping post-loop accumulators total.  Every emission is built at the **declared** extent `T`, not from the extracted value alone: a variant value carries only its own tag, so a column built from it would be width-narrower than `T` whenever the collapsed alternatives carry more tags between them — which is also why the `default` need only be *included in* `T` rather than equal to it (a conditional's trailing arm carries its tag and not its siblings').  Returns an empty scalar before `source` is terminal.  On the first terminal pull it releases both `source` and `default` universally — a final-consumer signal that propagates back through `FanOut`/`Memo`/mutation-loop bodies to the underlying data source. |
| `UnionOperator` | N inputs of `SealedFunction(dᵢ → Scalar(C))` tilings | `SealedFunction(Union(d₀,…,dₙ₋₁) → Scalar(C'))` | Merges N sealed-function operators into one by forming the discriminated union of their domains, over a codomain the **caller declares**. The domain keeps every arm apart — which arm a row came from is what `final_or_default` dispatches on. The codomain does the opposite: the arms are alternative values at one row, so it is their **join** — and that join already exists. A union node is typed `D ⤇ V` with `V` the arms' join as inference computed it, in the full type lattice; op-conversion reads `V` off the node and passes its extent in. Re-deriving it from the operand tilings meant a second join in `Extent`'s lattice, which has variant and range rules but **no record rule**, so two arms at different record widths came out as an anonymous positional sum where the type layer said `{a: Int}` — a shape no row holds and nothing downstream can project. Arms that *do* agree on a tiling keep it verbatim, since a `Tiling` carries a layout (struct-of-arrays for a record) that an `Extent` cannot express; that is the one thing still read off the operands. Release is per arm: an incoming `Predicate::Union` guard splits into per-variant predicates, so one arm can be released in full while its siblings still produce. |
| `VariantWrap` | Payload: `Scalar(Pₜ)` or `SealedFunction(D → Scalar(Pₜ))` | `Scalar(Union(P₀,…,Pₙ))` or `SealedFunction(D → Scalar(Union))` | **Sum introduction — dual of `VariantProject`.** Wraps the payload under tag `tag`, so that arm holds the payload and every other arm is empty. Arms are keyed by [`FieldKey`], not by position: a tag's *position* is not stable under width subtyping (``{`b} <: {`a | `b}`` renumbers `b`), and an arm set is part of a union column's layout, so a position-keyed arm would need a renumbering coercion at every subsumption. A bare `Scalar` payload (a scalar `VariantCtor`) yields `Scalar(Union)`; a payload *stream* (a `VariantCtor` inside a lambda, `Builtin::VariantWrap(tag)`) is wrapped element-wise **preserving the domain** `D`, so the constructor composes as the RHS of a `≫`. Because the domain is preserved, a domain release forwards to the payload verbatim. |
| `VariantProject` | Scrutinee: `Scalar(Union(P₀,…,Pₙ))` or `SealedFunction(D → Scalar(Union))` | `SealedFunction(UInt → Scalar(Pᵢ))` for a bare scrutinee (implicit `0..N` keys), or `SealedFunction(D → Scalar(Pᵢ))` for a stream scrutinee (the real `D` keys preserved) | **Sum elimination — the read-dual of `VariantWrap`.** Projects the arm named `tag` out of a tagged-union stream, *restricting to the sub-domain of rows carrying that tag* and yielding that arm's payload column, keyed by the original `UInt` position. A tag the scrutinee does not carry yields an **empty** projection rather than an error — that is what makes a width-subtype scrutinee, and so a `match` arm the scrutinee can never reach, inert instead of ill-formed. **Restrict and project are one op**: a [`UnionArm`] stores its rows alongside its payloads, so reading the arm *is* the tag restriction — there is no separate boolean `Restrict` step and no tag-discriminating `Predicate` (a domain-`Restrict` could not express it: the tag lives in the scrutinee's codomain, not its domain). Emitted by `lambda_elim` for a scrutinee-`Case`; consumed as a bare `Builtin::VariantProject(tag)` composed onto the fed scrutinee. |

**Pointwise `FunctionDef`s** (applied element-wise via `MapResult(input, Constant(FunctionDef))`, not standalone operators): `BinOp(op)` over a `{_0, _1}` record column, `UnaryOp(op)` over one column, and `RecordField(f)` projecting a field.

**Value-selecting `Case` in a writer decision body** (a conditional induction write `if 𝑝: acc += a else: acc += b`, or a `with begin():` per-key routing merge — a gate that varies with the element at a site with **no visible iteration source**). `lambda_elim` compiles it to the same **union of domain-restricts** as every other value-`Case`, over the *fed* element stream: `⧺ᵢ (filter_values(π̂ᵢ) ≫ eᵢ)`, first-match `π̂ᵢ`. `filter_values` (`Builtin::FilterValues` → the `Filter` tile operator, input stream + predicate) is a **value-preserving** filter — unlike `Restrict` (which returns the domain identity `{D|p}⇒{D|p}` for a source a map re-indexes), it keeps each surviving element's value `V`, so `eᵢ` maps the kept elements directly and a **partial op** (`//`) in `eᵢ` runs only where its guard holds — never eagerly at a rejected position (the retired `Select` computed both arms and faulted on the off-path one). The arms filter the *same* fed stream disjointly (first-match), so their union is a **flat merge** (`UnionOperator::new_flat`): it stays on one domain extent (not a tagged `Extent::Union`) and reassembles the full column sorted by domain key, co-iterating with the decision record's sibling `commit`/`writes` fields. The key is the arm's domain *value*, not a position: reassembly needs only a total order (to restore the fed order) and equality (to catch two arms claiming one key), and both hold for any single collection's keys, since its domain is one `Extent`. A `UInt` position is the common case; a fed stream whose own index set is a coproduct — a conditional-element comprehension, whose `Copair` domain is `Variant({Index(i): {D | π̂ᵢ}})` — carries `Union { tag, inner }` keys, which `Value`'s order compares lexicographically by tag then payload. Keys that are *not* mutually comparable mean the arms were fed different domains, which is a copairing rather than a disjoint join, and `flat_merge` says so. A sourceless value-`Case` (a top-level ternary) still takes the `UIntRange(1)`-driver C-form + `final_or_default` (a tagged union dispatch); the writer-body case differs only in filtering the fed stream rather than a synthetic driver.

**Scrutinee-`Case` over a variant** (`λ 𝑥 → match 𝑥 { 𝑐ᵢ(𝑤ᵢ) → 𝑒ᵢ }` — sum elimination, the read-dual of `VariantCtor`). `lambda_elim` compiles it to the same **union of restricts** as the value-`Case`, keyed on **tag** rather than a boolean first-match gate: `⧺ᵢ (𝑥 ≫ variant_project(𝑐ᵢ) ≫ (λ 𝑤ᵢ → 𝑒ᵢ))` — a `≫`-chain, because every element of it is a morphism out of the eliminated binder: the scrutinee is `𝑥 ⇒ scrut_ty`, `variant_project(𝑐ᵢ)` is `scrut_ty ⇒ Pᵢ`, and the eliminated arm body is `Pᵢ ⇒ V`. `variant_project(𝑐ᵢ)` (`Builtin::VariantProject(tag)` → the `VariantProject` tile op) fuses the tag-restrict and the payload projection into one step (an arm stores its own rows — see the operator table). The tags **partition** the scrutinee's domain, so the arms' sub-domains are disjoint and the union is a **flat merge** (`UnionOperator::new_flat`), re-totaling to the full domain — exhaustive by typing (inference's width-subtyping demands one arm per scrutinee tag), so no `final_or_default` scalar collapse is needed (this is the fan-out shape, not the C-form). A const arm (`abort → 0`, ignoring its payload) keeps its `variant_project` through simplification: `try_const_reduce` refuses to collapse past either element that *narrows the domain at runtime with no refinement left to re-materialise* (`simplify`'s `narrows_domain_irrecoverably` — `variant_project` and `filter_values`), since dropping one would apply the constant at every position and make the arms overlap. **Outer-binder arms.** When an arm body reads the *outer* binder as well as its payload (`𝑒ᵢ(𝑥, 𝑤ᵢ)` — e.g. a per-key view `λ __c → match __c.decision { commit(w) → (time: __c.time, write: w.i) }`, reading both the record's sibling field and the commit payload), the arm zips the whole element alongside the projected payload: `⧺ᵢ (⟨id, 𝑥.f ≫ variant_project(𝑐ᵢ)⟩ ▷ zip ≫ (λ (𝑥, 𝑤ᵢ) → 𝑒ᵢ))`. Both components of the pair are morphisms out of the *outer* binder, which is why `id` sits beside the projection chain rather than inside it — `𝑥.f ≫ ⟨id, variant_project(𝑐ᵢ)⟩` would pair the *scrutinee* with the payload, not the element the arm body reads its sibling fields off. For this, `VariantProject` keeps the scrutinee's **real domain keys** (a union *stream* `SealedFunction { D ⇒ Scalar(Union) }` carries them explicitly, unlike a bare `Scalar(Union)` whose implicit `0..N` positions become the keys), so the outer `id` arm and the tag-restricted payload co-iterate by key under the `zip`/`FanIn`, which inner-joins on shared keys — the outer arm need not be pre-restricted (the join drops the positions not carrying `𝑐ᵢ`). lambda_elim detects the outer-binder dependence structurally (the arm body has `𝑥` free beyond the payload binder) and merges the two into one pair binder (`𝑥 ↦ pair.0`, `𝑤ᵢ ↦ pair.1`); the payload-only path is unchanged. A scalar one-off `match` on a concrete value (rather than a per-element `λ x → match x`) would need the C-form scalar collapse; not built until a term needs it.

**`VariantCtor` inside a lambda body** (sum *introduction*, the dual of the scrutinee-`Case`). A `VariantCtor` in a lambda (``λ 𝑝 → `𝑐ᵢ(𝑒ᵢ(𝑝))``) must elaborate to a composable morphism `param_ty ⇒ Union` so it can be the RHS of a `≫` — e.g. a writer-decision arm ``filter_values(π̂ᵢ) ≫ 𝑒ᵢ ≫ variant_wrap(`commit)`` in the value-`Case` fan-out `⧺ᵢ (filter_values(π̂ᵢ) ≫ 𝑒ᵢ)`. `lambda_elim` compiles it to `𝑒ᵢ ≫ variant_wrap(𝑐ᵢ)` (`Builtin::VariantWrap(tag)` → the `VariantWrap` tile, fed the payload stream, wrapping it element-wise). The full arm set resolves from the node's `Type::Variant` codomain, mirroring `variant_project`. A `VariantCtor` whose payload is *constant* in the binder never reaches this arm — the `const` rule lifts the whole scalar variant with ``const(`𝑐ᵢ(…))``, which `MapResultToConst` broadcasts over the stream (`ColumnValue::repeat` handles a singleton `Union`). A genuinely scalar `VariantCtor` outside any lambda keeps its own node and its `expect_no_input` op-conversion arm (`Scalar(Union)`).

TODOs for implementing hash joins:

- Add support for MapResult to take a `CurriedFunction(A → UInt → B)` as the function argument, which will then convert `SealedFunction(C → A)` to `CurriedFunction(C → UInt → B)`

---

## The commit operator (`interpreter/commit_operator.rs`)

The transaction engine that backs a `Type::Txn` [`Transact`](../ccl/design/ir.md#transact--the-domain-parameterized-recurrence-carrier) store: concurrent writers propose transactions against a shared multi-key mutable variable, and the operator serializes them onto one monotonic `CommitTs` clock with optimistic-concurrency validation (allocate-on-commit + backward validation + serialize-and-retry). Op-conversion's `build_commit_store` assembles it. The design splits into a **pure engine** and its **tile adapters**:

- **`CommitEngine`** (tile-free, unit-tested) — the serialization logic. The store is `CommitTs ⇀ (Key ⇀ Value)`, held as per-tick write-set deltas with a per-key latest-write index. `attempt(proposal)` allocates the next tick and commits iff no read key was overwritten after the proposal's snapshot (else `Stale`, and the writer retries at the advanced watermark). `read_as_of(t, key)` folds the delta history.
- **`CommitOperator` / `CommitProducer`** — the store's tile adapter. It owns the engine, publishes its history as one [`Tile::Store`] output, drains each writer's new proposals in writer-index order (the serialization order, rotated per pull so no writer is starved), and acknowledges a commit by `release`ing that step back to its writer. Writer inputs are wired *after* construction, so the operator sits inside a cyclic `FanOut` and every writer reads the store back before proposing — the cyclic-`FanOut` feedback idiom, one writer per key.
- **`TransactDriver` / `TransactDriverProducer`** — one per `with begin():` site: it owns the transaction source, folds `(frontier, snapshot)` for the site's read keys out of the cyclic store, and **produces** the decision body's `(snap…, item)` input. A row is emitted once per `(item, frontier)`, so a retry at a moved frontier is a fresh position and a re-pull at an unchanged one emits nothing. It closes (terminal) once every transaction has been attempted and acked over a source that can deliver no more — the writer's completeness signal, since the writer owns no source of its own.
- **`TransactWriter` / `TransactWriterProducer`** — one *fused* writer per site (fused, not fanned: a stateful append-only proposal stream cannot be split across fanned branches without desyncing). Each pull it decides the driver's newest live position and appends a `{snap, reads, writes}` proposal when the body's decision is `` `commit ``, or advances locally when it is `` `abort ``. When the decision also reads an induction accumulator, that value arrives co-iterated in the writer *source* or broadcast as a constant — see [mutability.md](../ccl/design/mutability.md#reading-an-induction-accumulator-in-a-commit-decision), "Reading an induction accumulator in a commit decision".

  **The ack is a release intersection.** The driver sits behind a `FanOut` with two branches — the body and the writer — and advances its item cursor on what they *both* release. A body releases a row as soon as it has consumed it, which says nothing about commitment; the writer releases it when the attempt has finished, committed or denied without proposing. Only the intersection means "this item is done", which is why the writer holds a driver branch it barely reads: that branch is the ack channel.

  Both branches of that intersection are load-bearing, including the body's. A compiled body
  fans its input through a `Memo`, which releases each row as it *consumes* it — and it is
  that eager half which lets a superseded row be reclaimed before its item finishes. A body
  chain that released only when its own output was released would leave the intersection
  standing at the writer's ack, and the window below would grow one row per retry with the
  supersession release still in place. So this is an obligation on the body chain, alongside
  forwarding `domain_predicate`.

  **A release is not always an ack, though — supersession reclaims too.** The writer decides only the driver's *newest* live position, so every older one is abandoned and is released immediately rather than at the item's finish. That keeps a contended item's cost flat: the body re-renders the driver's whole live window each pull, so a window that grew one row per retry would make K retries cost K rows retained and K² body rows evaluated. The bound is `MAX_LIVE_ATTEMPTS`, asserted in the driver and measured at six contending writers — a window of 2 with the supersession release, 6 without it, over an item that lost five times. It also means the driver cannot read "a row was released" as "the item finished" — only the release of its **newest live row** is the ack, exactly as a release from the body alone is not one.
- **`StoreFinalRead` / `StoreFinalReadProducer`** — the **terminal read** of a commit key: `Scalar(V)`, the key's carried value at the position its own writers finish, or the store's tick-0 seed if no commit wrote it. It samples through the same `store_current` as `AsOf` and differs only in what fixes the position — a trigger's arrival there, the store's closure here — so it is neither a reduction nor a projection of the history, and needs no seed operand. Empty (and so non-terminal) until the store reports the key settled. A universal release retires it and releases the store branch; other readers hold their own guards through the fan, which the fan intersects, so the store still reclaims a version only once all of them have released it.
- **`StoreValueStream` / `StoreValueStreamProducer`** — projects one key's commit-value stream `CommitTs ⇀ V` out of the store changelog, carrying the value forward across ticks that wrote other keys (the step interpolation), so its own output is a `SealedFunction` with a decided value at every tick. It backs the in-block reply tap (`carry_forward: false` — one entry per committed transaction) and the read-your-writes mutable variable carry (`carry_forward: true`).
- **`AsOf` / `AsOfProducer`** — the **as-of (temporal) join**, the cross-endpoint read. Given a `trigger` stream (the positions to sample at, e.g. an HTTP request stream) and the store, it latches the store's current value for each trigger position the first time that position is observed — indexed by the *trigger*, not the commit clock. Reading several mutable variables latches them all from one store render, so a multi-variable read is one snapshot. The dual of the changelog store's own driver: the store latches a private accumulator per *source* step, `AsOf` latches the store per *trigger* step.

A single-writer induction store is the degenerate no-conflict case of this same contract, which is why one `Transact` carrier serves both engines.

### The store is a changelog, not a function

`CommitOperator`'s output is a [`Tile::Store`], not a `SealedFunction`: each tick carries only *that tick's* write-set delta, and a tick absent from the changelog is **decided-absent** — its value holds from the latest earlier change. Consumers must therefore **fold** the store (`store_current` / `store_value_at`), never index it. That is what makes a mutable variable readable while its store is still live: the current value is defined at the decided frontier, with no need for the history to end. Terminality is a flag separate from the frontier watermark, so a terminal store with trailing carries is not undercounted.

### The decision record

A writer body returns one **decision variant** per transaction, `` {`commit{𝑃} | `abort} `` (`ccl_utils::wrap_decision_variant`). `` `commit `` carries the payload record 𝑃 = `{writes, to_<defer>*}` — the positional tuple of proposed per-key new values, plus one field per reply tap — and `` `abort `` is the nullary whole-transaction deny: carry, no proposal. Making the grant/deny the *tag* rather than a `commit` field leaves "denied yet real writes" unrepresentable. `body_decision_at` decodes the tag by name, so the two ends agree without a canonical arm position. A tap fed under one arm of cross-key *routing* carries a companion `to_<defer>_k__fire : Bool` gate holding that tap's own control-flow path (see [mutability.md](../ccl/design/mutability.md#general-in-transaction-conditionals-and-conditional-writes), "General in-transaction conditionals (and conditional writes)"). The grant path omits a non-fired tap from the commit delta, so a routed reply fires only on its own route. A tap whose path *is* the commit — a single-guard or spine feed — carries no gate and fires with its transaction, keeping unconditional programs at their gate-free shape.

### Convergence: the writer re-arms, one step per pull

A writer processes **one source item per pull** and re-arms itself on the scheduler's deferred-wakeup queue whenever an item remains, returning non-terminal — the same one-step-per-pull idiom the induction and commit stores share. That single re-arm covers every continuation uniformly: a **commit** (the commit-ack `release` advances it, so the next pull takes the next item), a **deny** (it advances locally with no commit — invisible in the store frontier, which a frontier-growth signal alone would miss), and a **not-ready** decision (it does not advance, and reuses the pending body-input row). It is the *writer's* re-arm, not any reader's, that converges the store: the wakeup fans through the cyclic `FanOut` to re-pull the `AsOf` / `StoreValueStream` readers as commits land, so no reader drives a store to fixpoint. A writer **drained but live** does not re-arm, so an idle live server does not busy-poll — a future arrival wakes it through its source-forwarding consumer.

### Every fed-out mutable variable read is an as-of sample

A mutable variable read **fed out** of its `with begin():` block compiles to `AsOf` (born in `transact_phase::rewrite_as_of_reads`, from the `as_of_read` term the read is minted as) — a sample at an **arbitrary** position in the commit order — whatever the reading trigger's domain: a live `DataSource` request stream, a finite loop, or a standalone read's synthesized singleton. A bare read *outside* a block never reaches here: lowering rejects it (`lower_expr`'s read gate). There is no static finiteness classification anywhere on this path; the read folds to `AsOf` purely because its history domain is `Type::Txn`. Every trigger position latches at its own arrival, uniformly — a finite trigger has no special timing, so a read of a store still committing reports whatever it has committed, commonly the seed. `AsOf` stays non-terminal until the store is terminal *and* every live trigger position is latched, so it cannot report "done" while a store no other consumer drives is still committing.

The **terminal** read is a different term, not a different classification of this one: `await_final(x)` (see `src/ccl/design/mutability.md`, "`await_final`") is a `StoreFinalRead`, the same sample of the same key through the same `store_current` — what differs is what fixes the position, a trigger's arrival here and the store's closure there. The two are distinct terms all the way down from the surface — `as_of_read` and `final_read` — so which read a program gets never depends on the shape of the tree around it.

### Bounding a long-lived store

Three release paths keep a store that never ends from growing without bound. The writer's proposal stream is an **offset window**: committed prefixes are compacted away, and superseded proposals are dropped. The engine's `gc_released_prefix` reclaims released committed versions below the frontier while keeping each key's latest write — this is the load-bearing GC, because the per-consumer `FanOut` view folds the changelog whole, which makes `Tile::Store`'s `remove_guarded` a no-op (a released tick is not a deletable position). And `AsOf` releases the store fan *below* its latest decided tick — a future trigger only ever needs the latest-as-of-its-time — which is what lets `CommitProducer` reclaim a live store's superseded history.

---

## Operator Conversion (`interpreter/operator_conversion.rs`)

Op-conversion is the final stage of the front-end: it takes a fully simplified,
join-planned, iterate-marked CCL AST and emits a static `TileOperator` graph.  Each
AST node maps to one or more tile operators; the resulting graph is then driven by
the consumer attached at `compile_program`.

The pass is structured as a single recursive walk (`convert_impl`) that threads two
things through the recursion: a **scope** of let-bindings (each carrying a
[`FanOut`] handle plus a [`BindingKind`] tag), and an **input** — the upstream
[`TileOperator`] whose output the current sub-expression should consume.  Every
arm decides how to pass `input` (or `None`) down to its children, and that
dispatch is the heart of the pass.

### Input-policy dispatch

Op-conversion's arms split into two groups by how they handle their parent's
`input`:

- **Input-threading arms** accept `input=Some(upstream)` and either pass it
  unchanged into their argument (`Map`, `Restrict`) or fan it out to multiple
  children via [`FanOut`] (`Zip`, `Let`).  Their argument is *not* an iteration
  site; it inherits the surrounding iteration.

- **Input-internalising arms** assert `input.is_none()` and compile their
  argument with `input=None`.  The argument is an iteration source compiled in
  isolation, with its own iteration extent at the bottom of its chain.  Examples:
  `Iterate` (the canonical chain-head extent producer), `MapDomain`, `Uncurry`,
  `FlattenDomain`, `PermuteDomain`, `Copair` / `DisjointJoin`, `Sum` / `Max`,
  `FinalOrDefault`, and the catch-all `Apply` arm (where the function position
  is a `Proj` / `Var` / curried `Apply`).

`Converse` straddles the split: it accepts either `input=None` (produce an
iteration source itself by compiling its argument with `input=None`) or
`input=Some` (wrap the standalone converse in a `MapResult` over the upstream).

This dispatch is mirrored exactly by the iteration-marking pass in
[`crate::ccl::planning::insert_iterate_markers`] — its
`is_internalising_builtin_function` and `is_iteration_bearing` helpers both
consult [`Builtin::iterates_arg`], the single per-builtin policy method that
enumerates the input-internalising group.  The pass walks the AST inserting
`Apply(true ▷ const, Iterate)` as the source at every iteration site and
*applying* zero or more `restrict(p)` filter steps to it (one per refinement
layer) — `iterate ▷ (p ▷ restrict) ▷ …`, application rather than composition.
Op-conversion never has to invent an iteration source on its own.

### Iteration sources

After planning, the only ways op-conversion learns about an iteration are via
`Apply(_, Iterate)` (chain head) and `Apply(_, Restrict)` (mid-chain filter):

- **`Apply(predicate, Iterate)`** — requires `input=None`; the chain-head
  iteration source.  Construct `IterateExtent::new(extent_of(predicate.domain))`;
  when `predicate` is the trivially-true `Apply(Lit::Bool(true), Const)`
  (recognised via `is_trivially_true_predicate`), return that iteration source
  directly.  Otherwise compile `predicate` with the iteration as its input and
  wrap in `Restrict`, yielding an identity over the filtered domain.

- **`Apply(predicate, Restrict)`** — requires `input=Some(upstream)`; mid-chain
  filter.  Compile `predicate` with `upstream` as its input and wrap in a
  `Restrict` tile.  Planning emits this for every downstream filter step — the
  outer layers of a nested-refinement iteration site, and the residual
  predicates of `JoinPlan::Loop` and `JoinPlan::Hash`.

The invariant is: **every other op-conversion arm rejects `input=None` for
function-typed expressions** (the arms that compile arguments with `input=None`
do so only after planning has placed an `Iterate` at the chain head).  Any
non-`Iterate` arm reaching op-conversion with `input=None` fails an assertion —
a planner bug, not a user error.  Similarly, `Restrict` reaching op-conversion
with `input=None` is a planner bug.

**Constant-in-element predicates.** The scalar value-`Case` C-form
(`(unit | π̂ ≫ const 𝑒) ⧺ …`) and the data-collection gate fan-out
(`zs = xs if c else ys`) restrict a domain by a predicate that is *constant in
the element* — the gate is the arm's first-match path condition, not a function
of the position.  These compile through the ordinary `Restrict` path with no new
operator: a `const(c)` gate with a non-literal `c` is *not* matched by
`is_trivially_true_predicate` (which recognises only a literal `true`), so it
yields a real `Restrict` that gates the whole extent — empty when the gate is
false, identity when true — over both `Units(1)` one-shot drivers and full
extents.

### Let-bindings and `BindingKind`

`Let { binding, bound_expr, body }` fans the parent's input out to both children
(or passes `None` to both if there is no upstream input), then compiles
`bound_expr` and `body` independently against their respective fan-out branches.
The bound operator is wrapped in `Memo::new(...)` and pushed into the scope
under `binding.name` along with a [`BindingKind`]:

- **`BindingKind::Aligned`** — the bound expression was compiled with
  `Some(input)`, so its tile-domain matches the surrounding iteration.  At a
  `Var` reference inside that iteration, op-conversion returns the `FanOut`
  branch directly: the value already varies in lockstep.

- **`BindingKind::Free`** — the bound expression was compiled with `None`, so it
  is a stand-alone function value.  A reference under an iteration wraps it in
  `MapResult(input, bound_op)` to look up the function per iteration position.

This bit determines whether a `Var` use is a passthrough or a per-position
lookup.  It is recorded once at the let-bind site rather than re-derived at each
use, because the tile-level information needed to disambiguate is already gone
by Var-lookup time.

(There is a known limitation with multi-depth iterations — see the
TODO(nested-mutation) comment on `BindingKind` for the planned generalisation.)

### Fan-out and sharing

Three arms share an input across multiple downstream consumers:

- **`Apply(_, Zip)` with `Tuple` / `Record` arguments** fans the input out to
  each tuple / record element; the elements get `Some(fan_out_branch)` and
  combine via [`fan_in`] (function-tiled arms) or [`ScalarFanIn`] (scalar arms).
  The 2-arm Zip-with-const fast path skips the fan-out and emits a single
  `MapResultToConst` instead. A **store-read arm** (`__reg.k`) is a *leaf*
  source over its own domain, so it is converted with **no** input (rather than
  the fanned branch, which it would reject); `fan_in` co-aligns it with the
  input-driven arms by domain position. This is the cross-domain co-iteration a
  commit writer's source uses — `zip((reqs, __cnt.acc))` pairs the request stream
  with a request-indexed induction accumulator read so a commit decision can read
  the accumulator at its request position (`with begin(): balance += cnt`).

- **`Let { bound_expr, body }`** fans the parent input into both the bound
  expression and the body (described above).

- **Induction writer bodies** (the realization of a recognized `Transact` over a
  concrete iteration extent) fan-out the cyclic prev-accumulator stream and the
  body output (via `FanOut::new_cyclic`); see *Induction stores as a changelog*
  (`InductionStore` / `StoreDenseRead`) below for the full structure.

### Aggregates, sinks, and the program root

The pipeline always bottoms out at one of three consumer shapes:

1. A scalar produced by `Apply(<chain>, Sum)` / `Max` (compiles to
   `Aggregate` + `ExtractAggregate`) or `Apply(Tuple([stream, default]), FinalOrDefault)`
   (compiles to `ExtractFinal`).
2. A function-typed program result — `convert_to_operators` is the entry
   point, the resulting tile is subscribed by the user-supplied `main_consumer`
   at `compile_program`.
3. A trailing `Record` of sink-bound names — `convert_record_fields_to_operators`
   compiles one operator per field, sharing the scope (and therefore the
   `FanOut` / `Memo` of let-bound upstream) across every field.  Each field
   is subscribed by its corresponding `SinkConsumer`.

In all three cases planning has ensured every iteration site has an explicit
`iterate(p)` marker, so op-conversion is a context-free walk: each arm decides
what to emit based only on its own AST shape and the input flowing in.

---

## Induction stores as a changelog: `InductionStore` and `StoreDenseRead`

An induction store (a `mut`-loop accumulator, possibly with a conditional write and/or a
reply feed) is the **degenerate no-conflict dual of the commit store**, and shares its
machinery: it is a [`Tile::Store`] changelog driven by iteration *position* instead of by
concurrent proposals. Op-conversion (`build_induction_store_single`) routes **every**
induction store here — plain, conditional, or feed-carrying, over a finite (list) *or* an
async (`DataSource`) extent. An induction store is always **single-writer**: recognition
folds a conditional write to one carry-complete writer (`writes = Case[ĝ → w; true →
snapshot]`), so there is no multi-writer group and one realization serves every induction
store.

**Compound (tuple/record) accumulators.** A mutable variable holds one `Value`, so a tuple/record
accumulator is stored *boxed* — a `Scalar(Record)` codomain (one column of record values) —
while a tuple/record *literal* compiles to a struct-of-arrays `Record` tiling (a column per
field). The two representations meet at the mutable variable boundaries and are reconciled there with
the existing `scalar_tile_to_column_value` (box: `Tile::Record` → `ColumnValue::Records`) and
its inverse `column_value_to_tile` (unbox to a declared tiling shape): the `InductionStore`
init seed (`read_initial_scalar`), the conditional-write decision merge (`flat_merge`), and
the scalar-final read (`ExtractFinal`, which matches on *extent* not tiling shape). So a
compound accumulator folds, reads-its-own-writes, carries, and conditionally writes like a
scalar one. The **commit store** shares this: a `Mut[(int, int), Txn]` / `Mut[{x: int}, Txn]`
transactional mutable variable threads through the same `read_initial_scalar` seed and value-Case
decision merge, so unconditional, conditional (deny), `if`/`else`, record, and mixed
scalar+compound multi-key stores all commit correctly. (Enabling the transactional form needed
only the tuple/record *type annotation* syntax in `lower_type_annotation` — the store
machinery was already compound-ready.)

**Nothing in the substrate distinguishes a finite source from a streaming one.** The tiling
protocol treats a finite source as a stream that happens to terminate — comprehensions,
joins, aggregates and the changelog induction store all run over a literal list *and* a
`DataSource` through one graph (monotonic tile growth + pull-until-the-frontier-stalls). The
one thing the distinction would still buy is a memory bound on a never-terminating loop; see
[*Remaining: the never-terminating bound*](#remaining-the-never-terminating-bound).

**`InductionDriver` / `InductionStore` — the position-driven recurrence.** The two halves
of one loop, wired as a cycle: store → body → driver → `FanOut::new_cyclic(store)`.

The **store** owns a `CommitEngine` seeded at tick 0 with the accumulators' inits (so the
changelog is self-describing — a read below the first *iteration* change folds to the seed).
It consumes the body's `` {`commit{writes} | `abort} `` decisions (`body_decision_at` decodes
the union tag) contiguously from its decided watermark (which counts the positions already
stepped — the store keeps no separate cursor for them) and `step`s the engine: a `` `commit `` position
appends a change (tick `pos + 1`), an `` `abort `` (a failed guard) is a **carry** (no change;
the value inherits). It closes its frontier when the decision stream goes terminal.

That last clause is an **obligation on the body chain**, and worth stating because it is
easy to violate without noticing. The driver owns the source and closes its body-input tile,
so the store learns the loop is over only if every operator between the two forwards
`domain_predicate`. An operator that
renders a decision column but hardcodes a non-terminal predicate leaves the loop running
forever with the right values in it — a hang, not a wrong answer. The store asserts the
matching gaplessness property (a terminal decision stream with a hole in it) but cannot
assert this one, since "the body never went terminal" is indistinguishable from "the body
is not done yet".

The **driver** owns the iteration source and produces the body's `(prev…, item)` input. It
holds no part of the recurrence: the store's decided frontier already names the next position to
iterate (`step` advances the watermark unconditionally, so a carry decides its position
without appending a change), and the previous accumulator is that key's value *at* the
frontier (`store_value_at`, one fold per read key — folding *at* the position being fed,
which is what the recurrence means, rather than taking the key's latest write). So an
emitted row is a pure function of the store tile and the source tile, with nothing cached
that could drift. It decodes the source
into `(absolute position, item)` pairs (`decode_source_positioned`), since an async source's
domain arrives *unordered* and *compacts* as its consumed prefix is released; it reclaims
that prefix incrementally and releases the whole source (`True`) once the loop is done. It
also releases the changelog through the frontier — the store's keep-latest GC preserves each
key's latest write inside a released prefix, so the fold is never stranded, and without it
the store's `FanOut`-intersected watermark could never advance past the cycle branch.

**One position advances per outer pull**, because the cyclic `FanOut` serves a snapshot
taken before the traversal began: a position decided *during* a pull is not visible until
the next. This is a property of the cycle, not of the split — the store's producer is on
the stack for the whole traversal, so no arrangement of driver, body and store can refresh
the memo mid-pull. It is the rate every cyclic operator here runs at, and the driver re-arms
on the wakeup queue while a position remains to feed.

A pull-per-position means a long loop re-renders its changelog many times. That is a
**retention** problem, not a rate problem: the fix is a `Memo` in front of the store's
readers, caching the rendered tile and letting a reader release its consumed prefix early so
`gc_released_prefix` bounds what each render covers. Letting the store publish its
freshly-rendered tile into its own cyclic fan's memo, so the driver sees the position it just
decided, would buy a multi-position driver by inverting `get`'s direction — a change to the
model in exchange for a caching improvement, and not one to make.

There is one writer over the *full* source: a conditional write's carry positions produce no
change rather than a synthesized same-value write on a complement leg, which is what keeps a
restricted-source multi-leg realization's cyclic-convergence desync from arising.

**`StoreDenseRead` — the dense changelog read.** A `__reg.k` read folds the changelog at
*every* position of the loop extent → `Fun(D, V)`: an `IterateExtent(D)` trigger supplies
the domain positions (a live enumeration — over a `DataSource` it re-reads the arrived keys
each pull, so it spans live arrivals — and it aligns via `fan_in` with any co-iterated
source over the same `D`), and each position `p` reads tick `p + 1` via `store_value_at`
(which scans changes ≤ that tick — **independent of the store frontier**, so a carry
position inherits the latest earlier write and a leading carry folds to the tick-0 seed).
The trigger's positions are **sorted ascending** before folding: an async domain arrives in
arbitrary order, but the output domain must be position-ordered so that the **scalar-final**
read — `ExtractFinal` over this dense stream, i.e. the *final column* — is the highest loop
position (the final accumulator), not an arbitrary mid-loop value. (A **co-iterated** read —
an accumulator threaded into another store, e.g. `for r in …: cnt += 1; with begin(): store
:= store + cnt` — aligns by domain *value* via `fan_in`, so ordering is immaterial there;
sorting is correct for both.) One reader serves both shapes, and a downstream release of loop
positions is forwarded to the trigger so the source is reclaimed. Reading by fold rather
than by indexed projection is what unifies induction reads with transactional-variable reads.

Folding by position keeps the read independent of the store's own length — the positions
come from the trigger, the values from the fold. And the trailing-carry undercount that
once lurked in `Tile::len`/`store_frontier` is now closed at the source: a `Tile::Store`
carries terminality on a separate `terminal` flag and always keeps its numeric watermark as
`frontier = LessThanEq(w)` (never a `True` that discards `w`), so `len`/`store_frontier`
read `w` directly — spanning a trailing run of carries — instead of reconstructing it from
the latest *change* tick.

**Reply feeds ride the changelog as taps.** A feed inside the loop (`out << e`) rides the
writer decision as a `to_<defer>` field, exactly as a commit writer's reply tap does. Op-
conversion appends each tap as a write-only changelog key (after the accumulator keys), the
producer applies the decision's `tap_fired` gate (a fired tap joins the position's delta, a
non-fired one is omitted — the `__fire`-gate mechanism shared with the commit store), and a
`to_<defer>` read is a **non-carry** `StoreDenseRead` (`carry_forward: false`): for each loop
position it reads the tap **only if that position's delta actually wrote it**
(`store_delta_at`), so the feed's per-position stream spans exactly the fired positions. A
**conditional feed** (`if p: out << e`) is the same shape — the letrec phase gives it a
`to_<defer>__fire` gate (its guard path) and folds that path into the `commit` gate so a
feed-only position still appends a change carrying the tap. Because the driver is
position-sorted, the tap stream is position-ordered even over an async source (the dense
`Recurse` path scrambled it by arrival order — the bug this replaces).

<a id="remaining-the-never-terminating-bound"></a>
**Bounding a never-terminating loop (keep-latest changelog GC).** The changelog is bounded
the same way the commit store's is: a reader's release drives GC, and `StoreDenseRead`
forwards a store release derived **purely from the consumer's release** — never from who the
consumer is. A release of loop positions `≤ P` is a promise never to request them again, so
`StoreDenseRead::release_impl` computes what the store no longer needs:
- A **tap** read (`carry_forward: false`) reads only tick `p + 1`'s delta at position `p` (no
  back-reference), so positions `≤ P` make ticks `≤ P + 1` dead.
- A **carry** read (`carry_forward: true`) reads the latest write `≤` each position's tick. The
  earliest still-needed position is `P + 1` (reading tick `P + 2`); its **carry source** is the
  latest write to the key at a tick `≤ P + 2`, and the carry source only moves *forward* for
  later positions. So every tick strictly below that carry source is dead for all future
  positions — `StoreDenseRead` forwards a store release of `≤ carry_source − 1`.

The store sits behind a `FanOut`, so `InductionStoreProducer::release_impl` receives the
**intersection** over every reader and calls `CommitEngine::gc_released_prefix`, which drops the
superseded entries in the released prefix but **keeps each key's latest write**. Because a carry
read never releases *at or above* its carry source, keep-latest GC never drops a live carry
source — so the existing keep-global-latest GC suffices; no per-frontier retention is needed.
This bounds the changelog for *any* carry consumer (co-iterated or scalar-final) without the
producer knowing which it is.

The driver's own release runs the other way — outward, to the iteration source. `InductionStore`
reclaims the consumed prefix incrementally as `processed` advances, and releases the source in
full once it is complete and every arrived position is decided. That ends the driver: a drained
store serves the accumulated changelog, which is already the whole answer.

Keep-latest is also what makes the driver sound despite reading the changelog it writes:
`read_as_of(processed)` folds to the latest write ≤ `processed`, which GC never drops, so the
recurrence is never stranded (the delicate part — a naive GC that dropped the latest produced
the `30`-then-`10` failure a probe once hit). Retention is therefore **O(keys) + the slowest
reader's lag**, independent of the number of positions processed. A **scalar-final**
`ExtractFinal` drives its own bound: on each non-terminal pull it needs only the highest-domain
value, so it releases `[0, max)` incrementally — the same release path bounds the changelog even
though it never emits until (if ever) the source terminates.

## Open Challenges

### Streaming Joins
The current join design assumes a complete batch before emitting results. For true streaming joins
with incrementally advancing yield guards:
- How do we emit partial results as new batches arrive?
- Candidate approach: symmetric hash join (build on both sides, emit matches as data arrives)
- Windowed joins for time-ordered streams

### Multi-Level Nesting Optimization
Composing `parent_indices` through many nesting levels may be expensive. Trade-off: precompute
transitive indices (t1→t3 directly) vs. recompute on demand.

### Cycles
None of the above algorithms guarantee termination in the presence of cycles in the dataflow
graph. Detecting convergence (rather than truncating iteration) is an open problem.
