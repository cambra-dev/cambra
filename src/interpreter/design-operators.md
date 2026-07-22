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
| `ScalarFanIn` | `N` inputs with `Scalar` tilings | `Record(_0, … _N)` | Packs N scalar inputs into a single `Record` tiling where each field is a `Scalar` tiling. The scalar counterpart of `FanIn`; reachable from op-conversion via the `fan_in` factory. |
| `MapResult` | Function: any tiling of type `A → B`<br>Data: `SealedFunction(extent → Scalar(A))` | `SealedFunction(extent → Scalar(B))` | Applies a function element-wise over a sealed-function input, transforming each codomain value. The function input can have many different tilings; currently supports `Scalar(ComputableFunction)`, `Scalar(Function)`, `CurriedFunction`, and `SealedFunction` tilings. When the **data** input is itself a `CurriedFunction`, it maps the function over each codomain list, producing a `CurriedFunction` with the same domain and transformed values. |
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
| `FanOut` | `*` | Same as input | Allows multiple operators to consume the output of the same operator. Each consumer subscribes via a `FanOut::branch()` handle; the fan-out forwards `get` requests and tracks the intersection of release guards across branches. Constructed via either `FanOut::new` (no cyclic-mode overhead — the common case) or `FanOut::new_cyclic` (for fan-outs whose branches feed back into their own input, e.g. mutation-loop bodies whose other branch is wired to `Recurse::recursive_input`). Cyclic mode adds a per-pull tile-cache and a subscribe-in-progress flag so re-entrant subscribes / pulls skip redundant inner work and serve from the cached snapshot instead of re-entering the inner producer. |
| `Memo` | `*` | Same as input | Caches the output of an operator so it can be repeatedly read without recomputation. Immediately releases data from its input upon receipt so that the input can clear out any state. |
| `Recurse` | three inputs: `init` (any tiling — `Scalar(T)` for single-accumulator loops, `Record({f_i: Scalar(T_i)})` for multi-accumulator loops), `domain` (`SealedFunction(D → Scalar)` over the iteration extent), and `recursive_input` (`SealedFunction(D → init.tiling)` — the new-accumulator stream, wired after construction via the closure from `Recurse::recursive_input_setter`) | `SealedFunction(D → init.tiling)` (the **prev-accumulator stream**: `init` at position 0, `recursive_input[i-1]` at position `i > 0`) | Drives a mutation loop by closing the loop body's output back onto itself. Op-conversion wraps `Recurse` in a `FanOut::new_cyclic`; one branch is read by the loop body as `acc_var`, and another branch is the loop's external prev-acc stream. The loop body itself is always `Record({step, to_<defer>*})` and is wrapped in another `FanOut::new_cyclic(Memo(...))`: one branch is projected to `.step` and feeds back into `recursive_input` (closing the cycle), the other is the external output exposed directly as the body's Record stream. The cyclic `FanOut`'s `subscribing_inner` flag + "producer taken out during pull" pattern make the body's re-entrant `acc_var` reads safe: re-entrant pulls find `producer = None` and serve from the fan-out's cached tile rather than recursing back into the inner producer. **Release semantics.** `Recurse::release_impl` forwards downstream cycle-position releases to its upstream subscriptions incrementally: a release of cycle position `i` propagates directly to `domain` (same domain) and — shifted by one — to `recursive_input` (position `i` was emitted using `recursive_input[domain_values[i-1]]`, so releasing cycle `i` makes that recursive-input position obsolete).  The corresponding `known` HashMap entry is dropped; convergence tracking uses a separate `recorded_positions: HashSet<Value>` that grows monotonically even after `known` is compacted.  Streaming sources rely on this to free upstream state as positions are consumed.  On `fully_drained` (domain terminal + every position recorded), `Recurse` universally releases both `domain` and `recursive_input` so the source's release intersection reaches `Predicate::True`. |
| `ExtractLast` | two inputs: `source` (`SealedFunction(D → Scalar(T))`) and `default` (`Scalar(T)`) | `Scalar(T)` | Extracts the last codomain value of `source` once it signals terminal.  When `source` is terminal but emits zero values (e.g. a mutation loop whose body ran zero times because its iteration source was empty), emits the `default` scalar's value instead — keeping post-loop accumulators total.  Returns an empty scalar before `source` is terminal.  On the first terminal pull it releases both `source` and `default` universally — a final-consumer signal that propagates back through `FanOut`/`Memo`/mutation-loop bodies to the underlying data source. |
| `UnionOperator` | N inputs of `SealedFunction(dᵢ → Scalar(C))` tilings | `SealedFunction(Union(d₀,…,dₙ₋₁) → Scalar(C'))` | Merges N sealed-function operators into one by forming the discriminated union of their domains and deduplicating their codomains. The output domain is `Extent::Union` of all input domains; the codomain is shared when all inputs agree, or `Scalar(Union(…))` (deduplicated) otherwise. `UnionProducer::release_impl` splits an incoming `Predicate::Union` guard and forwards each per-variant predicate to the corresponding input, so release propagates correctly through the merge. |

**Pointwise `FunctionDef`s** (applied element-wise via `MapResult(input, Constant(FunctionDef))`, not standalone operators): `BinOp(op)` over a `{_0, _1}` record column, `UnaryOp(op)` over one column, and `RecordField(f)` projecting a field.

**Value-selecting `Case` in a writer decision body** (a conditional induction write `if 𝑝: acc += a else: acc += b`, or a `with begin():` per-key routing merge — a gate that varies with the element at a site with **no visible iteration source**). `lambda_elim` compiles it to the same **union of domain-restricts** as every other value-`Case`, over the *fed* element stream: `⧺ᵢ (filter_values(π̂ᵢ) ≫ eᵢ)`, first-match `π̂ᵢ`. `filter_values` (`Builtin::FilterValues` → the `Filter` tile operator, input stream + predicate) is a **value-preserving** filter — unlike `Restrict` (which returns the domain identity `{D|p}⇒{D|p}` for a source a map re-indexes), it keeps each surviving element's value `V`, so `eᵢ` maps the kept elements directly and a **partial op** (`//`) in `eᵢ` runs only where its guard holds — never eagerly at a rejected position (the retired `Select` computed both arms and faulted on the off-path one). The arms filter the *same* fed stream disjointly (first-match), so their union is a **flat merge** (`UnionOperator::new_flat`): it stays on one domain extent (not a tagged `Extent::Union`) and reassembles the full column sorted by position, co-iterating with the decision record's sibling `commit`/`writes` fields. A sourceless value-`Case` (a top-level ternary) still takes the `UIntRange(1)`-driver C-form + `final_or_default` (a tagged union dispatch); the writer-body case differs only in filtering the fed stream rather than a synthetic driver.

TODOs for implementing hash joins:

- Add support for MapResult to take a `CurriedFunction(A → UInt → B)` as the function argument, which will then convert `SealedFunction(C → A)` to `CurriedFunction(C → UInt → B)`

---

## The commit operator (`interpreter/commit_operator.rs`)

The transaction engine that backs a `Type::Txn` [`Transact`](../ccl/design/ir.md#transact--the-domain-parameterized-recurrence-carrier) store: concurrent writers propose transactions against a shared multi-key register, and the operator serializes them onto one monotonic `CommitTs` clock with optimistic-concurrency validation (allocate-on-commit + backward validation + serialize-and-retry). Op-conversion's `build_commit_store` assembles it. The design splits into a **pure engine** and its **tile adapters**:

- **`CommitEngine`** (tile-free, unit-tested) — the serialization logic. The store is `CommitTs ⇀ (Key ⇀ Value)`, held as per-tick write-set deltas with a per-key latest-write index. `attempt(proposal)` allocates the next tick and commits iff no read key was overwritten after the proposal's snapshot (else `Stale`, and the writer retries at the advanced watermark). `read_as_of(t, key)` folds the delta history; `gc_released_prefix(through)` reclaims released committed versions below the frontier, keeping each key's latest write.
- **`CommitOperator` / `CommitProducer`** — the store tile adapter. Output tiling `Store(CommitTs → Scalar(Key ⇀ Value))` (`full_store_tiling`) — a [`Tile::Store`] *changelog*, not a `SealedFunction`: each change tick carries that tick's write-set delta, and a tick absent from the changelog is *decided-absent* (its value holds from the latest earlier change), so consumers must **fold** it (`store_current` / `store_value_at`), never index it. This is what makes `store_current` well-defined on a live, non-terminal store — the fix for the `ExtractLast`-over-a-live-store hang. The watermark rides the `frontier` predicate as `LessThanEq(w)` throughout; terminality (no more commits) is a separate `terminal` flag on the tile, flipped once every writer is terminal — the frontier keeps its numeric watermark either way, so a terminal store with trailing carries is not undercounted. Each writer input is wired *after* construction via `writer_input_setter(k)`, so the operator is built inside a cyclic `FanOut` and each writer reads the store back before proposing (the `Recurse` feedback idiom, generalized to N writers). On each `get`, the producer drains every writer's new proposals in writer-index order (the serialization order) and `release`s each committed step back to its writer (the commit-ack that advances it). A store release names a prefix of decided ticks a consumer no longer reads at; the load-bearing GC is the engine's `gc_released_prefix` (keep-latest), while the per-consumer `FanOut` view folds the changelog whole, so `Tile::Store`'s `remove_guarded` is a no-op (a released tick is not a deletable position).
- **`TransactWriter` / `TransactWriterProducer`** — one *fused* writer per `with begin():` site (fused, not fanned: a stateful append-only proposal stream cannot be split across fanned branches without desyncing). Each pull reads the cyclic store, folds `(frontier, snapshot)` for its read keys, feeds `(snap…, item)` into its body via a `WriterBuffer`/`BodyInputSource`, and — per `(item, frontier)` (idempotent retry-suppression) — appends a `{snap, reads, writes}` proposal when the body grants (`commit: true`) or advances locally when it denies. Reply taps (`out << e` inside a block) ride the decision record as write-only keys committed atomically with the transaction. When a commit decision reads an induction accumulator *written by the same loop* at its request position (`store += cnt`), the accumulator is zipped into the writer *source* (`zip((reqs, __cnt.acc))`), so the `item` is a `(loop_item, acc(r))` `Record` the body destructures — `decode_source_items` decodes a `Record` codomain per position. When it reads an accumulator written by a *different, completed loop*, the decision instead broadcasts that loop's **final** value (a `Constant` via `MapResultToConst`); its `ExtractLast` is empty until the sibling loop's `Recurse` drains, so the decision body reads `None` until it converges. The writer **steps one source item per pull** and re-arms itself on the scheduler's deferred-wakeup queue (`WakeupQueue::request`) whenever an item remains to process (`current < n_items`), returning non-terminal — the same one-step-per-pull convergence idiom `Recurse` uses (#291). This single re-arm drives the cyclic store forward across pulls and covers every non-terminal continuation uniformly: a **commit** (`current` advances on the commit-ack `release`, so the next pull takes the next item), a **deny** (`current` advances here with no commit — invisible in the store frontier, so a frontier-growth signal alone would miss it), and a **not-ready** decision (`current` unadvanced, the pending body-input row reused so a re-push does not duplicate a buffer position against the body's `Memo`). It is the writer's re-arm — not any reader — that converges the store: the wakeup fans through the cyclic `FanOut` notify closure to every store branch, re-pulling the `AsOf` / `StoreValueStream` readers as commits land. A writer **drained but live** (`current >= n_items`, source not yet complete) does *not* re-arm, so an idle live server does not busy-poll — a future arrival wakes it through its source-forwarding consumer. This retires the readers' former producer-side drive-to-fixpoint (`drive_store_to_fixpoint`, deleted). Drain order rotates for fairness (round-robin `drain_start`) and retained state is bounded (superseded proposals dropped via `drop_superseded`). The proposal stream is an offset window: released (committed) prefixes are compacted away, keeping writer state bounded on a long-lived store.
- **`BodyInputSource` / `BodyInputSourceProducer`** — serves the writer body its `(snapshot…, item)` input off the shared `WriterBuffer`. It is **release-aware**: the body op fans this source through `FanOut`/`Memo` (which pull it repeatedly per round), so it emits only positions past its released cursor — re-emitting a released position would make the `Memo`'s append-merge duplicate a domain position (an invalid tile). This makes it delta-producing, like the induction body's `fan_in` input.
- **`StoreValueStream` / `StoreValueStreamProducer`** — folds the shared store's [`Tile::Store`] changelog to project one key's commit-value stream `CommitTs ⇀ V` (carrying values forward across ticks that wrote other keys — the step interpolation). Its own *output* is a `SealedFunction(CommitTs → Scalar(V))` — a genuine per-key value-over-time, each tick a decided value. It backs the **in-block reply tap** (`out << e` inside a block, a per-commit commit-tick-indexed event stream — `carry_forward: false`) and the read-your-writes register carry (`carry_forward: true`). A fed-out register read (`__reg.k` outside its block) does *not* reduce this via `ExtractLast` — that "terminal register value" path does not exist; every such read folds the store as-of via `AsOf` (below). `ExtractLast` reduces only genuinely-terminating histories (a post-loop induction accumulator, the broadcast source).
- **`AsOf` / `AsOfProducer`** — the **as-of (temporal) join**, the live cross-endpoint read. Two inputs: a `trigger` (`SealedFunction(B → *)` — the positions to sample at, e.g. an HTTP request stream) and a `source` — the shared commit store itself (a [`Tile::Store`] fan branch) — plus what to sample (`AsOfOutput`). For each trigger position, latch the store's **current value(s)** (`store_current`, folding the store at its decided frontier) at the moment that position is first observed, indexed by the *trigger* (the outer request loop), not the commit clock. Two output shapes: a **scalar** read of one register → `SealedFunction(B → Scalar(V))` (a single- or computed-register live read); a **snapshot** read of several registers → `SealedFunction(B → Record{field: Scalar(V)})`, every field folded from *one* source render at one commit frontier so the registers are read atomically (§I-c snapshot consistency), which the reply projects. It folds the store directly rather than through a per-key `StoreValueStream`: the latest-value logic lives in the step tiling (`store_frontier` / `store_current`), so `AsOf` is the thin residual sampler. On each pull it samples the `source` store's **current** tile *once* (consumer-driven — no producer-side drive-to-fixpoint) and latches that watermark's value to every newly-seen trigger position. It is not `AsOf` that converges the store: the store's own writer steps one commit per pull and re-arms itself on the wakeup queue, and that wakeup fans through the cyclic `FanOut` to re-pull `AsOf` as commits land. So a position latched on an early pull freezes to the watermark it then saw (an arbitrary as-of sample, which the unordered model permits — never a "final" value); a later position, re-pulled after further commits, latches a later value. `AsOf` propagates **non-terminal** until the store is terminal (`frontier == True`) *and* every live trigger position is latched — so it cannot report "done" while the store is still committing (which would freeze a store no other consumer drives) or while a live position still awaits a value; only then does the trigger's own terminality ride through. **Tile-legal by construction**: the output grows monotonically over the trigger domain and an already-latched position is never re-emitted with a different value (the "snapshot per request" invariant). It is the dual of the commit `Recurse`: `Recurse` latches a private accumulator per *source* step; `AsOf` latches the store's current value per *trigger* step. `release_impl` compacts released trigger positions (a prefix watermark, since the request domain is a monotone `UInt` prefix); `get_impl` releases the store fan *below* its latest decided tick (a future trigger only ever needs the latest-as-of-its-time, `≥` the current), letting `CommitProducer` reclaim a live store's superseded history. Born in `transact_phase::rewrite_live_reads` (pre-lambda-elim); carries its own recorded type (no inference scheme). **`AsOf` is every fed-out `Txn` register read**, regardless of the reading loop's domain (a live `DataSource` request stream, a finite loop, or a standalone singleton) — it is a *sample at the reading transaction's observation time*, i.e. the store as of an **arbitrary position** in the commit order. There is no terminal/"final" register read: no term requests the store's last value (a future `await_final` builtin would), so nothing routes a register read to `ExtractLast`. A standalone read is the singleton-trigger instance of the same `AsOf`; the position it observes is whatever watermark its latch pull happened to see (often an early one — e.g. the seed — since it freezes on first sight), a scheduling artifact, not a semantic guarantee of the drained value. (The only residual liveness check is `transact_phase::check_live_reads_resolved`, which rejects an *unrecognized-shape* fed-out read sitting beside a never-terminating `DataSource` trigger — not a semantic classification but a hang-guard, since such a read would otherwise fall through to an `ExtractLast` over an infinite stream.)

A single-writer induction store is the degenerate no-conflict case of this same contract, which is why one `Transact` carrier serves both engines.

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
  `FlattenDomain`, `PermuteDomain`, `CollectionUnion`, `Sum` / `Max`,
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

- **`Recurse` bodies** (the induction realization of a recognized `Transact`)
  fan-out the cyclic prev-accumulator stream and the body output (via
  `FanOut::new_cyclic`); see the `Recurse` description above for the full
  structure.

### Aggregates, sinks, and the program root

The pipeline always bottoms out at one of three consumer shapes:

1. A scalar produced by `Apply(<chain>, Sum)` / `Max` (compiles to
   `Aggregate` + `ExtractAggregate`) or `Apply(Tuple([stream, default]), FinalOrDefault)`
   (compiles to `ExtractLast`).
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

An induction store (a `mut`-loop accumulator, possibly with a conditional write) is the
**degenerate no-conflict dual of the commit store**, and shares its machinery: it is a
[`Tile::Store`] changelog driven by iteration *position* instead of by concurrent
proposals. Op-conversion (`build_induction_store_single`) routes a **single-writer,
tap-free** induction store over a **static** (finite, non-async) extent here; a **reply
tap** (a feed riding the loop) or an **async data-source** extent falls back to a dense
`Recurse` whose body stream is `D ⇀ {commit, writes}`, read by `.writes.(index)`.
(Multi-writer is *not* a fallback case — recognition folds every conditional write to one
writer, so `build_induction_store` rejects any writer count ≠ 1 outright rather than
carrying a multi-leg branch.)

This finite/async split is an **incompleteness, not a semantic distinction** — and the only
place in the substrate that makes it. Everywhere else the tiling protocol treats a finite
source as a stream that happens to terminate: comprehensions, joins, aggregates, and the
dense mutation loop all run over a literal list *and* a `DataSource` through one graph
(monotonic tile growth + pull-until-the-frontier-stalls). The changelog drive should serve
both too; that it does not yet is why the dense `Recurse` fallback still exists. See
[*Planned: one changelog realization for every loop*](#planned-one-changelog-realization-for-every-loop)
below for the mapped path to removing the fork.

**`InductionStore` — the position-driven producer.** It owns a `CommitEngine` seeded at
tick 0 with the accumulators' inits (so the changelog is self-describing — a read below
the first *iteration* change folds to the seed), and drives the accumulator recurrence
**sequentially inside the producer**: for each iteration position it folds the previous
accumulator out of the engine, feeds the writer body `(prev…, item)` through a
[`BodyInputSource`] buffer, reads the `{commit, writes}` decision, and `step`s the engine
— a `commit: true` position appends a change (tick `pos + 1`), a `commit: false` (a failed
guard) is a **carry** (no change; the value inherits). Because the accumulator lives in the
engine, not on a cyclic tile, there is **no cyclic `FanOut`** — the previous value is always
available before the body needs it. This dissolves the cyclic-convergence desync that a
restricted-source multi-leg realization suffered: there is one writer over the *full*
source, and a conditional write's carry positions simply produce no change rather than a
synthesized same-value write on a complement leg.

**`StoreDenseRead` — the dense changelog read.** A `__reg.k` read folds the changelog at
*every* position of the loop extent → `Fun(D, V)`: an `IterateExtent(D)` trigger supplies
the domain positions (so it aligns via `fan_in` with any co-iterated source over the same
`D`), and each position `p` reads tick `p + 1` via `store_value_at` (which scans changes
≤ that tick — **independent of the store frontier**, so a carry position inherits the
latest earlier write and a leading carry folds to the tick-0 seed). One reader serves both
shapes: a **scalar-final** read (`total` after the loop) is `ExtractLast` over this dense
stream; a **co-iterated** read (an accumulator threaded into another store, e.g.
`for r in …: cnt += 1; with begin(): balance := balance + cnt`) is the dense function itself.
This replaces the dense `.writes.(index)` projection with a fold, unifying induction reads
with commit-register reads.

Folding by position keeps the read independent of the store's own length — the positions
come from the trigger, the values from the fold. And the trailing-carry undercount that
once lurked in `Tile::len`/`store_frontier` is now closed at the source: a `Tile::Store`
carries terminality on a separate `terminal` flag and always keeps its numeric watermark as
`frontier = LessThanEq(w)` (never a `True` that discards `w`), so `len`/`store_frontier`
read `w` directly — spanning a trailing run of carries — instead of reconstructing it from
the last *change* tick.

### Planned: one changelog realization for every loop

Removing the finite/async fork means teaching **both ends** of the changelog path — the
drive and the dense read — to handle an async (incrementally-arriving, releasable) source;
the finite case is then just the terminating instance, and the dense `Recurse` fallback
retires. A probe that routed async loops through `build_induction_store_single` mapped the
work into three pieces (and validated that the *value* comes out right — the store is a
correct, terminal changelog — so this is realization plumbing, not a model gap):

1. **Drive — position-aware + releasing.** Read the source by its *absolute domain
   position*, not a 0-based codomain index: an async source's domain arrives **unordered**
   (a probe saw `[1, 0]`) and **compacts** as its consumed prefix is released, so a 0-based
   read misaligns. Sort the arrived `(pos, item)` pairs, drive positions `≥ processed`, and
   release the consumed source (universally once terminal). With this the drive computes the
   correct accumulator for a finite list, an async plain `mut` loop, and an async
   conditional loop.

2. **Read — fold the *live* trigger.** `StoreDenseRead`'s trigger is a **static**
   `IterateExtent(D)`; over an async source it enumerates only the statically-known
   positions and misses live arrivals (a probe read `30` where the correct — and correctly
   rendered, terminal — accumulator was `60`). The dense read must fold the source's **live
   trigger** (its actual arrival domain), exactly as the rest of the substrate iterates a
   `DataSource`, so the fold spans every arrived position.

3. **Memory bounding (the long-lived-store bound).** A never-terminating
   stream must bound both the retained source and the changelog. Incremental (non-terminal)
   prefix release and keep-latest changelog GC both interact with the drive's **own**
   `read_as_of` carry — the drive reads the changelog it is writing — so a naive
   reader-driven release drops commits the drive still needs (a probe produced `30`, then
   `10`, as GC/release ate the recurrence's past). The GC must keep each key's latest write
   and be gated by the drive's frontier, not merely a reader's released prefix.

Until these land, the dense `Recurse` path remains for async/tap loops: it is correct, just
a second realization of the same concept — the smell this section exists to retire.

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
