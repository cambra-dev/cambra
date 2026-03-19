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
| `SealedFunction(SealedFunctionGuard)` | Structured interest in a function tile (see below). |

`TileGuard::intersect()` computes the overlap between two guards (conjunction of interest
regions). `is_universal()` and `is_empty()` test the extremes.

TileGuards are also used to extract portions of a tile that a consumer is interested. This will be implemented
as a `split(guard: &TileGuard)` method on `Tile` in the future.

### SealedFunctionGuard

Refines interest in a `SealedFunction` tiling:

| Variant | Meaning |
|---------|---------|
| `Universal` | Interested in everything — domain and codomain. |
| `Empty` | Not interested in anything. Annihilator under `intersect`. |
| `Domain(Predicate)` | Interested only in domain elements matching the predicate. |
| `Codomain(TileGuard)` | Interested only in codomain elements that are part of the subtiling specified by the guard. |

### Predicate

A `Predicate` describes a subset of values within an extent. Used as a domain-completeness
signal in tiles and as a region specifier in guards.

| Variant | Meaning |
|---------|---------|
| `True` | All values. Universal predicate; identity under `intersect`. |
| `False` | No values. Empty predicate; annihilator under `intersect`. |
| `LessThanEq(Value)` | All values ≤ the given value (upper-bound streaming signal). |
| `Intervals(IntervalSet<Value>)` | Arbitrary union of intervals. |
| `Record(fields)` | Per-field predicates for record-typed extents. |

`Predicate::intersect()` computes the conjunction of two predicates.
`Predicate::as_bool()` short-circuits to `Some(true/false)` when the predicate is trivially
`True` or `False` (including uniform record predicates).

---

## Tile Operators

Each `TileOperator` is a static (compile-time) node in the dataflow graph. It knows its output
[`Tiling`] and can instantiate a live `TileProducer` via `subscribe`. Operators are constructed
during compilation; producers are created on demand at runtime.

| Operator | Input Tiling(s) | Output Tiling | Description |
|---|---|---|---|
| `Constant` | None | `Scalar` | Produces a fixed scalar `Value`. |
| `IterateExtent` | None | `SealedFunction(extent → Scalar(extent))` | Enumerates all values in an `Extent`, producing an identity-mapping sealed function (domain = codomain = extent) |
| `MapSource` | `SealedFunction(DataSourceDomain → Scalar(DataSourceDomain))` | `SealedFunction(DataSourceDomain → Scalar)` | Looks up each key of a data-source domain via `DataSourceDomainExtentImpl::get` to produce a sealed function from keys to their output values. |
| `Zip` | `N` inputs of `SealedFunction(shared_extent → *)` tilings |  `SealedFunction(shared_domain → Record(_0, … _N))` | Merges N sealed-function operators that share a domain into one sealed function whose codomain is a Record Tiling of all their codomains. |
| `ScalarTuple` | `N` inputs with `Scalar` tilings | `Record(_0, … _N)` | Packs N scalar inputs into a single `Record` tiling where each field is a `Scalar` tiling . The scalar analogue of `Zip`. |
| `MapApply` | Function: any tiling of type `A → B`<br>Data: `SealedFunction(extent → Scalar(A))` | `SealedFunction(extent → Scalar(B))` | Applies a function element-wise over a sealed-function input, transforming each codomain value. The function input can have many different tilings; currently supports `Scalar(ComputableFunction)`, `Scalar(Function)`, `CurriedFunction`, and `SealedFunction` tilings. |
| `MapToConst` | `SealedFunction(extent → *)` | `SealedFunction(extent → Scalar)` | Replaces every codomain value of a sealed-function input with the same constant, preserving the domain. |
| `ToScalar` | Constant: `Scalar`<br>Data: `SealedFunction(Unit → Scalar)` | `Scalar` | Unwraps a `SealedFunction` with `domain = Units(1)`, extracting and returning its single codomain element as a scalar tile. |
| `Converse` | `SealedFunction(domain -> Scalar(codomain))` | `CurriedFunction(codomain → domain)` | Inverts a sealed-function operator: each codomain value maps to the list of domain values that produced it. |
| `MapCompose` | Function: Function: any tiling of type `A → B`<br>Data: `CurriedFunction(extent → A)` | `CurriedFunction(extent → B)` | Applies a function to every value in each codomain list of a `CurriedFunction`, producing a new `CurriedFunction` with the same domain but transformed values. |
| `Filter` | Predicate: any tiling of type `A → bool` <br>Data: `SealedFunction(extent → Scalar(A))` | Same as input | Filters a sealed-function tile by a boolean predicate: keeps only domain elements where the predicate on the value evaluates to `true`. <br>TODO can probably remove this in favor of Restrict |
| `Restrict` | Predicate: any tiling of type `A → bool` <br>Data: `SealedFunction(A → *)` | Same as input | Filters a sealed-function tile by a boolean predicate: keeps only domain elements whose predicate evaluates to `true`. |
| `Aggregate` | `SealedFunction(* → Scalar)` | `Aggregation` | Reduces all codomain values of a `SealedFunction` input into a single running accumulator via an `AggregateKind` (e.g. Sum, Max). Currently, the aggregation is hardcoded in the graph, but we could add support for aggregate-kinds-as-data |
| `ExtractAggregate` | `Aggregation` | `Scalar` | Extracts the final value from an `Aggregation` tile, emitting it only when the aggregation is marked terminal. |
| `MapAggregate` | `CurriedFunction(domain → codomain)` | `SealedFunction(domain → Aggregation)` | Performs a per-key aggregation |
| `MapExtractAggregate` | `SealedFunction(extent → Aggregation)` | `SealedFunction(extent → Scalar)` | Extracts terminal per-key aggregation results from a `SealedFunction(D, Aggregation)`, producing `SealedFunction(D, Scalar)`. |
| `Split` | `*` | Same as input | Allows multiple operators to consume the output of the same operator. Forwards `get` requests and tracks the intersection of release guards. <br>TODO this should probably turn into the Memo operator |

TODOs for implementing hash joins:

- Add an uncurry that converts `CurriedFunction(A → UInt → B)` to `SealedFunction(Record(A, Uint) → B)`
- Add support for MapApply to take a `CurriedFunction(A → UInt → B)` as the function argument, which will then convert `SealedFunction(C → A)` to `CurriedFunction(C → UInt → B)`

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
