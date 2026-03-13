# CCL Operator Specifications

Specifications for each CCL (Cambra Core Language) operator. For the underlying protocol and
progress algebra formalism, see [docs/operational-semantics/semantics.md](/docs/operational-semantics/semantics.md).

Each operator is **stateless** and corresponds to program syntax. Calling `subscribe()` on an
operator creates a runtime **producer/consumer** pair that manages actual execution state.

---

## Literals

A `Literal` operator holds a constant value.

`subscribe()` immediately calls `notify()` on the consumer. `get()` returns the constant
as a single-element `ColumnValue` with a full yield guard. `release()` is a no-op.

---

## Data Sources

A `DataSourceDomain` wraps an external data source (e.g., stdin, a test fixture, a network stream).
Unlike computed operators, data sources are polled externally via the `Scheduler`.

Relevant interface:

```rust
trait DataSourceDomainExtentImpl {
    fn get_id(&self) -> String;
    fn check_for_new_data(&mut self) -> bool;
    fn get_yield_guard(&self) -> Guard;
    fn get_elements(&self) -> Box<dyn Iterator<Item = Value>>;
    fn release(&mut self, obsolete_guard: Guard) -> Guard;
}
```

The `Scheduler` holds references to all `VarProducer` objects backed by data sources and calls
`check_for_notifications()` in the main loop to drive incremental execution.

During compilation, the underlying `DataSourceDomainExtentImpl` objects will exist in a scoped registry
so that multiple references to the same source can share their internal state.

---

## Variables

Variables are split into **operators** (stateless, syntax-level) and **runtime producers**
(stateful, execution-level).

### Var

A variable definition — not an `Operator` and cannot be subscribed directly. Holds:
- The variable's name
- The variable's extent (its type), which may be `Extent::Restricted` when an `if` predicate is present
- The `owns_restriction` flag: set when this variable is responsible for setting up its `Restriction`'s
  compute producer at subscription time (see `Extent::Restricted` below)

`Var` does **not** hold a binding. Binding happens dynamically: the `Apply` operator binds
an argument to the variable; operators that consume the lambda directly cause it to iterate.

### VarProducer (Runtime State)

Created when subscribing to the lambda containing the `Var`. Has one of two sources:

**Argument source** (lambda is applied to an argument):
- Wraps a producer from the binding expression
- Forwards values directly from that producer

**Iteration source** (lambda consumed directly, e.g. by aggregation or output):
- Iterates over the variable's extent, applying the predicate to filter values
- For predicates referencing outer variables: executes as a join (see below)
- Produces `parent_indices` relating iteration results to outer iteration positions

Both sources:
- Maintain the list of all consumers subscribed to this variable
- Store a release guard for use by `VarRefProducer`

### VarRef (Operator)

A reference to a variable by name. At `subscribe()` time, looks up the variable in the provided
`VarScope` and creates a `VarRefProducer`.

### VarRefProducer (Runtime State)

Produced by `VarRef::subscribe()`. Responsibilities:
- Filter the `VarProducer`'s data by the intent guard
- **Alignment**: when referencing an outer variable from within an inner iteration, expand the outer
  variable's values using the inner iteration's `parent_indices` so all values are aligned at the
  innermost level
- On `release()`: return the stored release guard from the `VarProducer` rather than propagating
  upstream (the lambda handles upstream release)

### VarScope

A parent-chain lookup structure for variable scopes. Each scope holds exactly one variable
(the lambda's variable) plus a reference to the enclosing scope.

`lookup_variable(name)` walks the parent chain and returns:
1. The found `VarProducer`
2. The chain of intermediate iteration-source variables between the lookup site and the found variable
   (used by `VarRefProducer` to compose `parent_indices` for multi-level alignment)

### Variable Sources

| Source | When | Behavior |
|--------|------|----------|
| **Argument** | Lambda applied (`(\x. body) arg`) | `VarProducer` wraps argument's producer |
| **Iteration** | Lambda consumed directly (`sum(\x. body)`, `print(\x. body)`) | `VarProducer` iterates over extent |

### Scans as Joins

When multiple lambdas with iteration source are in nested scopes, execution is conceptually a join.
In the lowered representation, a list comprehension `[body for x in src1 for y in src2 if pred]`
is lowered to a single outer lambda over a packed index extent:

- **Single generator, no predicate**: the outer extent is the source's index extent directly.
- **Multiple generators**: the outer extent is `Extent::Record` packing all index extents under
  tuple-attribute keys (`_0`, `_1`, …); the runtime computes the cartesian product via
  `ColumnData::cartesian_product_with_correlation`.
- **`if` predicate present**: the outer extent is `Extent::Restricted` wrapping the base extent
  (see below). A `ComputeRestriction` operator is attached to evaluate the predicate.  During
  iteration, the computed restriction is used to limit the iteration to only the matching
  values.

The `parent_indices` field in `ColumnValue` is the output of the join: each inner row maps to the
outer row it is paired with.

The join strategy can either be a loop join for arbitrary predicates, or a hash join for equality
predicates between exactly two sources.

---

## Lambda

A lambda is a universally-quantified variable paired with a body expression.

### Lambda (Operator)

`subscribe()` splits the intent guard into domain and codomain components, creates a `VarProducer`
for the variable, and subscribes to the body with the new `VarScope`.

### LambdaProducer

`get()` returns a batch of function bindings. The yield guard from `get()` is a domain-only guard
(`Guard::Domain(...)`) because completeness information about function bodies is not currently
derived separately.

`release()`: if the obsolete guard is domain-only, only the variable (domain) is released.
Otherwise, the guard is split into domain and codomain parts and release is propagated to both
the variable and the body.

---

## Apply

Applies a function to an argument, resolving the argument and propagating it to the function.

### Apply (Operator)

`subscribe()` receives an intent guard for the codomain. It:
1. Uses the function's dependency relation to generate the domain intent guard (the preimage of
   the codomain intent guard)
2. Subscribes to the argument with the domain intent guard
3. Subscribes to the function with the combined domain/codomain intent guard

(The choice of eager vs. lazy evaluation is made here by whether the function is subscribed
before or after the argument notifies.)

### ApplyProducer

`notify()` is forwarded from the argument to the function.

`get()` retrieves values from both the argument and function and returns the corresponding
codomain elements.

`release()` implements bidirectional obsolescence flow:

```
def release(g_c):
    g_d1 = f.pre(g_c)               # preimage of codomain obsolete guard
    g_d2 = arg.release(g_d1)        # release argument; may expand domain obsolete guard
    g_fn = fn.release(combine(g_d2, g_c))  # release function with combined guard
    return g_fn.split_codomain()
```

Obsolescence flows upstream from the body (via the codomain guard) and downstream from variables
(via the domain guard). These flows meet at `Apply` nodes. Most of the time this reduces to
unidirectional flow, but the bidirectional handling is required for correct garbage collection in
composed programs.

---

## Memos

A memo caches a function's bindings so they need not be recomputed. It proxies all
producer/consumer interactions with its argument function, adding storage and cache logic.

`subscribe()` checks whether the current yield guard already covers the intent guard. If not,
it extends the upstream subscription to cover the union of previous and new intent guards, then
returns a new downstream subscription for the requested intent guard.

`notify()`:
1. Calls `get()` immediately and stores all returned bindings
2. Calls `release()` with the yield guard to release upstream interest in the now-stored region
3. Issues `notify()` to all downstream subscriptions with overlapping intent guards

`get()` returns a handle to the stored data, filtered to the subscription's intent guard.
Regions released by all subscriptions are not returned.

`release()` drops bindings for the given obsolete guard. Does not propagate upstream, because the
memo releases upstream interest as soon as it stores data.

---

## Records

A record is a map of field names to field operators. `subscribe()` splits the intent guard into
per-field sub-guards and subscribes to each field independently. `notify()` is called by each
field when ready. `get()` zips the fields' `ColumnValue`s together.

Open question: when some fields are ready but others are not, should `get()` return a partial
record or wait for all fields? Current position: wait for all subscribed fields.

`release()` splits the obsolete guard into per-field sub-guards and propagates them.

---

## Restricted Extents and ComputeRestriction

### `Extent::Restricted`

`Extent::Restricted { base, restriction }` wraps any extent with a `Restriction` handle. The
`Restriction` holds a `ComputeRestriction` operator and, once subscribed, a producer that evaluates
the predicate. At iteration time the runtime calls `get_correlations()` on the `Restriction` and
uses the result to limit iteration to matching rows only.

A `Var` whose extent is `Restricted` and whose `owns_restriction` flag is set is responsible for
calling `set_up_producer` on the `Restriction` during subscription; this wires the
`ComputeRestriction` operator into the live producer graph.

### `ComputeRestriction` (Operator)

Wraps a predicate operator and tags it with a `RestrictionType` that tells the caller how to
interpret the output:

- **`FilteredProduct`** (loop-join fallback): the wrapped operator is a lambda over the full
  cartesian-product index extent that returns `Bool` for each row. `get()` returns
  `FunctionBindings { outputs: Bools }`. `Restriction::get_correlations` converts this to a
  `Correlations::Positional(BitSet)` used to skip non-matching rows during iteration.

- **`HashJoin`**: the wrapped operator encodes an equality join using the `Converse` operator
  (see below). `get()` returns `FunctionBindings { inputs: probe_elements, outputs: Functions }`,
  where each output function lists the build elements whose key matches the corresponding probe
  element. `Restriction::get_correlations` decodes this into `Correlations::Tuples`, a flat list
  of `[probe_idx, build_idx]` pairs covering exactly the matching rows.

`subscribe()` subscribes to the wrapped predicate using an **isolated** `Scheduler` so the
predicate's dataflow does not participate in the main notification loop. Notifications flow through
the outer iterating variable instead, which shares the same sources.

### Hash Join Lowering

The lowerer (`lower_list_comp`) detects hash-join opportunities in `[body for x in A for y in B if x.k == y.k]`:
a two-generator comprehension with a single equality predicate where each side references exactly
one distinct generator. The equality predicate is detected by `try_extract_equality_join`, which
normalises so the lower-indexed generator is always the build side.

The join is expressed entirely in terms of existing interpreter primitives via the `Converse` operator:

```
join_op = Lambda(probe_var,
            Apply(
              Converse(Lambda(build_var, build_key(build_var))),
              probe_key(probe_var)
            ))
```

`Converse(Lambda(build_var, build_key))` inverts the build-side key function into a
`LookupTable` (`key_value → [build_indices]`) at evaluation time. Applying it to
`probe_key(probe_var)` looks up each probe key in the table, yielding the list of matching build
indices. The resulting `ComputeRestriction::new_join(join_op)` is attached to the outer extent's
`Restriction`.

### `Converse` (Operator)

`Converse` inverts a function `A → B` into a lookup table `B → List(A)`. Given an input with
extent `A → B`, it produces an operator with extent `B → (UInt → A)`, where each output value
maps to the indexed list of input values that produced it.

`subscribe()` wraps the input producer in a `ConverseProducer` that calls
`ColumnValue::function_converse` on the raw `FunctionBindings` result, converting it into a
`LookupTable`.

`subscribe_to_application()` further composes a `ConverseApplicationProducer` that applies the
`LookupTable` to a column of argument values, producing `FunctionBindings` pairing each argument
with its pre-image list as a `Value::Function`.

---

## Let-bindings

Existentially quantified variables — always argument source, never iteration. Let-binding lowers to a
`Lambda` applied immediately to its definition. Scoping is handled by `VarScope`.

*(Lowering support in progress.)*

---

## Pattern Matching

Dispatches on the variant of a union type. Each arm corresponds to a sub-lambda that binds the
destructured fields.

*(Design deferred; lowering support not yet started.)*

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
| `LookupFunction { domain, codomain }` | Logically, this tiling is equivalent to `SealedFunction(domain, SealedFunction(UInt, codomain))`. It has a custom layout for efficiency, detailed in the `Tile` table below. |
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
| `LookupFunction { map, domain_predicate }` | Each tile represents the known mappings of a curried function. In the implementation, this is realized as a map from the domain to lists of codomain elements. (This is also likely to change in the near future to be more efficient) |
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
| `LookupFunction(bool)` | All-or-nothing interest in the lookup table. |
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
