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

In practice this means tile operators need to be **tile-polymorphic in their inputs**: the same CCL-level combinator often needs two tile-level implementations, one per input tiling. The `MapResult` family handles this via `change_tiling_result`; fan-in is handled by [`fan_in`](./tile_operators.rs), which dispatches to [`FanIn`] (function-tiled arms) or [`ScalarFanIn`] (scalar arms) based on what the compiled arms ended up with. New combinators should assume the same pattern: don't commit to one tiling when the upstream context picks it.

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
| `MapResultToConst` | `SealedFunction(extent → *)` | `SealedFunction(extent → Scalar)` | Replaces every codomain value of a sealed-function input with the same constant, preserving the domain. |
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

TODOs for implementing hash joins:

- Add support for MapResult to take a `CurriedFunction(A → UInt → B)` as the function argument, which will then convert `SealedFunction(C → A)` to `CurriedFunction(C → UInt → B)`

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
  `LastOrDefault`, and the catch-all `Apply` arm (where the function position
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
  `MapResultToConst` instead.

- **`Let { bound_expr, body }`** fans the parent input into both the bound
  expression and the body (described above).

- **`Loop` bodies** fan-out the cyclic prev-accumulator stream and the body
  output (via `FanOut::new_cyclic`); see the `Recurse` description above for
  the full structure.

### Aggregates, sinks, and the program root

The pipeline always bottoms out at one of three consumer shapes:

1. A scalar produced by `Apply(<chain>, Sum)` / `Max` (compiles to
   `Aggregate` + `ExtractAggregate`) or `Apply(Tuple([stream, default]), LastOrDefault)`
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
