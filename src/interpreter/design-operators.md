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
| `DataFunction { domain, codomain }` | A collection `domain ⤇ codomain` — one new dimension over the rows it sits in. `codomain` is a tiling in its own right, so a chain of them nests one node per level and a `Record` may sit between two. Keys accumulate incrementally, and a `domain_predicate` on the tile says which of them are complete. The runtime layout is in the `Tile` table below. |
| `Aggregation { accumulator }` | An ongoing aggregate. Its accumulator is a tiling: a scalar for a fold that reduces, and the element's own tiling for `Sole`. |

`Tiling::extent()` converts a `Tiling` to the corresponding `Extent` (the type-level view).

`Tiling::empty_tile()` constructs the starting state for a tile — empty `ColumnValue`s and
`Predicate::False` domain predicates everywhere.

### Tile

A `Tile` holds the actual data. Its shape mirrors its `Tiling`:

| Variant | Contents |
|---------|----------|
| `Scalar(ColumnValue)` |  The two tiles in this tiling are `⊥` and the specific scalar of the tiling. `⊥` is represented as an empty `ColumnValue` and the scalar is represented as a `ColumnValue` of length 1 |
| `Record(fields)` | A Record of other `Tiles` |
| `DataFunction { row_starts, domain, codomain, domain_predicate, deleted }` | A tile is a value of type `T` vectorized over `R` rows: `R` is 1 for the tile as a whole, and inside a collection's `codomain` it is that collection's key count. A collection is the rule that introduces a dimension — `row_starts` has one entry per enclosing row naming where that row's run of `domain` begins, and `codomain` is a tile over those keys. Compressed-Sparse-Row-wise: every row's keys run together in one column, so a chain of collections holds the columns a flat level list would, and unlike a flat list it can say where a `Record` sits between two levels. |
| `Aggregation { accumulator, terminal }` | Logically, this tiling knows the final number of inputs `N` that will be aggregated and the tiles are of form `(count, accumulator)`.  However, for making this feasible to compute, we instead store a terminal flag indicating `count == N`. |

`Tile::is_terminal()` returns true when a tile carries complete, final data. No larger tiles will ever be returned, although
equivalent tiles with some data released may.

`Tile`s also support `merge` to combine two tiles, `remove_guarded` to filter out data in a `Tile` matching a `TileGuard`, and `to_guard` to construct a `TileGuard` that corresponds to the data in a `Tile`

A merge extends a collection with keys and rows that arrived later; `Tile::merge` states how a
key both sides hold is merged.

`Tile::append_level` builds a `DataFunction` one level deeper than the function tile it is given,
out of that tile's codomain: `Product` repeats each row's value across the group it opens.
One level is the base case, so an operator that appends a level is closed under its own
output. `Tiling::append_level` is the same step on the static shape.

The appended level is whole for every parent it names. A parent's keys occupy one contiguous run
of the level below and `merge` concatenates levels rather than reaching inside a group, so no
later tile adds to a group. The tile therefore calls every key present final together with the
level just built, and removals ride through level for level — the appended level has removed
nothing.

Tiles representing collections (`DataFunction`) support logical deletes by storing a `BitSet` of
deleted values. These are set by filtering operators like `Restrict` and compacted away by stateful
operators like `Memo` and aggregation. A `DataFunction` carries **one set per domain level**, so a bit
names a position in that level's own column and a removed group and a removed entry are different
bits rather than one bit read two ways. A producer marks the level its removals name: the filters
mark the innermost, a group going by way of its entries, which is where `Tile::retain_keys` reads.
An operator appending a level leaves its input's removals at the level that named them —
`append_level` promotes a one-level tile's flat set to level 0, the level its rows now sit at,
and carries a nested tile's per-level sets through unchanged.

An empty group and a removed key are different tiles: the first is two equal `row_starts`, which
`Tile::DataFunction`'s `row_starts` field states, and the second is a `deleted` bit at the key's own
level, taken with its subtree by `Tile::compact`. `Tile::retain_keys` produces the first and never
the second.

### TileGuard

A `TileGuard` specifies a sub-tiling (a downward-closed, ⊕-closed subset of tiles) of interest. It drives
demand-directed computation and incremental release, mirroring the intent/yield guard system of
the previous version of the interpreter.

| Variant | Meaning |
|---------|---------|
| `Scalar(Predicate)` | A value with no keys of its own, named under the paths reaching it: `True` under every path, `False` under none, or `Qualified { enclosing, here: True }` under the paths `enclosing` admits. |
| `Aggregation(Predicate)` | An aggregate's result, named under the paths reaching it as `Scalar` is. |
| `Record(fields)` | Per-field `TileGuard`s, allowing fine-grained field demand. |
| `Function(FunctionGuard)` | Structured interest in a function tile (see below). |
| `Or(arms)` | Union of two guards no single variant holds: a two-level tile is covered partly by its inner keys and partly by its outer, and `FunctionGuard` has no `Domain`-with-`Codomain` arm. Each arm is a chain of `Codomain` steps ending in one guard (`TileGuard::flatten_or`), so arms naming the same place merge, and an arm beneath a key a shallower arm names whole is dropped. |

`TileGuard::intersect()` computes the overlap between two guards, and `TileGuard::union()` their
union; `is_universal()` and `is_empty()` test the extremes. Both run field by field over a
`Record` guard, which names a region per field (`TileGuard::union`).

A `Codomain` arm is read against every row of the values it wraps, so `Tile::to_guard` names the
keys a still-growing row holds by their whole path. Named bare, a key would be released under
every row, including a row that has not received it yet.

TileGuards are also used to extract portions of a tile that a consumer is interested. This will be implemented
as a `split(guard: &TileGuard)` method on `Tile` in the future.

### FunctionGuard

Refines interest in a `DataFunction` tiling:

| Variant | Meaning |
|---------|---------|
| `Domain(Predicate)` | Interested only in domain elements matching the predicate. |
| `Codomain(TileGuard)` | Interested only in codomain elements that are part of the subtiling specified by the guard. |

Against a `DataFunction` the two compose into a level reference: `Domain` names the outermost
level, and each enclosing `Codomain` steps one level in, so a tile of 𝑛 levels names its innermost
under 𝑛−1 wrappers (`Tile::to_guard`).

A `Record` between two levels is a level reference too, not a leaf. Its fields stand over the
keys the record does, so a collection in one of them is a level under those keys, and a
`Codomain` naming a record carries a `Record` guard whose fields are read the same way. A key
is released once every field under it is complete, so a scalar field beside a still-growing
collection holds the key.

A keyless field beneath a level is named by the rows above it: `Scalar(Qualified { enclosing:
𝑅, here: True })` is that field's cell under the rows 𝑅. This is the only way a guard names
part of a record without naming whole keys, and it is how the meet of two readers of one
record, each done with a different field, stays exact. `TileGuard::flatten_or` states a record
whose every field is whole under 𝑅 as `Domain(𝑅)`.

A record ends the collection chain, and a collection in one of its fields still grows under the
record's key. `Tile::holds_a_level` states the two questions that differ there, and which of them
guards, the merge, and the chain walks each ask.

"Interested in everything" and "interested in nothing" are not separate variants — they are the trivial/degenerate guards, recognized via `is_universal()` / `is_empty()` (an empty guard is the annihilator under `intersect`).

### Predicate

A `Predicate` describes a subset of values within an extent. Used as a domain-completeness
signal in tiles and as a region specifier in guards.

| Variant | Meaning |
|---------|---------|
| `True` | All values. Universal predicate; identity under `intersect`. |
| `False` | No values. Empty predicate; annihilator under `intersect`. |
| `Intervals(IntervalSet<Value>)` | A scalar key's admitted values, clamped to the type's range. `Predicate::at_or_below(v)` builds the prefix `≤ v`, the upper-bound streaming signal, and `Predicate::below(v)` the strict one. Never built over records. |
| `Record(fields)` | A box over a record key: one predicate per field, with AND semantics. |
| `Or(arms)` | A union of boxes no two of which join into one box, as `flatten_or` leaves it; three or more arms can still cover one box. Arms are always flat (no nested `Or`). |
| `Qualified { enclosing, here }` | A key of an inner level **under the enclosing path that reaches it**: admits `(k₀ … k_d)` when `(k₀ … k_{d-1})` satisfies `enclosing` and `k_d` satisfies `here`. Built through `Predicate::qualified`, which drops the arm where `enclosing` admits everything. |
| `Union { tags, rest }` | A predicate over a union-typed extent (`Extent::Union`): one predicate per named tag, and `rest` (`True` or `False`) for every tag it does not name. A value `Union { tag, inner }` satisfies it iff the predicate for `tag`, its own or `rest`, admits `inner`. A predicate need not name every tag of its domain: a column names only the tags it holds, which width subtyping makes fewer than its extent's, and a point names one. Built through `Predicate::tagged`, whose canonical form names no tag that says what `rest` does; `Predicate::over_every_tag` builds one from the whole tag set, which is `True` when every tag is. Used as the domain predicate on tiles emitted by `UnionProducer`, and split by `UnionProducer::release_impl` to forward each tag's predicate to the upstream input for that tag. |

`Predicate::intersect()`, `union()`, `minus()`, and `subsumes()` are defined between any two
predicates over one domain, and refuse two predicates over different domains.
`Predicate::as_bool()` short-circuits to `Some(true/false)` when the predicate is trivially
`True` or `False`: a record whose fields are *all* `True`, a record with *any* `False` field
(the fields are an AND, so one empty field admits nothing whatever the others admit), and an
`Or` whose arms are all `False`.
A `Union` predicate in canonical form names only tags that differ from `rest`, so `as_bool()`
answers `None` for it; universality over a union domain is spelled `True`. The set operations
(`intersect`, `minus`, `union`, `subsumes`) apply tag by tag over every tag either side names,
reading an unnamed tag as its side's `rest`, and combine the two `rest`s the same way. A prefix
of a union domain (`at_or_below` of a union value) has no spelling: it would need the tags
ordered before the bound whole and those after it empty, which one `rest` cannot say.

### Qualified predicates

Every arm but `Qualified` is **unqualified**: read against the last component of a path alone,
it says the same of that key under every enclosing path. That is the whole of what a curried
collection's levels could state on their own, and it over-claims wherever the levels are not
alike — a nested carrier keeps its enclosing rows open while the row being run is decided, so a
key complete under the running row would be claimed under every row.

`Qualified` states a region of **paths** instead. `enclosing` is itself a predicate over the
level above's paths, `Qualified` again where the nest is deeper, so depth costs nesting rather
than a concept per level. `Predicate::exactly(path)` is the singleton region — one qualified
component per level.

Reading one takes the whole path. `contains_path` is the read; `contains` panics on a qualified
predicate rather than answering for a key it cannot place under an enclosing path, because a
conservative `false` would make the caller act on a region that is not the one it asked about.
`is_applicable_over` checks it against the extents of the levels the path runs through, where
`is_applicable_to` checks one level. `TileGuard::covers_path` is the same question asked of a
guard, and `TileGuard::check_from_under` threads the levels a `Codomain` step has walked past.

A qualified predicate is a box over two components ([Boxes and prefixes](#boxes-and-prefixes)).
`split_qualification` splits any predicate into the enclosing paths it is qualified by and the
keys it admits under them, an unqualified one as `(True, self)`, so one rule serves both shapes.

### Restating a moved group

A level's `domain_predicate` names whole paths from its tile's root. An operator that takes a
row's group out to work on it alone reads the group's statements over the group's own paths, and
one that puts a group back under a different row, or changes the levels around it, restates what
the group carries:

| Move | Restatement |
|------|-------------|
| Take row 𝑟's group out (`Tile::group_at`) | `within(𝑟)`, or `True` where the level above calls 𝑟 complete |
| Place a group under row 𝑟 (`Tile::regroup_beneath`) | `beneath(𝑟)` |
| Attach a column of groups to the rows 𝑅 it stands under | `qualified_by(𝑅)`; `Tile::qualify_codomain_by_keys` for a column under one row's keys |
| Insert a level before a path component | `with_level_inserted` |
| Merge two levels into one keyed by pairs | `with_levels_paired`, and `with_levels_unpaired` for a release handed back |

`Tile::map_level_predicates` applies one to every level of a chain, through record fields, and
`TileGuard::map_level_predicates` to every level a guard names. A group placed without
restating names paths under other rows, which the check in
[The completeness contract](#the-completeness-contract) reports as a change to a complete path.

### Boxes and prefixes

A `Record` and a `Qualified` predicate are both **boxes**: products of one predicate per
component, admitting a key when every component admits its part. A record's components are its
fields in name order, the order `Value`'s comparison takes them in; a qualified predicate's are
the enclosing path and the key. One algebra serves both (`BoxShape` in `tiling/predicate.rs`):

- A meet is componentwise.
- A join is one box where the two agree on every component but one, and an `Or` otherwise.
  `flatten_or` joins any two arms this way, so a region stated one row at a time stays one box
  per run of rows alike, not one arm per row.
- A difference is a staircase: step `i` keeps what component `i` alone leaves, over the
  components before it that the subtrahend holds and the components after it untouched.
- Containment is componentwise, which is exact for a nonempty box.

A **prefix** of a lexicographic order is a staircase of boxes: `≤ (𝑎, 𝑏)` is
`{_0 < 𝑎} ∪ {_0 = 𝑎, _1 ≤ 𝑏}`. `domain_prefix` builds one across levels, one qualified arm per
level, and `Predicate::at_or_below` builds one across a record key's fields. An interval is
never built over record values, so a record key has only the box algebra. A level keyed by a
nested loop's `(outer, inner)` pairs is released as a prefix, and a cartesian product's keys are
stated per field, because its factors grow independently; the two meet under the same rules as
any two boxes.

`subsumes` is exact. A union on the left may cover a box that no single arm covers, so where no
arm answers alone it asks whether `other ∖ self` is empty. Exactness rests on each region having
one spelling where the representation allows it: `Predicate::intervals` clamps a set to its
type's range, since the interval crate does not know that a `UInt` stops at 0 and would keep
`(-∞, 3]` and `[0, 3]` apart, and it returns `False` for an empty set and `True` for one
covering the type.

### Curry levels

A collection tiling is a curried data function `K₀ ⤇ K₁ ⤇ … ⤇ V`, held as one
`Tile::DataFunction` per level. `CurryLevel(n)` addresses the tile `n` levels in: `CurryLevel(0)`
is `K₀`, `CurryLevel(n)` is `Kₙ` grouped by the `n` levels above it, and
`CurryLevel(levels)` is the values every level stands over.

An operator acts at one level and leaves the levels above it standing. It states that level
once, at construction, and every level-addressed read goes through it — `values_at`,
`group_at`, `per_group`, `wrap_guard`. Destructuring a tile answers for the outermost level,
so a component that destructures instead of reading its own level reads `domain` and
`domain_predicate` at level 0 wherever any level stands above it.

**The level above is where the rows are.** A level's own `domain_predicate` says which of its
keys are complete; the rows an operator groups by, and their completeness, belong to
`CurryLevel::enclosing`. At depth two the enclosing level is the outermost one, so reading
the wrong one gives the same answer there and a different one at depth three and below.

**Completeness is downward-closed.** A key a level calls complete is complete at every depth
beneath it, so an element is final as soon as *some* level on its path calls that prefix
final. An operator that reduces one group per row — `MapAggregate` is the case — therefore
asks every level on the path rather than the outermost alone. Asking the outermost is sound
only while the statement says the same of every row: under a nested carrier the enclosing rows
stay open for as long as the drive runs, while the row being run is decided, so an aggregate
inside the nest would never settle.

Operators split into two families by what they replace at their level:

- **Replacing the values beneath it** — `Zip`, `VariantWrap`, `ExtractFinal`. Their
  tiling is `with_values_at(input, level, new_values)` and the producer writes
  `*values_at_mut(level)`. Nothing is grouped, so nothing is split per row. A member that
  *reads* the rows above it takes them from the level they sit at rather than from the top,
  because a standing level answers for every carrier beneath it and not for those rows.
- **Rebuilding the collection level itself** — `UnionOperator`, `Uncurry`, `Product`,
  `StoreDenseRead`. Each takes the level apart one row of the level above at a time and puts
  it back: `Tile::per_group`, which derives the empty level from the operator's own output
  tiling so a row that has been reached by nothing still answers at the right shape. Operands
  pulled from their own branches need not hold the same rows, nor hold them at the same
  positions, so an operator with several finds each row in the others by its path
  (`Tile::rows_by_path`). A union's standing rows are its arms' together, each arm holding its
  own share.

### CCL types vs. tilings

CCL types and tilings describe a term at two different layers, and the relationship is one of the things that makes the tile pipeline tick.

The CCL type layer is **pointwise**: `mul : (Int, Int) → Int`, `zip(f, g) : A → (B, C)`. A type describes an element-wise function — "given one input of type A, produce one output of type B." It says nothing about how many `A`s will arrive, in what order, or whether the result will be materialised as a single value or streamed.

The tile layer chooses **how the runtime materialises that pointwise function**. The same pointwise morphism can be compiled to either:

- **A scalar-tiled operator** — evaluate the function on a single input value. One `A` in, one `B` out. Used when the morphism sits at a scalar call site (e.g. a literal tuple fed into a multi-arg UDF).
- **A function-tiled operator** (`DataFunction`) — evaluate the function across a collection of inputs, essentially vectorising the pointwise definition. Used when the morphism sits downstream of an iteration or data source.

Both compiled forms satisfy the same CCL type; which one a specific call site gets is determined at op-conversion by the upstream `input`'s tiling, which flows in from whatever sits above the operator in the dataflow graph. This is what makes UDFs like `lambda x: x + 1` compile cleanly whether they're called once on a literal or mapped over a source — no duplication at the CCL level, the tile layer specialises automatically.

In practice this means tile operators need to be **tile-polymorphic in their inputs**: the same CCL-level combinator often needs two tile-level implementations, one per input tiling. The `MapResult` family handles this via `change_tiling_result`; a zip is handled by [`zip_arms_at`](./tile_operators/fan.rs), which builds [`Zip`] from function-tiled arms and [`MakeRecord`] from arms that all came out scalar, where there is no domain to share. New combinators should assume the same pattern: don't commit to one tiling when the upstream context picks it.

### A product value is a record of tiles

A `Tuple` or `Record` node whose extent is a record compiles to a `Tiling::Record`, each field
keeping the tiling its own term produced: a scalar field stays a scalar, and a collection field
stays the collection it was, with the domain it binds. `MakeRecord` assembles it and
[`SelectField`] reads one field back out. `build_product` in `operator_conversion.rs` chooses it
by the node's extent.

Keeping a field a tile is what lets it grow. A `Tile::DataFunction` merges by appending its
domain and unioning its domain predicate, which is a collection arriving in pieces. A collection
materialized into one cell merges as every `Tile::Scalar` does, by appending the column, so two
deliveries land as two cells: two tables where the program has one collection. The fields settle
at their own moments, so a release names one field at a time, and a settled scalar beside an
unsettled collection is released alone.

A `Tuple` or `Record` node whose extent is a function, `𝐷 ⤇ {…}`, is a collection of records.
`Tuple([acc, i])` under a binop is one: it pairs its components beneath the levels they were
applied over, which is what [`Zip`] assembles. Assembling a record extent as a zip instead yields
`𝐷 ⤇ (𝐴, 𝐵)`, a collection of products, where the type says a product of collections.

`SelectField` is a tile operation. The `RecordField` application is the other projection, and it
reads a record in a function's codomain one row at a time, so every field must be a value in a
column. A record holding a collection cannot supply one.

### A collection inside a value stays a tile

A collection inside a value is kept as a `Tile::DataFunction`: its keys in a column beneath the
rows that hold them, and its values in the tile below. A merge appends keys to it, and a guard
names them. Operators do not box it into a `Tile::Scalar` column of `Value::Function` maps, which
would arrive whole and be read only by opening each map. A map value is used only where one value
is required, as in a variant's payload and a store write.

`Tiling::from_extent` is the tiling a value of an extent takes in this form. `Tile::holds_a_level`,
and its static counterpart `Tiling::holds_a_level`, asks whether a tile holds a collection this
way; an operator putting a value into a column asks it, a column having nowhere to put one.
`Extent::holds_a_collection` asks whether a type contains a collection at all, which a column of
maps answers yes too. `open_collections` turns a column of maps into this form at every depth,
and `materialize_collections` turns this form back into maps where one value is required.

A pair an operator *forms* follows the same rule, and states it at construction. `Product`
pairs each row's element with the keys under it: where the element is a plain value the pair rides
materialized in one column, and where it carries a level — a nest whose elements are collections — the
pair is a `Tiling::Record` whose `_0` keeps its levels. `Uncurry` reads the rule from the other end:
it flattens two levels into a pair-keyed one and leaves the values it finds exactly as they are,
because materializing a level-carrying value is what has no column to go in.

**A variant's payload is the one place a collection rides as a value.** An arm holds one cell per
position, so `VariantWrap` materializes the collection into it (at the level the payload's own type
names, not the input's innermost) and `VariantProject` opens it back into levels. The round trip is
what carries a feed out of a nest: the enclosing decision's tap holds the inner loop's whole tap
collection, materialized on the way in and opened on the way out, and the channel flattens the two
levels to the positions the feed appended at.

---

## The release contract

`release(𝑅)` says the data in 𝑅 is **never requested again, and never returned again** — the same promise from each end of the wire. It holds at every granularity: a consumed prefix, one arm of a union, a record field, or the whole tiling (the *universal* release, after which the only conforming tile is the empty one). This is what makes bounded execution possible — a producer may reclaim 𝑅, and every tile it emits afterwards lies outside its accumulated obsolete guard.

Every operator must obey it in both directions, because a violation yields **wrong results rather than an error**. A producer that returns released data hands its consumer values that consumer already took delivery of; a `Tile::Scalar`'s positions are implicit, so `merge` cannot tell "this position again" from "one more position" and appends, and one value silently becomes two, surfacing wherever it is later broadcast. An operator that fails to forward a release it could make strands upstream state instead — `FanOut` forwards the *intersection* of its branches' guards, so one branch that swallows a release blocks reclamation for all of them.

`TileProducer::get` checks the producer's half in debug builds: the returned tile must carry no live data inside the accumulated `obsolete_guard`. What an operator can forward depends on how it reads its input, so it is specified per operator below.

An operator must therefore **reject a guard it cannot honor rather than ignore it**. The guard accumulates in `obsolete_guard` whether or not `release_impl` acts on it, so dropping one silently leaves the operator free to re-emit that region — from its own state, or by re-reading an input it never passed the release to. Every `release_impl` is exhaustive; an operator with no sub-region to reclaim piecewise checks the guard with `TileGuard::expect_universal_or_empty`. Rejecting fires where the guard arrives, which does not depend on anything pulling afterwards — the `get` post-condition only fires if something does.

A keyless field's cell beneath a level goes with its key. A record tile's fields stand over
the same rows, so a tile cannot hold a row without its cell. A release naming the cell under an
open key is recorded, and the producer returns the cell until the key is released
(`Tile::remove_guarded`). No consumer can have dropped the cell while it holds the row, so
the value it receives again is one it already has, matched by key.

### Guard operations are exact

`TileGuard::intersect`, `TileGuard::union`, `TileGuard::flatten_or`, and every function that
restates a guard for another operator's tiling name exactly the region they denote. A region the
representation cannot spell is a gap in the guard algebra. The fix is a spelling for it, and until
then the operation fails loudly (`todo!`, `unimplemented!`). It never answers a smaller region,
and never a larger one.

A consumer may release less than it has finished with, since what it releases is its own promise.
An operator computing a guard from the guards it received has no such choice:

- An understated guard fails to forward a release the operator could make, which strands upstream
  state. A `FanOut` forwards the meet of its branches, so one understated meet blocks
  reclamation for every branch.
- An overstated guard releases data a reader still needs, which yields wrong results.
- Either one is a different region from then on. `TileProducer::release` compares the spelling of
  the accumulated guard to decide whether a release added anything, and every later union and
  meet is computed from that spelling.

## The completeness contract

A level's `domain_predicate` is its **statement** of completeness: it names the paths reaching
that level that are **complete**. A complete path keeps its keys and values from then on and
stays complete. The statement covers every path at its level, including paths under rows that
have not arrived, and a path is complete at every depth beneath a level that calls it complete
([Curry levels](#curry-levels)), so a statement about some rows only names them
([Qualified predicates](#qualified-predicates)).

A release is the only way a complete path's content leaves an output: a producer may drop what
was released, and may stop stating it complete. Nothing is added beneath a complete path,
released or not. A consumer that needs a statement after releasing the region it covers keeps
the statement itself.

`TileProducer::get` checks this in debug builds against the producer's previous output
(`assert_complete_region_unchanged`):

1. every region the last output called complete, less what was released, the new one still
   calls complete;
2. every key and value the last output held beneath a complete path, the new one holds
   unchanged or has dropped because it was released, and it holds nothing beneath a complete
   path that the last output did not.

A violation panics and names the producer tree.

Where an output path's content comes from several inputs, the arms of a `Zip` or a union or the
two sides of a pairing, the path is complete only where every input calls it complete, so the
operator intersects their statements. A union arm
released whole stands in as an empty tile stating `True`, which constrains nothing.

## The notification contract

A producer whose output changes on a pull wakes its consumer. The change is made inside a
`get`, while the producers that must re-pull are still on the stack, so the wake is queued
(`WakeupQueue`) and delivered after the pull returns (`Scheduler::check_for_notifications`). A
`Memo` answers from its cache until notified, so without the wake it keeps the old output, and
a program waiting on it stalls without an error.

- A store's output changes when it opens, decides a position or commits, and closes.
  `ChangeNotifier` compares each pull's output with the last and wakes the store's readers
  when they differ.
- A `Memo` pulled without a notification, its cache still empty or a drained input a debug
  build still probes, wakes its consumer when the pull finds data the cache did not hold.

The contract makes a stuck program observable. A program is **quiescent** when a lap delivers no
notification and answers what the lap before did: every operator then sees what it saw, so
nothing moves until an input changes, and `pull_laps` stops there.

## Tile Operators

Each `TileOperator` is a static (compile-time) node in the dataflow graph. It knows its output
[`Tiling`] and can instantiate a live `TileProducer` via `subscribe`. Operators are constructed
during compilation; producers are created on demand at runtime.

### Operator identity and the graph the inspector reads

Every operator carries an `OperatorBase`, holding a `NodeId` minted at construction and the output
tiling. The id is drawn from the same counter as an expression node's, which is what lets a
provenance row resolve an operator against the expression it came from
(`src/ccl/design/provenance.md`, "Operator conversion").

`OperatorGraph` is the static graph of one compiled program, and it is the content of the
`post-conversion` pane. It is built by walking the operators from the program's outputs, not
recorded while they are constructed. The walk runs in `compile_program` between conversion and the
subscribe loop, which is the only window where it is total: `subscribe` takes every `CycleSlot` and
every store's keyed inputs, so an operator asked for its inputs afterwards answers without them.

`TileOperator::visit_inputs` is the single statement of what an operator holds, and it has two
readers: the graph walk, and `TileOperator::inspect`, which renders an operator's children from the
same answer rather than from a second hand-written list. An input stated nowhere is an edge the pane
does not have, and — when it is the only path to a subtree — a subtree the pane loses, so the method
is required rather than defaulted. It is a visitor rather than a returned list because two inputs
sit behind a `RefCell`: a fan branch's input and a `CycleSlot`'s contents both borrow for the extent
of the call. What an operator adds beyond its inputs — a constant's value, a variant arm's tag —
is `inspect_annotation`, so the two questions stay apart.

`inspect` follows `Value` edges only. A `Share` edge would draw the shared subtree once per branch,
and restricting to `Value` is also what makes the recursion terminate without a cycle guard, since
those edges are acyclic.

An edge is a **subscription**: the consumer holds the operator the edge names and calls `get` on it.
`notify` runs the other way along the same edges. Three properties ride each edge:

- **Kind.** `Value` for an exclusively owned `Box`, `Share` for a node several consumers may reach:
  a fan branch's edge to its fan input. The value edges form a forest, which is what lets a renderer
  follow them with no cycle guard.
- **`deferred`.** Set on a `Value` edge wired through a `CycleSlot` after its consumer was built.
  This is a property of the field rather than of the run: a slot is the only way an operator
  receives an input its constructor did not give it, so every slot-held input is deferred and no
  other input is. Removing the deferred edges makes every graph acyclic, which is what a layout
  cuts.
- **Role.** A field name, a position in a `Vec`, or a store key. The three stay distinct on the
  wire, because a field named `0` and the first element of a `Vec` render alike.

**What the walk cannot produce.** A sink is a graph node and not an operator, so it has no identity
a walk could read off an operator. Conversion records sink identity alone (`record_sink`), and
everything else about the graph comes from the walk: every operator, and every edge including the
edge into a sink.

**A data source is not a node.** Two operators read a source: an `IterateExtent` over its domain,
which the scheduler wakes when the source produces, and a `MapResultWithSource`, which looks up
values at the keys its `input` carries. That input descends from an `IterateExtent` over the same
source, because inference admits no literal of a `source(name)` type and iteration is the only
origin of such a key. The `IterateExtent` holds no input and its tiling names the source, so it is
where a path from the source starts. Neither operator states an edge for its read of the source.
`tests/inspector_goldens.rs` pins the descent (`a_source_read_descends_from_an_iteration_of_that_source`).

**Serialization.** `src/inspector_model/design.md`, "A node on the wire" owns the payload shape. An
operator node ships its label, its tiling, and its `inputs`; a boundary node ships no tiling,
because only an operator has one. Where a walk of the pane begins is derived on both sides of the
wire from the edges rather than shipped, so no second channel can disagree with them.

| Operator | Input Tiling(s) | Output Tiling | Description |
|---|---|---|---|
| `Constant` | None | `Scalar` from `Constant::new`, `DataFunction(domain → Scalar(codomain))` from `Constant::from_bindings`, any tiling from `Constant::collection` | Produces a fixed tile. Which of the two a bindings table is cannot be read off the value: in function position it is one value the consumer applies (a list literal's table), and as a collection it is what a map iterates. Every operator below derives its tiling from its input's, so the choice decides whether a map transforms the table or each of its outputs — and the call site states it. |
| `IterateExtent` | None | `DataFunction(extent → Scalar(extent))` | Enumerates all values in an `Extent`, producing an identity-mapping function (domain = codomain = extent). Holds no input, so it is the root a data source is read from: it registers a wake-up against each source its extent reaches (`Extent::for_each_source`), and its tiling names them. |
| `MapResultWithSource` | `DataFunction(DataSourceDomain → Scalar(DataSourceDomain))` | `DataFunction(DataSourceDomain → Scalar)` | Looks up each key of a data-source domain via `DataSourceDomainExtentImpl::get` to produce a function from keys to their output values. |
| `Zip` | `N` inputs of `DataFunction(shared_extent → *)` tilings |  `DataFunction(shared_domain → Record(_0, … _N))` | Merges N function operators that share a domain into one function whose codomain is a Record Tiling of all their codomains. Prefer the free `zip_arms_at` factory at op-conversion call sites: it dispatches to `Zip` (function-tiled arms) or `MakeRecord` (scalar arms) based on the compiled arms' tilings, since the same CCL-level `zip` maps to either tile shape depending on upstream `input`. |
| `MakeRecord` | `N` inputs at any tilings | `Record(name: input's own tiling, …)` | Builds a product value ([A product value is a record of tiles](#a-product-value-is-a-record-of-tiles)). Pulls every operand whole, and forwards each field's release to that field's operand. |
| `MapResult` | Function: any tiling of type `A → B`<br>Data: any tiling whose deepest codomain is `Scalar(A)` | The data's levels, then the function's below the one applied, over the function's codomain | Applies a function to the data's **deepest codomain**, element-wise. Application consumes the function's outermost level, and whatever sits below that level becomes further levels of the output, because a tile holds one flat level list. So a one-level function leaves the data's shape alone and changes only its deepest codomain, while the two-level lookup a keyed collection presents contributes its inner level: a collection of keys yields one group per key, and a `Scalar` key yields just that key's group — the single-key lookup `groupby(c, k)(v)`, one level shallower because the scalar contributes none of its own. A key absent from a *settled* grouping is the empty group; absent from an unsettled one it is simply not answered yet, which the function's `domain_predicate` distinguishes. A row whose key the function has not answered is **withheld** — dropped from the output, and its outermost-level owner subtracted from the output's `domain_predicate` — and answered on a later pull. The **data** input tracks the consumer's release; the **function** operand is re-read whole on every pull, so it is released only on a universal release. |
| `MapResultToConst` | `DataFunction(extent → *)` | `DataFunction(extent → C)`, `C` the constant's tiling | Replaces every codomain value of a function input with the same constant (or zips it in, per its mode), preserving the domain. A collection constant is one row, and each element gets a copy of its group (`repeat_tile`). The constant must be present (terminal) before it can be broadcast — a still-absent constant (e.g. a scalar read from a sibling induction loop that has not yet converged) yields an empty, non-terminal output rather than fabricating a value for the unknown positions. |
| `ToScalar` | `DataFunction(Unit → Scalar)` | `Scalar` | Unwraps a `DataFunction` with `domain = Units(1)`, extracting and returning its single codomain element as a scalar tile. |
| `SelectField` | `Record{name: T, …}` | `T` | Hands back one field's tile, the eliminator for `MakeRecord`. Pulls the product whole, and releases what its consumer released of the field it selects and every other field whole (`guard_at_field`). |
| `Converse` | `DataFunction(domain → Scalar(codomain))` | `DataFunction(codomain → domain)` | Inverts a function operator: each codomain value maps to the list of domain values that produced it. |
| `Uncurry` | `A ⤇ B ⤇ C` | `{_0: A, _1: B} ⤇ C` | Flattens a collection of collections into one keyed by pairs: the two key extents pack into a record key and the values stand as they were. |
| `MapDomain` | `DataFunction(A → *)` | `DataFunction(A → Scalar(A))` | Replaces the codomain of a function with a copy of the domain values (identity codomain), producing an identity mapping from domain to itself. |
| `Filter` | Predicate: any tiling of type `A → bool` <br>Data: `DataFunction(extent → Scalar(A))` | Same as input | Filters a function tile by a boolean predicate: keeps only domain elements where the predicate on the value evaluates to `true`. <br>TODO can probably remove this in favor of Restrict |
| `Restrict` | Predicate: any tiling of type `A → bool` <br>Data: `DataFunction(A → *)` | Same as input | Filters a function tile by a boolean predicate: keeps only domain elements whose predicate evaluates to `true`. |
| `MapFilter` | Predicate: `K ⤇ I ⤇ bool` <br>Data: `K ⤇ I ⤇ V` | Same as input | Filters the **inner** collections one outer key at a time — the survivors differ per key, which `Filter` and `Restrict` cannot express because they narrow a collection's own keys. The predicate's innermost values are the mask over the inner keys directly, so the outer level is untouched and `Tile::retain_keys` re-cuts the inner runs. Planning emits it where a refinement rides an inner collection's keys under the outer key's binder, which is what a per-group filter (`sum([s.amount for s in g if s.qty > 2])`) produces. |
| `Aggregate` | `DataFunction(* → Scalar)` | `Aggregation` | Reduces all codomain values of a `DataFunction` input into a single running accumulator via an `AggregateKind` (e.g. Sum, Max). Currently, the aggregation is hardcoded in the graph, but we could add support for aggregate-kinds-as-data |
| `ExtractAggregate` | `Aggregation` | `Scalar` | Extracts the final value from an `Aggregation` tile. Constructed with an `only_terminal` flag: when `true` it emits only once the aggregation is marked terminal (the `only_terminal: false` path is currently `todo!()`). |
| `MapAggregate` | `DataFunction(domain → codomain)` | `DataFunction(domain → Aggregation)` | Performs a per-key aggregation |
| `MapExtractAggregate` | `DataFunction(extent → Aggregation)` | `DataFunction(extent → Scalar)` | Extracts terminal per-key aggregation results from a `DataFunction(D, Aggregation)`, producing `DataFunction(D, Scalar)`. |
| `FanOut` | `*` | Same as input | Allows multiple operators to consume the output of the same operator. Each consumer subscribes via a `FanOut::branch()` handle; the fan-out forwards `get` requests and tracks the intersection of release guards across branches. Constructed via either `FanOut::new` (no cyclic-mode overhead — the common case) or `FanOut::new_cyclic` (for fan-outs whose branches feed back into their own input, e.g. a commit/induction store whose writer reads the store back before proposing, or a mutation-loop body whose other branch is wired to the cyclic prev-accumulator stream). Cyclic mode adds a per-pull tile-cache and a subscribe-in-progress flag so re-entrant subscribes / pulls skip redundant inner work and serve from the cached snapshot instead of re-entering the inner producer. |
| `Memo` | `*` | Same as input | Caches the output of an operator so it can be repeatedly read without recomputation. Releases each region as it takes delivery of it, so the input can clear its state; once the input is drained the cache is the sole source of the value. Only release builds then skip the upstream pull — a `Memo` sits above most scalar producers, so short-circuiting in debug would shield every one of them from the release-contract check. A `Memo` is also the one operator wired to `Notified`: while its input has not notified it and its cache is non-empty, the cache is the answer and no pull goes below, in every build. A drained input is exempt, which is what leaves the debug probe above intact. |
| `ExtractFinal` | two inputs: `source`, a collection per row of `rows` levels (`DataFunction(D → Scalar(T))` with none), and `default`, one value per row (`Scalar(T')` with none, for any `T'` that `T` includes); `default` is absent for a source declared total | the default's rows over `Scalar(T)`; `Scalar(T)` with no rows | The value at each collection's highest position once the source closes it, or the row's `default` where the collection holds no position — which keeps post-loop accumulators total when the loop ran nothing. Every emission is built at the **declared** extent `T`, not from the extracted value alone: a variant value carries only its own tag, so a column built from it would be width-narrower than `T` whenever the collapsed alternatives carry more tags between them — which is also why the `default` need only be *included in* `T` rather than equal to it (a conditional's trailing arm carries its tag and not its siblings'). See [*`ExtractFinal` reduces at any depth*](#extractfinal-reduces-at-any-depth) for rows, completion and release. |
| `UnionOperator` | N inputs of `DataFunction(dᵢ → Scalar(C))` tilings | `DataFunction(Union(d₀,…,dₙ₋₁) → Scalar(C'))` | Merges N function operators into one by forming the discriminated union of their domains, over a codomain the **caller declares**. The domain keeps every arm apart — which arm a row came from is what `final_or_default` dispatches on. The codomain does the opposite: the arms are alternative values at one row, so it is their **join** — and that join already exists. A union node is typed `D ⤇ V` with `V` the arms' join as inference computed it, in the full type lattice; op-conversion reads `V` off the node and passes its extent in. Re-deriving it from the operand tilings meant a second join in `Extent`'s lattice, which has variant and range rules but **no record rule**, so two arms at different record widths came out as an anonymous positional sum where the type layer said `{a: Int}` — a shape no row holds and nothing downstream can project. Arms that *do* agree on a tiling keep it verbatim, since a `Tiling` carries a layout (struct-of-arrays for a record) that an `Extent` cannot express; that is the one thing still read off the operands. Release is per arm: an incoming `Predicate::Union` guard splits into per-variant predicates, so one arm can be released in full while its siblings still produce. |
| `VariantWrap` | Payload: `Scalar(Pₜ)` or `DataFunction(D → Scalar(Pₜ))` | `Scalar(Union(P₀,…,Pₙ))` or `DataFunction(D → Scalar(Union))` | **Sum introduction — dual of `VariantProject`.** Wraps the payload under tag `tag`, so that arm holds the payload and every other arm is empty. Arms are keyed by [`FieldKey`], not by position: a tag's *position* is not stable under width subtyping (``{`b} <: {`a | `b}`` renumbers `b`), and an arm set is part of a union column's layout, so a position-keyed arm would need a renumbering coercion at every subsumption. A bare `Scalar` payload (a scalar `VariantCtor`) yields `Scalar(Union)`; a payload *stream* (a `VariantCtor` inside a lambda, `Builtin::VariantWrap(tag)`) is wrapped element-wise **preserving the domain** `D`, so the constructor composes as the RHS of a `≫`. Because the domain is preserved, a domain release forwards to the payload verbatim. |
| `VariantProject` | Scrutinee: `Scalar(Union(P₀,…,Pₙ))` or `DataFunction(D → Scalar(Union))` | `DataFunction(UInt → Scalar(Pᵢ))` for a bare scrutinee (implicit `0..N` keys), or `DataFunction(D → Scalar(Pᵢ))` for a stream scrutinee (the real `D` keys preserved) | **Sum elimination — the read-dual of `VariantWrap`.** Projects the arm named `tag` out of a tagged-union stream, *restricting to the sub-domain of rows carrying that tag* and yielding that arm's payload column, keyed by the original `UInt` position. A tag the scrutinee does not carry yields an **empty** projection rather than an error — that is what makes a width-subtype scrutinee, and so a `match` arm the scrutinee can never reach, inert instead of ill-formed. **Restrict and project are one op**: a [`UnionArm`] stores its rows alongside its payloads, so reading the arm *is* the tag restriction — there is no separate boolean `Restrict` step and no tag-discriminating `Predicate` (a domain-`Restrict` could not express it: the tag lives in the scrutinee's codomain, not its domain). Emitted by `lambda_elim` for a scrutinee-`Case`; consumed as a bare `Builtin::VariantProject(tag)` composed onto the fed scrutinee. |

**Pointwise `FunctionDef`s** (applied element-wise via `MapResult(input, Constant(FunctionDef))`, not standalone operators): `BinOp(op)` over a `{_0, _1}` record column, `UnaryOp(op)` over one column, and `RecordField(f)` projecting a field.

**Value-selecting `Case` in a writer decision body** (a conditional induction write `if 𝑝: acc += a else: acc += b`, or a `with begin():` per-key routing merge — a gate that varies with the element at a site with **no visible iteration source**). `lambda_elim` compiles it to the same **union of domain-restricts** as every other value-`Case`, over the *fed* element stream: `⧺ᵢ (filter_values(π̂ᵢ) ≫ eᵢ)`, first-match `π̂ᵢ`. `filter_values` (`Builtin::FilterValues` → the `Filter` tile operator, input stream + predicate) is a **value-preserving** filter — unlike `Restrict` (which returns the domain identity `{D|p}⤇{D|p}` for a source a map re-indexes), it keeps each surviving element's value `V`, so `eᵢ` maps the kept elements directly and a **partial op** (`//`) in `eᵢ` runs only where its guard holds — never eagerly at a rejected position (the retired `Select` computed both arms and faulted on the off-path one). The arms filter the *same* fed stream disjointly (first-match), so their union is a **flat merge** (`UnionOperator::new_flat`): it stays on one domain extent (not a tagged `Extent::Union`) and reassembles the full column sorted by domain key, co-iterating with the decision record's sibling `commit`/`writes` fields. The key is the arm's domain *value*, not a position: reassembly needs only a total order (to restore the fed order) and equality (to catch two arms claiming one key), and both hold for any single collection's keys, since its domain is one `Extent`. A `UInt` position is the common case; a fed stream whose own index set is a coproduct — a conditional-element comprehension, whose `Copair` domain is `Variant({Index(i): {D | π̂ᵢ}})` — carries `Union { tag, inner }` keys, which `Value`'s order compares lexicographically by tag then payload. Keys that are *not* mutually comparable mean the arms were fed different domains, which is a copairing rather than a disjoint join, and `flat_merge` says so. A sourceless value-`Case` (a top-level ternary) still takes the `UIntRange(1)`-driver C-form + `final_or_default` (a tagged union dispatch); the writer-body case differs only in filtering the fed stream rather than a synthetic driver.

**Scrutinee-`Case` over a variant** (`λ 𝑥 → match 𝑥 { 𝑐ᵢ(𝑤ᵢ) → 𝑒ᵢ }` — sum elimination, the read-dual of `VariantCtor`). `lambda_elim` compiles it to the same **union of restricts** as the value-`Case`, keyed on **tag** rather than a boolean first-match gate: `⧺ᵢ (𝑥 ≫ variant_project(𝑐ᵢ) ≫ (λ 𝑤ᵢ → 𝑒ᵢ))` — a `≫`-chain, because every element of it is a morphism out of the eliminated binder: the scrutinee is `𝑥 ⇒ scrut_ty`, `variant_project(𝑐ᵢ)` is `scrut_ty ⇒ Pᵢ`, and the eliminated arm body is `Pᵢ ⇒ V`. `variant_project(𝑐ᵢ)` (`Builtin::VariantProject(tag)` → the `VariantProject` tile op) fuses the tag-restrict and the payload projection into one step (an arm stores its own rows — see the operator table). The tags **partition** the scrutinee's domain, so the arms' sub-domains are disjoint and the union is a **flat merge** (`UnionOperator::new_flat`), re-totaling to the full domain — exhaustive by typing (inference's width-subtyping demands one arm per scrutinee tag), so no `final_or_default` scalar collapse is needed (this is the fan-out shape, not the C-form). A const arm (`abort → 0`, ignoring its payload) keeps its `variant_project` through simplification: `try_const_reduce` refuses to collapse past either element that *narrows the domain at runtime with no refinement left to re-materialise* (`simplify`'s `narrows_domain_irrecoverably` — `variant_project` and `filter_values`), since dropping one would apply the constant at every position and make the arms overlap. **Outer-binder arms.** When an arm body reads the *outer* binder as well as its payload (`𝑒ᵢ(𝑥, 𝑤ᵢ)` — e.g. a per-key view `λ __c → match __c.decision { commit(w) → (time: __c.time, write: w.i) }`, reading both the record's sibling field and the commit payload), the arm zips the whole element alongside the projected payload: `⧺ᵢ (⟨id, 𝑥.f ≫ variant_project(𝑐ᵢ)⟩ ▷ zip ≫ (λ (𝑥, 𝑤ᵢ) → 𝑒ᵢ))`. Both components of the pair are morphisms out of the *outer* binder, which is why `id` sits beside the projection chain rather than inside it — `𝑥.f ≫ ⟨id, variant_project(𝑐ᵢ)⟩` would pair the *scrutinee* with the payload, not the element the arm body reads its sibling fields off. For this, `VariantProject` keeps the scrutinee's **real domain keys** (a union *stream* `DataFunction { D ⇒ Scalar(Union) }` carries them explicitly, unlike a bare `Scalar(Union)` whose implicit `0..N` positions become the keys), so the outer `id` arm and the tag-restricted payload co-iterate by key under the `zip`/`Zip`, which inner-joins on shared keys — the outer arm need not be pre-restricted (the join drops the positions not carrying `𝑐ᵢ`). lambda_elim detects the outer-binder dependence structurally (the arm body has `𝑥` free beyond the payload binder) and merges the two into one pair binder (`𝑥 ↦ pair.0`, `𝑤ᵢ ↦ pair.1`); the payload-only path is unchanged. A scalar one-off `match` on a concrete value (rather than a per-element `λ x → match x`) would need the C-form scalar collapse; not built until a term needs it.

**`VariantCtor` inside a lambda body** (sum *introduction*, the dual of the scrutinee-`Case`). A `VariantCtor` in a lambda (``λ 𝑝 → `𝑐ᵢ(𝑒ᵢ(𝑝))``) must elaborate to a composable morphism `param_ty ⇒ Union` so it can be the RHS of a `≫` — e.g. a writer-decision arm ``filter_values(π̂ᵢ) ≫ 𝑒ᵢ ≫ variant_wrap(`commit)`` in the value-`Case` fan-out `⧺ᵢ (filter_values(π̂ᵢ) ≫ 𝑒ᵢ)`. `lambda_elim` compiles it to `𝑒ᵢ ≫ variant_wrap(𝑐ᵢ)` (`Builtin::VariantWrap(tag)` → the `VariantWrap` tile, fed the payload stream, wrapping it element-wise). The full arm set resolves from the node's `Type::Variant` codomain, mirroring `variant_project`. A `VariantCtor` whose payload is *constant* in the binder never reaches this arm — the `const` rule lifts the whole scalar variant with ``const(`𝑐ᵢ(…))``, which `MapResultToConst` broadcasts over the stream (`ColumnValue::repeat` handles a singleton `Union`). A genuinely scalar `VariantCtor` outside any lambda keeps its own node and its `expect_no_input` op-conversion arm (`Scalar(Union)`).

---

### `ExtractFinal` reduces at any depth

`ExtractFinal` reduces each collection its source holds to the value at its highest position,
or to a default where the collection holds none. It takes `rows`, the number of collection
levels standing above the reductions, and that number is the only thing that varies with
depth. With none it is one reduction over the whole source; with one or more it is a
reduction per row of the innermost. Three constructors build it:

- `ExtractFinal::new` is `final_or_default(stream, default)` over a stream, with no rows.
- `ExtractFinal::without_default` is the same over a source declared total, a tag partition
  that always covers exactly one position, so no default is invented.
- `ExtractFinal::per_row` is a nested loop's trailing read: the inner accumulator's history
  per enclosing row, falling back to the seed that row began with.

A `mut` loop's own trailing read is not among them. With no rows above it, that read is a
`StoreFinalRead` (see [Reads](#reads)).

#### A per-row reduction takes its rows from its default

The rows a per-row reduction answers are the default's, not the source's. A nested carrier's
history is sparse over them: a row whose inner loop ran no position has no group in the source
at all, because the store opens a row when it decides a position there. The default holds one
value per row by construction, being a morphism of the enclosing writer's parameter, and that
value is the row's answer. Pairing source and default into one collection first would lose
those rows, since `Zip` keeps only the rows both operands hold. Op-conversion therefore builds
the operator from the two legs of the `⟨source, default⟩ ▷ zip ≫ final_or_default` chain
rather than from the zip.

A row is answerable where the source has closed its group. The output's predicate at the rows
level is the default's met with the source's closure, widened by the rows already answered, so
the output never calls a row complete that the operator is not answering. The source's
statement leads that union because only it can say `True`: an enumeration of answered rows
never can, and a consumer waiting for the whole collection to close would wait forever on one.

A row's final is computed when its group closes and held until the operator's own consumer
releases the row. That release is also when the operator releases the row of its source, so
the held answer is never consulted after the source lets the row go.

#### What differs at depth zero

Three statements read differently at depth zero, and the operator states each rather than
branching on shape:

- **A group is closed** where the level above it says so. With rows, that is the innermost row
  level naming the row's key. With none there is no key to ask about, and the statement is the
  source's own terminality: a source over a tagged union domain is terminal with a `Union`
  predicate admitting every arm, and asking that predicate about the empty path answers no.
- **The rows are the default's** with rows above; with none there is one reduction, at the
  path that names the tile.
- **The default is pulled where it is needed.** With rows it is the row set, so every pull
  needs it. With none it is the fallback for a source that ran nothing, and pulling it before
  that is known would drive an input the reduction may never read.

A reduction with no rows retires on a universal release, releasing both inputs. Once it has
answered it releases its source in full, and before that it releases the source below the
highest position seen, since only the last one is wanted.

## The commit operator (`interpreter/commit_operator.rs`)

The transaction engine that backs a `Type::Txn` [`Transact`](../ccl/design/ir.md#transact--the-domain-parameterized-recurrence-carrier) store: concurrent writers propose transactions against a shared multi-key mutable variable, and the operator serializes them onto one monotonic commit-time clock with optimistic-concurrency validation (allocate-on-commit + backward validation + serialize-and-retry). Op-conversion's `build_commit_store` assembles it. The design splits into a **pure engine** and its **tile adapters**:

- **`CommitEngine`** (tile-free, unit-tested) — the serialization logic. The store is `Position ⇀ {key: value}`, held as one changelog per key. `attempt(proposal)` allocates the next tick and commits iff no read key was overwritten after the proposal's snapshot (else `Stale`, and the writer retries at the advanced watermark). `read_as_of(t, key)` folds the delta history.
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
- **`StoreFinalRead` / `StoreFinalReadProducer`** — the **settled read** of a store key: `Scalar(V)`, the key's carried value at the position its own writers finish, or the store's seed if nothing wrote it. Two terms reduce to it, differing in what mints them rather than in what they sample: a surface `await_final` on a `Txn` key, and `final_or_default` over an induction accumulator's own history. It samples through the same `store_current` as `AsOf` and differs only in what fixes the position — a trigger's arrival there, the store's closure here — so it is neither a reduction nor a projection of the history, and needs no seed operand. Empty (and so non-terminal) until the store reports the key settled — `closed_keys.contains(key) || terminal`, so it settles once every writer that can write the key has drained rather than waiting on a store-mate's. A universal release retires it and releases the store branch; other readers hold their own guards through the fan, which the fan intersects, so the store still reclaims a version only once all of them have released it.
- **`StoreValueStream` / `StoreValueStreamProducer`** — projects one key's commit-value stream, commit time ⇀ `V`, out of the store changelog, carrying the value forward across ticks that wrote other keys (the step interpolation), so its own output is a `DataFunction` with a decided value at every tick. It backs the in-block reply tap (`carry_forward: false` — one entry per committed transaction) and the read-your-writes mutable variable carry (`carry_forward: true`).
- **`AsOf` / `AsOfProducer`** — the **as-of (temporal) join**, the cross-endpoint read. Given a `trigger` stream (the positions to sample at, e.g. an HTTP request stream) and the store, it latches the store's current value for each trigger position the first time that position is observed — indexed by the *trigger*, not the commit clock. Reading several mutable variables latches them all from one store render, so a multi-variable read is one snapshot. The dual of the changelog store's own driver: the store latches a private accumulator per *source* step, `AsOf` latches the store per *trigger* step.

A single-writer induction store is the degenerate no-conflict case of this same contract, which is why one `Transact` carrier serves both engines.

### The store is a changelog, not a function

`CommitOperator`'s output is a [`Tile::Store`], not a `DataFunction`: each key carries only the ticks
that wrote it, and a tick absent from a key's changelog is **decided-absent** — its value holds from
the latest earlier change. Consumers must therefore **fold** the store (`store_current` /
`store_value_at`), never index it. That is what makes a mutable variable readable while its store is
still live: the current value is defined at the decided frontier, with no need for the history to
end. Terminality is a flag separate from the frontier watermark, so a terminal store with trailing
carries is not undercounted.

### One changelog per key

A `Tile::Store` holds a record with one field per store key — a mutable variable or a reply tap —
and each field is that key's changelog, `Txn ⇀ V`. A tick whose write set names several keys is one
tick in each of their changelogs, so a write set spanning different keys at different ticks is which
changelogs hold a tick rather than an encoding of its own.

The key space comes from the tiling, which names every key statically, so a key nothing has written
is present with an empty changelog. Two consequences follow. A key carries its own value tiling,
where one shared codomain could only name the union of what the keys hold. And two renders of one
store carry the same fields, which is what lets `merge` append them field by field.

A proposal's `reads` and `writes` still ride one `map_to_value` cell each. Their key sets are
as static as the store's — a decision writes every carry key of the store consuming it, and a
read set names every key its writer reads — so the cell is the representation they have rather
than one their shape requires.

### The decision record

A writer body returns one **decision variant** per transaction, `` {`commit{𝑃} | `abort} `` (`ccl_utils::wrap_decision_variant`). `` `commit `` carries the payload record 𝑃 = `{writes, __to_<defer>*}` — the proposed new values keyed by the variable each is for, plus one field per reply tap — and `` `abort `` is the nullary whole-transaction deny: carry, no proposal. Making the grant/deny the *tag* rather than a `commit` field leaves "denied yet real writes" unrepresentable. `body_decision_at` decodes the tag by name, so the two ends agree without a canonical arm position. A tap's value is `` {`fired{𝑉} | `idle} `` — the fed value on the positions its own control-flow path admits, `` `idle `` on the rest (see [mutability.md](../ccl/design/mutability.md#general-in-transaction-conditionals-and-conditional-writes), "General in-transaction conditionals (and conditional writes)"). The grant path omits an `` `idle `` tap from the commit delta, so a routed reply fires only on its own route. A tap whose path *is* the commit — a single-guard or spine feed — wraps unconditionally. Carrying the gate as the value's tag is what lets a fed value be domain-restricted: a value beside a separate `Bool` gate would have to answer wherever the record commits.

### Convergence: the writer re-arms, one step per pull

A writer processes **one source item per pull** and re-arms itself on the scheduler's deferred-wakeup queue whenever an item remains, returning non-terminal — the same one-step-per-pull idiom the induction and commit stores share. That single re-arm covers every continuation uniformly: a **commit** (the commit-ack `release` advances it, so the next pull takes the next item), a **deny** (it advances locally with no commit — invisible in the store frontier, which a frontier-growth signal alone would miss), and a **not-ready** decision (it does not advance, and reuses the pending body-input row). It is the *writer's* re-arm, not any reader's, that converges the store: the wakeup fans through the cyclic `FanOut` to re-pull the `AsOf` / `StoreValueStream` readers as commits land, so no reader drives a store to fixpoint. A writer **drained but live** does not re-arm, so an idle live server does not busy-poll — a future arrival wakes it through its source-forwarding consumer.

### Every fed-out mutable variable read is an as-of sample

A mutable variable read **fed out** of its `with begin():` block compiles to `AsOf` (born in `transact_phase::rewrite_as_of_reads`, from the `as_of_read` term the read is minted as) — a sample at an **arbitrary** position in the commit order — whatever the reading trigger's domain: a live `DataSource` request stream, a finite loop, or a standalone read's synthesized singleton. A bare read *outside* a block never reaches here: lowering rejects it (`lower_expr`'s read gate). There is no static finiteness classification anywhere on this path; the read folds to `AsOf` purely because its history domain is `Type::Txn`. Every trigger position latches at its own arrival, uniformly — a finite trigger has no special timing, so a read of a store still committing reports whatever it has committed, commonly the seed. `AsOf` stays non-terminal until the store is terminal *and* every live trigger position is latched, so it cannot report "done" while a store no other consumer drives is still committing.

The **terminal** read is a different term, not a different classification of this one: `await_final(x)` (see `src/ccl/design/mutability.md`, "`await_final`") is a `StoreFinalRead`, the same sample of the same key through the same `store_current` — what differs is what fixes the position, a trigger's arrival here and the key's own closure there. The two are distinct terms all the way down from the surface — `as_of_read` and `final_read` — so which read a program gets never depends on the shape of the tree around it.

### Bounding a long-lived store

Three release paths keep a store that never ends from growing without bound. The writer's proposal stream is an **offset window**: committed prefixes are compacted away, and superseded proposals are dropped. The engine's `gc_released_prefix` reclaims released committed versions below the frontier while keeping the carry source a live position still reads — this is the load-bearing GC, because the per-consumer `FanOut` view folds the changelog whole, which makes `Tile::Store`'s `remove_guarded` a no-op (a released tick is not a deletable position). And `AsOf` releases the store fan *below* its latest decided tick — a future trigger only ever needs the latest-as-of-its-time — which is what lets `CommitProducer` reclaim a live store's superseded history.

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
consult [`Builtin::iterates_arg`], the single per-builtin policy method for the
input-internalising group. It derives that group's aggregate half from
[`Builtin::as_aggregate`], so a newly added `AggregateKind` joins by construction rather
than by a second list agreeing.  The pass walks the AST inserting
`Apply(true ▷ const, Iterate)` as the source at every iteration site and
*applying* zero or more `restrict(p)` filter steps to it (one per refinement
layer) — `iterate ▷ (p ▷ restrict) ▷ …`, application rather than composition.
Op-conversion never has to invent an iteration source on its own.

### The level a node is converted at

Every node is converted at a `CurryLevel`: how many levels of its input are the iteration it is
lifted over, rather than part of the element it takes. The AST around the node sets it
(`OpConversionContext::level`), and no operator's level is read off a tiling, because a tiling
cannot tell a level the node iterates from a level inside the element it takes. Over grouped rows,
`(sum(g), max(g))` and `(g, [s.qty for s in g])` both pair at the groups' keys, while their arms
carry one level and two.

| Node | Converts its children at |
|---|---|
| a root: a conversion with no input | a stream of its own: level 1 when its type is a collection, 0 when a scalar |
| `map(𝑓)` | 𝑓 one level in |
| `map_filter(𝑞)` | 𝑞 one level in: it asks of each key of each element collection |
| an application `𝑓(𝑎)` | 𝑎 as a root; 𝑓 at 𝑎's level, since it runs over 𝑎's iteration |
| `curry(𝑔)` over a stream, `curry_over(𝑠, 𝑔)` | 𝑔 one level in, over the iteration `Product` appends; 𝑠 is a root |
| a top-level carrier | its body at level 1, over the store's own domain |
| a nested carrier | its source and its seed (over the flattened pairs) at the carrier's level, its body one level in |
| every other node, composition included | the level it is converted at |

The operators that act at one level ([Curry levels](#curry-levels)) take it from here. `Zip`
pairs at it, and so does a product morphism with no input, at the domains its type is curried
over. `MapResult` applies at it, `MapFilter` filters the element collections there, and a
per-row `ExtractFinal` reduces the rows above it. A composed `VariantWrap` wraps at it, and an applied one at its payload's root level.
A fed copairing merges one level above it, and a nested carrier leaves standing the levels above
its own row, one fewer than it.

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

#### Constant-in-element predicates

The scalar value-`Case` C-form
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

Which iteration a binding is aligned to is `LetBinding::depth`. A reference made in a deeper
iteration reads a tile keyed by one it is not running over, so it is spread over the keys beneath
each of the binding's rows first (`lift_into_iteration`).

### Fan-out and sharing

Four arms share an input across multiple downstream consumers:

- **`Apply(_, Zip)` with `Tuple` / `Record` arguments** fans the input out to
  each tuple / record element; the elements get `Some(fan_out_branch)` and
  combine via [`zip_arms_at`] (function-tiled arms) or [`MakeRecord`] (scalar arms).
  The 2-arm Zip-with-const fast path skips the fan-out and emits a single
  `MapResultToConst` instead. A **store-read arm** (`__hist.k`, or a nested store's
  `__hist ≫ .k`, one history per enclosing row) is a *leaf*
  source over its own domain, so it is converted with **no** input (rather than
  the fanned branch, which it would reject); `zip_arms_at` co-aligns it with the
  input-driven arms by domain position. This is the cross-domain co-iteration a
  commit writer's source uses — `zip((reqs, __cnt.acc))` pairs the request stream
  with a request-indexed induction accumulator read so a commit decision can read
  the accumulator at its request position (`with begin(): balance += cnt`).

- **`Let { bound_expr, body }`** fans the parent input into both the bound
  expression and the body (described above).

- **A nested carrier** shares its enclosing drive, its per-row source, its pairs and
  each seed between several readers, and each of those fans sits on a `Memo`: a
  `FanOut` passes every branch's pull to its input, which without the cache is
  recomputed once per reader per lap. None of these fans' releases is read as a
  drive's progress, which is what keeps a `Memo` off an iteration source.

- **Induction writer bodies** (the realization of a recognized `Transact` over a
  concrete iteration extent) fan-out the cyclic prev-accumulator stream and the
  body output (via `FanOut::new_cyclic`); see
  [*Induction stores as a changelog*](#induction-stores-as-a-changelog-inductionstore-and-storedenseread)
  below for the full structure.

### Aggregates, sinks, and the program root

The pipeline always bottoms out at one of three consumer shapes:

1. A scalar produced by `Apply(<chain>, Sum)` / `Max` (compiles to
   `Aggregate` + `ExtractAggregate`) or `Apply(Tuple([stream, default]), FinalOrDefault)`
   (compiles to `ExtractFinal`, or to `StoreFinalRead` over an induction accumulator's own
   history).
2. A function-typed program result — `convert_to_operators` is the entry
   point, the resulting tile is subscribed by the user-supplied `main_consumer`
   at `compile_program`.
3. A trailing `Record` of sink-bound names — `convert_outputs_to_operators`
   compiles one operator per entry, sharing the scope (and therefore the
   `FanOut` / `Memo` of let-bound upstream) across every entry.  Each entry
   is subscribed by its corresponding `SinkConsumer`.

In all three cases planning has ensured every iteration site has an explicit
`iterate(p)` marker, so op-conversion is a context-free walk: each arm decides
what to emit based only on its own AST shape and the input flowing in.

### A correlated inner comprehension

An inner comprehension whose body reads the **outer** binder runs once per outer row, over its
own copy of the inner domain. `lambda_elim` writes that as `curry(𝑔)` composed onto the outer
stream, where `𝑔` takes the pair of the outer value and the inner element. The pair is what
carries the correlation: an uncorrelated body never forms one, leaving a `const` that is
computed once and broadcast.

Compiling it is the pairing. [`Product`] gives each outer row a group holding the whole inner
domain, one level deeper than the outer collection — a collection per row — and `𝑔` then compiles over
that like any other morphism over a stream, its result inheriting the grouping.
The inner source does not mention the outer binder, so every row iterates the same domain and
the pairing is a cartesian product (`Product::shared_at`). While the inner side is still
arriving, each row is paired with the elements it holds so far and left open: no row is complete
until the inner side is, since every row can gain its next element. Every row reads the whole
inner side, so it is released only when everything is. A source that differs per row is the same
operator's per-row form (`Product::per_row_at`, [Where a collection is materialized](#where-a-collection-is-materialized)),
where the per-row collection arrives as a value rather than being selected by the binder.

Nothing downstream of the pairing is required. `MapAggregate` consumes the grouping where the
comprehension is aggregated, and a comprehension that yields a collection per row leaves the
two-level tile as the answer.

**Nesting is unbounded, because the two operators are inverse at one level each.** `Product`
takes a collection at any depth and appends a level; `MapAggregate` collapses the
innermost level and leaves whichever shape that implies, one level fewer than it
received. So a comprehension nested 𝑛 deep pairs 𝑛−1 times on the way in and
folds 𝑛 times on the way out, and no operator sees a shape it did not already handle at
depth two.

**Where the inner domain comes from is what the term has to say**, and planning decides which
of two shapes op-conversion sees (`src/ccl/planning/correlated.rs`). A site whose source
planning named is [`Builtin::CurryOver`], whose first operand compiles as its own iteration; a
site it left alone keeps its `curry`, and op-conversion reads the domain off the type.

[`CheckedLookup`] gains a second reading from this, as a consumer now meeting a per-row
stream: it answers a group of keys per row, keeping the grouping — one answer per key, where
its key sits. A tile that cannot answer every key answers none, since an undecided key would
have to re-offset the groups it left.

### Where a collection is materialized
A **filter** on the inner source rides the pair it filters, as a refinement `lambda_elim`
writes on the product. Planning emits it as `filter_values` — a term, which is what applies
it, since this site is a morphism under `curry` rather than one the iterate-then-restrict
chain reaches. A keyed collection's carried present-key proof is a different kind of
refinement and stays on the binder whose lookup reads it.

[`Filter`] reads the resulting mask **positionally**: the predicate compiled over the same
pairs, so its flat codomain is one boolean per entry in entry order, which is the mask
`Tile::retain` takes and re-offsets the shortened groups from. Each side is pulled from its own
branch of the pairs and they need not have reached the same rows. An input with nothing in it
is already filtered, which is the ordinary end of a pull; anything else out of step is refused
with a message that says so, rather than reading the mask across the misalignment, which drops
the wrong entries silently, or answering empty, which waits for an alignment that is not
coming. A source delivering its rows one at a time — a transaction's — is what produces that
misalignment, so a correlated filter inside a transaction is not served yet.

Still not compiled: a correlated filter whose **body reads nothing outer**, whose binder is
free only in the type, so lambda elimination takes the Pi-const arm and the site never becomes
a pair at all.

### Reading a collection held per row

A collection reaches an operator in one of two shapes. A **streamed** one carries its keys in
a domain column, one row per key, and is what every consumer that iterates a collection reads.
A **materialized** one is a single map value, a binding list carrying its own keys, which is
what a column holds: a column has one value per row, and a level is not a value.

A producer that knows its values hold a collection hands out the level instead of the cell,
rather than leaving an adapter to open it downstream. Three do:

- A **list literal** builds the table it denotes, recursing on the element extent: a
  collection element contributes its own keys as the level below, and a record element
  holding a collection contributes one sub-tile per field (`list_levels`).
- A **store read** opens each position's stored value the same way, at every depth, so a
  collection-valued key reads as a collection per position rather than a map per position
  (`read_tiling` / `read_tile`, through `open_collections`).
- A **record field** of either keeps the tiling its own term produced, so a projection out
  of it is a tile operation (`SelectField`) rather than a column one.

Two consumers still take the materialized shape, and both are cases where nothing would read
the keys: `CheckedLookup` searches the bindings of the row's own value, and `Sole` and
`Drain` fold a collection whole, so the element they yield is the collection itself.

A **writer body's parameter record** opens its read slots the same way, so a collection-valued
read reaches the body as a level it can iterate (`commit_operator.rs`'s `body_input_tiling`). Its
**item** slot has nothing to open: the drive holds each row as a one-row slice of the source tile
and runs the slices together, so that slot's tiling is the source's own (`source_item_tiling`,
`column_of_rows`). Deriving it from the item's extent instead reads a record of columns as one
column of records, which is a store read's rule and not a source's.

A body's writes go the other way: a store write is one value per key, so a keyed write's `insert`
takes the level, at any depth, and the payload materializes where it becomes the decision's value
(`FunctionDef::apply_tile`, `materialize_collections`). The written value reopens into the shape
the collection's values take, so the rebuilt level is one gather over the collection's entries
followed by the written ones. An accumulator's seed and the stand-in an absent snapshot slot takes
are values for the same reason, read out of the row their producer delivered (`materialized_row`).

**A per-row collection is complete as soon as its row arrives.** A map value carries its own
keys, so nothing waits on a domain closing to know the group is whole. A producer opening one
says so by naming the rows it delivers in its `domain_predicate`. `MapAggregate` marks each
accumulator terminal where the predicate names its key, rather than reading the predicate as
one bool for the whole domain; without that, an aggregate over a live store holds every row
open forever.

**Its keys repeat across rows.** Two commits of one map carry the same keys, which a nested
tile permits: `validate_tile` asks for uniqueness within a group and no more. A codomain
guard names keys and not the group they sit in, so releasing one would release it in every
other row. `Tile::to_guard` therefore names keys only for the groups its predicate leaves
open, and releases the whole ones by their own outermost key.

---

## Induction stores as a changelog: `InductionStore` and `StoreDenseRead`

An induction store is the recurrence a `mut` loop compiles to: a [`Tile::Store`] changelog
driven by iteration position rather than by concurrent proposals, and so the no-conflict dual of
the commit store, sharing its engine. Op-conversion (`build_induction_store_single`) routes every
induction store here — plain, conditional or feed-carrying, over a finite (list) or an async
(`DataSource`) extent. An induction store has exactly one writer: recognition folds a
conditional write into one carry-complete writer (`writes = Case[ĝ → w; true → snapshot]`), so
one realization serves them all.

Nothing here distinguishes a finite source from a streaming one. The tiling protocol treats a
finite source as a stream that happens to terminate, and the memory bound a never-terminating
loop needs comes from [reclaiming the changelog](#reclaiming-the-changelog), which runs the same
way over both.

### The store

`InductionStore` holds one `CommitEngine` per open store. An engine records four things: the
**seed**, the value every key stands at before any change; a **changelog** per key, holding the
positions that wrote it; the **domain**, the positions it has decided; and the **frontier**, the
watermark every position at or below has been decided through. A position a key's changelog omits
is a **carry** for that key: decided, and holding its latest earlier value. The frontier bounds the
domain without being one of its positions, because a reclaim trims the domain and a store resuming
its predecessor's run is decided through positions it never ran. The rendered `Tile::Store` holds
the seed, the domain and the frontier per row, so projecting one row of a nested carrier is the
ordinary row retain. The seed is the
base of the step function rather than a point of its domain, because a changelog is keyed by the
positions writes land at and no position stands below the first. A fold that finds no change at
or below the position it asks about resolves to the seed.

A store opens on the pull its seed arrives, not at subscribe. A seed is ordinary dataflow: `b :=
a` after a loop over `a` settles once that loop reaches its final position, which takes as many
pulls as it has positions. The store reads its seed streams at the head of every `get`, and
`Engines::store_at` opens the engine at the first value they carry. Until then the store renders
an undecided frontier and the driver holds its first position back.

The store consumes the body's `` {`commit{writes} | `abort} `` decisions (`decision_at_index`
decodes the tag) in ascending position order from its decided watermark and `step`s the engine.
A `` `commit `` position appends a change there; an `` `abort `` position, a failed guard, is a
carry. The store closes its frontier when the decision stream goes terminal.

That last rule is an obligation on the body chain. The driver owns the source and closes its
body-input tile, so the store learns the loop is over only if every operator between the two
forwards `domain_predicate`. An operator that renders a decision column under a hardcoded
non-terminal predicate leaves the loop running forever with the right values in it: a hang, not
a wrong answer. The store asserts the converse — a terminal decision stream it has not fully
consumed — but cannot assert this one, because a body that never goes terminal is
indistinguishable from one that is not done yet.

Positions are the source's keys, each a `Position` ordered within its domain, so a `mut` loop
over a map runs with the map's keys as its positions. They are ascending but not contiguous. A restricted source (`for l in [x for x in xs if p(x)]`) delivers a subset of its
extent's positions and the recurrence runs over exactly those, so the watermark bounds the next
position from below rather than naming it. Iterating the extent densely and gating the write
would need the store to recover a filter the source's refined extent already carries. A product
source, keyed by a record, is refused: its readers release it per factor where a drive releases
a prefix, and the guard algebra has no meet between the two
(`induction_domain_releases_as_a_prefix`).

### The driver

`InductionDriver` owns the iteration source and produces the body's `(prev…, item)` input. It
holds no part of the recurrence and reads the store on two axes:

- The **frontier** is a position cursor. `step` advances the watermark whether or not the
  position wrote anything, so a frontier equal to `emitted_through` says every emitted position
  is decided and the next may go.
- The **previous accumulator** is the key's value at the frontier (`store_value_now`): the value
  after the predecessor iteration's position, which is what the recurrence means.

What the driver keeps is `emitted_through`, the item cursor, because a restricted source's
positions are sparser than its extent's and the frontier does not name the next one. The next
position is the smallest delivered path above it. An emitted row is otherwise a function of the
store tile and the source tile. The driver decodes the source into `(path, item)` pairs
(`decode_source_paths`), since an async source's domain arrives unordered and compacts as its
consumed prefix is released.

A **nested drive** is the same driver at a deeper path, carrying two additions in `NestedDrive`.
It **reseeds** at each enclosing row: a boundary is a position whose enclosing components differ
from the last one emitted, and there the previous accumulator comes from the accumulator's
reseed stream rather than from the store. It **passes the enclosing parameter through**, because
parameter elimination gave the body `((ᴘ, Pos), slots)`, and rewriting that would leave each
inner level's own type stale. At depth zero both vanish: the only boundary is the first position,
where the store already holds its seed.

A nested drive states which rows at each level are complete, and a row is complete once the
source will put no more positions under it and the store has folded every position it did. The
first half is the source's statement, which the drive accumulates across pulls: the source may
stop stating a row once the drive has released it, and the store can fold the row's last
position after that release. The second half reads the frontier: under the enclosing path the
frontier is inside, the rows before the frontier's are folded, and the frontier's own row once
every position under it is at or below the frontier. That counts the positions the drive has
emitted as well as those the source still holds, because an emitted position is released back to
the source before the store decides it.

### One carrier at every depth

`Engines` is a tree with one node per collection level above the stores and an engine at each
leaf. A loop inside one loop has one level, a loop inside two has two, and a loop on its own has
none and is reached at the empty path. The depth lives in the tree, so the code walking it has no
depth-specific case:

- `render_carrier_tile` walks the tree, and `store_tile` assembles a run of engines into one
  `Tile::Store` whose per-key changelogs group CSR-wise by store.
- `decided_paths` reads a body's decisions as paths, one component per level, in drive order, and
  `open_at` opens the store a path names.
- `domain_prefix` spells what a drive has consumed as one arm per level.

At depth zero each of these is its one-component case.

### One position per pull

The cyclic `FanOut` serves a snapshot taken before the traversal began, so a position decided
during a pull is not visible until the next. The store's producer is on the stack for the whole
traversal, so no arrangement of driver, body and store refreshes the memo mid-pull. The driver
wakes its consumer when a pull emits a row or states a level complete further, and the store
wakes its readers whenever its output changes
([The notification contract](#the-notification-contract)). Neither wakes itself while waiting,
so a stuck nest is quiescent rather than busy.

Each pull renders the retained changelog, so the cost of a pull follows retention, which
[reclamation](#reclaiming-the-changelog) bounds. Having the store publish its freshly rendered
tile into its own fan's memo, so the driver sees the position it just decided, would allow a
multi-position driver, but it inverts `get`'s direction, and is not done.

### Reads

**`StoreDenseRead`** folds one key's changelog at every position the store decided, producing
`Fun(D, V)`. The positions are the store's own domain, not an enumeration of the loop extent, so
a restricted source's read spans the positions the recurrence ran at. They are ascending by
construction, which a co-iterated read needs to align by domain value through `zip_arms_at`. The
fold is one ascending pass (`fold_changelog_key_ascending`) and reads the changelog rather than
the frontier, so a carry position takes the latest earlier write and a leading carry takes the
seed. A **carry** read (`carry_forward: true`, an accumulator) resolves at every position; a
**tap** read (`carry_forward: false`) appears only at the positions whose own change wrote the
key (`store_delta_at`).

Under rows the read produces the same shape per enclosing row: one history per row, each folded
against that row's own store, so a position that writes nothing resolves to the value its row
began with rather than the previous row's last write. A row's positions at or below its frontier
are decided, so the read states them complete beneath that row rather than waiting for the row
to close.

The trailing read of an accumulator, `final_or_default(history, init)`, takes one of two
operators by depth:

- **With no rows above**, it is a `StoreFinalRead`: the key's value once the store has settled,
  sampled from the store rather than reduced from a stream. A store resuming mid-fold has not
  decided its predecessor's positions, so a reduction over its history would find nothing and
  answer with the declared init instead of the value carried in.
- **Under rows**, it is [`ExtractFinal`](#extractfinal-reduces-at-any-depth) per row over the
  dense read, falling back to each row's seed.

A co-iterated read (`for r in …: cnt += 1; with begin(): store := store + cnt`) consumes the
dense read directly.

A `Tile::Store` carries terminality on its `terminal` flag and keeps its watermark as `frontier =
at_or_below(w)`, never a `True` that discards `w`, so `store_frontier` reads `w` directly and a
trailing run of carries is counted.

### Reply feeds

A feed inside the loop (`out << e`) rides the writer decision as a `__to_<defer>` field, as a
commit writer's reply tap does. Op-conversion appends each tap as a write-only changelog key after
the accumulator keys, and the store applies the decision's `tap_fired` gate: a `` `fired `` tap
joins the position's change, an `` `idle `` one is omitted. A `__to_<defer>` read is a tap
`StoreDenseRead`, so the feed's stream spans exactly the fired positions. A conditional feed (`if
p: out << e`) has the same shape: the letrec phase makes its guard the tap's `` `fired ``
condition and folds it into the `commit` gate, so a position that only feeds still appends a
change carrying the tap. Because the driver runs in position order, the tap stream is
position-ordered even over an async source, whose domain arrives in arbitrary order.

### Compound accumulators

A mutable variable holds one `Value`, so a tuple or record accumulator is stored materialized, as a
`Scalar(Record)` codomain, while a tuple or record literal compiles to a struct-of-arrays `Record`
tiling. The two meet at the mutable variable's boundaries, where `scalar_tile_to_column_value`
materializes and `column_value_to_tile` opens a value into a declared tiling. Three sites do this:
the seed decode (`seed_value`, reading a tile's row as the one value a store holds), the
conditional-write decision merge (`flat_merge`), and the trailing read. A compound accumulator
therefore folds, reads its own writes, carries and writes conditionally as a scalar one does. The
commit store shares all three, so a `Mut((Int, Int), Txn)` or `Mut({x: Int}, Txn)` threads
through the same seed decode and decision merge.

### Reclaiming the changelog

A carrier reclaims its changelog as it runs, at any depth. Each reader releases what its consumer
has taken; the drive releases through the frontier; the `FanOut` in front of the store meets the
branches; and `InductionStoreProducer::release_impl` hands the meet to
`CommitEngine::gc_released_prefix`, one store at a time. The meet cannot advance past a branch that
has released nothing, so a reader holding its branch until it retires holds every version of every
key for the length of the run. The flat trailing read therefore releases as it goes:
`StoreFinalRead` releases through the frontier on every pull, and `ExtractFinal` over a stream
releases below the highest position it has seen.

Measured over a 90-position flat loop: 4 retained changelog entries with the reads releasing, and
180 without. Over `for x in [1..30]: for y in [1, 2]: total += x * y`: 2 open stores holding 3
changelog entries and 3 decided positions, against 30 stores holding 60 of each without the rules
below. Retention is O(keys) plus the slowest reader's lag, independent of how many positions have
run and of how many rows.

**A reader forwards the region it was released, unchanged.** It computes no bound of its own,
because the rules below make which versions a later fold can reach the store's question, and the
store is the side that holds the answer. A release naming a row of a read names the same row of
the carrier, since the two tilings agree on every level above the store, so one forward serves
either depth.

**A reclaim keeps the carry source a live position reads.** For each key the entry kept from the
released prefix is its latest write at or below the boundary, and it is kept only where some
position can still fold back to it:

- where the key has no write above the boundary, since every later position reads this entry,
  including positions the store has not run yet; or
- where the earliest live position lies below the key's next write above the boundary.

Otherwise every live position reads a write of its own and the entry goes. Keeping each key's
latest write overall instead is wrong: a key written at positions 1 and 5 and released through 3
still answers position 4 from the write at 1, and without it position 4 folds back to the seed, a
value the recurrence never held there. The drive and `StoreFinalRead` both release through the
frontier and then fold at it, which the first case keeps safe.

**A reclaim trims the domain and leaves the frontier.** A release says a position will not be read
at again, not that the store never ran it, and where each row has got to is its own entry of the
store's frontier. A frontier recovered from the domain instead — the highest decided position —
reads a finished row whose positions were all reclaimed as one that never started, and the drive
above it never learns it can move on.

**A row the meet names whole leaves the engine tree and the render together.** The drive's
release names every row before the one it is running whole (`domain_prefix`), and a per-row
`ExtractFinal` releases a row of its dense read once its own consumer has taken the row's final.
Where every branch names a row, so does the meet, and `Engines::remove_covered` drops that row in
the same release that reclaims the rest. The next render therefore cannot rebuild what was
released, which `TileProducer::get` asserts against. The row's watermark goes with it, since
nothing is left to ask where that store got to.

The driver's own release runs outward, to the iteration source. It reclaims the consumed prefix as
`emitted_through` advances and releases the source in full once the source is complete and every
delivered position has been emitted, which ends the driver.

**A nested carrier's pair-keyed inputs release as the drive passes them.** The enclosing
parameter (`pairs`) and each accumulator's reseed are streams keyed by the body's
`(enclosing, position)` pairs. The driver reads them only at positions past its cursor, so it
releases each through `emitted_through`; the store reads a row's seed only to open that row, so it
releases its seed streams through the path it has decided. Both name the region as a prefix of the
pair-keyed domain, `domain_prefix` over the path with its last two components composed back into
the pair, which `Predicate::at_or_below` spells as a staircase over the pair's fields. The seed and
reseed streams are one stream behind a `FanOut`, so either consumer holding its branch would pin
the pair stream, and the operators pairing it (`Uncurry`, `Product`) would re-deliver the
whole run on every pull. `Uncurry` releases an outer key where a pair release covers that key's
whole inner collection, under whatever standing rows qualify it.

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
