# CCL Operator Specifications

This reference describes the runtime's tile representation, producer protocol and operator
conversion. The [operational semantics](../../docs/operational-semantics/semantics.md#1-tilings)
defines the progress algebra.

A `TileOperator` describes a computation. Subscribing connects a consumer to a producer that
holds execution state. `FanOut` coordinates shared inputs through separate slot producers.

## Tilings and Tiles

An `Extent` describes possible values. A `Tiling` describes how partial results of those values
are represented. A `Tile` contains a partial result with that shape. An extent alone does not
distinguish a collection from a store or an aggregate from its final result.

### Extent

[`Extent`](types/extent.rs) describes value and domain shapes used by runtime operators.

| Variant | Representation |
| --- | --- |
| `Base(BaseType)` | A primitive type: `Int`, `UInt`, `String`, `Bool` or `Unit`. |
| `Function { domain, codomain }` | A mapping between extents. |
| `Record(fields)` | Field names mapped to their extents. |
| `Union(variants)` | Tagged alternatives and their extents. |
| `UIntRange(IntervalSet<u64>)` | A finite set of unsigned indices. `uint_range(n)` creates the half-open range from zero to `n`; `uint_range_interval(start, end)` creates a half-open interval. |
| `DataSourceDomain(…)` | A streaming source domain whose elements and completion are provided by the source implementation. |
| `Restricted { base, restriction }` | A base extent with a placeholder restriction handle. The tile path does not implement iteration of this variant. |

An `IterateExtentProducer` subtracts released indices from its remaining `UIntRange`.
Source-domain availability and release are delegated to the source implementation.
Runtime filtering uses `Filter` operators, not a populated `Restriction` handle;
`iterate_extent` panics on `Extent::Restricted`.

### Tiling

[`Tiling`](tiling/tiling_kind.rs) specifies the tiles a `TileOperator` produces.

| Variant | Tile shape |
| --- | --- |
| `Scalar(Extent)` | A column of values, empty where no scalar has arrived. |
| `Record(fields)` | One sub-tiling per field. |
| `DataFunction { domain, codomain }` | One collection level: keys in the domain extent and values with the codomain tiling. Collections and records can nest. |
| `Aggregation { kind, accumulator }` | An aggregate kind and its accumulator tiling. A reducing fold has a scalar accumulator; `Sole` retains the element's tiling. |
| `Store { domain, codomain }` | A step function over a sequencing domain with a per-key state record; see [The store is a changelog, not a function](#the-store-is-a-changelog-not-a-function). |

`extent()` returns the value extent. It removes the aggregation wrapper and maps both
`DataFunction` and `Store` to `Extent::Function`; that conversion is not an invertible
encoding of every tiling.

`empty_tile()` constructs an empty tile over one enclosing row. A collection starts with an
empty key run and a `False` completion predicate; its codomain stands over zero rows.
`empty_at_no_rows()` constructs the zero-row state used to initialize accumulators.
Records recursively preserve the enclosing row count.

### Tile

[`Tile`](tiling/tile.rs) stores partial values in columns. The enclosing row count is one at
the root and the parent collection's key count inside a codomain.

| Variant | Stored state |
| --- | --- |
| `Scalar(ColumnValue)` | Scalar cells in row order. An empty root column denotes an unknown scalar; a known root scalar has one cell. |
| `Record { fields, absent }` | A tile per field over the same rows. `absent` records released field cells while sibling fields keep their rows live. |
| `DataFunction { row_starts, domain, codomain, domain_predicate, deleted }` | Collection keys grouped by enclosing row, their value tiles, completion information and logical deletions. |
| `Aggregation { kind, accumulator, terminal }` | The aggregate's accumulator tile and per-row completion flags. |
| `Store { … }` | Per-key changelogs, initial values and progress state, with step-function reads rather than collection lookup. The [commit operator](#the-commit-operator-interpretercommit_operatorrs) defines that contract. |

For count-augmented aggregate tilings, the runtime's completion flag represents `count == N`
without storing the final input count. The formal account is
[Unsplittable Tilings](../../docs/operational-semantics/semantics.md#unsplittable-tilings).

A collection's `row_starts` contains one nondecreasing offset per enclosing row into the
concatenated `domain` column. The next offset, or the column length for the last row, ends
the run. Equal adjacent offsets represent an empty group. The codomain has one row per key,
and a nested collection introduces another set of grouped runs. Records may occur between levels.

`domain_predicate` states which key paths are complete, including all values below them.
`is_terminal()` reads universal completion for a collection, the completion flag for a store,
and the single-row completion flag for an aggregate. A scalar is terminal when its column is
nonempty; a record requires every field to be terminal. Terminality does not prevent release
of data already consumed.

`merge` combines newly delivered information. A repeated collection key merges its groups
when its values can grow. Under scalar values a repeated key stays as two entries, which
`validate_tile` reports in debug builds, and a top-level scalar column appends the second cell.
[The release contract](#the-release-contract) keeps a delivery from repeating.
`remove_guarded` releases the region named by a guard.
`to_guard` identifies releasable data; see [The release contract](#the-release-contract).

`append_level` replaces the innermost collection's values with a newly constructed collection
level. Each appended group must be whole, so its parent key becomes complete. Completion at
higher levels is unchanged. `append_open_level_beneath` is the operation for groups that may
still grow. Both require the new level to have no logical deletions and a `False` completion
predicate; existing levels retain their own deletion sets. `Tiling::append_level` performs the
corresponding transformation on the static shape.

Each collection level has its own `deleted` bitset, indexed by positions in that level's
domain column. Removing an outer key removes its subtree; removing an inner key affects only
that level. `compact` physically removes marked keys. `retain_keys` can instead leave an
enclosing key with an empty group, which is distinct from deleting that key.

Logical deletion does not itself release input data. Guards built by `to_guard` include
logically deleted keys when those keys are releasable. An operator that compacts its input
before emitting must release the removed keys itself: its consumers cannot release keys
they never receive. `MapResult`, `MapResultToConst`, `Zip`, `SelectField` and `CheckedLookup`
use `deleted_keys_guard`; `Memo`, `Aggregate` and `MapAggregate` release the input's
`to_guard` before compacting.

`deleted_keys_guard` names nested deletions by their complete key paths, preserving an equal
key under another parent. It returns `None` when no rows are deleted. It panics on a tile that
has deletions and stands over several enclosing rows: the paths above that tile are unavailable.
It also panics on deletions inside an aggregate accumulator, for which aggregate guards have no
representation. These are limits of the guard constructor, not a ban on nested deletions.

### TileGuard

A `TileGuard` names a region for demand or release. Its formal interpretation is a
[guard](../../docs/operational-semantics/semantics.md#2-guards): a downward-closed, ⊕-closed
subset of a tiling.

| Variant | Region |
| --- | --- |
| `Scalar(Predicate)` | Whole scalar cells under the paths admitted by the predicate. |
| `Aggregation(Predicate)` | Whole aggregate results under the paths admitted by the predicate. |
| `Record(fields)` | One region per field. |
| `Function(FunctionGuard)` | Keys or values within a function tiling, as specified below. |
| `Or(arms)` | A union of regions that no single guard variant represents, such as a mixture of outer-key and inner-key regions. |

A keyless leaf predicate is `True` for every enclosing path, `False` for none, or
`Qualified { enclosing, here: True }` for the selected paths. It selects whole cells, not
portions of a scalar value.

`intersect` and `union` combine regions. Record guards combine field by field.
`is_universal` and `is_empty` test the extremes; there are no separate universal/empty
guard variants. An empty guard annihilates intersection.

`flatten_or` distributes codomain wrappers over unions and produces arms that are chains of
`Codomain` steps ending in one guard. It merges arms naming the same place and removes regions
already covered by shallower whole-key guards. This prevents a sequential release from
retaining a redundant inner arm for each completed outer row.

`check_from` validates a guard against a tiling. A record guard must have exactly the tiling's
field names. Codomain recursion retains the enclosing extents so qualified predicates can be
checked at the level they name.

The runtime has no counterpart to the formal
[split operation](../../docs/operational-semantics/semantics.md#the-split-operation).

### FunctionGuard

A `FunctionGuard` distinguishes a collection's keys from the values beneath them.

| Variant | Region |
| --- | --- |
| `Domain(Predicate)` | Selected keys and the complete subtrees under them. |
| `Codomain(TileGuard)` | Selected regions within the values under those keys. |

`Domain` addresses the current collection level. Each enclosing `Codomain` steps down one
level; a chain of 𝑛 collections addresses its innermost keys under 𝑛−1 wrappers.
A predicate that names a nested key must carry its enclosing path when the same key can be
live under another parent. An unqualified key would name it under every parent, including
parents not yet delivered.

A record between collection levels contributes no level of its own. Its fields share the
record's enclosing rows, and `Codomain(Record(...))` gives each field its own region.
A whole-key release requires every field's region beneath that key to be whole.
A scalar field can be released separately while a sibling collection keeps the key open;
[The release contract](#the-release-contract) owns the resulting absent-cell rule.

`Scalar(Qualified { enclosing: 𝑅, here: True })` names a scalar field's cells under rows 𝑅.
This preserves field-specific regions when readers release different fields of one record.
When every field is whole under 𝑅, `flatten_or` lifts the record guard to `Domain(𝑅)`.

A record ends a direct collection chain but can still contain collections in its fields.
`Tile::holds_a_level`'s doc states which question guard construction, `merge` and the chain walks
each ask there.

### Predicate

A `Predicate` selects values within an extent, or paths through nested collection levels.
Tiles use predicates to state domain completeness; guards use them to select regions.

| Variant | Meaning |
|---------|---------|
| `True` | All values. Universal predicate; identity under `intersect`. |
| `False` | No values. Empty predicate; annihilator under `intersect`. |
| `Intervals(IntervalSet<Value>)` | A scalar key's admitted values, clamped to the type's range. `Predicate::at_or_below(v)` builds the prefix `≤ v`, the upper-bound streaming signal, and `Predicate::below(v)` the strict one. Never built over records. |
| `Record(fields)` | A componentwise predicate over a record key: one predicate per field, with AND semantics. |
| `Or(arms)` | Union of the arms' regions. `flatten_or` removes nested `Or` nodes and joins pairs of componentwise arms where possible. |
| `Qualified { enclosing, here }` | Keys admitted by `here` under paths admitted by `enclosing`. See [Qualified predicates](#qualified-predicates). |
| `Union { tags, rest }` | Predicate for each named tag of an `Extent::Union`; Boolean `rest` applies to every unnamed tag. |

`intersect`, `union`, `minus`, and `subsumes` operate on predicates over the same domain.
Incompatible predicate shapes are rejected, not converted to an approximate region.
`subsumes(other)` means that every value admitted by `other` is admitted by the receiver.

`as_bool` recognizes empty regions and some representations of the whole domain. A record is
empty if any field is empty, and universal if every field is universal. An `Or` is empty if
every arm is empty, and recognized as universal if one arm is universal. Arms that jointly
cover the domain need not produce `Some(true)`; use `subsumes` for exact containment.

A tagged predicate tests a union value's payload against its tag's predicate, or against `rest`
when the tag is unnamed. A point names one tag. A column names only the tags present in it,
which may be fewer than its extent permits. The default therefore remains part of the predicate:
complementing a finite list of named tags also complements `rest`.

`Predicate::tagged` removes entries equal to `rest` and collapses an empty tag map to `True` or
`False`. A retained `Union` returns `None` from `as_bool`. A constructor that knows every tag of
the domain uses `over_every_tag`, which also recognizes universality over that tag set.
Set operations combine the predicates for every tag named by either operand and combine their
defaults separately.

A tagged `UnionProducer` splits releases by tag and forwards each payload predicate to that tag's
input. It splits a pull the same way: a guard of its keys by tag reaches each arm as what it names
under that arm's tag, an arm it names nothing of is not pulled, and a key guard of any other shape
panics. A guard that names every arm of a union domain whole reads as the universal guard once
closed over the tiling (`TileGuard::closed_over`), since a union predicate does not know the
domain's tags. `TileProducer::release` closes the accumulated guard, so the releases of each arm add
up to the universal guard, and a tagged union closes a pull's guard before splitting it. A flat
union instead forwards the whole predicate over the domain shared by its arms, even when that domain
is itself union-keyed. Prefix construction over union keys is specified under [Componentwise
predicates and prefixes](#componentwise-predicates-and-prefixes).

### Qualified predicates

`Qualified { enclosing, here }` admits a path when `enclosing` admits its prefix and `here`
admits its last key. `enclosing` can itself be qualified. `Predicate::exactly(path)` constructs
a singleton path with one component per level.

An unqualified predicate admits the same key under every enclosing path. That is insufficient
for completeness local to one parent: completing an inner key in one row must not complete
the same key in all other rows. `Or` can contain qualified arms and forwards the full path to
each arm.

`contains_path` tests a path. `contains` takes one key and panics if it encounters a
qualified predicate; the missing prefix cannot be replaced by a conservative `false` without
changing the region being tested. `is_applicable_over` checks a predicate against a sequence of
level extents; `is_applicable_to` checks one extent. The corresponding guard operations are
`TileGuard::covers_path` and `check_from_under`, which retains the extents crossed by codomain
steps.

`Predicate::qualified` returns `False` if either component is empty and returns `here` if
`enclosing` is universal. `split_qualification` returns the two components of a `Qualified`
node, or `(True, self)` for another shape. The operations distribute over `Or` before applying
the [componentwise algebra](#componentwise-predicates-and-prefixes).

### Restating a moved group

A level's `domain_predicate` is relative to its tile's root. Moving a group changes the paths
that its predicates describe. Operators apply the following transformations to retain the
same completeness or release region:

| Move | Restatement |
|------|-------------|
| Take row 𝑟's group out (`Tile::group_at`) | `within(𝑟)`, or `True` where the level above calls 𝑟 complete |
| Place a group under row 𝑟 (`Tile::regroup_beneath`) | `beneath(𝑟)` |
| Attach a column of groups to the rows 𝑅 it stands under | `qualified_by(𝑅)`; `Tile::qualify_codomain_by_keys` for a column under one row's keys |
| Insert a level before a path component | `with_level_inserted` |
| Merge two levels into one keyed by pairs | `with_levels_paired`, and `with_levels_unpaired` for a release handed back |

`Tile::map_level_predicates` traverses the collection chain and record fields.
`TileGuard::map_level_predicates` traverses the levels named by a guard. Omitting the
transformation can attribute completeness to a different row and violate
[The completeness contract](#the-completeness-contract).

### Componentwise predicates and prefixes

A componentwise predicate is a product of regions: a key is admitted when every component is
admitted. `Componentwise` in `tiling/predicate.rs` implements this algebra for record fields
in name order and for the `(enclosing, here)` components of a qualified predicate.

| Operation | Rule |
| --- | --- |
| Intersection | Intersect corresponding components. |
| Pairwise join | Combine into one product when at most one component differs; otherwise retain separate `Or` arms. |
| Difference `A ∖ B` | Union the steps indexed by `i`: use `A[j] ∩ B[j]` before `i`, `A[i] ∖ B[i]` at `i`, and `A[j]` after `i`. |
| Containment of nonempty `B` | Every component of `A` contains the corresponding component of `B`. |

Subtracting every component independently into one product is incorrect: it would discard
`(1, 0)` when subtracting `{1} × {1}`. The difference steps retain it.
`flatten_or` repeatedly joins compatible pairs, which coalesces adjacent rows with the same
remaining components. It does not find every possible product representation: three or more
arms can jointly cover one product even when no pair combines.

A **prefix** of a lexicographic order is a staircase of componentwise predicates: `≤ (𝑎, 𝑏)` is
`{_0 < 𝑎} ∪ {_0 = 𝑎, _1 ≤ 𝑏}`. `domain_prefix` builds one across levels, one qualified arm per
level, and `Predicate::at_or_below` builds one across a record key's fields. An interval is
never built over record values, so a record key has only the componentwise algebra. A level keyed
by a nested loop's `(outer, inner)` pairs is released as a prefix, and a cartesian product's keys
are stated per field, because its factors grow independently; the two meet under the same rules
as any two componentwise predicates.

A union key is ordered by tag, then payload. Its prefix includes every earlier tag, the
payload prefix at the bound's tag, and no later tag. `at_or_below_in` and `below_in` require
the domain extent to enumerate those earlier tags; `at_or_below` and `below` panic on a union
value. Record fields recurse with their own extents. `domain_prefix_over` supplies each level's
extent, allowing a loop over concatenated collections to release its consumed prefix.

`subsumes` handles collective coverage by testing whether `other ∖ self` is empty when no
individual `Or` arm suffices. `Predicate::intervals` clamps scalar intervals to the value
type's range and normalizes their bounds, returning `False` for the empty set and `True` for
the whole type. For example, a `UInt` interval has lower bound zero; treating `(-∞, 3]` and
`[0, 3]` as distinct regions would give incorrect containment answers.

### Curry levels

A collection tiling is a curried data function `K₀ ⤇ K₁ ⤇ … ⤇ V`, held as one
`Tile::DataFunction` per level. `CurryLevel(n)` addresses the tile `n` levels in: `CurryLevel(0)`
is `K₀`, `CurryLevel(n)` is `Kₙ` grouped by the `n` levels above it, and
`CurryLevel(levels)` is the values every level stands over.

An operator stores its level at construction and uses it for `values_at`, `group_at`,
`per_group`, and `wrap_guard`. Destructuring the root tile instead reads level zero, regardless
of the operator's level. `CurryLevel::enclosing` identifies the level whose keys provide the
rows grouping the selected level. These are not necessarily the root rows: the distinction
first affects an innermost operation in a collection with three levels.

Completeness applies to all descendants of a complete path. `Tile::completion_at` combines
the statements along that path, not just the selected level's `domain_predicate`.
`MapAggregate` needs this combined statement to decide when a group is final. Checking only
the outermost statement can leave a completed inner row unresolved while its enclosing
induction store remains open. The temporal obligations are specified by
[The completeness contract](#the-completeness-contract).

Level-addressed operators use two constructions:

| Change | Construction | Examples |
| --- | --- | --- |
| Replace values without changing enclosing keys | `with_values_at` for the output tiling; `values_at_mut` for the tile. No regrouping is required. | `Zip`, `VariantWrap`, `ExtractFinal`, `MapDomain` |
| Rebuild a collection's keys and groups | Extract with `group_at`; rebuild with `regroup_beneath` or `per_group`. | `UnionOperator`, `Uncurry`, `Converse`, `Product`, `StoreDenseRead` |

`regroup_beneath` requires an empty tile of the rebuilt output level for the case with no
enclosing rows. `per_group` derives it from the output tiling. The outermost level is one
implicit group. Nested levels have one group per enclosing key and require the predicate
transformations in [Restating a moved group](#restating-a-moved-group).

Separate inputs need not contain the same rows or use the same row indices. Multi-input
operators match rows by full path with `Tile::rows_by_path`; a union includes the rows from
all of its arms. A row-reading operator must also use the selected level's enclosing rows,
even if its output construction only replaces values.

### CCL types vs. tilings

A CCL compute function type describes its input and result, not their runtime batching.
For example, a function of type `Int ⇒ Int` can be applied once to a scalar or at each key of
a collection. Operator conversion selects the implementation using the input tiling and the
level at which the function is applied.

The `MapResult` family uses `change_tiling_result` to preserve enclosing collection levels
while changing the result tiling. `zip_arms_at` constructs `MakeRecord` when all compiled arms
are scalar, and `Zip` otherwise, pairing at the supplied level. The operator must preserve any
collection levels inside the arms' values rather than treating them as additional iteration
levels. [A product value is a record of tiles](#a-product-value-is-a-record-of-tiles) specifies
the separate case of a record-valued expression.

A zip converts its input once for the arms that read it. One non-leaf arm reads the input itself,
and two or more read slots of a memoized `FanOut`, so a single reader pays for neither the fan nor
the `Memo`. A leaf arm (a store read) is a source over its own domain and reads none. Without the
`Memo`, the lone arm sees the input's deleted rows and releases the input only when its own consumer
does, so an arm chain that does not hand back what it consumes holds the producer upstream. A
`Transact` writer body therefore reads the driver's slot through a `Memo`.

### A product value is a record of tiles

`build_product` in `operator_conversion.rs` selects product construction by the node's extent.
A record extent produces `MakeRecord` and `Tiling::Record`. Each field retains the tiling of
its compiled term, including any collection levels. `SelectField` projects one of those tiles.

A function extent `𝐷 ⤇ {…}` instead describes a collection of records. Its components are
paired at the level determined by the function type through `zip_arms_named_at`. For example,
the pair `(acc, i)` used by a pointwise binary operation is assembled beneath the levels over
which its components were applied. Using that construction for a record of collections would
change its shape into a collection of records.

A product that ends an element-wise chain does not reach `build_product`. Conversion fuses the
chain into one map, whose values are one column of records, `Tiling::Scalar` of a record extent
([Element-wise chains](../ccl/design/optimization.md#element-wise-chains)).

Fields can complete and release independently. A scalar field can be released while a sibling
collection continues to grow; see [The release contract](#the-release-contract). Collections
retain the incremental representation described below rather than becoming successive scalar
cells on each delivery.

`RecordField` is distinct from `SelectField`: it projects a materialized record value in a
function's codomain, one row at a time. It requires column values and cannot project a field
that remains an incrementally growing collection tile.

### A collection inside a value stays a tile

An incrementally growing collection is a `Tile::DataFunction`, including when it occurs inside
a record value. Its keys remain addressable by guards and its codomain remains a tile.
Materializing each partial delivery into a `Tile::Scalar` cell would append separate map values
instead of extending one collection.

`Tiling::from_extent` constructs this representation. `Tile::holds_a_level` and
`Tiling::holds_a_level` detect collection levels, including levels inside record fields.
`Extent::holds_a_collection` instead tests the value type and also recognizes a collection
already materialized as a map. `open_collections` opens materialized maps recursively;
`materialize_collections` performs the reverse conversion where a complete value is required.

`Product` preserves collection-valued elements when pairing them with keys: a plain element
and key fit in one column, but an element containing a collection requires a `Tiling::Record`
whose `_0` field retains its levels. `Uncurry` combines two key levels into one pair-keyed level
without materializing their values.

Variant payloads and store writes require materialized values. `VariantWrap` waits for a
collection payload to complete, then emits it as one cell at the level named by the payload's
type, not necessarily the input's innermost level. `VariantProject` opens it back into levels.
For a feed leaving a nested loop, this round trip carries the inner tap collection through the
enclosing decision's variant payload; the channel then flattens the two collection levels.

---

## The producer protocol

A subscription connects one producer to one consumer. `TileOperator::subscribe` constructs
that producer with an intent guard, a consumer notification handle and a scheduler.
`FanOut` shares an input through separate slot producers; each slot still has one consumer.

| Call | Contract |
| --- | --- |
| `subscribe(intent, consumer, scheduler)` | Establish the subscription for the requested region of the output tiling. |
| `Consumer::notify()` | Signal that the consumer should pull again. It carries no tile and does not count individual changes. |
| `get(projection)` | Request the current tile for a projection. Tile values cross the edge only through this call. |
| `release(obsolete)` | Permanently relinquish a region; see [The release contract](#the-release-contract). |

`get` and `release` are provided `TileProducer` methods around required producer-specific
`get_impl` and `release_impl` methods. The `get` wrapper removes released scalar record cells,
checks the returned tile, records a probe observation and returns the result. It does not
implement projection for the producer.

| Check | Build configuration |
| --- | --- |
| Returned tile matches the producer's tiling (`check_from`) | All builds |
| Returned tile contains no data inside `obsolete_guard` | Debug assertions |
| Tile structure passes `validate_tile` | Debug assertions |
| Previously complete paths obey the completeness contract | Debug assertions |

The `release` wrapper checks that the guard matches the tiling in every build, normalizes it,
unions it into `obsolete_guard`, and closes the result over the tiling (`TileGuard::closed_over`).
If the accumulated representation changes, it calls `release_impl` with the normalized argument,
not with the entire accumulated guard. When the closure makes the accumulated guard universal, it
calls `release_impl` with the universal guard instead, which overlaps the pieces released before
it: a `release_impl` reclaims everything only on a universal guard.

Sources are polled separately from producers. `Scheduler::poll_sources` buffers source arrivals
and returns a `Delivery` without notifying consumers. `Scheduler::deliver` notifies those
consumers, drains deferred wakeups, then runs queued sink pulls. `check_for_notifications`
performs both operations. The deferred queue deduplicates consumers by handle identity; a wake
requested during its drain remains for the next drain.

The poll/delivery split permits inspection of buffered arrivals before a sink pulls and releases
them. A `Delivery` retains its consumers strongly until delivery. Dropping a nonempty delivery
without delivering it is a debug assertion failure, except during unwinding; the data remains
buffered but no consumer has been woken. [The notification contract](#the-notification-contract)
specifies forwarding and reentrancy.

### Projection guards

A projection guard names the part of a producer's tile that a `get` asks for. The producer
returns that part and nothing outside it, and states completeness only for that part.

A projection (`Projection`) is everything, nothing, or the keys of one collection level that a
predicate 𝑝 admits (`Projection::Keys`). At the outermost level its guard is `Domain(𝑝)`. At level 𝑛
beneath it, 𝑝 admits whole paths ([Qualified predicates](#qualified-predicates)), and its guard
wraps the domain guard in 𝑛 codomain guards (`CurryLevel::wrap_guard`). Two projections meet at the
deeper of their levels, where a key above is every path beneath it, and a region of every path
beneath some keys is spelled at the level of those keys (`Projection::keys_at`). Any other guard is
a release's shape. Each producer declares the levels whose keys it restates
(`TileProducer::restates`). `Restates::Outermost`, the default, names the outermost keys only.
`Restates::Above(𝑛)` names the outermost keys and the levels above 𝑛, for a producer that keeps its
input's keys above its level 𝑛 and computes the values beneath them. `Restates::Every` names every
level. A producer that declares more than the outermost keys reads its projection with
`TileGuard::projection_for`, and any other with `TileGuard::projection`. Either panics with the
guard on a shape that is no projection or that names keys at a level the producer does not restate,
as [Guard operations are exact](#guard-operations-are-exact) requires of a restatement with no
spelling. A debug build's `get` panics on a pull at such a level. `Tile::restrict_to_paths` cuts a
tile at a level beneath the outermost (`src/interpreter/design-path-projections.md`,
"Representation").

- **The answer.** `Tile::restrict_to_keys` keeps the outermost keys 𝑝 admits, each with the value
  under it, and intersects the tile's `domain_predicate` with 𝑝. A group is whole under its key. A
  producer asked for part of its keys says nothing about the rest.
- **The input.** An operator whose outermost keys are its input's forwards 𝑝 to the input, so the
  input produces only that part. Its answer is built from the input's, so it does not cut, and its
  operator test compares the answer with the whole answer cut to 𝑝 (`assert_conforms`). An operator
  that builds its answer from anything else cuts: accumulators held across pulls (`MapAggregate`),
  arms already released (`UnionOperator`), or a cache read at a wider region (`Memo`, and `FanOutSlot`
of a cyclic fan-out).
  An operator whose output keys are not its input's keys, such as `Converse`, pulls the input in
  full and cuts its own output. An operator that cannot restate 𝑝 for an input pulls the input in
  full and still cuts its output: pulling more is sound for a `get`, where a release that names
  more is not.
- **Completeness between pulls.** The completeness contract compares a producer's answers inside
  the region pulled, and a pull of one projection states completeness over its keys only, so a pull
  of another region withdraws nothing it said of the first. The debug check keeps the last statement
  of each region.
- **Check.** A debug build's `TileProducer::get` compares each answer with the projection it was
  asked for (`Tile::within`) and panics on a key the projection omits, on any cell where the
  projection names nothing, and on a pull for keys that a non-collection answers. A producer that
  has not restated projections answers whole and fails the check on the first pull for keys.
- **Test double.** `ProjectionSpy` answers a fixed tile cut to the guard it is pulled with, and
  logs each projection and release it receives. An operator test pulls the operator over it and
  reads the log to see the guard the operator restated.

| Operator | Projection |
| --- | --- |
| `IterateExtent` | A finite range is cut to the admitted interval before it is rendered. Every other extent renders whole and is cut after. |
| `Constant` | A collection constant answers the admitted keys. A scalar constant answers the whole value or nothing. |
| `MapResult` | A keyed input is pulled at the projection; a scalar input is a key looked up in the function, has no keys to project, and is read whole. A function operand that is a collection is pulled at the projection too where the input's values are its keys, the arguments stand at the first level, and the operand is a data function; its keys are released with the data's. Any other function operand is read whole. Beneath the outermost keys the input is pulled at a projection above the level the function applies at (`Restates::Above`), and the function operand is read whole. |
| `MapResultToConst` | A collection input is pulled at the projection where the constant applies one level in or deeper. At the outermost level the constant replaces the whole input, so the input is read whole. The constant is read whole, since every row reads all of it. A projection beneath the outermost keys is answered above the constant's level (`Restates::Above`), and one at or beneath it panics. |
| `MapResultWithSource` | The input is pulled at the projection, so a morsel reads only its own keys from the source. |
| `RecordWrap` | The input is pulled at the projection, which beneath the outermost keys is one above the wrapped level (`Restates::Above`). |
| `SelectField` | A stream of records is pulled at the projection. A product of collections is pulled whole and the selected field is cut. A projection beneath the outermost keys panics ([Differences of nested guards](design-path-projections.md#differences-of-nested-guards)). |
| `Zip` | Every arm is pulled at the projection, since the arms share the pair's keys. The pair is complete only where every arm is. A projection beneath the outermost keys is answered above the record's level (`Restates::Above`). |
| `MakeRecord` | A record of values has no keys: the projection is the whole record or nothing, and a guard naming keys panics. |
| `VariantWrap` | A payload stream is pulled at the projection. A payload that is itself a collection becomes one union column and is read whole. A projection beneath the outermost keys is answered above the wrapped level (`Restates::Above`). |
| `VariantProject` | A union stream is pulled at the projection. A bare union has no keys of its own, so it is read whole and its positions are cut. |
| `VariantIs` | A union stream is pulled at the projection, since every key in is a key out. A bare union has no keys of its own, so it is read whole and its positions are cut. |
| `Filter` | A predicate or input that is a collection is pulled at the projection, since they share the keys of the level the mask names. A side that is not a collection is read whole. With a collection predicate it takes a projection at any level down to the masked one (`Restates::Above`). The predicate holds no level beneath that one. With a function predicate, which masks the outermost keys, it takes a projection at any level (`Restates::Every`). |
| `Restrict` | The predicate is pulled at the projection, since the restricted domain is the predicate's keys that pass. |
| `MapDomain` | The input is pulled at the projection, since every level's keys stand. |
| `Uncurry` | Beneath standing levels the input is pulled at the projection. Pairing the whole tile reads the groups whose first component the projection admits, and the pairs are cut after. |
| `Product` | Both sides are pulled at the projection, since they are aligned row for row. The outer side has no paired level, so a projection at or beneath it pulls both sides at the rows its paths run through (`Projection::above`), and the pairs are cut. |
| `Converse` | Beneath standing levels the input is pulled at the projection. Inverting the outermost collection reads the whole input and cuts the groups, and the rows of a group the projection does not name stay unreleased at the input. |
| `FanOutSlot` | Pulls the shared input at its own projection and cuts its answer to it. A producer states completeness only for the region it returns, so slots at different regions each pull the one input at their own and a pull of one region retracts nothing it said of another (the debug check compares the last output inside the region pulled). A cyclic fan-out reads its input whole, because a sibling that re-enters mid-pull is answered from the cache of the last completed pull, which has to cover whatever region that sibling asks for. A projection beneath the outermost keys is read and cut as one of the outermost keys is. |
| `Memo` | Reads its input at the projection and caches what it read; a pull over a region it has read answers from the cache cut to the projection, and a region it has not read reaches the input however quiet the input has been. The regions it has read and must read again are projections at any level, so a projection beneath the outermost keys is read and cached as one of the outermost keys is. |
| `UnionOperator` | A flat union pulls every arm at the projection and cuts the merge to it: the arms are disjoint slices of one collection, and an arm the consumer has released contributes an empty tile that states every key decided, which the cut brings back to the projection. A tagged union keys its rows by arm. It pulls each arm at what a guard of its keys by tag names under that arm's tag, as its `release_impl` splits a release, and does not pull an arm the guard names nothing of; a key projection of any other shape panics. |
| `CheckedLookup` | A stream of keys, or of `(collection, key)` rows, is pulled at the projection, since each answer sits at its key's position; the collection is read whole, because every key is answered against all of it. One key has no keys to project and admits only `Everything` and `Nothing`. |
| `ExtractFinal` | Admits `Everything` and `Nothing`. The last position of a stream is not known before the stream ends, so the source is read whole, and the one value or collection it yields is released whole. A key projection panics, including over a collection-valued final position, which is not implemented. |
| `PermuteRecordDomain` | Reads its input whole and cuts the answer to the projection over the permuted keys: a region of record keys is componentwise, and the input's fields are renamed, so the projection is not forwarded. |
| `FlattenTupleDomain` | Reads its input whole and cuts the answer to the projection over the flat keys, as `PermuteRecordDomain` does: the nested keys are restated flat, so the projection is not forwarded. |
| `Aggregate` | Admits `Everything` and `Nothing`: the accumulator has no keys, and the input is read whole whatever the consumer asks. A key projection panics. |
| `ExtractAggregate` | Admits `Everything` and `Nothing`: one extracted value has no keys. A key projection panics. |
| `MapAggregate` | Pulls the input at the projection, at any level (`Restates::Every`), and cuts the answer to it: the answer is built from every accumulator held, including those of keys pulled earlier, and each group beneath a key is whole. |
| `MapExtractAggregate` | Pulls the input at the projection, at any level of the input (`Restates::Above`). The answer keeps the input's keys, and only unfinished groups drop. |

### Producer attribution and probes

Each `subscribe` returns one producer attributed to the operator that constructs it.
`ProducerBase::new` records the operator's `node_id` and the scheduler's `ProbeSlot`.
Input producers are constructed by their own operators' subscriptions.

Probe keys are `(node_id, producer_id)`. `alloc_id` counts by producer display name, so two
producer types built for one operator could collide; `ProbeTable` checks conflicting names
with a debug assertion. Observations are rendered with a row limit after `get_impl` and the
wrapper checks, without changing the tile returned to the consumer. No probe-table borrow is
held across `get_impl`, whose upstream pulls may use the same table.

An empty probe slot records nothing. Connection lifetime is specified by
[Probing follows the live route](../inspector_model/design.md#probing-follows-the-live-route).
Dropping a producer detaches its probe. The rendered frame is specified by
[The live model is a separate path](../inspector_model/design.md#the-live-model-is-a-separate-path).

## The release contract

After `release(𝑅)`, the consumer must not request data in 𝑅 again and the producer must not
return it. Subsequent pulls remain valid outside the accumulated obsolete region. After a
universal release, every subsequent result must be empty.

Release permits reclamation and prevents duplicate delivery. Under scalar values a repeated
collection key stays as two entries, which `validate_tile` reports in debug builds. A top-level
scalar column has implicit positions and appends the second cell. The producer wrapper checks
for returned released data in debug builds, but the contract applies in every build.
An operator must also forward the releases permitted by its input
usage. `FanOut` forwards the intersection of its slots' releases; a slot that retains a
region prevents the shared input from reclaiming it.

`release_impl` must honor or reject the incoming guard. The wrapper accumulates it before
calling the implementation, so ignoring it does not cancel the promise. Operators that only
support whole-value release use `TileGuard::expect_universal_or_empty` to reject partial guards
at release time, even if no subsequent pull would exercise the `get` postcondition.

A scalar record field can be released at its enclosing row before a sibling collection is
complete. `Tile::to_guard` names that cell, and `Tile::Record::absent` records its absence
without removing the row. A producer may reconstruct the row from inputs released only by
whole key; the `get` wrapper removes those previously released field cells before returning
it. `Zip` also preserves a row with an absent field when that field's input has already
released its cell.

### Guard operations are exact

Guard algebra is exact. `intersect`, `union`, `flatten_or`, and guard restatements must preserve
the specified region. An unrepresentable result requires a new representation; until it is
implemented, the operation must fail rather than return an approximation.

An understated result can prevent upstream reclamation; an overstated result can discard data
still needed by a reader. Subsequent unions, intersections and release-growth comparisons use
the returned representation, so neither error is confined to one call.

A consumer may choose to release less than it has consumed only if it can accept that data
again. That choice does not permit an implementation to approximate a requested guard operation.
For the caching case, see
[A `Memo` releases everything it takes](#a-memo-releases-everything-it-takes).

### A `Memo` releases everything it takes

`Memo` releases everything it merges, with `to_guard`
([The release contract](#the-release-contract)). It obtains that guard before compaction,
then releases the region upstream. Open collection groups and join-combined
aggregate or store state can remain unreleased. A debug check uses `holds_a_plain_value` to
reject an input whose release would leave ordinary values available for duplicate delivery.

`to_guard` includes complete keys by full path and scalar cells at their enclosing rows, including
cells whose enclosing key is still open. A nested tile whose held keys form a prefix is released as
one staircase (`domain_prefix`) and, at each level whose statement calls keys complete above the
last key held, an arm naming those keys. For such a tile the guard names exactly what the statement
makes releasable, and its size grows with the tile's depth, not with the keys it holds. A statement
that is itself a prefix reaching above the last key held ends the staircase at its greatest key
instead of adding an arm. A last key the statement calls whole, or whose group's statement calls
every key complete, ends the staircase at that key. A tile whose held keys form no prefix is
released key by key; at a nested level that guard names only the keys held (`Tile::held_guard`),
which leaves out the keys the statement calls complete and the tile does not hold. Three tiles whose
held keys form a prefix still take that path: a last key whose group holds nothing, an earlier key
whose own group's statement calls every key complete, and a statement about the keys beneath an
enclosing key the tile does not hold. Naming those exactly needs `held_guard` to carry each open
key's statement, which it does not yet. A universal input release latches `upstream_drained`.
Release builds then return the cache without pulling that input again; debug builds continue pulling
to exercise its post-release checks.

### What a producer holds

`TileProducer::state_info` reports values retained by that producer between pulls, excluding
its inputs' state. Counts include cached cells (`Tile::cell_count`), accumulators, store seeds,
changelog entries, decided positions and driver-window rows. A stateless producer returns zero.
`inspect` attaches the count to the producer's node for retention measurements.

The unit is values, not bytes. Retention that grows with execution length despite bounded live
data indicates unreclaimed state; `a_long_nest_holds_the_same_store_state_at_any_length` tests
this property for nested stores.

## The completeness contract

A level's `domain_predicate` declares complete paths, including paths beneath rows that have
not arrived. A complete path cannot gain keys or change values. Its descendants are complete
at every depth; see [Curry levels](#curry-levels). A statement limited to particular enclosing
rows must name them with [qualified predicates](#qualified-predicates).

Release permits removal of completed data and withdrawal of the corresponding completeness
statement. It does not permit new content beneath that path. A consumer needing completeness
information after release must retain that information itself.

In debug builds, `TileProducer::get` compares consecutive outputs through
`completeness_violation`. It checks that:

1. Previously complete regions remain complete, except where released.
2. Previously present keys and values beneath complete paths remain unchanged, or are absent
   because they were released.
3. No new key or value appears beneath a previously complete path.

A violation panics with the producer tree. Store checks cover both semantic reads at decided
positions and the component collections: seeds, frontiers, changelogs and decided positions.
Frontiers must not move backward. Store release guards name sequencing positions.

For output assembled from multiple inputs, completeness requires all contributing inputs to
be complete. `Zip`, unions and pairing operators therefore intersect their statements.
A fully released union arm contributes an empty tile with `True` completeness and imposes
no further restriction.

## The notification contract

An output change discovered during a pull must wake readers that may still hold the previous
result. That wake is deferred through `WakeupQueue`, not delivered synchronously inside
`get`: a feedback path could re-enter a producer while its `RefCell` is borrowed.

A notification carries the region of the notifying producer's outermost keys that changed:
`Consumer::notify(arrived: &Projection)`. A producer that cannot name the region sends `Everything`, and
none sends `Nothing`. A closure consumer ignores the region. A consumer that pulls on notification
has no use for it, since its pull reads whatever arrived. A consumer that does not pull acts on the
region instead.

A component that merges notifications to one consumer unites their regions with
`Projection::union` and narrows none. A gate passes the first notification after a pull, and after
it each one that names a key no notification passed since that pull named (`scheduler::Admission`).
It drops the rest, whose keys its consumer has already heard of: a consumer that pulls reads them in
its next pull, and one that acts on the region, as a memo marks it dirty, has marked them.

**Forwarding.** An operator keeps an input's keys, forwarding its region unchanged, only if its row
of the "Projection guards" table pulls that input at the projection and the input's keys are the
operator's own output keys: a region of changed input keys is then a region of possibly changed
output keys, and a changed completeness statement at a key is a change at that key. A tagged union
restates an arm's region as the same keys under the arm's tag (`forwarding_consumer_tagging`),
since its outermost keys are its arms' keys by tag. An operator that re-keys otherwise, or reads an
input whole, sends `Everything` for that input, since it cannot say which of its own keys changed.
`MapResult`'s function operand is pulled at the projection where the input's values are its keys,
and still widens: its keys are the values looked up, not the result's keys. A producer with no keys
of its own notifies `Everything` whatever it is read through. Where a row depends on the input's
shape, the operator decides from its tiling when it subscribes, as its `get_impl` does when it
pulls.

| Operator | Input | Notification | Reason |
| --- | --- | --- | --- |
| `MapResult` | the input | keeps if applied one level in to a collection, else widens | A keyed input is pulled at the projection; applied at the outermost level or to a scalar, the function's keys are the result's. |
| `MapResult` | the function operand | widens | Its keys are the values looked up, not the result's keys. |
| `MapResultToConst` | the input | keeps where the constant applies one level in or deeper to a collection, widens at the outermost level or for a scalar | At the outermost level the constant replaces the whole input, so the output's keys are the constant's. |
| `MapResultToConst` | the constant | widens | Every row reads all of it. |
| `MapResultWithSource` | the input | keeps | Pulled at the projection, so its keys are the output's. |
| `RecordWrap`, `MapDomain`, `Restrict` | the input, the predicate | keeps | Pulled at the projection; a restricted domain is the predicate's keys that pass. |
| `SelectField` | the input | keeps for a stream of records, widens for a product of collections | The product is read whole and the field cut. |
| `VariantWrap` | the payload | keeps where the result is a collection (applied at level 1 or beyond), widens at level 0 | The values at the level become one union column, which has no keys of its own at level 0. |
| `VariantProject`, `VariantIs` | the input | keeps for a stream, widens for a bare union | A bare union has no keys of its own. |
| `Zip`, `Product` | every arm, both sides | keeps | Pulled at the projection and aligned row for row. |
| `MakeRecord` | every field | widens | A record of values has no keys. |
| `Filter` | the predicate, the input | keeps for a side that is a collection, else widens | A collection side shares the mask's keys; the other is read whole. |
| `Uncurry`, `Converse` | the input | keeps beneath a standing level, widens at the outermost | Inverting or pairing the outermost collection re-keys it. |
| `UnionOperator` | every arm | keeps for a flat union, restates under the arm's tag for a tagged one | Flat arms are disjoint slices of one collection; a tagged union keys an arm's rows by the arm's keys under its tag, and `Everything` of an arm is every key under that tag. |
| `CheckedLookup` | a stream of keys, or the pairs | keeps | Each answer sits at its key's position. |
| `CheckedLookup` | one key | widens | One key has no keys to project. |
| `CheckedLookup` | the collection | widens | Every key is answered against all of it. |
| `Memo` | the input | keeps | Read at the projection, and its keys are the input's. |
| `FanOutSlot` | the shared input | keeps | The fan-out forwards the input's region to every live slot. Between pulls it passes only a notification naming a key it has not passed since the last pull, as a gate does, and drops the rest, whose keys every slot consumer has heard of. |
| `ExtractFinal`, `PermuteRecordDomain`, `FlattenTupleDomain` | the input | widens | Read whole; the keys are re-keyed or the last position. |
| `Aggregate`, `ExtractAggregate` | the input | widens | The accumulator has no keys. |
| `MapAggregate`, `MapExtractAggregate` | the input | keeps | The groups keep the input's outermost keys. |
| Stores, recurrences and the commit operators (`commit_operator.rs`) | every input | widens | A recurrence re-keys its inputs by its own positions. |

`GatedConsumer` forwards a notification between pulls only where it names a key not passed since the
last pull. `shared_consumer` constructs it with `Notified::clear()`, so the first notification
passes, including one sent during `subscribe`. Forwarding sets the flag and grows the region passed;
`ProducerBase::sharing` holds the `Gate` token that clears the flag before each pull, which starts
the region afresh. A notification of keys already passed behind a closed gate is not delivered, and
the consumer's next pull reads the change. `Notified::flag()` instead starts set to permit an
initial input read. A `Notified::Flag` is set by notification and cleared by `take()`.
`FanOutShared::admission` gates forwarding to fan-out slots. Clearing does not depend on whether
the pull reads the notifying input. Without this suppression, a change can reach a sink once per
path through the graph, and cyclic notification paths can continue indefinitely.

`forwarding_consumer` delivers through the gate when its consumer can be borrowed. On reentry,
it drops the notification where the gate would stop it: the gate is set, and the notifications
passed since the last pull name every key it names (`Admission::covers`). Otherwise it queues the
consumer on the wakeup queue, because a pull during the current cascade may have missed the new
change. The queue holds handles, not regions, so the deferred notification is delivered as
`Everything`. Sharing notification handles does not share tile data; tiles still pass through
`get`.

A consumer woken by an operator must pull that operator if it still reads it. Until then, the
operator's gate stops every later notification from its inputs that names only keys already
passed. Finished reads, settled seeds,
recurrences with no remaining reader and wholly released operators need no further pull.
When `pull_laps` reaches quiescence, a debug check walks `TileProducer::visit_input_producers`
and rejects an input whose forwarding flag remains set after its reader was pulled that lap.

A sink does not pull when notified. It queues its pull on a queue of its own, which holds it
once however many notifications arrive. `Scheduler::check_for_notifications` delivers its wakes
first and then runs the sink pulls queued so far, so each sink is pulled once per call, in the
call that delivered the change. Installing a version pulls its sinks at once, because a version
a reload replaces hands its state to its successor only if it was pulled.

- `ChangeNotifier` compares successive store outputs and queues a wake when they differ,
  including initialization, decided positions, commits and closure.
- `Memo` keeps a dirty region of its input: what it has not read, and what its input has notified
  since. A pull that overlaps it reads the whole projection and removes it from the dirty region.
  A pull outside it answers from the cache, even when the cache is empty, preventing fan-out slots
  from repeatedly pulling their shared input.
  A debug build probes once after each read when no wakeup is pending, checking for new cells
  or completeness without notification. It also continues probing drained inputs; if such a
  pull changes the cache without a notification, `Memo` queues a wake for its consumer.

The test helper `pull_laps` alternates notification delivery and pulls. It returns when its
completion predicate succeeds, the lap limit is reached, or a lap after the first delivers
no notification, returns the previous tile, and leaves both wakeup and sink-pull queues empty.
That last case is quiescence relative to the current inputs, not proof that no source can change
later.

## Pipeline breakers

A pipeline breaker is the end of a pipeline: it consumes the pipeline's work packages into state of
its own. `Breaker` (`src/interpreter/tile_operators/mod.rs`) is what the dispatcher drives:
`consume_impl`, `input_tiling`, `input_released`, `inputs`, `as_producer` and `finish`. A breaker
consumes one input per pipeline it is the breaker of: `inputs` answers how many, one but for a
transaction store, which consumes one per writer. `consume_impl`, `input_tiling` and
`input_released` name the input (`InputId`). A breaker that other pipelines read is also a producer,
which answers pulls from that state: `BreakingProducer`, a subtrait of `TileProducer` and `Breaker`,
adds `held`, `final_guard`, `morsels`, `pushes_while_consuming`, `offer_impl` and `entry_placement`,
the placement of the entry at an input, which a planner sets to that input's pipeline. Its
`as_producer` answers itself, and the driver's push after each consume and `Breaker`'s default
`finish` push through that producer. A sink's breaker is no producer, so its `as_producer` answers
`None`: no pipeline reads it, and it holds, offers and pushes nothing.

| Call | What it does |
|---|---|
| `consume_impl(input, guard)` | Pulls the input `input` at `guard`, a guard of the tiling the input answers, merges the answer into the breaker's state, and releases the input at the guard the answer states once it has taken delivery of the answer. The caller handles no tile. |
| `as_producer()` | The breaker as a `BreakingProducer`, or `None` for a breaker that is no producer. |
| `finish(pushes, last)` | Finishes an epoch once the pipeline has consumed every package of it. The default pushes, through `as_producer`, what the breaker holds and no push named before, one morsel of its outermost keys per work package, through its consumer to the pipelines that read it; a breaker that is no producer pushes nothing. `last` says the epoch is the run's last, after which nothing calls the breaker. An empty guard pushes nothing. It wakes no one. |
| `morsels(guard, rows)` | Cuts a guard the breaker pushes into morsels of at most `rows` held rows, which partition it. The default answers the guard whole. |
| `pushes_while_consuming()` | Whether the driver also pushes after each `consume_impl`. The default answers `true`. |
| `offer_impl(guard)` | Answers from the state `consume_impl` built and pulls nothing. The breaker's own `get_impl` calls it once the breaker is consuming. |

`Memo`, `Aggregate`, `ExtractAggregate`, `MapAggregate`, `Converse`, `ExtractFinal`, and an
induction store and a transaction store ([A store as a breaker](#a-store-as-a-breaker)) are
breakers that are producers; `SinkBreaker`, in a test's program run, is one that is not.
A breaker starts in the pull mode described in [The producer protocol](#the-producer-protocol) and
is a consuming producer from its first `consume_impl`, which it stays. `final_guard` is provided
over `held()`: it is `held()` less the guard released to the breaker, and the driver pushes the part
of it no earlier push named, after each consume and at the epoch's `finish`. When a pipeline may
finish an epoch is the dispatcher's to check ([The dispatcher](#the-dispatcher)). A release removes
rows from the state and leaves the statement of the tile as it was, so the difference is taken in
the guard algebra. `guard_minus` (`tile_operators/mod.rs`) spells it for guards of a collection's
outermost keys, of a scalar and of an aggregation, none of them qualified by an enclosing path, and
for a record of such guards field by field. Two guards of a collection's keys at any levels differ
as their projections do: a release up to the path `(𝑘, 𝑗)` leaves of a held row 𝑘 its paths past 𝑗,
which `TileGuard::closed_over` drops where the row's level is a finite range of positions with none
past 𝑗; `final_guard` closes the difference over the producer's tiling. A state of another shape has
no spelling, and a push after the first panics naming the gap instead of answering a smaller or
larger region. `MapAggregate` and `Converse` hold a state released beneath the keys of a group, and
what a release beneath them leaves is a region beneath the outermost keys. A reader's chain may
restate only the outermost keys (`TileProducer::restates`), so they answer `pushes_while_consuming`
with `false` and push once per epoch, at `finish`. A push beneath the outermost keys lands in each reader
as a projection at its level ([The dispatcher](#the-dispatcher)).

### Memo

A consuming memo answers from its cache, and the cache's statement says which region that answer
covers. A consume over a memo whose input has drained pulls nothing. The memo's consumer is woken by
the input's notifications, which reach it as they do for a memo in pull mode, and by the rule that
wakes it when a pull finds rows no notification announced. A consuming memo's only reader is the
pipeline the dispatcher pushes to, so a consume wakes no consumer and a push queues no wake: what
the memo holds reaches its reader through the packages the driver pushes after each consume.

### Aggregate

A consuming `Aggregate` folds the rows its input answers at the guard into the accumulator, which is
final when the input has been released whole and holds the one value until the consumer releases the
output. A consume at part of the input folds that part once: the input releases what it answered and
does not answer it again. Its guards are `Aggregation` guards, which are all or nothing. `held`
names the accumulator only once it is final, when the input has been released whole, so no guard
names a partial aggregation. The last epoch's `finish` panics where the output is unreleased and the
input has not been released whole, because no later consume completes the accumulator.

### ExtractAggregate

A consuming `ExtractAggregate` pulls its input, an aggregation, at the guard and extracts the value
once the aggregation is terminal. A terminal aggregation states all of itself releasable and is
released; a partial one states nothing releasable, so it is left in place for the next consume and
the extraction holds nothing. The value is final once the input has been released whole, and stays
until the consumer releases the output.

### MapAggregate

A consuming `MapAggregate` folds each group the input answers at the guard into the group's
accumulator and keeps what the answers state about completeness, united across consumes. A group is
final per key once the input states it complete. The input releases a complete group whole and an
open one only beneath its key, so a group that arrives later in a region already consumed is still
the input's to answer. The dispatcher finishes the pipeline's epoch once its input has released
every guard the pipeline consumed in it, so every group it holds is then final, and `MapAggregate`
pushes then rather than after each consume. The guard it pushes is the guard of the output built
from the accumulators, less the guard released. A release of the output drops the accumulators it
covers and forwards to the input, as in pull mode.

### Converse

A consuming `Converse` holds the input rows it merged, because which rows share a value is known
only once the rows are read, and builds the groups from them on each offer. Beneath standing levels
it holds each enclosing row's input rows under that row's path and inverts each row's rows on their
own, as pull mode does. A group is final once the input has been released whole. A row whose group
the consumer already released is dropped when it is merged, and a release of a group removes its
rows and forwards to the input as in pull mode. The members of a group keep the order the rows
arrived in, where a pull in pull mode orders them by key. `finish` pushes the guard of the groups
built from the held rows, less the guard released; a `Converse` pushes nothing after a consume.

#### A release of a converse group

A release of a `Converse` names its output region exactly. Upstream it is forwarded in two parts:
the held input rows the region covers at once, and each later row of a released group on the read
that first holds it (`ConverseProducer::release_late_rows`). An input guard names rows by key, and
a group is the rows whose value is the group's key, so no input guard names a group before its rows
are read. The two parts together release exactly the region named, as
[Guard operations are exact](#guard-operations-are-exact) requires. In consuming mode no held input
row stands in a released group once a consume returns; `finish` checks this in a debug build by
removing the released region from the groups the held rows build
(`ConverseProducer::debug_assert_released_groups_freed`).

### ExtractFinal

A consuming `ExtractFinal` merges the source rows it answers at the guard and keeps the row at the
greatest key, where the values are a column of scalars; any other shape of value keeps every merged
row. Merged rows are in arrival order, so the last row is not the final one and the key says which
is. Pull mode takes the last row of a source it reads whole and assumes the source is sorted by key,
which a consuming `ExtractFinal` does not. Keys of one collection are totally ordered, and a
collection whose keys do not compare panics. The value is extracted once the source has been
released whole. A source that held nothing falls back to the default, which `consume_impl` reads
when the source drains and reads again at each later `consume_impl` until it has converged; until
then nothing is held. The dispatcher issues no `consume_impl` after the last epoch, so `finish` at
the last epoch panics when the output is unreleased and no value has been extracted rather than push
nothing. A source declared total that held nothing panics as it does in pull mode. The value is
final from then, and stays until the consumer releases the output, which is all or nothing.

### A store as a breaker

An induction store (`InductionStoreProducer`) and a transaction store (`CommitProducer`,
`commit_operator.rs`) are pipeline breakers. A transaction store is the breaker of one pipeline per
writer (`Breaker::inputs`): a writer's cycle, the store, the writer and its drive, is the pipeline
of the writer's input, and the operators inside it stay in pull mode. An induction loop runs in
rounds ([A loop in rounds](#a-loop-in-rounds)), and its store steps once per round; a loop nested in
it runs as a scope inside that loop's scope, a row of its store per round. A cyclic `FanOut` holds
its store in a cell of its own (`Inner::Store`, `tile_operators/fanout.rs`) and hands the store a
`Cycle` when it subscribes it (`TileProducer::enter_cycle`). The call that steps the store holds the
store's cell, so the recurrence's pull of the store finds the cell borrowed and is answered from the
snapshot the store published after its previous step.

A store's input is what a morsel names: an induction store's body, its decision stream, whose
positions are the loop's, and a transaction store's input 𝑘, writer 𝑘's source, whose positions are
its items. `consume_impl` steps the store until the input has released the morsel. Before each step
the store has the operators inside its cycle read again (`read_cycle_again`, `commit_operator.rs`):
every producer in its chain on a path to a recurrence slot of its fan-out reads that input again at
its next pull (`TileProducer::read_again`, through `read_again_toward`). A `Memo` there reads every
region again, as after a notification of `Everything`, and a drive reads its source again where that
input is on such a path. The store then clears its gate, as a pull does
(`ProducerBase::clear_gate`): no pull of the store clears it while the store steps itself, since a
read through the recurrence is answered from the snapshot. After the step the store publishes its
snapshot (`Cycle::publish`). A store is queued a morsel only for positions its input can release, so
a step that changes neither the store nor its input's release panics, and so does a store not
terminal at the run's last epoch. A transaction's deny commits nothing and progresses through its
source's release alone.

An induction store holds everything once it is terminal and nothing before, since a reader pulls the
store tile, which `restrict_to` cannot cut to part of its positions, and it pushes once, at the
finish where it is terminal (`pushes_while_consuming` answers `false`). A transaction store holds
the commit ticks it has decided, through its watermark (`store_frontier`), and everything once it is
terminal, and it pushes the ticks each consume decides (`pushes_while_consuming` answers `true`). A
store pushes to its reader slots and not its recurrence slots (`FanOutInput::push`), and every
reader pulls the store whole. `StoreValueStream`, a reader of a transaction store's changelog, keeps
the store's keys and cuts its answer to the ticks a pull names, so a feed inside a transaction takes
the ticks as they are decided; any other reader widens the push, so its pipeline takes a package of
the store only once the store's pipeline has finished the epoch ([The dispatcher](#the-dispatcher)),
or, over a live source, once every epoch has run. A store's `final_guard` is `held()`. A release of
a store with no rows above it names the positions a reader reads no more and removes nothing from
the store tile; a nested store's offer cuts the rows its readers released ([A loop in
rounds](#a-loop-in-rounds)). A consuming store answers a pull from its snapshot. A store placed
in a pipeline (`ProducerBase::is_placed`) answers a pull before its first consume with the unopened
store, which states nothing final, and steps nothing: it steps only at its pipeline's consumes, and
a transaction store's writers decide only against a tile it published. A store no planner placed
steps itself at a pull, as pull mode does.

In pull mode an induction store releases its body whole once the body is terminal and every decision
is stepped, and a transaction drive releases its source whole once it is done. A nested induction
drive releases each row of its source it calls complete, in either mode. A consuming nested store
releases its body a position at a time, and whole each row the body calls complete once its every
decision is stepped, at every level above its positions: the release through the decided path names
the row's positions only, not its paths past the last of them. A consuming store wakes no reader
outside its cycle: its readers there take the rows it closes from its pushes, and the planner
refuses a store read inside the cycle of a store that steps itself (`Planner::beneath_cycle`). A
seed sits behind an entry no planner places (`subscribe_pulled`), since the store reads it by pull
at a step, so a push from beneath the seed stops there rather than climb to the store's readers. A
drive with no rows above it states complete every position below its next one that its source calls
complete along with every position before, so a position it reads past, one the source filtered out
or holds nothing at, is stated as one it emitted (`complete_prefix_below`). An induction store with
no rows above it releases its body through what the body states complete and holds no decision at,
and a transaction drive releases its source through what it has read past, so either releases such a
position without waiting for a later one to be decided. The dispatcher's finish checks that a
store's input released every morsel the pipeline consumed.

`run_program` plans a store's pipelines where it reaches a reader slot of the store's fan-out
(`TileProducer::store_read`), one per input, numbered one after another. The pipeline of an input
reads the pipelines beneath the store's cycle under that input: a subtree that reaches no recurrence
slot of the store (`reaches_recurrence`) is planned as any chain is, and inside the cycle a breaker
is no pipeline. A store's pipelines are ordered, since a store decides its positions in order. A
store that steps itself runs in the run's dispatcher, and the pipeline of an input that reads
pipelines reads the input whole; an induction store runs in a loop's scope instead ([A loop in
rounds](#a-loop-in-rounds)). A reader of a store reads every pipeline of it, so its queue in an
epoch closes once the last of them has finished the epoch. The pipelines of one store share one
record of what the store has pushed (`Dispatcher::share_pushes`), so no tick is pushed twice, and
`plan_edges` plans their edges into one reader as one: a stream edge whose pushes name no key twice,
or a widened edge from each of them. The planner refuses:

- outside a loop's scope, a nested store, one per enclosing row, whose frontier a flat morsel does
  not name, and a store whose seed reads a pipeline;
- a store inside the cycle of a store that steps itself, which no round reaches;
- a transaction store of several writers whose sources' positions are not `UInt` positions, which
  key order cannot compare.

The planner asserts that a transaction store has a writer: its keys are the footprints of its
`with begin():` blocks, each one of its writers
([How many commit stores a program has](../ccl/design/mutability.md#how-many-commit-stores-a-program-has)).

#### Commits in key order

A consuming transaction store commits in key order. Pull mode commits in the order
`CommitProducer::drain` attempts proposals, writer by writer from a start that rotates each pull.
The key of an item's decision is `(𝑝, 𝑤)`: the source position 𝑝 of the item, then its writer's
index 𝑤.

The store, its writers and their drives speak through tiles only. A transaction drive's body-input
row carries its item's source position after the read slots and the item (`item_position_field`,
`_{r+1}`), which inference types as the last component of the body's domain
(`transaction_body_domain`, `src/ccl/infer/emit.rs`); the body reads no position. The writer copies
it into its proposal, whose record is `{snap, reads, writes, pos}` (`proposal_stream_tiling`).

A drive's output and a writer's proposal stream are each a record of two fields
(`transact_stream_tiling`): `rows`, the rows above, and `decided`, a collection over the source's
positions that holds no key. Its domain predicate states how far the drive has decided its source:
every position through the last item acked or read past, and every position once the source is
exhausted (`decided_tile`). The drive states it on every pull, row or none, and the writer forwards
the statement it last read. A decision made again for an item the store names adds no key to the
collection, so the statement only grows. The body reads the drive's rows through a `SelectField`,
and the releases of either stream name its rows. From its first step a consuming store states, per
writer, what it says of the decisions it took (`WriterTakes`, the store tile's `writer_takes`):
`settled`, the highest item whose decision has committed or stood with every item of the writer
below it, and `again`, the items above it whose decisions went stale. Both grow by join. The drive
and the writer read them through the store's recurrence. A store in pull mode and an induction store
state none.

A step of the store toward input 𝑘 pulls writer 𝑘 and takes each proposal it brings into the
store's queue for writer 𝑘, keyed by its `pos` (`CommitProducer::take`). The take is a release of
the proposal's step to the writer, which acks its attempt, so the drive releases the item from its
source and moves on to its next item. Where the store states `writer_takes`, the writer hands a
decision that proposes nothing, a deny or a grant that writes nothing, to the store as a proposal
that writes nothing rather than acking it itself; the store holds it with the frontier it was made
against (`Held::Local`). From then on the drive keeps a copy of every item it acks, since the
decision the store holds may need making again, and drops the items at or below `settled`. Input
𝑘's release is its source's: the items the store holds a decision for or has committed, and those
the drive read past. A pipeline's finish rests on that release alone, and a step that only takes a
decision progresses through it.

After each take the store commits while the least key among the held decisions, `(𝑝, 𝑤)`, may
commit: once every other writer has passed 𝑝 or is terminal (`CommitProducer::commit_in_key_order`).
A writer has passed 𝑝 where its proposal stream states 𝑝 decided, or where the store has taken its
decision for an item at or past 𝑝, since a writer decides its items in order
(`CommitProducer::passed`). The stream states what its drive had decided when the writer was pulled,
which is short of the decision the same pull brings. A proposal commits where the engine validates
it. A decision that proposed nothing stands where nothing has committed since it was made, since the
store holds no read set for it. A decision that neither commits nor stands keeps its key. The store
names the item in the writer's `again`, publishes its state, pulls the writer, and takes the fresh
decision before anything with a larger key commits (`CommitProducer::drive_again`); a pull that
brings none panics. The drive emits an item `again` names, from its kept copy, ahead of its next
item. Its window holds no row then: a pull of a writer decides the row its drive emits in that pull,
and each decision is taken in the pull that makes it. The fresh decision is made against the store
as the engine holds it and is the least key, so it commits or stands in the same pass: `again` names
at most one item of a writer, and none once the pass ends, which the pass asserts. A writer decides
only against a published tile that states `writer_takes`, since the store publishes none only before
it opens, when no writer has a frontier to decide at. `take` asserts it of every decision it takes;
a deny a writer acked itself against a tile with no `writer_takes` never reaches the store, and
nothing checks for one.

The store reclaims its changelog where every slot of its fan-out has released it
(`CommitProducer::release_impl`), and a held proposal is in no slot's window, so the reclaim stops
strictly below the oldest snapshot of a held proposal, in every build. The store then still answers
the proposal's reads at its snapshot, which `attempt` checks in a debug build; staleness reads each
key's latest change, which no reclaim drops.

A writer whose live source is idle holds back the commit of every larger position, and the store's
queues and the drives' kept items grow with each decision the other writers make meanwhile. The
changelog behind the oldest held proposal stays too, so it grows with every commit meanwhile.

A transaction store finishes an epoch of an input as any breaker does, pushing what it has decided.
It counts the inputs that have finished the run's last epoch, and the last of them settles the store
(`SteppedStore::settle`): it takes what each writer still decides and commits every held decision
in key order, until a pull of every writer brings nothing. That pull finds each writer terminal, so
the store is terminal, which the finish then checks.

A drive releases an item from its source at the take rather than at the commit. A drive that takes
over a running program starts where the source's release says
([program-evolution.md](../ccl/design/program-evolution.md#where-a-producer-registering-now-starts)),
so it would skip an item whose decision a store held uncommitted. A dispatched run runs no program
that another takes over ([Running a compiled program](#running-a-compiled-program)), and a
resuming drive under a store that states `writer_takes` panics at its first pull.

### The dispatcher

`Dispatcher` (`src/interpreter/dispatcher.rs`) holds the graph of pipelines, which pipelines each
one reads and so which one reads it, a window of epochs in flight, a queue of work packages per
pipeline per epoch, and the morsel size `morsel_rows`. A work package is a pipeline, a guard for its
breaker to consume, one morsel of at most `morsel_rows` held rows, the epoch it belongs to, and the
package's index in the pipeline's queue for that epoch. The dispatcher holds no breaker: the driver,
`run`, reaches each breaker, with the input of it the pipeline consumes, through a handle its caller
passes, indexed by pipeline, and borrows it for one call at a time.

`Dispatcher::new` refuses a zero morsel size, a graph with a cycle, and a pipeline that reads one
pipeline twice. A pipeline may read several pipelines, and its queue in an epoch closes at the
finish of the last of them. A work package is a guard of the breaker's own input, whichever
pipeline's push queued it. Several pipelines may read one. The release of one reader would remove
rows from the breaker's state that another has still to read, so readers of one pipeline need a
`FanOut` between them, which the dispatcher does not check.

A source pipeline, one that reads no pipeline, is queued the regions of its breaker's input that
have arrived. `Dispatcher::notify` queues one such region in the current epoch, cut every
`morsel_rows` positions where it names finite runs of positions (`Value::UInt` keys) and whole
otherwise. `Dispatcher::close` says no more of the source's input arrives. A pipeline that reads
pipelines can also take arrivals (`Dispatcher::take_arrivals`): it is notified, sealed and closed as
a source is, and its queue in an epoch closes once both the epoch's seal and the finishes of the
pipelines it reads have happened ([Reading rows again](#reading-rows-again)).
`Dispatcher::start_source` queues the input whole and closes the source: where the input's tiling
states a finite range of positions for its outermost keys (a `UIntRange`), the dispatcher cuts it
every `morsel_rows` positions, the last morsel open above. Any other input starts as one package at
its universal guard: a sparse source's keys are not known before it is pulled, and enumerating them
is not built. `Dispatcher::limit` caps a source's packages queued and not acknowledged, in every
epoch: `notify` waits while the source has that many outstanding, and `try_notify` answers that it
did not queue. A notify admitted below the limit queues every morsel it cuts, so the packages
outstanding pass the limit by at most one notify's morsels less one, for one thread that notifies. A
notify returns once the run fails, having queued nothing.

`run` starts every source whole, so its run is one epoch. It consumes the package at the front of
the lowest pipeline's queue that has one. When no pipeline has one, it finishes the oldest epoch's
lowest pipeline that may finish it, and it stops once every pipeline has finished the last epoch.

`Pushes::push_final` pushes what a breaker has decided and its pipeline has not pushed before, its
final guard less the region pushed, one package per morsel the breaker cuts it into
(`BreakingProducer::morsels`); a breaker no pipeline reads cuts nothing. The dispatcher keeps each
breaker's pushed region across epochs, which the pipelines of one breaker share
(`Dispatcher::share_pushes`). A push computes the difference and grows the region in one
step under that region's lock, so two threads pushing for one pipeline push disjoint regions, and a
push, after a consume or at an epoch's finish, pushes only what no earlier push did. The driver
lands a push made after a consume at once (`Dispatcher::land`), before it acknowledges the package,
so a reader may claim it while the pipeline runs; the finish lands its own push and closes the
queue of each pipeline that reads it, where every other pipeline that one reads has finished. A
breaker whose output is one value, `Aggregate`, `ExtractAggregate` and `ExtractFinal`, pushes one
morsel. `Memo`, `MapAggregate` and `Converse` cut
at the outermost keys they hold, in key order (`cut_at_keys`): a cut falls before every
`morsel_rows`-th held key the guard names, the first morsel reaches down from the guard's lower end
and the last is open above. The morsels partition the guard exactly. A key the breaker states absent
rides in the morsel that covers it, so the releases of a reader's input at its morsels add up to the
whole guard, and a reader that is final once its input is released whole, such as `Aggregate`,
becomes final. A released key is in no morsel, because the final guard already excludes it. A guard
naming no more than `morsel_rows` held keys is one morsel. A package is a guard of the reader's
input tiling, as the reader's chain restates the morsel, and `run` asserts in a debug build that a
package fits its breaker's input.

A push lands by climbing the breaker's consumer (`ProducerBase::downstream`) one morsel at a time,
as a projection of the breaker's keys at any level (`Consumer::push`). Each consumer between two
breakers restates the region in its operator's keys, as it restates a notification ([The
notification contract](#the-notification-contract)), and passes it on: a fan-out to every live slot,
a tagged union under the arm's tag. No gate holds a push back, since every pushed region is a work
package, and a consumer that pulls ignores it, so a push wakes no one. The `dispatcher::Entry` at
the input of each breaker the push reaches queues the region, as a guard of that breaker's input
tiling, for the breaker's pipeline in the epoch, less what is queued for that pipeline there
already. The difference and the queue's growth are one step under the queue's lock, so a push that
reaches a breaker along two paths, as a filter reads one memo for its values and its predicate, is
queued once. A push an operator widens to `Everything` on its way fails the run at a reader that
reads that pipeline's pushes (`Landing::widened` marks the path, `Landing::queue` refuses it), since
the reader could not tell which of its keys it names: a reader reached that way reads the pushing
pipeline once it has finished, instead of its pushes. A reader that keeps open rows reads again
every open row such a push reaches it with ([Reading rows again](#reading-rows-again)). A push that
re-enters a consumer it is passing through has met a cycle, and fails the run too. A compiled
program's dispatched run notifies no consumer: a producer that caches what it reads reads it again
where a store steps or a live source yields more (`TileProducer::read_again`), and a debug build
checks that no consumer is notified inside the run (`dispatcher::in_a_run`). `notify`, its gates and
`WakeupQueue` stay for pull mode.

`dispatcher::finish_epoch` finishes a pipeline's oldest unfinished epoch. It asserts six invariants
before it calls the breaker: the pipeline has not begun to finish the epoch, its queue there is
closed and empty, no package claimed for it there is in flight, every pipeline it reads has finished
the epoch, the epoch is sealed or known to be the last, and its breaker's input has released every
guard the pipeline consumed in the epoch. A pipeline that keeps open rows may leave rows unreleased
until the run's last epoch ([Reading rows again](#reading-rows-again)). The release check is closed
over the input's tiling (`TileGuard::closed_over`): an input that released a row through the last
position of its finite range of positions has released the row, though the difference of the two
guards names the row's paths past that position. A source's input releases the regions queued for
it; a reading pipeline's input releases only what the guards pushed or queued at the start for it
name, and nothing at all when nothing was; a pipeline that reads its input whole releases all of it.
A debug build also asserts that the morsels of a pushed guard partition it (`partition_gap`), and
that a pipeline consumes each region once in an epoch: a guard pushed to a pipeline meets none
pushed to it before. A package of open rows read again is the one exception.

The dispatcher reads a breaker's input `input` through `input_tiling` and `input_released`, the
tiling a package's guard is a guard of and the guard the breaker has released of that input, so a
breaker whose input sits inside a shared cell can answer both.

A dispatcher run delivers no wake-up queued on the scheduler. A breaker's reader learns of what it
holds through the push, and a producer's notifications queue on the scheduler as in pull mode
(`WakeupQueue`), to be delivered by a scheduler that pulls the program afterwards.

Nothing calls the dispatcher or the breakers' methods outside unit tests, and no scheduler runs
pipelines.

#### Running a compiled program

`dispatcher::run_program` (`dispatcher/plan.rs`) runs a compiled program's pipelines on the calling
thread. It walks the producer chains under the program's sinks and `main` outputs with
`TileProducer::visit_input_producers_mut`, the mutable twin of `visit_input_producers`, and takes
each producer whose `as_breaking_mut` answers one as a pipeline breaker. A breaker's pipeline reads
the pipelines of the nearest breakers beneath it, which are numbered before it, and the walk places
the `Entry` at the breaker's input in the pipeline. A breaker's operator installs that entry when it
subscribes its input (`BreakerInput`), and keeps the consumer it was subscribed with as the one it
pushes to; a store and the induction drive build their entries themselves, since each shares its
consumer with other inputs, a store's with its seeds and the drive's with the store, and a range
(`IterateExtent`) keeps its consumer too. A producer is identified by its address, since
`producer_id` counts per producer type. A breaker a second reader reaches keeps its pipeline, and a
reader that reaches one along two paths, as a filter reads its input for the values and the
predicate, reads it once. A pipeline that reads directly a pipeline another pipeline reads is
refused, since only a fan-out slot keeps one reader's release from removing what another still
reads. A store is the breaker of a pipeline per input, and a loop's scope of a pipeline of its own
([A store as a breaker](#a-store-as-a-breaker), [A loop in rounds](#a-loop-in-rounds)), which the
walk plans where it reaches a reader slot of the store's fan-out (`TileProducer::store_read`).
Each package reaches its breaker by walking the chains again, and the pushes a call makes land
once the walk has returned, since a breaker reached through a fan-out slot is called while the walk
holds the fan-out its push climbs.

Before the run, the planner reads each edge from a pipeline to the pipeline that reads it off the
consumers between them (`Consumer::route`). Each consumer declares how it passes a push on without
any region being pushed: a consumer that keeps its operator's input's keys passes the route on, a
tagged union's arm passes it on under the arm's tag, a widening consumer marks it widened
(`Routes::widened`), and the `Entry` of a placed breaker records its pipeline. Where every path to
the reader's entry keeps the keys, or the pushing breaker holds one value, whose push is
`Everything`, the reader is queued the rows the pushes name: a stream edge. Where a path widens
them, as a lookup's table reaches its reader, a push names every row of the reader's input: a
widened edge. Its reader keeps open rows and reads them again at the push, and takes its rows from
its other edges and from a region queued at the start. So does a reader with two stream edges whose
pushes can name one key, as the output's memo reads two aggregates of one binding
([Reading rows again](#reading-rows-again)). A reader reads its input whole once every pipeline it
reads has finished (`Dispatcher::read_whole`) where a pipeline it reads pushes along no route to
it, or where no stream edge and no region queued at the start names a row of its input. Which region
of the reader's input a push names comes from a probe: the read pipeline's breaker pushes
`Everything` through its consumer into a landing that records what reaches each entry instead of
queueing it (`Landing::probe`). A widened edge is probed so, and so is each range under a reader of
pushes, such as the positions of a literal arm of a concatenation. A constant keeps no consumer. A
constant whose keys a reader consumes is one of four kinds, and none brings a key the ranges and the
pushes do not name:

- a list literal's table, the function operand of a `MapResult` over the literal's positions
  (`IterateExtent`), so the positions bring every key the table would;
- bound by a `let`, beneath the binding's `Memo`, whose pipeline is a source and reads its input
  whole;
- empty, which brings no key;
- a scalar, which has one position, so any push to its reader names all of it.

`run_program` refuses, in a debug build, a constant collection beneath a reader of pushes that is
not a function operand. What those probes bring, less everything the stream edges' pushes can
name, is queued for the reader at the start of the run as one region
(`Dispatcher::queue_for`).

Each sink is the breaker of a pipeline of its own (`SinkBreaker`), planned after the pipelines its
producer's chain reads and read by no pipeline. The walk places the sink's `SinkConsumer` in that
pipeline, so a push that climbs to the sink queues there a guard of the sink's producer's tiling,
as an `Entry` queues one of its breaker's input. A `SinkBreaker` consumes a package by pulling the
sink's producer at the package's guard, handing the answer to the `DataSink`, and releasing the
producer at what the answer states. Pull mode makes the same pull, hand-off and release at the
universal guard. The sink's pipeline is not ordered: a tile carries its keys, and a `DataSink` takes
each answer by key, as `TestSink` merges it and the HTTP sink answers each request by its index. A
package's answer states only its own region complete, so it is terminal only where the package is
the producer's whole input. A sink is done once its producer is released whole, however many
packages that took. The run ends with one pull of each sink, as pull mode's last: the producer
answers from what its breakers consumed and is released whole, so the pull hands the sink nothing
new and finds it done (`DoneNotifier::signal`), which fires `CompiledProgram::done` once every sink
has. The pull closes its answer's outermost statement over the producer's tiling
(`Tile::closed_over`): an answer assembled arm by arm of a tagged union, as a sink fed from two
sites is, states each arm complete on its own, and only the closed statement reads as terminal.

A `main` output's producer is the driver's to pull. The run takes it into a slot and makes it the
root of a sink's pipeline, and hands the producer back after; a program has at most one. The compile
subscribes the producer to the driver's consumer behind an unplaced `Entry`
(`CompiledOutput::main_entry`), which the walk places in that pipeline as it places a sink's
`SinkConsumer`. A push that climbs to the `main` output therefore queues a guard of the producer's
tiling there, and the pipeline plans its edges and its live sources as a sink's does: a map over a
live source at the `main` output is notified of each delivery's keys. The pipeline's `SinkBreaker`
(`SinkBreaker::per_epoch`) hands the `DataSink` the caller passes `run_program_into` one answer per
epoch, at the pipeline's finish of it: the answers of the epoch's packages merged with a pull of the
producer at the universal guard. That pull adds no key, since the epoch's packages consumed all the
producer holds, and states what the producer states complete, so the answer is the one a pull in
pull mode makes once the epoch's arrivals have reached it. The pipeline is ordered
(`Dispatcher::order`), so it consumes an epoch's packages after its finish of the epoch before. The
run's last finish answers a terminal tile, as pull mode's last pull does. `run_program` passes a
`DataSink` that merges the answers (`Collected`) and answers the merged tile (`Run::main`). The
driver holds the producer, released whole, once the run returns.

The run pulls only the breakers' inputs. The program is compiled with
`GlobalContext::defer_sink_pulls`, which leaves out the pull each sink takes once subscribed, and
`CompiledProgram::sink_pulls_deferred` records it. The planner refuses, before anything runs, with
a `Refused` error that names the shape, and pull mode runs every refused program:

- a program compiled with its sinks pulled;
- a live source whose arrivals reach no pipeline's entry or reach one beneath its outermost keys
  (below);
- a pipeline notified of a live source's arrivals beside a range no live source yields, or beside a
  pipeline it reads whose pushes arrive as its own keys, since no arrival names those rows, or whose
  pushes reach it nowhere, since no push would name a row waiting on it;
- a store or a loop's scope that reads a pipeline beside a live source (below);
- a pipeline read directly by a pipeline another pipeline reads;
- a breaker with no consuming mode (`Breaker::no_consuming_mode`): a transaction store of several
  writers whose sources' positions are not `UInt` positions;
- the stores [A store as a breaker](#a-store-as-a-breaker) lists;
- a loop nested in another whose rounds pull an operator beneath the outermost keys that restates
  no projection there ([A loop in rounds](#a-loop-in-rounds)).

A range over a live source's domain (`TileProducer::data_sources`, an `IterateExtent` over a
`DataSourceDomain`) is no range the run queues whole at its start. The pipeline that stands for it
in the run's dispatcher is live (`Planned::live`), and the run notifies it of what the source yields
in one of four ways (`LivePipeline::poll`):

- Every route from the range's consumer to the pipeline's entry keeps the range's keys
  (`Consumer::route`), and a push of one key reaches the entry as a guard of the input's outermost
  keys: the pipeline is notified of the keys each delivery adds, as the region a push of them
  brings its entry.
- A route widens the keys, as a feed `out << 𝑒` widens its source's keys, which sit beneath the
  sink's one row: the pipeline reads its input whole once every live source under it yields
  everything (`Planned::whole`). The widened pushes of several ranges, as of a sink fed from
  two sites, name their parts of the input together.
- The range is read inside a loop's scope, whose pipeline stands for every pipeline inside it
  (`Planner::members`). Where the range's routes reach the scope's own drive keeping its keys, and
  a push of one key reaches the drive as that key, the scope is notified of each delivery's keys as
  positions of its rounds. Where it reaches no drive of the scope, the source is
  read inside a loop nested in it, whose rows end only once the source yields everything, so the
  scope reads its input whole then, as pull mode waits for each row.
- The range is read under a writer of a transaction store, whose source is the input of the
  writer's pipeline, read behind an entry no planner places: that pipeline is notified of each
  delivery's keys as its items.

A drive and a transaction store decide positions in order, and a debug build checks that a delivery
adds positions after every one before it. A dispatched run delivers no notification: a loop's scope
has its drive read its source once the drive has emitted every position it read, and a delivery to a
transaction store has its writer's drive read its source again (`Breaker::read_source_again`). A
package of positions the drive emits none of, such as the delivery that completes a source or one of
keys a filter on its source drops, runs no round of a position; the scope runs a closing round at
the package, queued to every inner pipeline but the sources in the store's chain, which has them
read what the drive read past, and the store's step releases the package. A pipeline whose chain
reads a live source and a pipeline takes the source's arrivals beside the pushes of the pipelines
it reads, and keeps open rows ([Reading rows again](#reading-rows-again)); a store or a loop's scope
that does is refused.

The run starts the other sources whole and then polls: each pass asks every live source for new data
(`DataSourceDomainExtentImpl::check_for_new_data`), notifies each live pipeline of the keys its
sources yield beyond what it was notified of (`get_yield_predicate`), and seals the epoch where it
notified one and one is still open. A live pipeline closes once its sources yield everything, and
the run ends with the epoch the last one closes in. A pass that finds nothing new calls the caller's
`on_idle` after running what is claimable (`run_program_polling`): `run_program` sleeps for a
millisecond, and a test feeds the source there. A range reads one source, keyed by positions: the
planner refuses a cross product of sources, a source beside a static extent, and a source with other
keys, whose arrivals no region of one source's positions spells.

The binary runs a program dispatched where `CAMBRA_DISPATCH` is set and not `0`, and neither
`--inspect` nor `--control` is given, at morsels of `CAMBRA_MORSEL_ROWS` rows (1024 unset; a value
that is no positive count panics). It prints each epoch's answer of the `main` output where the
answer holds a key or a value or is terminal, as pull mode prints each pull's answer: a collection
cut into several morsels prints once, and a map over stdin prints each line's answer as the line
arrives. A refused program runs in pull mode after a note on stderr, in the context the dispatched
run compiled it in: the compile has opened its sources and sinks, a port bound or stdin taken, which
a second compile could not open again.

`tile_operators/program_run_tests.rs` checks that the run releases each sink's producer whole, that
it finds every sink done, that a pull of each sink afterwards reaches no producer beneath a breaker
and changes no sink's value, and that each program answers what pull mode answers. Every program
of the differential suite (`tests/it/differential_interp.rs`) runs dispatched too, at morsels of
one row and of every row, and answers what pull mode answers, or the planner refuses it as
`tests/it/dispatch_refused.txt` pins by test name. `tests/it/dispatch_cli.rs` runs the binary both
ways.

#### Reading rows again

A pipeline keeps open rows (`Dispatcher::keep_open_rows`) where its chain can answer nothing for a
row it consumes. An operator that reads a sibling input does not answer a row from that input before
it is final: `MapResultToConst` answers no row while its scalar constant is not terminal
(`empty_beneath_live_rows`), a binop combines only the positions both operands hold, `CheckedLookup`
answers a missing key only once its table is terminal, a `VariantWrap` emits a collection payload
only once it is whole, and `ExtractFinal` answers once its source is terminal. The answer names
nothing of such a row, so the breaker's input does not release it, and the row is open: consumed,
and not released by the input.

Each consume of a pipeline that keeps open rows records the rows of its package that the breaker's
input has not released after the consume (`Dispatcher::end_read`, `OpenRows`). A push or an arrival
to the pipeline queues, in its own epoch, the open rows its region names as one package read again,
and those rows leave the record. A push widened on its way names the whole input. A push that is
not widened, to a pipeline that takes no arrivals, also queues fresh what of its region no queue of
the pipeline held before, in any epoch (`OpenRows::queued`), so a key two stream edges name is
queued fresh once. A pipeline that takes arrivals is queued fresh only its arrivals, since a push
can name rows that have not arrived. A package read again consumes only its rows the input has not
released (`consume_with`). Each finish removes from the record what the input has released
(`settle_open_rows`), and at the run's last epoch a row still open fails the run. The pipeline
finishes its epochs in order (`Dispatcher::ready`).

A consume records itself in flight before its breaker consumes (`Dispatcher::begin_read`). A push
lands after its pipeline decided the region it names, so a consume that begins after the push reads
that region final. A push that names the package of a consume in flight holds the pipeline's queue
in the push's epoch open, as one more event its close waits for (`EpochPipeline::unfinished`). The
consume's end queues there, as a package read again, what the push named of the rows the consume
left open, and then ends the hold.

The planner keeps open rows in a pipeline of the run's dispatcher in three cases (`plan_edges`):

- Its chain reads a live source and other pipelines (`Dispatcher::take_arrivals`). It takes the
  source's arrivals, and its queue in an epoch counts the seal as one more event. It is queued no
  start region and reads nothing whole.
- A route from a pipeline it reads widens that pipeline's keys, so the pipeline's push names every
  row of its input, as the group-by's memo reads its input's memo (`a_group_by`).
- Two of its stream edges can push one key, as `sum([x * n for x in xs])` reads the list's memo and
  `n`'s sum (`a_comprehension_reading_a_sum`). A key consumed at the first push before the other
  pipeline decided it is read again at the other's push.

No reader waits for a pipeline it reads in the run's dispatcher: a row it consumes before that
pipeline is final for the row is read again at the pipeline's push. A loop's scope keeps no open
rows, since a round consumes its inner pipelines' packages in order and runs once. Its planner
reads whole, in pull mode, a pipeline that would keep them ([A loop in rounds](#a-loop-in-rounds)),
and orders two edges by the round instead (`Dispatcher::follow`): a nested loop's scope takes a
round's row only once the pipelines its rounds pull have finished the round, and a reader of a
nested loop's scope, which pushes its store only once it is terminal, takes its packages only once
that scope has finished the round.

A row left open beneath its outermost keys is not read again correctly. A chain can refuse a pull
there, as `MapResultToConst` refuses a pull beneath the keys it restates
(`a_let_bound_map_over_a_live_source`), and a `Memo` that reads such a row again over a live source
holds and pushes only the keys the source delivered, not the positions past its last, so the
`MapAggregate` of `[sum([y * x for y in ys]) for x in [1, 2]]` never finds a row's group complete
(`a_reader_building_on_a_live_pipeline_reads_its_input_whole`).

`[x for x in source1() if sum([1, 2, 3]) > 5]` at `main` takes each delivery's rows as they arrive,
and a row consumed before the sum is final is read again at the sum's push. With `sum(source1())`
in its place, the rows of every delivery but the last are open until the last epoch, whose push of
the sum reads them again (`a_filter_over_a_live_source_reading_a_sum`).

#### A loop in rounds

An induction loop runs in rounds, one per position. The breakers inside the store's cycle are the
pipelines of a dispatcher of their own, which runs one epoch per position, and the store steps
after each epoch. `run_program` plans the loop's scope (`LoopScope`, `dispatcher/loop_scope.rs`) as
the breaker of a pipeline of the run's dispatcher where it reaches a reader slot of the store's
fan-out. The walk tags each breaker with the dispatcher it runs in, the scope whose cycle it is
inside or the run's, and a read between two dispatchers is a read of the scope's pipeline in the
run's dispatcher. The scope's input is the store's, and its pipeline is ordered and reads its input
whole. The store is the breaker of no pipeline, and its entry stays unplaced.

The drive (`InductionDriverProducer`) is a pipeline breaker, and its pipeline is a source of the
scope's dispatcher. A package names the position a round runs, and a consume emits it where the
store has decided the position before it, as a pull does. A consuming drive answers a pull from
what its last consume rendered, and wakes no consumer. The entry in front of its source stops a
push from beneath while it is unplaced; a round places it once the pipelines beneath the source
have finished. The drive's nested inputs sit behind entries no planner places. A consume of the
scope runs a round per position of its morsel that the drive emits, the next its source delivers
(`TileProducer::next_position`), until the store is terminal; a position the source filters out
runs none:

1. The store has the operators inside its cycle read again (`TileProducer::read_cycle_again`). Its
   last step pulled the operators in pull mode there before the pipelines they read took this
   position.
2. Each source is notified of the position (`Dispatcher::notify`), and the scope of each loop
   nested in this one is queued it (`Dispatcher::queue_for`).
3. The epoch is sealed, and the scope's dispatcher runs until nothing is claimable.
4. The store consumes the position, which one step decides and releases
   ([A store as a breaker](#a-store-as-a-breaker)).

A consume of the drive emits a position only where the package names its whole path at the
positions' level, so a round emits one position and a round at a row emits none; a pull in pull mode
emits the next position whatever it names. A consume at no position reads the drive's source and
emits nothing. A dispatched run notifies the drive of nothing. A consume of a scope whose store has
no rows above it has the drive read its source again once it has emitted every position it read and
the store is not terminal, at most once per consume; a consume of a nested row has it read at the
row's start and end. The first consume of the scope has the drive consume at no position, then steps the
store once, which opens the store at its seed and publishes it: the drive reads the open store
before it emits a position, and emits none outside a round. The scope pushes the store at the finish
where the store is terminal, to the readers of the store's fan-out.

The scope places its pipelines' entries only while it runs (`Placed`). A push into the cycle comes
from a pipeline beneath it, which has finished before the scope consumes, and stops at the unplaced
entry rather than queue for a pipeline of the scope's dispatcher. The scope reaches a breaker inside
the cycle by walking the store's chain with the store's cell borrowed, so a read of the store
through its recurrence is answered from the published snapshot.

A pipeline the scope's dispatcher would read whole, which happens only in the run's last epoch,
stays in pull mode, and its readers read the pipelines beneath it; the round has it read again.

A loop nested in another runs as a scope inside the scope of the loop around it: a pipeline of that
scope's dispatcher, with a dispatcher of its own for the whole run. A scope inside 𝑑 others runs its
rounds at paths of 𝑑 + 1 keys (`Projection::of_path`). The scope around it queues it each round's
position, a row of its store, once the pipelines it reads have finished the round, and a consume of
the row runs:

1. Before the row's rounds, the drive consumes at no position: the nested loop's source is read
   through pipelines of the scope around it, which take their packages from the dispatcher and
   notify no one.
2. A round per position of the row that the drive emits, each at the position's path.
3. A round at the row, which closes it. The drive consumes at no position again, and the row is
   queued to every other inner pipeline: a drive states a row complete only once the store has
   decided every position of it, and a consuming memo answers from what it read. The store's step
   then releases the row of its body whole.

A nested store releases its body a position at a time and each row it decides whole, at every level
above its positions. Its readers release its rows as they finish with them, so its offer cuts the
rows released since its last step from the snapshot.

The planner refuses a nested loop where an operator its rounds pull beneath the outermost keys
restates no projection at the level it is pulled at. The check runs once every scope is built
(`Planner::refusal_of_nested`). Its walk starts at each breaker a nested scope keeps, at the level
of its rounds, and passes each operator's level to its inputs as `TileProducer::input_level`
declares. It ends at every breaker that consumes, in any dispatcher, since that breaker's consume
pulls its inputs and its own scope checks them; a breaker whose pipeline its dispatcher would read
whole runs in pull mode and passes the pull on. A refused program runs in pull mode, and
`tests/it/dispatch_refused.txt` pins each one the differential suite holds.

`dispatcher/loop_scope.rs` tests the rounds of one scope, `dispatcher/plan.rs` tests the refusal's
walk, and `tile_operators/program_run_tests.rs` runs flat, guarded and nested loops, a loop nested
twice among them, against pull mode.

#### Epochs

An epoch is a part of the run: the regions notified to the sources between two seals, and everything
the pipelines consume and push because of them. `Dispatcher::seal` ends the current epoch: every
open source's queue in it closes, and later notifies land in the next. A source closed before is
closed in every epoch after its close. Once every source is closed, the current epoch is the run's
last, and a seal after it is refused. The threads that seal and close order every seal before the
last close: a seal that waits for its slot while the last source closes is refused too.

The window holds `window` epochs, four unless `Dispatcher::window` says otherwise, and at least two,
since a seal opens the next epoch while the one it seals is in flight. Each epoch has a slot of its
own: slot `𝑒 mod window` holds epoch 𝑒, every pipeline's queue, counters and phase in it, from its
opening until every pipeline has finished it. The finish that is the epoch's last retires it, and
the slot is swapped for a fresh epoch `𝑒 + window`. A seal opens the next epoch only once its slot
holds it, so it waits while the epoch a window before is in flight, and the window bounds what the
dispatcher keeps. A claim clones an epoch's handle under the slot's read lock, so a slot swapped
under a claim leaves that claim the epoch it read, which has nothing left to claim. A package in
flight keeps its epoch in the window, since an epoch retires only after every package of it is
acknowledged.

A pipeline moves through an epoch in three steps. Its queue there is open while appends land in it:
a source's notifies, and the pushes of the pipelines it reads, which land as those pipelines consume
and at their finishes. The queue closes at the epoch's seal or the source's close, for a source, and
at the finish of the last of the pipelines it reads, for a reader, which a count of the pipelines it
reads that have not finished the epoch tells. A pipeline that takes arrivals beside the pipelines it
reads counts the seal or its close as one more event, and one that keeps open rows counts each
consume in flight that a push in the epoch named ([Reading rows again](#reading-rows-again)). In a
loop's scope a reader takes a package in a round only once every pipeline it follows
(`Dispatcher::follow`) has finished the round, and takes no push of theirs
([A loop in rounds](#a-loop-in-rounds)). A claim hands out the pipeline's finish of the
epoch (`Next::Finish`) once the queue is closed, every package in it acknowledged, and the epoch
sealed or known to be the last; a compare and exchange of the pipeline's phase in the epoch picks
one claim. The finish pushes what the epoch decided and no consume pushed into the queues of the
pipelines that read it for the epoch, and closes the queue of each whose last pipeline read to
finish it is this one. A pipeline's epochs run in parallel and finish in any order, except that its
last epoch finishes after every earlier one, since the breaker's `finish` there, with `last` set, is
its last call. An ordered pipeline runs its epochs one after another: it has at most one package in
flight, takes it from the oldest epoch it has not finished, and finishes each epoch after the one
before. A pipeline that keeps open rows finishes each epoch after the one before too, and claims
from several epochs at once.

#### Claiming from several threads

`Dispatcher` is `Sync`, and a claim takes no lock beyond a read lock on each epoch's slot, which it
holds only to clone the epoch's handle. A pipeline's queue in an epoch is appended to while it is
open, and a closed queue takes nothing more. A source's queue grows at each `notify` and closes at
the epoch's seal or the source's close. A reader's queue in an epoch is filled by the pushes the
pipelines it reads land as they consume, and closed at the last of their `finish`es in the epoch,
since each finishes each epoch once.

A queue's slots sit in buckets that double in size, each allocated by the first append that reaches
it, so a slot never moves. An append reserves its indices together, by compare and exchange on
`reserved`, and then writes each slot, once. The top bit of `reserved` says the queue is closed, so
an append reserves only while the queue is open, and one read gives both the count and the close. A
claim reads a slot only once it is written. The queue keeps the region its packages partition under
a lock that appends and the move of the pipeline's epoch to finishing take, and a claim of a package
never does. Two counters per pipeline per epoch only grow: `claimed`, the index of the next package
to claim, and `acknowledged`, how many packages have been acknowledged. Each pipeline's phase in
each epoch (running, finishing, finished), a failure flag and the generation, the count of changes a
waiting worker waits on, are atomics too. A worker takes a lock only to sleep while there is nothing
to claim, and a change that can end a sleep takes it to wake the sleepers, only while there are
some. A pipeline that keeps open rows takes the lock on its `OpenRows` at its finish, at a push to
it and at the close of its queue. A seal and a close take a lock that orders them, since both move
the current epoch or close a source's queues. The graph, the morsel size, the window, the limits and
the ordered pipelines are fixed before the dispatcher is shared, since the methods that set them
take `&mut self`; every other method takes `&self`. The breakers stay `Rc<RefCell<…>>` and are not
`Send`. `run` claims on the calling thread, and nothing outside the unit tests in
`tile_operators/dispatcher_thread_tests.rs` drives the dispatcher from more than one thread. Those
tests run scripted work on up to 16 threads, plain data rather than breakers, except in one test
where each worker builds its own breaker over one atomic of held keys that every worker sets. Some
feed a source and seal its epochs from a thread of their own while workers claim.

A worker asks `Dispatcher::try_claim` what to do next, and the answer (`Next`) is one of five:

| Answer | The worker |
|---|---|
| `Package(package)` | hands the package to its pipeline's breaker, then calls `acknowledge` |
| `Finish { pipeline, epoch, consumed, last }` | finishes the pipeline's epoch, pushing through `pushes_in(pipeline, epoch)` and the breaker's `finish`, then calls `Dispatcher::finish` with the pushes |
| `Wait(generation)` | calls `wait(generation)` and asks again |
| `Done` | stops: every pipeline has finished the last epoch |
| `Failed` | stops: the run failed, whatever has not finished |

`claim` is `try_claim` and `wait` in a loop, and never answers `Wait`. A claim takes the package at
the front of the queue of the pipeline the worker prefers, where it may, and otherwise that of the
lowest pipeline whose queue it may take from, each pipeline's oldest epoch first. With no package to
take, it finishes the oldest epoch's lowest pipeline that may finish it. Single-threaded, with no
preferred pipeline, this is the order `run` follows, and a `Wait` there panics, because an acyclic
graph with every source closed and nothing queued has a pipeline that may finish.

A source pipeline may finish an epoch only once its queue there is closed and the epoch is sealed or
known to be the last, so workers may start claiming before the sources start: they wait until then,
and no source finishes before its input of the epoch has stopped arriving. A closed source refuses a
`notify`, a second `close` and a second `start_source`.

A claim reads `claimed`, and takes that index's package where its slot is written, by moving
`claimed` on with a compare and exchange. A claim that loses the exchange reads `claimed` again, so
no two claims take one package and none skips a package an append writes later: `claimed` never
passes `reserved`. A claimed package is in flight until the worker acknowledges it. `acknowledge`
refuses a package whose epoch the window no longer holds, whose index no claim has handed out, whose
guard is not the queued one, or that was acknowledged before, the last through a flag per package
that the first acknowledgement sets. A pipeline may finish an epoch when it is running in it, its
queue there is closed and every package in it acknowledged, and the epoch is sealed or known to be
the last. A claim reads the count and the close in one read, and nothing is reserved after the
close, so the count of a closed queue is its last. The counters only grow, so a pipeline that may
finish an epoch stays so until it does. Its packages there partition the region its queue was filled
with, and the finish gets that region as `consumed`: the regions notified to a source in the epoch,
its input whole in the last epoch for a pipeline that reads its input whole, or the union of the
guards pushed to the pipeline in it.

The claim that finds a pipeline that may finish an epoch moves its phase there from running to
finishing with a compare and exchange, so exactly one claim finishes each pipeline in each epoch.
`Dispatcher::begin_finish` makes the same move for the oldest epoch of a pipeline the caller names
and asserts each condition; `dispatcher::finish_epoch` calls it. A finish's pushes collect in its
`Pushes`. `finish` moves the pipeline from finishing to finished in the epoch with a compare and
exchange, so a second finish is refused, and then lands the pushes and closes the queue in the
epoch of each pipeline that reads it and reads no pipeline still to finish. A push after a consume
collects in a `Pushes` of its own, which `Dispatcher::land` lands at once. A reader claims the
packages landed there while the pipelines it reads run, and finishes the epoch only from a closed
queue. Its chain may therefore read the breaker of a pipeline it reads while that pipeline
consumes, which a driver on
several threads would have to order; the breakers are not `Send`, and `run` drives them on one
thread. `finish` asserts that the reader has not begun to finish the epoch, and dropping a `Pushes`
whose morsels never landed panics.

An ordered pipeline has at most one package in flight across its epochs. A flag per pipeline, taken
by compare and exchange before a claim of it looks and kept for the package it takes, admits one
claim at a time, and its acknowledgement drops the flag. Its morsels are therefore consumed one at a
time, in each epoch in the order they were queued.

The pipelines of a transaction store share its breaker, and each is ordered on its own, so two of
them may each have a package in flight. A consume of one takes from its writer and commits from
every writer's queue ([Commits in key order](#commits-in-key-order)), so a driver on several threads
has to serialize the consumes and finishes of one breaker's pipelines; `run` drives them on one
thread.

A claim reads the generation before it scans the pipelines, and one that finds nothing to do while a
pipeline has not finished answers `Wait` with that generation. The generation advances after each
change that can let a claim succeed: an append (`notify`, `start_source`, `finish`), a seal, a
close, an acknowledgement of an ordered pipeline's package, of a limited source's package or of the
last package reserved in a queue, a finish, and a failure. A change the scan missed therefore
advanced the generation past the one the claim answers, and `wait` returns at once instead of
missing it. `wait` sleeps on a `Condvar` under a `Mutex` that guards no data, counting itself as a
sleeper under that lock before it reads the generation. An advance writes the generation before it
reads the count of sleepers, and takes the lock to wake every sleeper only when the count is not
zero; all four accesses are sequentially consistent, so either the sleeper reads the new generation
or the advance wakes it. Waking every sleeper at each advance costs spurious wake-ups and needs no
choice of which one to wake. A `notify` waiting at its limit and a `seal` waiting for a slot wait
the same way.

`Dispatcher::fail` sets the failure flag and advances the generation: every claim from then answers
`Failed`, and every waiter wakes. A worker thread holds the handle `Dispatcher::worker` returns for
as long as it claims, and dropping that handle while the thread panics calls `fail`, so no worker
waits for a package the panicking one claimed and never acknowledged. A dispatcher method refuses a
caller that breaks the protocol through one check, which calls `fail` before it panics, so the run
fails with or without a worker handle. That includes a pipeline the dispatcher does not have. The
debug-build assertions on a breaker's morsels and on a `Pushes` finishing through its own dispatcher
panic without failing the run. After a failure, `acknowledge` and `finish` record nothing, and
`notify` and `seal` return at once.

Every claim reads the generation and writes the `claimed` counter of the pipeline it takes from, and
an acknowledgement writes `acknowledged`, so those cache lines move between the cores that claim
from one pipeline.

Claiming without a lock matters only for pipelines whose work packages are short. In one
measurement, it mattered below 1 ms of work per package. Above that, a package's own work hides the
dispatcher's cost, and the morsel size rather than the lock sets the overhead. The measurement ran
on 16 threads of an 18-core Mac, one pipeline in one-row morsels, with a scratch benchmark that is
not in the tree, so the numbers are a one-off record and no test checks them:

| Work per package | One `Mutex` | Lock-free |
|---|---|---|
| 1 µs | 188 thousand packages/s | 9.9 million packages/s |
| 100 µs | 89% of the ideal rate | 98% of the ideal rate |
| 1 ms | 98% of the ideal rate | 98% of the ideal rate |

A claim hands out a finish only when no package anywhere is claimable, so a pipeline ready to finish
an epoch waits behind the packages of every other pipeline, which delays its reader when the reader
is on the run's longest path. A reader starts on the first push of a pipeline it reads, which lands
after that pipeline's first consume, unless that pipeline pushes only at its finish
(`pushes_while_consuming`).

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
sit behind a `RefCell`: a fan slot's input and a `CycleSlot`'s contents both borrow for the extent
of the call. What an operator adds beyond its inputs — a constant's value, a variant arm's tag —
is `inspect_annotation`, so the two questions stay apart.

`inspect` follows `Value` edges only. A `Share` edge would draw the shared subtree once per slot,
and restricting to `Value` is also what makes the recursion terminate without a cycle guard, since
those edges are acyclic.

An edge is a **subscription**: the consumer holds the operator the edge names and calls `get` on it.
`notify` runs the other way along the same edges. Three properties ride each edge:

- **Kind.** `Value` for an exclusively owned `Box`, `Share` for a node several consumers may reach:
  a fan slot's edge to its fan input. The value edges form a forest, which is what lets a renderer
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
`tests/it/inspector_goldens.rs` pins the descent (`a_source_read_descends_from_an_iteration_of_that_source`).

**Serialization.** `src/inspector_model/design.md`, "A node on the wire" owns the payload shape. An
operator node ships its label, its tiling, and its `inputs`; a boundary node ships no tiling,
because only an operator has one. Where a walk of the pane begins is derived on both sides of the
wire from the edges rather than shipped, so no second channel can disagree with them.

| Operator | Input Tiling(s) | Output Tiling | Description |
|---|---|---|---|
| `Constant` | None | `Scalar` from `Constant::new`, `DataFunction(domain → Scalar(codomain))` from `Constant::from_bindings`, any tiling from `Constant::collection` | Produces a fixed tile. Which of the two a bindings table is cannot be read off the value: in function position it is one value the consumer applies (a list literal's table), and as a collection it is what a map iterates. Every operator below derives its tiling from its input's, so the choice decides whether a map transforms the table or each of its outputs — and the call site states it. |
| `IterateExtent` | None | `DataFunction(extent → Scalar(extent))` | Enumerates all values in an `Extent`, producing an identity-mapping function (domain = codomain = extent). Holds no input, so it is the root a data source is read from: it registers a wake-up against each source its extent reaches (`Extent::for_each_source`), and its tiling names them. |
| `MapResultWithSource` | `DataFunction(DataSourceDomain → Scalar(DataSourceDomain))` | `DataFunction(DataSourceDomain → Scalar)` | Looks up each key of a data-source domain via `DataSourceDomainExtentImpl::get` to produce a function from keys to their output values.  Built with paths (`MapResultWithSource::projecting`, from `Source(name, paths)`: an empty list reads the whole value), it returns the leaf at the one path, or the tuple of the leaves in the order named, and its output extent is that of the leaf or tuple. |
| `Zip` | `N` inputs of `DataFunction(shared_extent → *)` tilings |  `DataFunction(shared_domain → Record(_0, … _N))` | Merges N function operators that share a domain into one function whose codomain is a Record Tiling of all their codomains. Prefer the free `zip_arms_at` factory at op-conversion call sites: it dispatches to `Zip` (function-tiled arms) or `MakeRecord` (scalar arms) based on the compiled arms' tilings, since the same CCL-level `zip` maps to either tile shape depending on upstream `input`. |
| `MakeRecord` | `N` inputs at any tilings | `Record(name: input's own tiling, …)` | Builds a product value ([A product value is a record of tiles](#a-product-value-is-a-record-of-tiles)). Pulls every operand whole, and forwards each field's release to that field's operand. |
| `MapResult` | Function: any tiling of type `A → B`<br>Data: any tiling whose deepest codomain is `Scalar(A)` | The data's levels, then the function's below the one applied, over the function's codomain | Applies a function to the data's **deepest codomain**, element-wise. Application consumes the function's outermost level, and whatever sits below that level becomes further levels of the output, because a tile holds one flat level list. So a one-level function leaves the data's shape alone and changes only its deepest codomain, while the two-level lookup a keyed collection presents contributes its inner level: a collection of keys yields one group per key, and a `Scalar` key yields just that key's group — the single-key lookup `groupby(c, k)(v)`, one level shallower because the scalar contributes none of its own. A key absent from a *settled* grouping is the empty group; absent from an unsettled one it is simply not answered yet, which the function's `domain_predicate` distinguishes. A row whose key the function has not answered is **withheld** — dropped from the output, and its outermost-level owner subtracted from the output's `domain_predicate` — and answered on a later pull. The **data** input tracks the consumer's release; the **function** operand is re-read whole on every pull, so it is released only on a universal release. |
| `MapResultToConst` | `DataFunction(extent → *)` | `DataFunction(extent → C)`, `C` the constant's tiling | Replaces each value of a function input at the level op-conversion states with the same constant (or zips it in, per its mode), preserving the levels above it. A value at that level may itself be a collection, which the constant replaces or pairs with whole. A scalar constant must be present (terminal) before it can be broadcast: a still-absent one (e.g. a scalar read from a sibling induction loop that has not yet converged) yields an empty, non-terminal output rather than fabricating a value for the unknown positions. A collection constant streams: each row holds what has arrived of it and is left open until it is complete, and the constant is released once everything is. |
| `RecordWrap` | `DataFunction(… → T)` | `DataFunction(… → Record(name: T))` | The values of the input at one level as a one-field record, keeping the input's keys: `Zip` with one arm. `zip_arms_named_at` builds it for a record literal with one field over a collection; a lone scalar field is a `MakeRecord`. Forwards a release to the input, naming the field's part at its level. |
| `SelectField` | `Record{name: T, …}` | `T` | Hands back one field's tile, the eliminator for `MakeRecord`. Pulls the product whole, and releases what its consumer released of the field it selects and every other field whole (`guard_at_field`). |
| `Converse` | `DataFunction(domain → Scalar(codomain))` | `DataFunction(codomain → domain)` | Inverts a function operator: each codomain value maps to the list of domain values that produced it. |
| `Uncurry` | `A ⤇ B ⤇ C` | `{_0: A, _1: B} ⤇ C` | Flattens a collection of collections into one keyed by pairs: the two key extents pack into a record key and the values stand as they were. |
| `MapDomain` | `DataFunction(A → *)` | `DataFunction(A → Scalar(A))` | Replaces the codomain of a function with a copy of the domain values (identity codomain), producing an identity mapping from domain to itself. |
| `Filter` | Predicate: a function `A → bool`, or a collection over the input's levels down to some depth with `bool` beneath <br>Data: a collection holding at least the predicate's levels | Same as input | Keeps the entries the predicate maps to `true`, with their values. A function predicate is applied to the outermost keys. A collection predicate's innermost values are the mask over the keys at the level op-conversion states ([The level a node is converted at](#the-level-a-node-is-converted-at)), which is the predicate's innermost level, and `Tile::retain_keys` re-cuts that level's groups and leaves the levels above standing. Its mask is positional: an input holding nothing at that level passes through, and any other difference in count is refused. A deeper predicate filters the inner collections one outer key at a time: the survivors differ per key, which a correlated filter and a per-group filter (`sum([s.amount for s in g if s.qty > 2])`) produce. `filter_values` compiles to it, and under `map` it filters each element collection. A rejected key stays inside the region the output states complete, so a consumer's release of that region releases it from the input, and from the predicate when the predicate is a collection. An entry the predicate has not answered is withheld and stated incomplete (`Tile::withhold`). <br>TODO the function form can probably be replaced by Restrict |
| `Restrict` | Predicate: any tiling of type `A → bool` <br>Data: `DataFunction(A → *)` | Same as input | Filters a function tile by a boolean predicate: keeps only domain elements whose predicate evaluates to `true`. |
| `Aggregate` | `DataFunction(* → Scalar)` | `Aggregation` | Reduces all codomain values of a `DataFunction` input into a single running accumulator via an `AggregateKind` (e.g. Sum, Max, Min). Currently, the aggregation is hardcoded in the graph, but we could add support for aggregate-kinds-as-data |
| `ExtractAggregate` | `Aggregation` | `Scalar` | Extracts the final value from an `Aggregation` tile. Constructed with an `only_terminal` flag: when `true` it emits only once the aggregation is marked terminal (the `only_terminal: false` path is currently `todo!()`). |
| `MapAggregate` | `DataFunction(domain → codomain)` | `DataFunction(domain → Aggregation)` | Performs a per-key aggregation |
| `MapExtractAggregate` | `DataFunction(extent → Aggregation)` | `DataFunction(extent → Scalar)` | Extracts terminal per-key aggregation results from a `DataFunction(D, Aggregation)`, producing `DataFunction(D, Scalar)`. |
| `FanOut` | `*` | Same as input | Allows multiple operators to consume the output of the same operator. Each consumer subscribes via a `FanOut::slot()` handle; the fan-out forwards `get` requests and tracks the intersection of release guards across slots. Constructed via either `FanOut::new` (no cyclic-mode overhead — the common case) or `FanOut::new_cyclic` (for fan-outs whose slots feed back into their own input, e.g. a commit/induction store whose writer reads the store back before proposing, or a mutation-loop body whose other slot is wired to the cyclic prev-accumulator stream). Cyclic mode adds a per-pull tile-cache and a subscribe-in-progress flag so re-entrant subscribes / pulls skip redundant inner work and serve from the cached snapshot instead of re-entering the inner producer. |
| `Memo` | `*` | Same as input | Caches the output of an operator so it can be repeatedly read without recomputation. Releases each region as it takes delivery of it, so the input can clear its state; once the input is drained the cache is the sole source of the value. Release builds then skip the upstream pull. A debug build probes the drained input once after it drains and again after each notification of a region the pull reads, so an input that answers with released data trips the release-contract check at the input; probing on every pull would re-read a shared subgraph once per path to it. A `Memo` keeps a dirty region of its input, which starts as everything and takes each region the input notifies (`Arrivals`): a pull outside the dirty region answers from the cache and no pull goes below, in every build, apart from that probe, and a pull inside it reads the input and removes what it read. A `Memo` is also a [pipeline breaker](#pipeline-breakers): a consuming memo answers from its cache and pulls nothing. |
| `ExtractFinal` | two inputs: `source` (`DataFunction(D → Scalar(T))`) and `default` (`Scalar(T')` for any `T'` that `T` includes) | `Scalar(T)` | Extracts the final codomain value of `source` once it signals terminal.  When `source` is terminal but emits zero values (a stream that closed without delivering), emits the `default` scalar's value instead — keeping post-loop accumulators total.  Every emission is built at the **declared** extent `T`, not from the extracted value alone: a variant value carries only its own tag, so a column built from it would be width-narrower than `T` whenever the collapsed alternatives carry more tags between them — which is also why the `default` need only be *included in* `T` rather than equal to it (a conditional's trailing arm carries its tag and not its siblings').  Returns an empty scalar before `source` is terminal.  On the first terminal pull it releases both `source` and `default` universally — a final-consumer signal that propagates back through `FanOut`/`Memo`/mutation-loop bodies to the underlying data source. |
| `UnionOperator` | N inputs of `DataFunction(dᵢ → Scalar(C))` tilings | `DataFunction(Union(d₀,…,dₙ₋₁) → Scalar(C'))` | Merges N function operators into one. The domain is the discriminated union of the arms' domains, and the codomain is one the caller declares. The domain keeps the arms apart, and `final_or_default` dispatches on the arm a row came from. The codomain is the arms' join, because the arms are alternative values at one row. A union node is typed `D ⤇ V`, with `V` the join inference computed in the full type lattice, and op-conversion reads `V` off the node and passes its extent in. The operator does not join the operand tilings: `Extent`'s lattice has variant and range rules but no record rule, so it would join two arms at different record widths to an anonymous positional sum where the type is `{a: Int}`, a shape no row holds. Arms that agree on a tiling keep it, because a `Tiling` carries a layout (struct-of-arrays for a record) that an `Extent` cannot express. Arms whose codomain tilings differ must each fit in one column (`Tiling::is_scalar`: a `Scalar`, or a `Record` of such at any depth), and each is rebuilt as one column, keeping its own record fields, before the arms merge. Release is per arm: an incoming `Predicate::Union` guard splits into per-variant predicates, so one arm can be released in full while its siblings still produce. |
| `VariantWrap` | Payload: `Scalar(Pₜ)` or `DataFunction(D → Scalar(Pₜ))` | `Scalar(Union(P₀,…,Pₙ))` or `DataFunction(D → Scalar(Union))` | **Sum introduction — dual of `VariantProject`.** Wraps the payload under tag `tag`, so that arm holds the payload and every other arm is empty. Arms are keyed by [`FieldKey`], not by position: a tag's *position* is not stable under width subtyping (``{`b} <: {`a | `b}`` renumbers `b`), and an arm set is part of a union column's layout, so a position-keyed arm would need a renumbering coercion at every subsumption. A bare `Scalar` payload (a scalar `VariantCtor`) yields `Scalar(Union)`; a payload *stream* (a `VariantCtor` inside a lambda, `Builtin::VariantWrap(tag)`) is wrapped element-wise **preserving the domain** `D`, so the constructor composes as the RHS of a `≫`. Because the domain is preserved, a domain release forwards to the payload verbatim. A payload that is a collection is one value, held materialized in its arm's cell: an applied `VariantCtor` wraps its whole payload, and a composed one each row's. A cell cannot grow, so a row's cell is emitted once that row's collection is complete. |
| `VariantProject` | Scrutinee: `Scalar(Union(P₀,…,Pₙ))` or `DataFunction(D → Scalar(Union))` | `DataFunction(UInt → Scalar(Pᵢ))` for a bare scrutinee (implicit `0..N` keys), or `DataFunction(D → Scalar(Pᵢ))` for a stream scrutinee (the real `D` keys preserved) | **Sum elimination — the read-dual of `VariantWrap`.** Projects the arm named `tag` out of a tagged-union stream, *restricting to the sub-domain of rows carrying that tag* and yielding that arm's payload column, keyed by the original `UInt` position. A tag the scrutinee does not carry yields an **empty** projection rather than an error — that is what makes a width-subtype scrutinee, and so a `match` arm the scrutinee can never reach, inert instead of ill-formed. **Restrict and project are one op**: a [`UnionArm`] stores its rows alongside its payloads, so reading the arm *is* the tag restriction — there is no separate boolean `Restrict` step and no tag-discriminating `Predicate` (a domain-`Restrict` could not express it: the tag lives in the scrutinee's codomain, not its domain). Emitted by `lambda_elim` for a scrutinee-`Case`; consumed as a bare `Builtin::VariantProject(tag)` composed onto the fed scrutinee. |

**Pointwise `FunctionDef`s** (applied element-wise via `MapResult(input, Constant(FunctionDef))`,
not standalone operators): `BinOp(op)` over a `{_0, _1}` record column, `UnaryOp(op)` over one
column, `RecordField(f)` projecting a field, and `Scalar(program)` over one column. `Scalar` is a
`ScalarProgram` (`scalar_expr.rs`): a straight-line program over slots. Instruction 𝑖 names slot 𝑖
and its operands name earlier slots. An instruction is `Input { path }` (the input column or a field
path into it, a column of a base type, read as one slice), `Const(value)` (a value of a base type),
`Bin(op, a, b)`, `Un(op, a)` or `Record(fields)`, a column of records naming one slot per field in
field-name order. A comparison of two records, `==` or `!=`, is read as one comparison per field
both records carry (`compared_fields`, which `compare_records` also calls for columns), joined by
`and` for `==` and `or` for `!=`, and recursing into a field that is a record. Each record is read
from the input, a constant, or built by a `zip` in the chain.
The last instruction is the result: an operation, or, for a chain that ends in a `zip`, a `Record`,
nested to the depth of the `zip`s. A `Record` is only the last instruction or a field of a later
`Record`, and no operation reads one. A value that two operations read is one slot, so a computed
subterm read twice is computed once, and two reads of one field path are one `Input`. The parser
appends instructions and cuts the program at the chosen prefix, so equal chains give equal programs.
The parser reads projections of the input only, and a projection of a product built in the chain
ends the prefix. `simplify` reduces such a projection of a two-arm tuple before conversion, and not
one of a record or of a wider tuple. Evaluation works through the input in blocks of 1024 rows
(`BLOCK_ROWS`) and runs the instructions in order for each block. An `Input` or a `Const` writes no
slot: its block is read in place as a `ColumnView`, a region of the input or the constant's own
value repeated over the block. An operation writes its block-sized column into a slot of its own
that later blocks reuse (the `_into` kernels). The last instruction appends to the result instead:
an operation by its kernel, and a `Record` by copying each field's block from the slot, input region
or constant the field names. The result's room is reserved once at the first block. Peak memory is
the input, the result, and the slots of one block, where a pass over whole columns would hold a
full-length column per instruction. Conversion builds it from an element-wise chain of at least
two operations ([Element-wise chains](../ccl/design/optimization.md#element-wise-chains)), so it
replaces the operators of that chain, including the `Memo`, `FanOut`, per-arm `MapResult`s, `Zip`
and combining `MapResult` where it contains a `zip`.

**Column views** (`src/view.rs`, `interpreter/types/column_view.rs`). An operand of an element-wise
operation is read as a `View`: a borrowed slice of stored values, or one value repeated over a
length. A `ColumnView` is a `View` of `Int`, `UInt`, `String` or `Bool` values, taken from a
`ColumnValue` of one of those types or built from a literal. A record, a union and a `Units` column
have no view. The kernels in `scalar_ops.rs` take views, so a region of the input is read without a
copy and a repeated operand is read as one value, not as a column of copies. `apply_binop_views` and
`apply_unaryop_views` apply an operation to views; `apply_binop_column` and `apply_unaryop_column`
do the same for `ColumnValue`s, and `apply_binop_column` also compares two record columns.
`ColumnValue::extend_from_view` appends a view's values to a column of its element type.

**Value-selecting `Case` in a writer decision body** (a conditional induction write `if 𝑝: acc += a else: acc += b`, or a `with begin():` per-key routing merge — a gate that varies with the element at a site with **no visible iteration source**). `lambda_elim` compiles it to the same **union of domain-restricts** as every other value-`Case`, over the *fed* element stream: `⧺ᵢ (filter_values(π̂ᵢ) ≫ eᵢ)`, first-match `π̂ᵢ`. `filter_values` (`Builtin::FilterValues` → the `Filter` tile operator, input stream + predicate) is a **value-preserving** filter — unlike `Restrict` (which returns the domain identity `{D|p}⤇{D|p}` for a source a map re-indexes), it keeps each surviving element's value `V`, so `eᵢ` maps the kept elements directly and a **partial op** (`//`) in `eᵢ` runs only where its guard holds — never eagerly at a rejected position (the retired `Select` computed both arms and faulted on the off-path one). The arms filter the *same* fed stream disjointly (first-match), so their union is a **flat merge** (`UnionOperator::new_flat`): it stays on one domain extent (not a tagged `Extent::Union`) and reassembles the full column sorted by domain key, co-iterating with the decision record's sibling `commit`/`writes` fields. The key is the arm's domain *value*, not a position: reassembly needs only a total order (to restore the fed order) and equality (to catch two arms claiming one key), and both hold for any single collection's keys, since its domain is one `Extent`. A `UInt` position is the common case; a fed stream whose own index set is a coproduct — a conditional-element comprehension, whose `Copair` domain is `Variant({Index(i): {D | π̂ᵢ}})` — carries `Union { tag, inner }` keys, which `Value`'s order compares lexicographically by tag then payload. Keys that are *not* mutually comparable mean the arms were fed different domains, which is a copairing rather than a disjoint join, and `flat_merge` says so. A sourceless value-`Case` (a top-level ternary) still takes the `UIntRange(1)`-driver C-form + `final_or_default` (a tagged union dispatch); the writer-body case differs only in filtering the fed stream rather than a synthetic driver.

**Scrutinee-`Case` over a variant** (`λ 𝑥 → match 𝑥 { 𝑐ᵢ(𝑤ᵢ) → 𝑒ᵢ }` — sum elimination, the read-dual of `VariantCtor`). `lambda_elim` compiles it to the same **union of restricts** as the value-`Case`, keyed on **tag** rather than a boolean first-match gate: `⧺ᵢ (𝑥 ≫ variant_project(𝑐ᵢ) ≫ (λ 𝑤ᵢ → 𝑒ᵢ))` — a `≫`-chain, because every element of it is a morphism out of the eliminated binder: the scrutinee is `𝑥 ⇒ scrut_ty`, `variant_project(𝑐ᵢ)` is `scrut_ty ⇒ Pᵢ`, and the eliminated arm body is `Pᵢ ⇒ V`. `variant_project(𝑐ᵢ)` (`Builtin::VariantProject(tag)` → the `VariantProject` tile op) fuses the tag-restrict and the payload projection into one step (an arm stores its own rows — see the operator table). The tags **partition** the scrutinee's domain, so the arms' sub-domains are disjoint and the union is a **flat merge** (`UnionOperator::new_flat`), re-totaling to the full domain — exhaustive by typing (inference's width-subtyping demands one arm per scrutinee tag), so no `final_or_default` scalar collapse is needed (this is the fan-out shape, not the C-form). A const arm (`abort → 0`, ignoring its payload) keeps its `variant_project` through simplification: `try_const_reduce` refuses to collapse past either element that *narrows the domain at runtime with no refinement left to re-materialise* (`simplify`'s `narrows_domain_irrecoverably` — `variant_project` and `filter_values`), since dropping one would apply the constant at every position and make the arms overlap. It also keeps a `const` whose type is dependent, `(𝑘: 𝐾) ⇒ 𝐶[𝑘]`, as a step of its own: collapsed into what precedes it, nothing would bind `𝑘`. **Outer-binder arms.** When an arm body reads the *outer* binder as well as its payload (`𝑒ᵢ(𝑥, 𝑤ᵢ)` — e.g. a per-key view `λ __c → match __c.decision { commit(w) → (time: __c.time, write: w.i) }`, reading both the record's sibling field and the commit payload), the arm zips the whole element alongside the projected payload: `⧺ᵢ (⟨id, 𝑥.f ≫ variant_project(𝑐ᵢ)⟩ ≫ (λ (𝑥, 𝑤ᵢ) → 𝑒ᵢ))`. Both components of the pair are morphisms out of the *outer* binder, which is why `id` sits beside the projection chain rather than inside it — `𝑥.f ≫ ⟨id, variant_project(𝑐ᵢ)⟩` would pair the *scrutinee* with the payload, not the element the arm body reads its sibling fields off. For this, `VariantProject` keeps the scrutinee's **real domain keys** (a union *stream* `DataFunction { D ⇒ Scalar(Union) }` carries them explicitly, unlike a bare `Scalar(Union)` whose implicit `0..N` positions become the keys), so the outer `id` arm and the tag-restricted payload co-iterate by key under the `zip`/`Zip`, which inner-joins on shared keys — the outer arm need not be pre-restricted (the join drops the positions not carrying `𝑐ᵢ`). lambda_elim detects the outer-binder dependence structurally (the arm body has `𝑥` free beyond the payload binder) and merges the two into one pair binder (`𝑥 ↦ pair.0`, `𝑤ᵢ ↦ pair.1`); the payload-only path is unchanged. A scalar one-off `match` on a concrete value (rather than a per-element `λ x → match x`) would need the C-form scalar collapse; not built until a term needs it.

**`VariantCtor` inside a lambda body** (sum *introduction*, the dual of the scrutinee-`Case`). A `VariantCtor` in a lambda (``λ 𝑝 → `𝑐ᵢ(𝑒ᵢ(𝑝))``) must elaborate to a composable morphism `param_ty ⇒ Union` so it can be the RHS of a `≫` — e.g. a writer-decision arm ``filter_values(π̂ᵢ) ≫ 𝑒ᵢ ≫ variant_wrap(`commit)`` in the value-`Case` fan-out `⧺ᵢ (filter_values(π̂ᵢ) ≫ 𝑒ᵢ)`. `lambda_elim` compiles it to `𝑒ᵢ ≫ variant_wrap(𝑐ᵢ)` (`Builtin::VariantWrap(tag)` → the `VariantWrap` tile, fed the payload stream, wrapping it element-wise). The full arm set resolves from the node's `Type::Variant` codomain, mirroring `variant_project`. A `VariantCtor` whose payload is *constant* in the binder never reaches this arm — the `const` rule lifts the whole scalar variant with ``const(`𝑐ᵢ(…))``, which `MapResultToConst` broadcasts over the stream (`ColumnValue::repeat` handles a singleton `Union`). A genuinely scalar `VariantCtor` outside any lambda keeps its own node and its `expect_no_input` op-conversion arm (`Scalar(Union)`).

---

## The commit operator (`interpreter/commit_operator.rs`)

The transaction engine that backs a `Type::Txn` [`Transact`](../ccl/design/ir.md#transact--the-domain-parameterized-recurrence-carrier) store: concurrent writers propose transactions against a shared multi-key mutable variable, and the operator serializes them onto one monotonic commit-time clock with optimistic-concurrency validation (allocate-on-commit + backward validation + serialize-and-retry). Op-conversion's `build_commit_store` assembles it. The design splits into a **pure engine** and its **tile adapters**:

- **`CommitEngine`** (tile-free, unit-tested) — the serialization logic. The store is `Position ⇀ {key: value}`, held as one changelog per key. `attempt(proposal)` allocates the next tick and commits iff no read key was overwritten after the proposal's snapshot (else `Stale`, and the writer retries at the advanced watermark). `read_as_of(t, key)` folds the key's changelog.
- **`CommitOperator` / `CommitProducer`** — the store's tile adapter. It owns the engine, publishes its history as one [`Tile::Store`] output, drains each writer's new proposals in writer-index order in pull mode (the serialization order, rotated per pull so no writer is starved), and acknowledges a commit by `release`ing that step back to its writer. A consuming store takes each decision ahead of its commit and commits in key order instead ([Commits in key order](#commits-in-key-order)), and each proposal carries its item's source position (`pos`) for it. Writer inputs are wired *after* construction, so the operator sits inside a cyclic `FanOut` and every writer reads the store back before proposing — the cyclic-`FanOut` feedback idiom, one writer per key.
- **`TransactDriver` / `TransactDriverProducer`** — one per `with begin():` site: it owns the transaction source, folds `(frontier, snapshot)` for the site's read keys out of the cyclic store, and **produces** the decision body's `(snap…, item)` input. A row is emitted once per `(item, frontier)`, so a retry at a moved frontier is a fresh position and a re-pull at an unchanged one emits nothing. It closes (terminal) once every transaction has been attempted and acked over a source that can deliver no more — the writer's completeness signal, since the writer owns no source of its own. It releases the source through each finished item on its ack, and through each filtered row once it reads past it, since no ack comes for a row nothing attempts. Under a consuming store an ack is the store's take of the attempt's decision, and the drive keeps the item, to emit it again, until the store lets go of it. It reads the source when the source has notified since the last read, as the induction driver does, and answers every other pull from the last decode (`DecodedSource`, with each position a path of one component). It also releases the store below the decided frontier, through the last change strictly below it, so the commit store can reclaim its changelog.
- **`TransactWriter` / `TransactWriterProducer`** — one *fused* writer per site (fused, not fanned: a stateful append-only proposal stream cannot be split across fanned slots without desyncing). Each pull it decides the driver's newest live position and appends a `{snap, reads, writes, pos}` proposal when the body's decision is `` `commit ``, or advances locally when it is `` `abort `` and the store states no `writer_takes`; `pos` is the item's source position, copied from the driver's row. When the decision also reads an induction accumulator, that value arrives co-iterated in the writer *source* or broadcast as a constant — see [mutability.md](../ccl/design/mutability.md#reading-an-induction-accumulator-in-a-commit-decision), "Reading an induction accumulator in a commit decision".

  **The ack is a release intersection.** The driver sits behind a `FanOut` with two slots — the body and the writer — and advances its item cursor on what they *both* release. A body releases a row as soon as it has consumed it, which says nothing about commitment; the writer releases it when the attempt has finished, committed or denied without proposing. Only the intersection means "this item is done", which is why the writer holds a driver slot it barely reads: that slot is the ack channel.

  Both slots of that intersection are load-bearing, including the body's. A compiled body
  fans its input through a `Memo`, which releases each row as it *consumes* it — and it is
  that eager half which lets a superseded row be reclaimed before its item finishes. A body
  chain that released only when its own output was released would leave the intersection
  standing at the writer's ack, and the window below would grow one row per retry with the
  supersession release still in place. So this is an obligation on the body chain, alongside
  forwarding `domain_predicate`.

  **A release is not always an ack, though — supersession reclaims too.** The writer decides only the driver's *newest* live position, so every older one is abandoned and is released immediately rather than at the item's finish. That keeps a contended item's cost flat: the body re-renders the driver's whole live window each pull, so a window that grew one row per retry would make K retries cost K rows retained and K² body rows evaluated. The bound is `MAX_LIVE_ATTEMPTS`, asserted in the driver and measured at six contending writers — a window of 2 with the supersession release, 6 without it, over an item that lost five times. It also means the driver cannot read "a row was released" as "the item finished" — only the release of its **newest live row** is the ack, exactly as a release from the body alone is not one.
- **`StoreFinalRead` / `StoreFinalReadProducer`** — the **settled read** of a store key: the key's carried value at the position its own writers finish, or the store's seed if nothing wrote it, in the tiling of `V` (`Tiling::from_extent`), so a collection-valued key arrives as a level, as every store read hands it out. Two terms reduce to it, differing in what mints them rather than in what they sample: a surface `await_final` on a `Txn` key, and `final_read`, an induction accumulator's trailing read. It samples through the same `store_current` as `AsOf` and differs only in what fixes the position — a trigger's arrival there, the store's closure here — so it is neither a reduction nor a projection of the history, and needs no seed operand. Empty (and so non-terminal) until the store reports the key settled — `closed_keys.contains(key) || terminal`, so it settles once every writer that can write the key has drained rather than waiting on a store-mate's. A universal release retires it and releases the store slot; other readers hold their own guards through the fan, which the fan intersects, so the store still reclaims a version only once all of them have released it.
- **`StoreValueStream` / `StoreValueStreamProducer`** — projects one key's commit-value stream, commit time ⇀ `V`, out of the store changelog, carrying the value forward across ticks that wrote other keys (the step interpolation), so its own output is a `DataFunction` with a decided value at every tick. It backs the in-block reply tap (`carry_forward: false` — one entry per committed transaction) and the read-your-writes mutable variable carry (`carry_forward: true`).
- **`AsOf` / `AsOfProducer`** — the **as-of (temporal) join**, the cross-endpoint read. Given a `trigger` stream (the positions to sample at, e.g. an HTTP request stream) and the store, it latches the store's current value for each trigger position the first time that position is observed — indexed by the *trigger*, not the commit clock. Reading several mutable variables latches them all from one store render, so a multi-variable read is one snapshot. The dual of the changelog store's own driver: the store latches a private accumulator per *source* step, `AsOf` latches the store per *trigger* step.

A single-writer induction store is the degenerate no-conflict case of this same contract, which is why one `Transact` serves both engines.

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
is present with an empty changelog. Two consequences follow. A key carries its own value extent,
where one shared codomain could only name the union of what the keys hold. And two renders of one
store carry the same fields, which is what lets `merge` append them field by field.

A key's tiling is `Tiling::Scalar` of its value extent, so each change holds the key's whole value
as one cell, a collection included. A collection's entries do not yet stand as a level beneath the
change (`TODO(store-key-levels)`).

A proposal's `reads` and `writes` ride one `map_to_value` cell each, and their key sets vary
from one decision to the next. A write set holds every carry key of the store consuming it and
only the taps that fired. A read set omits a key the store holds no value for yet.

### The decision record

A writer body returns one **decision variant** per transaction, `` {`commit{𝑃} | `abort} `` (`ccl_utils::wrap_decision_variant`). `` `commit `` carries the payload record 𝑃 = `{writes, __to_<defer>*}` — the proposed new values keyed by the variable each is for, plus one field per reply tap — and `` `abort `` is the nullary whole-transaction deny: carry, no proposal. Making the grant/deny the *tag* rather than a `commit` field leaves "denied yet real writes" unrepresentable. `body_decision_at` decodes the tag by name, so the two ends agree without a canonical arm position. A tap's value is `` {`fired{𝑉} | `idle} `` — the fed value on the positions its own control-flow path admits, `` `idle `` on the rest (see [mutability.md](../ccl/design/mutability.md#general-in-transaction-conditionals-and-conditional-writes), "General in-transaction conditionals (and conditional writes)"). The grant path omits an `` `idle `` tap from the commit's write set, so a routed reply fires only on its own route. A tap whose path *is* the commit — a single-guard or spine feed — wraps unconditionally. Carrying the gate as the value's tag is what lets a fed value be domain-restricted: a value beside a separate `Bool` gate would have to answer wherever the record commits.

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
  `FlattenDomain`, `PermuteDomain`, `Copair` / `DisjointJoin`, `Sum` / `Max` / `Min`,
  `FinalOrDefault`, and the catch-all `Apply` arm (where the function position
  is a `Proj` / `Var` / curried `Apply`).

`Converse` straddles the split: it accepts either `input=None` (produce an
iteration source itself by compiling its argument with `input=None`) or
`input=Some` (wrap the standalone converse in a `MapResult` over the upstream).

Composed into a chain, `Converse` and `MapDomain` take a third path: they act on the input at the
level they are converted at ([The level a node is converted at](#the-level-a-node-is-converted-at)),
inverting or re-valuing the collection each row of the input holds there and leaving the levels
above it standing (`Converse::new_at`, `MapDomain::new_at`). A group-by whose key or source varies
with an enclosing row reaches conversion this way.

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
(`OpConversionContext::level`). A tiling cannot tell a level the node iterates from a level inside
the element it takes, so the operators listed below this table take their level from here. Over
grouped rows, `(sum(g), max(g))` and `(g, [s.qty for s in g])` both pair at the groups' keys,
while their arms carry one level and two.

| Node | Converts its children at |
|---|---|
| a root: a conversion with no input | a stream of its own: level 1 when its type is a collection, 0 when a scalar |
| `map(𝑓)` | 𝑓 one level in |
| an application `𝑓(𝑎)` | 𝑎 as a root; 𝑓 at 𝑎's level, since it runs over 𝑎's iteration |
| `curry_over(𝐹, 𝑔)` | 𝑔 one level in, over the iteration `strength_over` appends; 𝐹 at the node's level |
| a top-level `Transact` | its body at level 1, over the store's own domain |
| a nested `Transact` | its source and its seeds at the `Transact`'s level, a seed being one value per enclosing position; its body one level in |
| every other node, composition included | the level it is converted at |

The operators that act at one level ([Curry levels](#curry-levels)) take it from here. `Zip`
pairs at it, and so does a product morphism with no input, at the domains its type is curried
over. `MapResult` and `MapResultToConst` apply at it. `Filter` masks the keys one level above it, the keys a `filter_values`' elements
stand at; under `map`, one level in, those are the keys of each element collection. A composed
`Converse` inverts the collections at it and a composed `MapDomain` re-values them. A composed
`VariantWrap` wraps at it, and an applied one at the outermost level, its whole payload being one
variant value. A fed copairing merges one level above it, and a nested `Transact` leaves standing
the levels above its own row, one fewer than it.

Three operators read their level off a tiling. `VariantProject` projects at the level
holding its scrutinee's union column, which is always the deepest: an arm holds its payload as one
materialized cell, so no level sits beneath a union. That level can be deeper than the AST's,
because a feed tap inside a nest reaches the projection as a collection per enclosing position.
`MapAggregate` folds the innermost collection its input holds. `StoreFinalRead` answers one value
per row of the levels its store's tiling stands beneath, every one of which is an enclosing
position.

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
`bound_expr` and `body` independently against their respective fan-out slots.
The bound operator is wrapped in `Memo::new(...)` and pushed into the scope
under `binding.name` along with a [`BindingKind`]:

- **`BindingKind::Aligned`** — the bound expression was compiled with
  `Some(input)`, so its tile-domain matches the surrounding iteration.  At a
  `Var` reference inside that iteration, op-conversion returns the `FanOut`
  slot directly: the value already varies in lockstep.

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
  each tuple / record element; the elements get `Some(fan_out_slot)` and
  combine via [`zip_arms_at`] (function-tiled arms) or [`MakeRecord`] (scalar arms).
  The 2-arm Zip-with-const fast path skips the fan-out and emits a single
  `MapResultToConst` instead. A **store-read arm** (`__hist.k`, or a nested store's
  `__hist ≫ .k`, one history per enclosing position) is a *leaf*
  source over its own domain, so it is converted with **no** input (rather than
  the fanned slot, which it would reject); `zip_arms_at` co-aligns it with the
  input-driven arms by domain position. This is the cross-domain co-iteration a
  commit writer's source uses — `zip((reqs, __cnt.acc))` pairs the request stream
  with a request-indexed induction accumulator read so a commit decision can read
  the accumulator at its request position (`with begin(): balance += cnt`).

- **`Let { bound_expr, body }`** fans the parent input into both the bound
  expression and the body (described above).

- **A nested `Transact`** shares its enclosing drive, its per-row source, its pairs and
  each seed between several readers, and each of those fans sits on a `Memo`: a
  `FanOut` passes every slot's pull to its input, which without the cache is
  recomputed once per reader per lap. None of these fans' releases is read as a
  drive's progress, which is what keeps a `Memo` off an iteration source.

- **Induction writer bodies** (the realization of a recognized `Transact` over a
  concrete iteration extent) fan-out the cyclic prev-accumulator stream and the
  body output (via `FanOut::new_cyclic`); see
  [*Induction stores as a changelog*](#induction-stores-as-a-changelog-inductionstore-and-storedenseread)
  below for the full structure.

### Aggregates, sinks, and the program root

The pipeline always bottoms out at one of three consumer shapes:

1. A scalar produced by `Apply(<chain>, Sum)` / `Max` / `Min` (compiles to
   `Aggregate` + `ExtractAggregate`) or `Apply(Tuple([stream, default]), FinalOrDefault)`
   (compiles to `ExtractFinal`), or `final_read` of an accumulator's history (compiles to
   `StoreFinalRead`).
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
carries the correlation: an inner comprehension whose body and filter both read nothing outer
never forms one, leaving a `const` that is computed once and broadcast.

Compiling it is the pairing. The inner source does not mention the outer binder, so every row
iterates the same collection 𝐾, and planning writes the site as `const(𝐾) ▷ strength_over ≫ map(𝑔)`
(`src/ccl/planning/correlated.rs`). `const` puts 𝐾 beside each row (`MapResultToConst`), and
`strength_over` gives each row a group holding 𝐾's values, one level deeper than the outer
collection. `𝑔` then compiles over the pairs like any other morphism over a stream, its result
inheriting the grouping. While 𝐾 is still arriving, each row holds what has arrived and is left
open: no row is complete until 𝐾 is, since every row can gain its next element. Every row reads the
whole of 𝐾, so `MapResultToConst` releases it only when everything is.

`𝐹 ▷ strength_over` compiles to `Product::per_row_values_at`, which pairs each row with the values
of its own collection and keeps that collection's keys as the paired level; `Product::per_row_at`
pairs a row with the keys instead. The input is fanned to the row side and to `𝐹`, and the product
takes the two directly, so no pair is built between them. A collection whose values are collections
pairs with whole. `simplify` emits the same `strength_over` for a generator over a sum whose element
function reads the enclosing scope, where each row's collection is its own
(`src/ccl/design/optimization.md`, "A generator over a sum composes with its source"). A per-row
collection that arrives as a value rather than being selected by the binder has the same output
shape ([Where a collection is materialized](#where-a-collection-is-materialized)).

Nothing downstream of the pairing is required. `MapAggregate` consumes the grouping where the
comprehension is aggregated, and a comprehension that yields a collection per row leaves the
two-level tile as the answer.

**Nesting is unbounded, because the two operators are inverse at one level each.** `Product`
takes a collection at any depth and appends a level; `MapAggregate` collapses the
innermost level and leaves whichever shape that implies, one level fewer than it
received. So a comprehension nested 𝑛 deep pairs 𝑛−1 times on the way in and
folds 𝑛 times on the way out, and no operator sees a shape it did not already handle at
depth two.

**Where the inner domain comes from is what the term has to say**, and planning names it
(`src/ccl/planning/correlated.rs`): 𝐾 is the inner source re-viewed at its keys,
`map_domain(𝑠)`, where the body applies one, and `iterate` over the type's domain where it does
not. A site whose type is dependent, a correlated filter narrowing the inner domain by the outer
value, stays one node, [`Builtin::CurryOver`], which op-conversion compiles to the same
operators.

`curry_over` takes the keys as a family `𝐹` of the row, `const(𝐾)` where every row reads one
collection, and op-conversion pairs each row with `𝐹`'s collection for it, `𝐹 ▷ strength_over`.
**A site over a dependent tuple has keys per row**, so its `𝐹` is a family of distinct collections
(`src/ccl/design/type-inference.md`, "Iterating a dependent tuple"). A group-by under a loop whose
key reads the loop's binder has `𝐹 = 𝑀 ≫ converse ≫ map_domain`, the keys of the collection
`𝑀` builds per row, and `converse` and `map_domain` act at that level, one row's collection at a
time. A nested `Converse` passes a guard naming standing keys to its input as those keys. A guard
naming part of one row's inversion names input rows through their values, so the `Converse` records
each input row it read with the output path `[𝑠…, value, key]` it stands at and its input path
`[𝑠…, key]`, and releases the input rows whose output path the guard covers. A row read after its
group was released is released on the read that holds it (`ConverseProducer::release_late_rows`).

[`CheckedLookup`] gains a second reading from this, as a consumer now meeting a per-row
stream: it answers a group of keys per row, keeping the grouping — one answer per key, where
its key sits. A key the collection has not decided is left out of its group, and every level
states the keys' completeness less the paths of the keys left out and of the rows above them.
The rest of the group goes out as it is answered and is released by path, so the keys left out
arrive beneath the same row once decided. A one-level stream is the same rule at depth zero.

### A correlated filter rides the pair

A **filter** on the inner source rides the pair it filters, as a refinement `lambda_elim`
writes on the product. Planning emits it as `filter_values` — a term, which is what applies
it, since this site is a morphism under `curry` rather than one the iterate-then-restrict
chain reaches. A keyed collection's membership refinement is a different kind of refinement
and stays on the binder whose lookup reads it.

[`Filter`] reads the resulting mask by path. The predicate is compiled over the same pairs, so
its flat codomain is one boolean per entry, which is the mask `Tile::retain_keys` takes and
re-offsets the shortened groups from. Each side is pulled from its own branch of the pairs, and
the two need not have reached the same entries. Where they hold the same paths, the mask is
positional. Otherwise each input entry takes the answer at its own path. An entry the predicate
has not answered yet is undecided: it is left out of the pull, and its path and the rows above
it are left out of every level's completeness, so it arrives beneath the same row once
answered. An answer for an entry the input has not reached stays in the predicate until the
filter's output releases that entry. An input with nothing in it is already filtered.

A filter that reads the outer binder forms the pair even when the body reads nothing outer.
The binder is then free only in the filter's cast, and `lambda_elim` rewrites that cast to the
lambda it denotes, whose binder carries the filter as a refinement. The nested-lambda rule
lifts it onto the pair as it does any other filter
([type-inference.md, "Dependent application and
reconstruction"](../ccl/design/type-inference.md#dependent-application-and-reconstruction)).

### Where a collection is materialized

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

A body's writes go the other way, because a store holds each key's value as one cell per change
([One changelog per key](#one-changelog-per-key)). A keyed write's `insert` takes the level, at
any depth, and the payload materializes where it becomes the decision's value
(`FunctionDef::apply_tile`, `materialize_collections`). The written value reopens into the shape
the collection's values take, so the rebuilt level is one gather over the collection's entries
followed by the written ones, and a keyed write costs the size of the whole collection. An
accumulator's seed and the stand-in an absent snapshot slot takes are values for the same reason,
read out of the row their producer delivered (`materialized_row`). A collection's entries standing
as a level beneath each change would make a keyed write one entry (`TODO(store-key-levels)`).

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
the seed, the domain and the frontier per row, so projecting one row of a nested induction store is
the ordinary row retain. The seed is the base of the step function rather than a point of its
domain, because a changelog is keyed by the positions writes land at and no position stands below
the first. A fold that finds no change at or below the position it asks about resolves to the
seed.

A store opens on the pull its seed arrives, not at subscribe. A seed is ordinary dataflow: `b :=
a` after a loop over `a` settles once that loop reaches its final position, which takes as many
pulls as it has positions. The store reads its seed streams at the head of every `get`, and
`Engines::store_at` opens the engine once every key's seed carries a value, a store waiting on
the slowest of them (`a_store_waits_for_every_accumulators_seed`). Until then the store renders
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
over a map runs with the map's keys as its positions. They are ascending but not contiguous. A
restricted source (`for l in [x for x in xs if p(x)]`) carries its extent's keys, the filtered ones
marked deleted. The decode reads only the surviving positions and the recurrence runs over exactly
those, so the watermark bounds the next position from below rather than naming it. The store
decides no filtered position, and every read of the store runs over the positions it decided, so
no read emits one. Iterating the extent densely and gating the write would need the store to
recover a filter the source's refined extent already carries. A product
source is keyed by a record and a concatenation by a union, so a loop over a product runs its pairs
in lexicographic order and one over a concatenation runs each part in turn.

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
position is the smallest delivered path above it, and it goes only once the source calls every
path before it complete. A source need not deliver in the drive's order: a product or a
concatenation with a streamed part delivers a later position before an earlier one. The drive
never looks back, so a path arriving below the cursor would be dropped. It waits on the paths
before the next position and on nothing after it. An emitted row is otherwise a function of the
store tile and the source tile. The driver decodes the source into `(path, item)` pairs
(`decode_source_paths`), since an async source's domain arrives unordered and compacts as its
consumed prefix is released.

The driver reads the source when the source has notified since the last read, and answers every
other pull from the last decode (`DecodedSource`: the undelivered items in drive order, and every
path the source held, deleted rows included). A tile only grows between a source's notifications
and the driver's own releases, so the last read still describes it. An emitted position leaves
the decode, and a release forgets every path through it. A pull that emits one position costs
that position, and a loop over `n` rows costs `n` rather than `n²`. The source notifies through a
flag the driver sets ahead of the forwarding consumer, because the forwarding consumer drops a
notification that re-enters it behind a closed gate. The nested drive's enclosing-parameter and
reseed streams are still decoded on every pull (`decode_pairs_pathed`), as are the row-level
completeness reads over the undelivered paths, so a nested loop keeps the quadratic term.

The driver releases the source prefix it has consumed: every position it has emitted, and every
filtered row it has read past. A filtered row stays in the source tile, marked deleted, and no
decision or ack ever names it, so the driver releases it once the source calls it complete along
with every path before it (`source_read_through` states the rule for a drive with no rows above
it, and a nested drive reads it over paths). Releasing a prefix the source has not called
complete would name a position still to arrive, and a drive placed across a reload resumes past
whatever its predecessor released. The transaction driver releases filtered rows by the same rule.

A **nested drive** is the same driver at a deeper path, carrying two additions in `NestedDrive`.
It **reseeds** at each enclosing position: a boundary is a position whose enclosing components
differ from the last one emitted, and there the previous accumulator comes from the accumulator's
reseed stream rather than from the store. It **passes the enclosing parameter through**, because
parameter elimination gave the body `((ᴘ, Pos), slots)`, and rewriting that would leave each
inner level's own type stale. At depth zero both vanish: the only boundary is the first position,
where the store already holds its seed.

A nested drive states which rows at each level are complete, and a row is complete once the
source will put no more positions under it and the store has folded every position it did. The
first half is the source's statement, which the drive accumulates across pulls: the source may
stop stating a row once the drive has released it, and the store can fold the row's last
position after that release. The second half is that no position under the row is left to
decide: no position the source has delivered and the drive has not emitted, and no emitted
position past the store's frontier. Positions run in order, so everything at or below the
frontier is decided. The drive counts the positions it has emitted as well as those the source
still holds, because an emitted position is released back to the source before the store decides
it. A row with no position under it is folded when it arrives, so a source that holds no
positions leaves every row folded.

### One induction store at every depth

`Engines` is a tree with one node per collection level above the stores and an engine at each
leaf. A loop inside one loop has one level, a loop inside two has two, and a loop on its own has
none and is reached at the empty path. The depth lives in the tree, so the code walking it has no
depth-specific case:

- `render_engines` walks the tree, and `store_tile` assembles a run of engines into one
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

Under rows the read produces the same shape per enclosing position: one history per row, each folded
against that row's own store, so a position that writes nothing resolves to the value its row
began with rather than the previous row's last write. A row's positions at or below its frontier
are decided, so the read states them complete beneath that row rather than waiting for the row
to close.

The trailing read of an accumulator, `final_read(history)`, is a `StoreFinalRead`: the key's
value once the store has settled, sampled from the store rather than reduced from a stream, and
the seed where the loop ran no position. `mut_elim` mints it as a sample, as `transact_phase`
mints `await_final`'s, because a reduction is the wrong term for it: a store resuming mid-fold
has not decided its predecessor's positions, so a reduction over its history would find nothing
and answer with the declared init instead of the value carried in.

An inner loop's trailing read is the same term over one store per enclosing position:
`StoreFinalRead::per_row_at` answers each row its store's value once the induction store calls the
row complete. Every enclosing position has a store, a row whose inner loop runs no position
included, because a nested `Transact`'s seed is a morphism of the enclosing position and so arrives
for every row: the store opens a row at its first decision, or once the drive calls it complete
where it has none, and the row's value is then its seed.

A co-iterated read (`for r in …: cnt += 1; with begin(): store := store + cnt`) consumes the
dense read directly.

A `Tile::Store` carries terminality on its `terminal` flag and keeps each row's watermark `w` in
`frontier` when it closes, so `store_frontier` reads `w` directly and a trailing run of carries is
counted.

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

An induction store reclaims its changelog as it runs, at any depth. Each reader releases what its
consumer has taken; the drive releases through the frontier; the `FanOut` in front of the store
meets the branches; and `InductionStoreProducer::release_impl` hands the meet to
`CommitEngine::gc_released_prefix`, one store at a time. The meet cannot advance past a branch that
has released nothing, so a reader holding its branch until it retires holds every version of every
key for the length of the run. The flat trailing read therefore releases as it goes:
`StoreFinalRead` releases through the frontier on every pull, and `ExtractFinal` over a stream
releases below the highest position it has seen.

Measured over a 90-position flat loop: 4 retained changelog entries with the reads releasing, and
180 without. Over `for y in [1, 2]: total += x * y` nested in 5, 10 or 20 enclosing positions,
the stores never hold more than 10 values at once, counting seeds, changelog entries and decided
positions as `TileProducer::state_info` does
(`a_long_nest_holds_the_same_store_state_at_any_length`); without the reclaim they hold two more
per enclosing position. Retention is O(keys) plus the slowest
reader's lag, independent of how many positions have run and of how many rows.

A commit store reclaims the same way. The `TransactDriver` releases through the last change
strictly below the frontier, as `AsOf` does; a `TransactWriter` with read keys releases strictly
below the oldest tick it read, and one without releases through the frontier; the final read
releases through the frontier. `release_store_below` states the strictly-below bounds once, and
`release_store_through` the inclusive bound of a writer without read keys.

**A reader forwards the region it was released, unchanged.** It computes no bound of its own,
because the rules below make which versions a later fold can reach the store's question, and the
store is the side that holds the answer. A release naming a row of a read names the same row of
the induction store, since the two tilings agree on every level above the store, so one forward
serves either depth. `StoreFinalRead` under rows holds one value where the induction store holds a
store, so it passes on a row's release only once that row's value is released whole
(`through_shared_levels`).

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
release names every row before the one it is running whole (`domain_prefix`), and
`StoreFinalRead` under a nest forwards its consumer's release of a row, which names that row of
the store.
Where every branch names a row, so does the meet, and `Engines::remove_covered` drops that row in
the same release that reclaims the rest. The next render therefore cannot rebuild what was
released, which `TileProducer::get` asserts against. The row's watermark goes with it, since
nothing is left to ask where that store got to.

The driver's own release runs outward, to the iteration source. It reclaims the consumed prefix as
`emitted_through` advances and releases the source in full once the source is complete and every
delivered position has been emitted, which ends the driver.

**A nested induction store's inputs release as the drive passes them.** The enclosing parameter
(`pairs`) is keyed by the body's `(enclosing, position)` pairs, and the driver reads it only at
positions past its cursor, so it releases it through `emitted_through`. The region is
`domain_prefix` over the path with its last two components composed back into the pair, which
`Predicate::at_or_below` spells as a staircase over the pair's fields. Each accumulator's seed is
keyed by the enclosing positions and read once per row: the driver reads it as the reseed at a
row's first position, and the store reads it to open the row. The driver therefore releases the
rows through its cursor's, and the store the rows through the path it has decided
(`release_seeds_through`). Seed and reseed are one stream behind a `FanOut`, so either consumer
holding its branch pins it. The pairs are built from the enclosing input by `Product` and
`Uncurry`, which re-deliver the whole run on every pull unless it is released. `Uncurry` forwards a
release of pairs as the inner keys they name under their outer keys, under whatever standing rows
qualify it, so the row being run is reclaimed as it goes rather than when it finishes.

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
