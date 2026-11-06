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
still grow, and the new level states the completion predicate its caller passes. Both require the
new level to be built with no logical deletions and a `False` completion predicate; existing levels
retain their own deletion sets. `Tiling::append_level` performs the corresponding transformation on
the static shape.

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

Union normalization and mixed-shape intersection are specified under
[Guard normalization](#guard-normalization).

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

### Guard normalization

`TileGuard::flatten_or` normalizes a nonempty list of union arms. It distributes `Codomain`
wrappers over nested `Or` guards, then calls `lift` on each resulting chain. A region covering
all values beneath a key can be represented by that key's domain guard:
`Codomain(Domain(Qualified(𝐸, True)))` lifts to `Domain(𝐸)`. Partial regions remain at their
original depth. Keyless leaves lift through their enclosing-row predicates. A record lifts
only the rows covered in full by every field; its remaining field regions stay in a record arm.

Normalization returns a universal arm if one is present. Otherwise it removes empty arms,
retaining the first if every arm is empty. Arms with the same nesting and leaf shape combine
through `union_in_place`; record fields combine independently. `without_covered_arms` then
prunes deeper domain arms where `Predicate::without_covered` can subtract keys already covered
by shallower domain arms. If that helper cannot express a subtraction, the arm is retained.
One remaining arm is returned directly; several become `Or`. An empty input list panics.
This is the implemented normalization procedure, not a guarantee of structural equality for
every pair of semantically equivalent guards.

`TileGuard::union` and `intersect` require compatible guard shapes. Record operands must have
identical field sets; mismatches panic. A record guard selects independent field regions,
unlike `Predicate::Record`, which tests a conjunction over a record value's components.
Consequently, record-guard union combines fields directly rather than constructing a predicate
union of products.

Function intersection handles a mixed `Domain`/`Codomain` pair by qualifying the inner region
with the domain predicate at the current collection depth. It does not discard either
constraint. Function union combines equal shapes and handles empty/universal operands;
a remaining mixed pair returns `None`, causing `TileGuard::union` to retain separate arms.
Intersection distributes across `Or` and normalizes the results.

`covers_path` tests a full path of collection keys. A domain guard covers every deeper path
through its selected keys. A record path is covered only if all fields cover it. `whole_keys`
extracts the normalized outer-domain region for producers reclaiming key-indexed state; it
does not include separately released cells in still-live rows. Those cells remain subject to
[The release contract](#the-release-contract).

`through_standing_levels` translates a guard across unchanged outer collection levels and
delegates the region below them to the operator's callback. Empty and universal guards use
the input tiling's corresponding guard without calling the callback. `through_shared_levels`
uses this traversal when the values differ. Normalization lifts whole-value regions to domain
guards on their enclosing shared keys, so whole values pass through as key releases. The callback
receives only partial value regions and releases no input values for them. This translation is an
operator retention rule, not an approximation to the output region.

`domain_prefix_over` constructs an inclusive nested-key prefix from one arm per path component.
Nonfinal components select keys strictly before their bound; the final component includes its
bound. Inner arms are qualified by the preceding path. The path must be nonempty. Domain
extents are required for union-key bounds; `domain_prefix` supplies none and therefore cannot
construct those prefixes.

### Predicate

A `Predicate` selects values within an extent, or paths through nested collection levels.
Tiles use predicates to state domain completeness; guards use them to select regions.

| Variant | Meaning |
|---------|---------|
| `True` | All values. Universal predicate; identity under `intersect`. |
| `False` | No values. Empty predicate; annihilator under `intersect`. |
| `Intervals(IntervalSet<Value>)` | A scalar key's admitted values, clamped to the type's range. `Predicate::at_or_below(v)` builds the prefix `≤ v`, the upper-bound streaming signal, and `Predicate::below(v)` the strict one. Never built over records. |
| `Record(fields)` | A componentwise predicate over a record key: one predicate per field, with AND semantics. |
| `Or(arms)` | Union of the arms' regions. `flatten_or` removes nested `Or` nodes, joins two `Intervals` arms into one, and joins pairs of componentwise arms where possible. |
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

### Absent keys

A collection level records apart from its statement the paths it knows absent everywhere
(`absent_keys`). A statement covers the region a tile answers, so a cut to a projection keeps only
what it says of the region kept; an absent key has no path in any region, so a cut keeps the record
whole, and a merge unites the two sides'. A key in it is complete wherever completeness is read for
that level. `Converse` writes it: once every input key it has read is complete, a value no row
carried has no group ([Converse](#converse)). `MapAggregate` reads it with the outer statement, so
a group no answer holds is stated absent after any cut beneath the groups' keys. A key held is
never recorded absent.

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
  input produces only that part. Its answer is built from the input's, so it does not cut, and it
  equals the whole answer cut to 𝑝. An operator that builds its answer from anything else cuts:
  accumulators held across pulls (`MapAggregate`), arms already released (`UnionOperator`), or a
  cache read at a wider region (`Memo`, and the `FanOutSlot` of a cyclic fan-out). An operator whose
  output keys are not its input's keys, such as a `Converse` pulled at its values, pulls the input
  in full and cuts its own output. An operator that cannot restate 𝑝 for an input pulls the input in
  full and still cuts its output: pulling more is sound for a `get`, where a release that names more
  is not.
- **Completeness between pulls.** The completeness contract compares a producer's answers inside the
  region pulled, and a pull of one projection states completeness over its keys only, so a pull of
  another region withdraws nothing it said of the first. The debug check keeps the last statement of
  each region.
- **Check.** A debug build's `TileProducer::get` compares each answer with the projection it was
  asked for (`Tile::within`) and panics on a key the projection omits, on any cell where the
  projection names nothing, and on a pull for keys that a non-collection answers. A producer that
  answers whole fails the check at its first pull for keys.

Each operator answers a projection as its row of this table states.

| Operator | Projection |
| --- | --- |
| `IterateExtent` | A finite range is cut to the admitted interval before it is rendered. Every other extent renders whole and is cut after. |
| `Constant` | A collection constant answers the admitted keys. A scalar constant answers the whole value or nothing. |
| `MapResult` | A keyed input is pulled at the projection; a scalar input is a key looked up in the function, has no keys to project, and is read whole. A function operand that is a collection is pulled at the projection too where the input's values are its keys, the arguments stand at the first level, and the operand is a data function; its keys are released with the data's. Any other function operand is read whole. Beneath the outermost keys the input is pulled at a projection above the level the function applies at (`Restates::Above`), and the function operand is read whole. |
| `MapResultToConst` | A collection input is pulled at the projection where the constant applies one level in or deeper. At the outermost level the constant replaces the whole input, so the input is read whole. The constant is read whole, since every row reads all of it. A projection beneath the outermost keys is answered above the constant's level (`Restates::Above`), and one at or beneath it panics. |
| `MapResultWithSource` | The input is pulled at the projection, at any level (`Restates::Every`), so a morsel reads only its own keys from the source. |
| `RecordWrap` | The input is pulled at the projection, which beneath the outermost keys is one above the wrapped level (`Restates::Above`). |
| `SelectField` | A stream of records is pulled at the projection, which beneath the outermost keys is one above the record's level (`Restates::Above`). A product of collections is pulled whole and the selected field is cut. Its release names the other fields' cells at every path, and a breaker's final guard names each key under which a cell is still held ([Differences of nested guards](design-path-projections.md#differences-of-nested-guards)). |
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
| `Converse` | Every level is restated (`Restates::Every`). A projection of the input's keys one level beneath the inverted one under every value pulls the input at those keys ([Converse](#converse)). Otherwise, beneath standing levels the input is pulled at the standing keys the projection names (`Projection::above`), and inverting the outermost collection reads the whole input; the groups are cut to the projection, and the rows of a group the projection does not name stay unreleased at the input. |
| `FanOutSlot` | Pulls the shared input at its own projection and cuts its answer to it. A producer states completeness only for the region it returns, so slots at different regions each pull the one input at their own and a pull of one region retracts nothing it said of another (the debug check compares the last output inside the region pulled). A cyclic fan-out reads its input whole, because a sibling that re-enters mid-pull is answered from the cache of the last completed pull, which has to cover whatever region that sibling asks for. A projection beneath the outermost keys is read and cut as one of the outermost keys is. |
| `Memo` | Reads its input at the projection and caches what it read; a pull over a region it has read answers from the cache cut to the projection, and a region it has not read reaches the input however quiet the input has been. The regions it has read and must read again are projections at any level, so a projection beneath the outermost keys is read and cached as one of the outermost keys is. |
| `UnionOperator` | A flat union pulls every arm at the projection and cuts the merge to it: the arms are disjoint slices of one collection, and an arm the consumer has released contributes an empty tile that states every key decided, which the cut brings back to the projection. A tagged union keys its rows by arm. It pulls each arm at what a guard of its keys by tag names under that arm's tag, as its `release_impl` splits a release, and does not pull an arm the guard names nothing of; a key projection of any other shape panics. |
| `CheckedLookup` | A stream of keys, or of `(collection, key)` rows, is pulled at the projection, since each answer sits at its key's position; the collection is read whole, because every key is answered against all of it. One key has no keys to project and admits only `Everything` and `Nothing`. |
| `ExtractFinal` | Admits `Everything` and `Nothing`. The last position of a stream is not known before the stream ends, so the source is read whole, and the one value or collection it yields is released whole. A key projection panics, a collection-valued final position included. |
| `PermuteRecordDomain` | Reads its input whole and cuts the answer to the projection over the permuted keys: a region of record keys is componentwise, and the input's fields are renamed, so the projection is not forwarded. |
| `FlattenTupleDomain` | Reads its input whole and cuts the answer to the projection over the flat keys, as `PermuteRecordDomain` does: the nested keys are restated flat, so the projection is not forwarded. |
| `Lookup` | Reads its input whole and cuts the answer to the projection: each row's key is looked up in that row's collection, and the answer keeps the input's keys above the rows. |
| `Aggregate` | Admits `Everything` and `Nothing`: the accumulator has no keys, and the input is read whole whatever the consumer asks. A key projection panics. |
| `ExtractAggregate` | Admits `Everything` and `Nothing`: one extracted value has no keys. A key projection panics. |
| `MapAggregate` | Pulls the input at the projection, at any level (`Restates::Every`), and cuts the answer to it: the answer is built from every accumulator held, including those of keys pulled earlier, and from what every pull's answer stated, and each group beneath a key is whole. |
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
released key by key (`Tile::held_guard`). At a nested level that guard names each key held and each
key the level's statement calls complete under a row the tile holds, both by whole path, so a key
stated absent under an open row is released at that row. A level's statement is also named as it is
spelled under rows the tile does not hold (`Tile::stated_by_path`). A part qualified by whole paths
names its rows, so it releases nothing under any other. A part unqualified at a level above states
its keys complete under every row there, those not yet delivered included, so it is named under
every one: an inverse states its input's keys so, since each stands beneath one value
([Converse](#converse)). Three tiles whose held keys form a prefix still take that path: a last key
whose group holds nothing, an earlier key whose own group's statement calls every key complete, and
a statement about the keys beneath an enclosing key the tile does not hold. The guard names all
three exactly, the third by path. A universal input release latches `upstream_drained`. Until the
input notifies again, release builds then return the cache without pulling it, and debug builds
probe it once to exercise its post-release checks. A drained input inside a loop's cycle delivers
again where a round has it read again (`read_again`), and every build reads the region it notified.

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
`Consumer::notify(arrived: &Projection)`. A producer that cannot name the region sends `Everything`,
and none sends `Nothing`. A closure consumer ignores the region. A consumer that pulls on
notification has no use for it, since its pull reads whatever arrived. A consumer that does not pull
acts on the region instead.

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
| `Uncurry` | the input | restates beneath a standing level, widens at the outermost | A region at or beneath the paired level names the pairs it heads; pairing the outermost collection re-keys it, and a decided region of outer keys names every pair they head. |
| `Converse` | the input | keeps the standing keys, and restates the inverted level's keys one level in, beneath every value (`scheduler::one_level_in`) | Each input key stands beneath exactly one value. |
| `UnionOperator` | every arm | keeps for a flat union, restates under the arm's tag for a tagged one | Flat arms are disjoint slices of one collection; a tagged union keys an arm's rows by the arm's keys under its tag, and `Everything` of an arm is every key under that tag. |
| `CheckedLookup` | a stream of keys, or the pairs | keeps | Each answer sits at its key's position. |
| `CheckedLookup` | one key | widens | One key has no keys to project. |
| `CheckedLookup` | the collection | widens | Every key is answered against all of it. |
| `Memo` | the input | keeps | Read at the projection, and its keys are the input's. |
| `FanOutSlot` | the shared input | keeps | The fan-out forwards the input's region to every live slot. Between pulls it passes only a notification naming a key it has not passed since the last pull, as a gate does, and drops the rest, whose keys every slot consumer has heard of. |
| `ExtractFinal` | the input | widens | Read whole; the keys are the last position. |
| `PermuteRecordDomain`, `FlattenTupleDomain` | the input | restates | The keys are the input's with their fields renamed or spliced, so a region of the input's keys is the same keys renamed or spliced. |
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
operator's gate stops every later notification from its inputs that names only keys already passed.
Finished reads, settled seeds, recurrences with no remaining reader and wholly released operators
need no further pull. When `pull_laps` reaches quiescence, a debug check walks
`TileProducer::visit_input_producers` and rejects an input whose forwarding flag remains set after
its reader was pulled that lap.

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
| `enter_consuming_mode()` | Puts the breaker in consuming mode for a dispatched run, before its first `consume_impl`; nothing else changes the mode. |
| `as_producer()` | The breaker as a `BreakingProducer`, or `None` for a breaker that is no producer. |
| `finish(pushes)` | Finishes once the pipeline has consumed every package and nothing more can be queued for it, the breaker's last call. The default pushes, through `as_producer`, what the breaker holds and no push named before, one morsel of its outermost keys per work package, through its consumer to the pipelines that read it; a breaker that is no producer pushes nothing. An empty guard pushes nothing. It wakes no one. |
| `morsels(guard, rows)` | Cuts a guard the breaker pushes into morsels of at most `rows` held rows, which partition it. The default answers the guard whole. |
| `pushes_while_consuming()` | Whether the driver also pushes after each `consume_impl`. The default answers `true`. |
| `offer_impl(guard)` | Answers from the state `consume_impl` built and pulls nothing. The breaker's own `get_impl` calls it once the breaker is consuming. |

An operator that consumes its input into state of its own is a breaker. One that answers pulls from
that state is a producer; `SinkBreaker`, the breaker of a sink's pipeline and of the `main`
output's, is one that is not. A breaker is in the pull mode described in [The producer
protocol](#the-producer-protocol) for a whole run, or consuming for a whole run. A dispatched run
puts every breaker it drives in consuming mode once its plan stands, before any package
(`Breaker::enter_consuming_mode`), and a pull-mode run never does, so no consume changes the mode. A
consuming breaker pulled before its first consume answers what it has consumed, which is nothing,
and steps nothing. `final_guard` is provided over `held()`: it is `held()` less the guard released
to the breaker, and the driver pushes the part of it no earlier push named, after each consume and
at its `finish`. When a pipeline may finish is the dispatcher's to check ([The
dispatcher](#the-dispatcher)). A release removes rows from the state and leaves the statement of the
tile as it was, so the difference is taken in the guard algebra. `guard_minus`
(`tile_operators/mod.rs`) spells it for guards of a collection's outermost keys, of a scalar and of
an aggregation, none of them qualified by an enclosing path, and for a record of such guards field
by field. Two guards of a collection's keys at any levels differ as their projections do: a release
up to the path `(𝑘, 𝑗)` leaves of a held row 𝑘 its paths past 𝑗, which `TileGuard::closed_over`
drops where the row's level is a finite range of positions with none past 𝑗; `final_guard` closes
the difference over the producer's tiling. A state of another shape has no spelling, and a push
after the first panics naming the gap instead of answering a smaller or larger region.
`MapAggregate` holds state released beneath a group's keys. A release there leaves a region beneath
the outermost keys, which a reader's chain may be unable to restate (`TileProducer::restates`). It
returns `false` from `pushes_while_consuming`. It publishes at finish and during explicit held-state
publication passes (`dispatcher::push_held`), including loop-body settlement. A push beneath the
outermost keys lands in each reader as a projection at its level ([The
dispatcher](#the-dispatcher)).

### Memo

A consuming memo answers from its cache, and the cache's statement says which region that answer
covers. A consume over a memo whose input has drained pulls nothing. A consuming memo is woken by no
notification. Its reader takes what it holds from the pushes after each consume, and the memo reads
its input again where a store steps or a live source yields more (`TileProducer::read_again`). A
consuming memo's only reader is the pipeline the dispatcher pushes to, so a consume wakes no
consumer and a push queues no wake: what the memo holds reaches its reader through the packages the
driver pushes after each consume.

### Aggregate

A consuming `Aggregate` folds the rows its input answers at the guard into the accumulator, which is
final when the input has been released whole and holds the one value until the consumer releases the
output. A consume at part of the input folds that part once: the input releases what it answered and
does not answer it again. Its guards are `Aggregation` guards, which are all or nothing. `held`
names the accumulator only once it is final, when the input has been released whole, so no guard
names a partial aggregation. `finish` panics where the output is unreleased and the input has not
been released whole, because no later consume completes the accumulator.

### ExtractAggregate

A consuming `ExtractAggregate` pulls its input, an aggregation, at the guard and extracts the value
once the aggregation is terminal. A terminal aggregation states all of itself releasable and is
released; a partial one states nothing releasable, so it is left in place for the next consume and
the extraction holds nothing. The value is final once the input has been released whole, and stays
until the consumer releases the output.

### MapAggregate

A consuming `MapAggregate` folds each group the input answers at the guard into the group's
accumulator and keeps what the answers state about completeness, united across consumes. A group is
final per key once the input states it complete, at a level on its path or at the folded level
under its key. An answer of a pull beneath the groups' keys states only the elements it reads, so
the folded level's statements are united too, and a group is final once they cover every element
under its key (`Stated::settled`). The input releases a complete group whole and an open one only
beneath its key, so a group that arrives later in a region already consumed is still the input's to
answer. `MapAggregate` pushes at the pipeline's finish rather than after each consume.
The guard it pushes is the guard of the output built from the accumulators, less every group whose
accumulator is not terminal, less the guard released. The dispatcher pushes each region once
(`Pushes::push_final`), so a group still folding at one finish is pushed at the finish where it is
final, and a reader that kept the row open reads it again then. A release of the output drops the
accumulators it covers and forwards to the input, as in pull mode.

### Converse

`Converse` is no breaker: it consumes no input into state it answers from. Inverting a level puts
the input's keys at that level one level in, beneath the values that become the keys there, and each
input key stands beneath exactly one value. So a region of the input's keys names exactly the output
paths it changed, with the value step admitting anything: `Converse` passes its input a consumer
that restates the region there (`scheduler::one_level_in`), and a pull at such a region pulls the
input at the same keys (`Predicate::without_open_level`) and inverts only those rows. A region of
the standing keys above the inverted level passes through as it is. It keeps the input rows it read
and has not released, which a release of a group names by their values. At the outermost level it
also keeps the input keys its answers stated complete and the values those answers held, and once
every input key is complete it records every other value absent ([Absent keys](#absent-keys)): such
a value has no group, and a cut beneath the values keeps no statement of the groups it does not
hold.

#### A release of a converse group

A release of a `Converse` names its output region exactly. Upstream it is forwarded in two parts:
the input rows the region covers among those it holds, at once, and each later row of a released
group on the read that first holds it (`ConverseProducer::release_late_rows`). An input guard names
rows by key, and a group is the rows whose value is the group's key, so no input guard names a group
before its rows are read. The two parts together release exactly the region named, as
[Guard operations are exact](#guard-operations-are-exact) requires.

### ExtractFinal

A consuming `ExtractFinal` merges the source rows it answers at the guard and keeps the row at the
greatest key, where the values are a column of scalars; any other shape of value keeps every merged
row. Merged rows are in arrival order, so the last row is not the final one and the key says which
is. Pull mode takes the last row of a source it reads whole and assumes the source is sorted by key,
which a consuming `ExtractFinal` does not. Keys of one collection are totally ordered, and a
collection whose keys do not compare panics. The value is extracted once the source has been
released whole. A source that held nothing falls back to the default, which `consume_impl` reads
when the source drains and reads again at each later `consume_impl` until it has converged; until
then nothing is held. The dispatcher issues no `consume_impl` after the finish, so `finish` panics
when the output is unreleased and no value has been extracted rather than push nothing. A source
declared total that held nothing panics as it does in pull mode. The value is final from then, and
stays until the consumer releases the output, which is all or nothing.

### A store as a breaker

A transaction store (`CommitProducer`, `commit_operator.rs`) is the breaker of one pipeline per
writer (`Breaker::inputs`): a writer's cycle, the store, the writer and its drive, is the pipeline
of the writer's input, and the operators inside it stay in pull mode. An induction store
(`InductionStoreProducer`) implements `Breaker` and owns its request and store-step control through
per-run `InductionRun` metadata. Its body runs before each store step ([A loop in
rounds](#a-loop-in-rounds)). A nested request names one row of the nested store and remains in
flight until that row finishes. A cyclic `FanOut` holds its store in a cell of its own
(`Inner::Store`, `tile_operators/fanout.rs`) and hands the store a `Cycle` when it subscribes it
(`TileProducer::enter_cycle`). The call that steps the store holds the store's cell, so the
recurrence's pull of the store finds the cell borrowed and is answered from the snapshot the store
published after its previous step.

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
terminal at its finish. A transaction's deny commits nothing and progresses through its
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
the store only once it is terminal ([The dispatcher](#the-dispatcher)). A store's `final_guard` is `held()`. A release of
a store with no rows above it names the positions a reader reads no more and removes nothing from
the store tile; a nested store's offer cuts the rows its readers released ([A loop in
rounds](#a-loop-in-rounds)). A consuming store answers a pull from its snapshot. Its first
consume opens it, and a pull before that answers the unopened store, which states nothing final.
It steps only at its pipeline's consumes, or its scope's. A transaction store's writers decide only
against a tile it published. In pull mode a store steps itself at a pull.

In pull mode an induction store releases its body whole once the body is terminal and every decision
is stepped, and a transaction drive releases its source whole once it is done. A nested induction
drive releases each row of its source it calls complete, in either mode. A consuming nested store
releases its body a position at a time, and whole each row the body calls complete once its every
decision is stepped, at every level above its positions: the release through the decided path names
the row's positions only, not its paths past the last of them. A consuming store wakes no reader
outside its cycle: its readers there take the rows it closes from its pushes, and the planner
refuses a store read inside the cycle of a store that steps itself (`Planner::beneath_cycle`). An
induction store's seed sits behind an entry placed in the pipeline of the loop's scope, which takes
no push of it, since the store reads it by pull at a step, and records what the seed has decided. A
transaction store reads its seeds as its input 0 instead (below). A drive with no
rows above it states complete every position below its next one that its source calls complete along
with every position before, so a position it reads past, one the source filtered out or holds
nothing at, is stated as one it emitted (`complete_prefix_below`). An induction store with no rows
above it releases its body through what the body states complete and holds no decision at, and a
transaction drive releases its source through what it has read past, so either releases such a
position without waiting for a later one to be decided. The dispatcher's finish checks that a
store's input released every morsel the pipeline consumed.

`run_program` plans a transaction store's pipelines where it reaches a reader slot of the store's
fan-out (`TileProducer::store_read`), one per input, numbered one after another. The pipeline of an
input reads the pipelines beneath the store's cycle under that input: a subtree that reaches no
recurrence slot of the store (`reaches_recurrence`) is planned as any chain is, and inside the cycle
a breaker is no pipeline. A store's pipelines are ordered, since a store decides its positions in
order. A store that steps itself runs in the run's dispatcher, and the pipeline of an input that
reads pipelines reads the input whole, or over a live source each delivery once those pipelines have
decided it (below). A transaction store with seed streams reads them as its input 0, ahead
of its writers' sources, which are its inputs from 1: each seed is subscribed behind an entry placed
in input 0's pipeline, a push of any seed queues that input whole, and the store's consume of it
opens the store. A store opens before it steps, so each writer's pipeline reads input 0's, its
sibling, and takes no package before input 0's has finished. Once input 0's pipeline
has consumed its package, each writer's records it wholly decided, which releases what it parked
(`Dispatcher::opens_before`, [Parking arrivals until a read is
decided](#parking-arrivals-until-a-read-is-decided)). A store's decided push that reaches its own
pipelines around its recurrence is no read and records nothing. An induction store runs in a loop's
scope instead ([A loop in rounds](#a-loop-in-rounds)). A reader of a store reads every pipeline of
it, so its queue closes once the last of them has finished. The pipelines of
one store share one record of what the store has pushed (`Dispatcher::share_pushes`), so no tick is
pushed twice, and `plan_edges` plans their edges into one reader as one. The planner refuses:

- outside a loop's scope, a nested transaction store, one per enclosing row, whose frontier a flat
  morsel does not name;
- a store inside the cycle of a store that steps itself, which no round reaches;
- a transaction store of several writers whose sources' positions are neither `UInt` positions nor
  the tagged positions of a concatenation, which key order cannot compare.

The planner asserts that a transaction store has a writer: its keys are the footprints of its `with
begin():` blocks, each one of its writers ([How many commit stores a program
has](../ccl/design/mutability.md#how-many-commit-stores-a-program-has)).

#### Commits in key order

A consuming transaction store commits in key order. Pull mode commits in the order
`CommitProducer::drain` attempts proposals, writer by writer from a start that rotates each pull.
The key of an item's decision is `(𝑝, 𝑤)`: the source position 𝑝 of the item, then its writer's
index 𝑤. Two writers' positions compare level by level (`key_order`). A `UInt` position comes before
a tagged one, a concatenation's. Two `UInt` positions compare as their values do. Two tagged
positions compare by tag, then by their arms' positions in key order, so within one writer key order
is the order its source iterates. The order is fixed and the same at every morsel size;
[8.5 Ordering and concurrency](../../docs/chl-spec.md#85-ordering-and-concurrency) leaves writers
whose only trigger is the program start unordered. A writer over `[60] ++ [10]` beside one over
`[50]` commits 50 at `0`, then 60 at `` `0(0) ``, then 10 at `` `1(0) ``. Key order puts every
tagged position after every `UInt` one, so beside a writer over a live source a writer over a
concatenation commits nothing until the live writer's stream states every position decided.

The store, its writers and their drives speak through tiles only. A transaction drive's body-input
row carries its item's source position after the read slots and the item (`item_position_field`,
`_{r+1}`). The body reads no position, so its domain lists the slots and the item only
(`transaction_body_domain`, `src/ccl/infer/emit.rs`). The writer copies the position into its
proposal, whose record is `{snap, reads, writes, pos}` (`proposal_stream_tiling`).

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
(`CommitProducer::passed`). Where 𝑝 is no position of the writer's source, a position of a different
shape, the writer has passed it where key order puts 𝑝 before every position of its source, where
its stream states every position decided, or where the store has taken one of its decisions at a key
at or past 𝑝. The stream states what its drive had decided when the writer was pulled, which is
short of the decision the same pull brings. A proposal commits where the engine validates it. A
decision that proposed nothing stands where nothing has committed since it was made, since the store
holds no read set for it. A decision that neither commits nor stands keeps its key. The store names
the item in the writer's `again`, publishes its state, pulls the writer, and takes the fresh
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

A transaction store finishes an input as any breaker does, pushing what it has decided. It counts
the inputs that have finished, and the last of them settles the store
(`SteppedStore::settle`): it takes what each writer still decides and commits every held decision
in key order, until a pull of every writer brings nothing. That pull finds each writer terminal, so
the store is terminal, which the finish then checks.

A drive releases an item from its source at the take rather than at the commit. A drive that takes
over a running program starts where the source's release says
([program-evolution.md](../ccl/design/program-evolution.md#where-a-producer-registering-now-starts)),
so it would skip an item whose decision a store held uncommitted. A dispatched run runs no program
that another takes over ([Running a compiled program](#running-a-compiled-program)), and a resuming
drive under a store that states `writer_takes` panics at its first pull.

### The dispatcher

`Dispatcher` (`src/interpreter/dispatcher.rs`) holds the graph of pipelines, which pipelines each
one reads and so which one reads it, a queue of work packages per pipeline, and the morsel size
`morsel_rows`. A work package is a pipeline, a guard for its breaker to consume, one morsel of at
most `morsel_rows` held rows, and the package's index in the pipeline's queue. The dispatcher holds
no breaker: the driver, `run`, reaches each breaker, with the input of it the pipeline consumes,
through a handle its caller passes, indexed by pipeline, and borrows it for one call at a time.

`Dispatcher::new` refuses a zero morsel size, a graph with a cycle, and a pipeline that reads one
pipeline twice. A pipeline may read several pipelines, and its queue closes at the finish of the
last of them. A work package is a guard of the breaker's own input, whichever
pipeline's push queued it. Several pipelines may read one. The release of one reader would remove
rows from the breaker's state that another has still to read, so readers of one pipeline need a
`FanOut` between them, which the dispatcher does not check.

A source pipeline, one that reads no pipeline, is queued the regions of its breaker's input that
have arrived. `Dispatcher::notify` queues one such region, cut every `morsel_rows` positions where
it names finite runs of positions (`Value::UInt` keys) and whole otherwise.
`Dispatcher::close` says no more of the source's input arrives. A pipeline that reads pipelines can
also take arrivals (`Dispatcher::take_arrivals`): it is notified and closed as a source is, and its
queue closes once both its close and the finishes of the pipelines it reads have happened
([Reading each row once](#reading-each-row-once)).
`Dispatcher::start_source` queues the input whole and closes the source: where the input's tiling
states a finite range of positions for its outermost keys (a `UIntRange`), the dispatcher cuts it
every `morsel_rows` positions, the last morsel open above. Any other input starts as one package at
its universal guard: a sparse source's keys are not known before it is pulled. `Dispatcher::limit`
caps a source's packages queued and not acknowledged: `notify` waits while the
source has that many outstanding, and `try_notify` answers that it did not queue. A notify admitted
below the limit queues every morsel it cuts, so the packages outstanding pass the limit by at most
one notify's morsels less one, for one thread that notifies. A notify returns once the run fails,
having queued nothing.

`run` starts every source whole. It consumes the package at the front of the lowest pipeline's
queue that has one. When no pipeline has one, it finishes the lowest pipeline that may finish, and
it stops once every pipeline has finished.

`Pushes::push_final` pushes what a breaker has decided and its pipeline has not pushed before, its
final guard less the region pushed, one package per morsel the breaker cuts it into
(`BreakingProducer::morsels`); a breaker no pipeline reads cuts nothing. The dispatcher keeps each
breaker's pushed region, which the pipelines of one breaker share (`Dispatcher::share_pushes`). A
push computes the difference and grows the region in one step under that region's lock, so two
threads pushing for one pipeline push disjoint regions, and a push, after a consume or at the
finish, pushes only what no earlier push did. The driver lands a push
made after a consume at once (`Dispatcher::land`), before it acknowledges the package, so a reader
may claim it while the pipeline runs; the finish lands its own push and closes the queue of each
pipeline that reads it, where every other pipeline that one reads has finished. A breaker whose
output is one value, `Aggregate`, `ExtractAggregate` and `ExtractFinal`, pushes one morsel. `Memo`
and `MapAggregate` cut at the outermost keys they hold, in key order (`cut_at_keys`): a cut falls
before every `morsel_rows`-th held key the guard names, the first morsel reaches down from the
guard's lower end and the last is open above. The morsels partition the guard exactly. A key the
breaker states absent rides in the morsel that covers it, so the releases of a reader's input at its
morsels add up to the whole guard, and a reader that is final once its input is released whole, such
as `Aggregate`, becomes final. A released key is in no morsel, because the final guard already
excludes it. A guard naming no more than `morsel_rows` held keys is one morsel. A package is a guard
of the reader's input tiling, as the reader's chain restates the morsel, and `run` asserts in a
debug build that a package fits its breaker's input.

A push lands by climbing the breaker's consumer (`ProducerBase::downstream`) one morsel at a time,
as a projection of the breaker's keys at any level (`Consumer::push`). Each consumer between two
breakers restates the region in its operator's keys, as it restates a notification ([The
notification contract](#the-notification-contract)), and passes it on: a fan-out to every live slot,
a tagged union under the arm's tag. No gate holds a push back, since every pushed region is a work
package, and a consumer that pulls ignores it, so a push wakes no one. The `dispatcher::Entry` at
the input of each breaker the push reaches queues the region, as a guard of that breaker's input
tiling, for the breaker's pipeline, less what is queued for that pipeline already. The difference
and the queue's growth are one step under the queue's lock, so a push that reaches a breaker along
two paths, as a filter reads one memo for its values and its predicate, is queued once. A push an
operator widens to `Everything` on its way fails the run at a reader that reads that pipeline's
pushes (`Landing::widened` marks the path, `Landing::queue` refuses it), since the reader could not
tell which of its keys it names: a reader reached that way reads the pushing pipeline once it has
finished, instead of its pushes. A reader that parks takes no row from such a push, and reads each
row once its reads have decided it ([Reading each row once](#reading-each-row-once)). A push that
re-enters a consumer it is passing through has met a cycle, and fails the run too. A compiled
program's dispatched run notifies no consumer: a producer that caches what it reads reads it again
where a store steps or a live source yields more (`TileProducer::read_again`), and a debug build
checks that no consumer is notified inside the run (`dispatcher::debug_assert_outside_a_run`).
`notify`, its gates and `WakeupQueue` serve pull mode.

`dispatcher::finish_pipeline` finishes a pipeline. It asserts five invariants before it calls the
breaker: the pipeline has not begun to finish, its queue is closed and empty, no package claimed for
it is in flight, every pipeline it reads has finished, and its breaker's input has released every
guard the pipeline consumed. A pipeline consumes only rows its reads have decided
([Reading each row once](#reading-each-row-once)), so its input releases them. The release check is
closed
over the input's tiling (`TileGuard::closed_over`): an input that released a row through the last
position of its finite range of positions has released the row, though the difference of the two
guards names the row's paths past that position. A source's input releases the regions queued for
it; a reading pipeline's input releases only what the guards pushed or queued at the start for it
name, and nothing at all when nothing was; a pipeline that reads its input whole releases all of it.
A debug build also asserts that the morsels of a pushed guard partition it (`partition_gap`), and
that a pipeline consumes each region once: a guard pushed to a pipeline meets none pushed to it
before, except a loop's round, which reads its row again ([A loop in rounds](#a-loop-in-rounds)).

The dispatcher reads a breaker's input `input` through `input_tiling` and `input_released`, the
tiling a package's guard is a guard of and the guard the breaker has released of that input, so a
breaker whose input sits inside a shared cell can answer both.

A compiled program's dispatched run queues no wake-up: `WakeupQueue::request` drops one inside the
run (`dispatcher::in_a_run`). A breaker's reader learns of what it holds through the push.

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
predicate, reads it once. A pipeline that reads directly a pipeline another breaker's pipeline reads
is refused, since only a fan-out slot keeps one reader's release from removing what another still
reads. The pipelines of one store's inputs count as one reader: the store reads and releases a seed
once, when it opens. A store is the breaker of a pipeline per input, and a loop's scope of a
pipeline of its own ([A store as a breaker](#a-store-as-a-breaker),
[A loop in rounds](#a-loop-in-rounds)), which the walk plans where it reaches a reader slot of the
store's fan-out (`TileProducer::store_read`). Each package reaches its breaker by walking the chains
again, and the pushes a call makes land once the walk has returned, since a breaker reached through
a fan-out slot is called while the walk holds the fan-out its push climbs.

Before the run, the planner reads each edge from a pipeline to the pipeline that reads it off the
consumers between them (`Consumer::route`). Each consumer declares how it passes a push on without
any region being pushed: a consumer that keeps its operator's input's keys passes the route on, a
tagged union's arm passes it on under the arm's tag, a widening consumer marks it widened
(`Routes::widened`), and the `Entry` of a placed breaker records its pipeline. Where every path to
the reader's entry keeps the keys, or the pushing breaker holds one value, whose push is
`Everything`, a push names the rows of its own keys. Where a path widens them, as a lookup's table
reaches its reader, a push names every row of the reader's input. Either way the reader parks the
rows a push brings until the pipelines it reads have decided them, and reads each once
([Reading each row once](#reading-each-row-once)). A reader reads its input whole
(`Dispatcher::read_whole`) where a pipeline it reads pushes along no route to it, or where no push
and no region queued at the start names a row of its input. Which region of the reader's input a
push names comes from a probe: the read pipeline's breaker pushes `Everything` through its consumer
into a landing that records what reaches each entry instead of queueing it (`Landing::probe`). So
is each range under a reader of pushes probed, such as the positions of a literal arm of a
concatenation. A constant keeps no consumer.
A constant whose keys a reader consumes is one of four kinds, and none brings a key the ranges and
the pushes do not name:

- a list literal's table, the function operand of a `MapResult` over the literal's positions
  (`IterateExtent`), so the positions bring every key the table would;
- bound by a `let`, beneath the binding's `Memo`, whose pipeline is a source and reads its input
  whole;
- empty, which brings no key;
- a scalar, which has one position, so any push to its reader names all of it.

`run_program` refuses, in a debug build, a constant collection beneath a reader of pushes that is
not a function operand. What the ranges bring, less everything the pushes can name, is queued for
the reader at the start of the run as one region (`Dispatcher::queue_for`).

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
(`SinkBreaker::main`) hands the `DataSink` the caller passes `run_program_into` the output's
answers. With no live source it hands one answer, at the pipeline's finish: the answers of its
packages merged with a pull of the producer at the universal guard, the answer pull mode's one pull
makes. That pull states what the producer states complete and adds no key, since the packages
consumed all the producer holds. Where the output reads a loop's scope, the pull also answers the
rows the loop's rounds have written, each final as it is written (`SinkBreaker::reads_a_loop`). Over
a live source the run finishes the output only once every source yields everything, so the breaker
hands each package's answer as it consumes it (`SinkBreaker::hand_each_package`), and at the finish
the pull's answer, which states the output complete, unless an answer before was terminal. The
pipeline is ordered (`Dispatcher::order`), so it consumes its packages in queue order. The answers
add up to a terminal tile, as pull mode's last pull is. `run_program` passes a `DataSink` that
merges the answers (`Collected`) and answers the merged tile (`Run::main`). The driver holds the
producer, released whole, once the run returns.

The run pulls only the breakers' inputs. The program is compiled with
`GlobalContext::defer_sink_pulls`, which leaves out the pull each sink takes once subscribed, and
`CompiledProgram::sink_pulls_deferred` records it. The planner refuses, before anything runs, with
a `Refused` error that names the shape, and pull mode runs every refused program:

- a program compiled with its sinks pulled;
- a live source whose arrivals reach no pipeline's entry or reach one as a region that is no
  projection of its keys (below);
- a pipeline notified of a live source's arrivals beside a range no live source yields, or beside a
  pipeline it reads whose pushes arrive as its own keys, since no arrival names those rows;
- a pipeline read directly by a pipeline another pipeline reads;
- a breaker with no consuming mode (`Breaker::no_consuming_mode`): a transaction store of several
  writers over positions key order does not compare, neither `UInt` positions nor a
  concatenation's tagged ones ([Commits in key order](#commits-in-key-order));
- the stores [A store as a breaker](#a-store-as-a-breaker) lists.

A range over a live source's domain (`TileProducer::data_sources`, an `IterateExtent` over a
`DataSourceDomain`) is no range the run queues whole at its start. The pipeline that stands for it
in the run's dispatcher is live (`Planned::live`), and the run notifies it of what the source yields
in one of four ways (`LivePipeline::poll`):

- Every route from the range's consumer to the pipeline's entry keeps the range's keys
  (`Consumer::route`), and a push of one key reaches the entry as a projection of the input's keys
  at any level, as a `Converse` restates its input's keys one level in: the pipeline is notified of
  the keys each delivery adds, as the region a push of them brings its entry.
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

A scope or a store that also reads pipelines takes each delivery once those pipelines have decided
it (`Dispatcher::take_arrivals`,
[Parking arrivals until a read is decided](#parking-arrivals-until-a-read-is-decided)).

A drive and a transaction store decide positions in order, and a debug build checks that a delivery
adds positions after every one before it. A dispatched run delivers no notification: a loop's scope
has its drive read its source once the drive has emitted every position it read, and a delivery to a
transaction store has its writer's drive read its source again (`Breaker::read_source_again`). A
package of positions the drive emits none of, such as the delivery that completes a source or one of
keys a filter on its source drops, runs no round of a position; the scope runs a closing round at
the package, queued to every inner pipeline but the sources in the store's chain, which has them
read what the drive read past, and the store's step releases the package. A pipeline other than a
store or a loop's scope whose chain reads a live source and a pipeline takes the source's arrivals
beside the pushes of the pipelines it reads, and parks them
([Reading each row once](#reading-each-row-once)).

The run starts the other sources whole and then polls: each pass asks every live source for new data
(`DataSourceDomainExtentImpl::check_for_new_data`), notifies each live pipeline of the keys its
sources yield beyond what it was notified of (`get_yield_predicate`), and runs what is claimable. A
live pipeline closes once its sources yield everything, and the run ends once every pipeline has
finished. Once a pass's claims run out, every breaker pushes what it holds and no push named, and
the pass runs on while that brings anything: `MapAggregate` pushes only so, and finishes only once
every source yields everything. A run starts with every breaker pushing what it holds
(`dispatcher::push_held`), as a run after a pause or a reload starts over breakers an earlier run
consumed into. A pass that finds nothing new calls the caller's `on_idle` after running what is
claimable (`run_program_polling`): `run_program` sleeps for a millisecond, and a test feeds the
source there. A range reads one source, keyed by positions: the planner refuses a cross product of
sources, a source beside a static extent, and a source with other keys, whose arrivals no region of
one source's positions spells.

The binary runs a program dispatched where `CAMBRA_DISPATCH` is set to anything but `0` or the empty
string, and neither `--inspect` nor `--control` is given, at morsels of `CAMBRA_MORSEL_ROWS` rows
(1024 unset; a value that is no positive count panics). It prints each answer of the `main` output
where the answer holds a key or a value or is terminal, as pull mode prints each pull's answer: a
collection cut into several morsels prints once, and a map over stdin prints each line's answer as
the line arrives. A refused program runs in pull mode after a note on stderr, in the
context the dispatched run compiled it in: the compile has opened its sources and sinks, a port
bound or stdin taken, which a second compile could not open again.

Every program of the differential suite (`tests/it/differential_interp.rs`) runs dispatched too, at
morsels of one row and of every row, and answers what pull mode answers, or the planner refuses it.

#### Parking arrivals until a read is decided

A loop's scope or a transaction store steps on the pipelines it reads by pull, and a step that pulls
a pipeline not yet final reads a partial answer: a seed `sum(source1())` before `source1` yields
everything opens the store at a wrong value. A scope or store over a live source that reads
pipelines parks its arrivals (`Dispatcher::park`). A notify of a region that some pipeline it reads
has not decided keeps its morsels out of the queue. Each pipeline's decided pushes record what it
has decided of the reader's input ([Completeness in pushes](#completeness-in-pushes)). The decided
push that covers a parked morsel appends it to the scope's or store's queue, before the pushing
pipeline counts its finish toward the reader's close. From then on each delivery the reads have
decided is queued as it arrives.

The parked morsels are guards of the scope's or store's input, not rows: the rows stay in the live
source, which releases none of them until the scope or store consumes them. Over a seed whose
sources never yield everything, the scope or store never steps, and its source keeps every row it
delivered.

A pipeline that reads its input whole (`Dispatcher::read_whole`) parks that input from the start. A
decided push releases the part of a parked region that every pipeline the reader reads has decided,
and the rest stays parked (`Dispatcher::decided_part`). A transaction store over a let-bound list,
whose list's pipeline is decided before any delivery, reads its input then. A morsel a source's
notify cut counts as one of that source's packages, so it is released whole.

A loop's drive reads its source by pull, behind an entry no planner places in the run's dispatcher,
so a push of the source stops there. The positions the drive emits are its source's keys, so the
entry records a decided push of the source at the loop's scope, as the same keys of the store's
input (`DecidedTarget`, set by `InductionStoreProducer::decide_through_drive`). A loop over a
let-bound list of a live source then steps at each position the list has decided, before the source
yields everything.

#### Completeness in pushes

A key of a pipeline's output is decided where its value can no longer change and its presence or
absence is settled: a key present in the output, whose value is complete once it is there, or a key
the domain predicate rules out ([The completeness contract](#the-completeness-contract)). That is
the region `Tile::to_guard` names and `BreakingProducer::decided` states. The decided region enters
the dispatcher as a guard, pushed up the consumer chain beside the region that changed, and the
dispatcher decides that a read is final by guard containment.

Both ends of a pipeline push a decided region:

- A range pushes its decided region each time it grows (`Dispatcher::land_range_decided`). A range
  over a static extent pushes the universal guard when the run starts. A range over a live source
  pushes the keys it has delivered for good.
- A breaker pushes its decided region beside its final guard (`Pushes::push_final`).

A push carries two guards: the region that changed, which a reader reads again, and the region
decided. An operator restates each in its own keys by its own rule:

| Operator | Changed region | Decided region |
| --- | --- | --- |
| keeps its input's keys | unchanged | unchanged |
| keeps them under another spelling (`Uncurry` beneath a standing level) | restated (`scheduler::restating`) | restated |
| looks a collection operand up at each row's own key (`MapResult` over values that equal their keys, as a group-by's) | the rows whose last key it names, under every path (`keys_looked_up`) | the rows whose last key it names, under every path, as a part of what those rows depend on |
| widens its input's keys | the universal guard (`Landing::widened`) | the empty guard, and the universal guard once the input's decided region is universal; an outermost `Uncurry` restates it as the pairs its outer keys head (`scheduler::widening_restating_decided`) |
| reads several inputs (`Zip`, `Filter`, `Product`) | each input's region, as it arrives | the intersection of the inputs' decided regions |

A widened change rounds up and a widened decided region rounds down: every output key of a widening
operator depends on every input key, so none is decided until all of the input is. Each restatement
is exact, as every guard operation must be ([Guard operations are
exact](#guard-operations-are-exact)). The dispatcher intersects the decided regions of inputs that
come from different pipelines, since a step needs each pipeline it reads to cover it. An operator
intersects those of inputs within one chain, as a static arm beside a live arm.

A pipeline that reaches a reader along a path whose decided region names only part of what a row
depends on (`Routes::deciding_part`), and along another path, decides the reader's input only once
it is whole (`Dispatcher::decides_whole_only`). The dispatcher records one region per pipeline, so
it cannot intersect the paths. A widening passes a region that is not whole as nothing, and a
lookup's operand names the rows reading a decided key whatever their input holds. A group-by's memo
is the case: it reads a list both as its rows and as the table of a lookup.

The dispatcher keeps, per pipeline, the union of the decided regions each pipeline it reads has
pushed. A unit of work is claimable once that union covers the region the work pulls, checked with
`guard_minus`:

- a whole read (`Dispatcher::read_whole`);
- a step of a store or a loop's scope over a live source;
- a parked delivery of a store or a loop's scope (`Dispatcher::park`);
- a row a push, an arrival or a loop's round brings
  ([Reading each row once](#reading-each-row-once)).

Loop body pipelines use the same rule in the shared dispatcher, with keys carrying the loop's
position. A nested request takes a round's row once the pipelines its rounds pull are quiescent
(`Dispatcher::follow`), since it reads them by pull and no decided push of theirs reaches it.

In the program below, store `a` reads a static list, and the loop reads a live source that never
yields everything:

```
a: Mut(Int, Txn) := 100
for r in [10, 20]:
    with begin():
        a := a - r
last := await_final(a)
for x in source1():
    last := last + x
out << last
```

The range over `[10, 20]` pushes the universal guard at the start, and `a` pushes its decided region
once it has consumed it, so `a` is final then and the loop steps per delivery of `source1`, with no record of
which pipelines have closed.

A breaker states its decided region in `BreakingProducer::decided`, which is its held region but
for the induction store: the transaction store its positions through its watermark, a memo, a map
aggregate and an induction drive their tiles' `to_guard`, and an aggregate or an extraction
everything once it is final. An induction store holds nothing until it is terminal
(`BreakerState::held`), since a reader pulls its tile whole, but decides its positions one at a
time: its decided region is its tile's statement, the positions it has stepped, row by row under
rows, so a reader of one row of a store per row waits for that row alone.

#### Reading each row once

A pipeline's chain can answer nothing for a row whose input is not yet decided. An operator that
reads a sibling input does not answer a row from that input before it is final: `MapResultToConst`
answers no row while its scalar constant is not terminal (`empty_beneath_live_rows`), a binop
combines only the positions both operands hold, `CheckedLookup` answers a missing key only once its
table is terminal, a `VariantWrap` emits a collection payload only once it is whole, and
`ExtractFinal` answers once its source is terminal. The planner keeps a pipeline from consuming such
a row early: the pipeline parks each row a push or an arrival brings until every pipeline it reads
has decided it ([Parking arrivals until a read is
decided](#parking-arrivals-until-a-read-is-decided)), so it reads each row once, final, and its
breaker's input releases what it consumed.

A row waits only for the pipelines that reach it. The planner records, per pipeline a reader reads,
the region of the reader's input that pipeline can decide: what a push of its every key, wholly
decided, lands as at the reader's entry (`Dispatcher::reaches`). A row outside that region does not
depend on the pipeline. A pipeline read by pull, whose push reaches no entry of the reader, reaches
all of its input, and the reader records it whole once it is wholly decided.

Every pipeline that reads another parks the rows its pushes, its arrivals and its start bring, in
the run's dispatcher and in a loop's scope's (`plan_edges`). A push brings the rows it names at the
reader's entry, a widened one every row, less what a push brought before. A pipeline read along no
route is read by pull, so its reader reads its input whole (`Dispatcher::read_whole`), released as
the pipelines it reads decide it.

A pipeline whose chain reads a live source and other pipelines takes the source's arrivals
(`Dispatcher::take_arrivals`), and its queue counts its close as one more event. It is
queued no start region and reads nothing whole.

A pipeline that takes arrivals brings rows only from its arrivals: a push brings it none, since its
arrivals name its rows. A push of one value that names only rows the arrivals bring reaches rows
that wait parked for its decided push.

A loop body reader parks arrivals until its dependencies decide their rows. Its keys carry the
loop's position, so a decided region names the rows of one position. A round queues its row to each
inner reader as a push of the row from the drive lands at the reader's entry, restated by every
operator on the way (`InductionStoreProducer::row_for`), and queues none to a reader whose input has
released the row whole. A row a round queues waits whole until the pipelines the reader reads have
decided all of it, the row's end included, which a closing round's reads state
(`Dispatcher::queue_round`). Every round queues its row whole, whatever it queued before, since a
closing round reads its row again (`Queue::append_again`). A nested loop's scope takes a round's row
only once the pipelines its rounds pull are quiescent (`Dispatcher::follow`), and so does a reader
of a nested loop's scope.

A pull beneath a path over a live source's domain states the source's positions complete only
through those it delivered, not past its last once it is complete, so a reader of a push beneath its
outermost keys does not release those positions.

`[x for x in source1() if sum([1, 2, 3]) > 5]` at `main` takes each delivery's rows once the sum is
decided, before the first delivery. With `sum(source1())` in its place, the rows of every delivery
stay parked until the source yields everything, where the sum is decided.

#### A loop in rounds

An induction loop runs one round per source position. Its request, body and ordered store-step
pipelines share the run's dispatcher. The request and store-step pipelines target the same
`InductionStoreProducer`. Its optional `InductionRun` retains the pending request package, current
round and global pipeline IDs. The producer retains the accumulator and its published snapshot;
scheduling metadata contains no handle back to its own store cell. `Dispatcher` queues guards and
tracks claims, acknowledgements and finishes; it holds no loop or operator state. The
`run_program` planner and execution handler live in `dispatcher/plan.rs`.

The planner configures each body graph locally, removes whole-input breakers that must remain in
pull mode, and appends the configured graphs to the run. Composition remaps dependency and follower
indices. The `Planned.rounds` report remains a tree with indices local to each sibling list; those
indices describe planning and are not runtime pipeline IDs.

Each plan installs fresh run metadata through a plan-scoped `InductionRuns` owner. The owner covers
graph construction and execution, and clears run metadata when the plan exits or unwinds. Cleanup
clears body entry placements and keeps engines, snapshots and input releases unchanged.

A scope's request pipeline is ordered. Claiming a request opens its store if necessary and queues
one round. The execution handler retains the request's acknowledgement until every position and
closing round in that request has stepped. Other pipelines remain claimable during that interval.
A nested scope's request names one row of its store and remains in flight until that row finishes,
so the outer store-step cannot pass a pending nested row.

A round proceeds as follows:

1. The store has its cycle's pull-mode operators read again (`TileProducer::read_cycle_again`). The
   previous step pulled them before the body pipelines consumed this position.
2. Explicitly queued source pipelines receive the position. Nested requests and closing-row readers
   receive the region restated at their own input entries. The store-step pipeline receives one
   package for the same round, after those body packages have been queued.
3. The body pipelines consume through the shared dispatcher. Their held and decided output pushes
   land before their packages are acknowledged.
4. Once claims drain, the execution handler has the active scope's body pipelines push held state.
   Followers remain held until that scope's publication pass changes nothing. `MapAggregate` can be
   quiescent while it still holds unpublished groups, so quiescence alone does not release a step.
5. The serial execution driver releases followers for one claim, then holds them again before
   another publication pass. The ordered step follows every direct body pipeline and becomes
   claimable only after they are quiescent. Its handler steps the store and queues the next position
   or closing row.

The execution driver coordinates one claim at a time because breakers use `Rc<RefCell<_>>`. A scope
compares the dispatcher generation only around its own publication pass; no other claim runs during
that pass, so another scope's work cannot be mistaken for one of these pushes.

Body pipelines are held from claims and finishes until their first request activates them. Their
non-source entries then stay placed at global IDs until the scope finishes. Each body entry accepts
pushes only from the configured body graph (`Dispatcher::restrict_ingress`); a push from outside
that graph stops there. Cross-scope dependencies are represented by request pipelines instead of
entering a body outside its current round. A breaker inside the cycle is reached by walking the
store's chain while its cell is borrowed, so recurrence reads use the published snapshot.

The drive (`InductionDriverProducer`) is an explicitly queued source pipeline. Its source entry
stays unplaced; the controller alone queues positions for the drive. The drive consumes at an empty
guard to read its source without emitting a position. A position package emits only the next
position it covers; a consuming pull returns that rendering and advances nothing. A position the
source filters out runs no position round.

The first request has the drive read its source before the store's opening step publishes its seed.
A flat request reads the source again after its buffered positions run out, at most once per
request.
A nested row reads at its start and end. Its closing round queues the whole row to every body
pipeline except the sources in the store's chain, including a row containing no positions. The last
position alone does not state the row's end, so this closing round has every reader observe that
completeness and lets the store release the row whole. A row is restated at each reader's input by
`InductionStoreProducer::row_for`; a reader whose input has released the whole row is not queued it.

A flat package can name positions the source filtered out, or a delivery that only closes the
source.
If it emitted no position and its input remains unreleased, it runs a closing round at that package.
The body pipelines read what the drive read past, and the store step releases those absent
positions.

Finishing a request pipeline closes its body sources. The execution handler retains the finish
until all body and step pipelines have finished in the same dispatcher. The store is terminal then;
its final push lands before the request pipeline's finish releases its readers. A nested store
releases its body a position at a time and each row it decides whole. Its readers release their
rows as they finish with them, and the store's offer cuts rows released since its last step from
the snapshot. A flat store holds nothing short of terminal.

A scope whose store has 𝑑 row levels above its positions runs rounds at paths of 𝑑 + 1 keys
(`Projection::of_path`). The planner asserts that operators its rounds pull restate a projection
at that level (`Planner::unrestated_in_rounds`). This check covers nested loops and stores per
comprehension row. The walk stops at consuming breakers: their consumes pull their own inputs, and
their scopes check those pulls. A breaker left in pull mode passes the pull on. A level violation
panics before execution.

#### One finish per pipeline

A run has no batches. A pipeline's queue is open while appends land in it: a source's notifies, and
the pushes of the pipelines it reads, which land as those pipelines consume and at their finishes.
The queue closes at the source's close, for a source, and at the finish of the last of the
pipelines it reads, for a reader, which a count of the pipelines it reads that have not finished
tells. A pipeline that takes arrivals beside the pipelines it reads counts its close as one more
event ([Reading each row once](#reading-each-row-once)). Nothing is queued for a pipeline once its
queue is closed, so it finishes once: a claim hands out its finish (`Next::Finish`) once the queue
is closed and every package in it acknowledged, and a compare and exchange of the pipeline's phase
picks one claim. The finish is the breaker's last call (`Breaker::finish`). It pushes what the
breaker decided and no consume pushed into the queues of the pipelines that read it, and closes the
queue of each whose last pipeline read to finish it is this one. The finish of the last pipeline to
finish ends the run.

A reader learns what a breaker decides from its pushes after each consume, not from a finish: every
breaker pushes while consuming, but `MapAggregate`, whose groups beneath its outermost keys a
reader's chain cannot restate (`BreakingProducer::pushes_while_consuming`). A run after a pause or a
reload starts over breakers that hold what an earlier run consumed, so it starts with every breaker
pushing what it holds and no push named (`dispatcher::push_held`), before any arrival.

In a loop's scope a reader takes a package only once every pipeline it follows
(`Dispatcher::follow`) is quiescent: it has consumed every package queued for it, and so has every
pipeline it reads (`Dispatcher::quiescent`). It takes no push of theirs
([A loop in rounds](#a-loop-in-rounds)). A claim of such a reader reads the package's index first,
then checks the pipelines it follows, then takes that index alone, so the check sees the work that
the package was queued after. A round holds its followers while its pushes settle
(`Dispatcher::hold_followers`). An ordered pipeline has at most one package in flight and
takes its packages in queue order.

#### Claiming from several threads

`Dispatcher` is `Sync`, and a claim takes no lock. A pipeline's queue is appended to while it is
open, and a closed queue takes nothing more. A source's queue grows at each `notify` and closes at
the source's close. A reader's queue is filled by the pushes the pipelines it reads land as they
consume, and closed at the last of their `finish`es, since each finishes once.

A queue's slots sit in buckets that double in size, each allocated by the first append that reaches
it, so a slot never moves. An append reserves its indices together, by compare and exchange on
`reserved`, and then writes each slot, once. The top bit of `reserved` says the queue is closed, so
an append reserves only while the queue is open, and one read gives both the count and the close. A
claim reads a slot only once it is written. The queue keeps the region its packages partition under
a lock that appends and the move of the pipeline to finishing take, and a claim of a package never
does. Two counters per pipeline only grow: `claimed`, the index of the next package to claim, and
`acknowledged`, how many packages have been acknowledged. Each pipeline's phase (running,
finishing, finished), a failure flag and the generation, the count of changes a waiting worker
waits on, are atomics too. A worker takes a lock only to sleep while there is nothing
to claim, and a change that can end a sleep takes it to wake the sleepers, only while there are
some. A pipeline that parks takes the lock on its parked rows at a push or an arrival to it and at a
decided push that releases them. The graph, the morsel size, the limits and the ordered pipelines
are fixed before the dispatcher is shared, since the methods that set them
take `&mut self`; every other method takes `&self`. The breakers are `Rc<RefCell<…>>`, which is not
`Send`. `run` claims on the calling thread, and no driver claims from several threads.

A worker asks `Dispatcher::try_claim` what to do next, and the answer (`Next`) is one of five:

| Answer | The worker |
|---|---|
| `Package(package)` | hands the package to its pipeline's breaker, then calls `acknowledge` |
| `Finish { pipeline, consumed }` | finishes the pipeline, pushing through `pushes(pipeline)` and the breaker's `finish`, then calls `Dispatcher::finish` with the pushes |
| `Wait(generation)` | calls `wait(generation)` and asks again |
| `Done` | stops: every pipeline has finished |
| `Failed` | stops: the run failed, whatever has not finished |

`claim` is `try_claim` and `wait` in a loop, and never answers `Wait`. A claim takes the package at
the front of the queue of the pipeline the worker prefers, where it may, and otherwise that of the
lowest pipeline whose queue it may take from. With no package to take, it finishes the lowest
pipeline that may finish. Single-threaded, with no
preferred pipeline, this is the order `run` follows, and a `Wait` there panics, because an acyclic
graph with every source closed and nothing queued has a pipeline that may finish.

A source pipeline may finish only once its queue is closed, so workers may start claiming before the
sources start: they wait until then, and no source finishes before its input has stopped arriving. A
closed source refuses a `notify`, a second `close` and a second `start_source`.

A claim reads `claimed`, and takes that index's package where its slot is written, by moving
`claimed` on with a compare and exchange. A claim that loses the exchange reads `claimed` again, so
no two claims take one package and none skips a package an append writes later: `claimed` never
passes `reserved`. A claimed package is in flight until the worker acknowledges it. `acknowledge`
refuses a package whose index no claim has handed out, whose guard is not the queued one, or that
was acknowledged before, the last through a flag per package that the first acknowledgement sets. A
pipeline may finish when it is running, its queue is closed and every package in it acknowledged. A
claim reads the count and the close in one read, and nothing is reserved after the close, so the
count of a closed queue is its last. The counters only grow, so a pipeline that may finish stays so
until it does. Its packages partition the region its queue was filled with, and the finish gets
that region as `consumed`: the regions notified to a source, its input whole for a pipeline that
reads its input whole, or the union of the guards pushed to the pipeline.

The claim that finds a pipeline that may finish moves its phase from running to finishing with a
compare and exchange, so exactly one claim finishes each pipeline. `Dispatcher::begin_finish` makes
the same move for a pipeline the caller names and asserts each condition;
`dispatcher::finish_pipeline` calls it. A finish's pushes collect in its `Pushes`. `finish` moves
the pipeline from finishing to finished with a compare and exchange, so a second finish is refused,
and then lands the pushes and closes the queue of each pipeline that reads it and reads no pipeline
still to finish. A push after a consume collects in a `Pushes` of its own, which `Dispatcher::land`
lands at once. A reader claims the packages landed there while the pipelines it reads run, and
finishes only from a closed queue. Its chain may therefore read the breaker of a pipeline it reads
while that pipeline consumes, which a driver on several threads would have to order; the breakers
are not `Send`, and `run` drives them on one thread. `finish` asserts that the reader has not begun
to finish, and dropping a `Pushes` whose morsels never landed panics.

An ordered pipeline has at most one package in flight. A flag per pipeline, taken by compare and
exchange before a claim of it looks and kept for the package it takes, admits one claim at a time,
and its acknowledgement drops the flag. Its morsels are therefore consumed one at a time, in the
order they were queued.

The pipelines of a transaction store share its breaker, and each is ordered on its own, so two of
them may each have a package in flight. A consume of one takes from its writer and commits from
every writer's queue ([Commits in key order](#commits-in-key-order)), so a driver on several threads
has to serialize the consumes and finishes of one breaker's pipelines; `run` drives them on one
thread.

A claim reads the generation before it scans the pipelines, and one that finds nothing to do while a
pipeline has not finished answers `Wait` with that generation. The generation advances after each
change that can let a claim succeed: an append (`notify`, `start_source`, `finish`), a close, an
acknowledgement of an ordered pipeline's package, of a limited source's package or of the last
package reserved in a queue, a finish, and a failure. A change the scan missed therefore advanced
the generation past the one the claim answers, and `wait` returns at once instead of missing it.
`wait` sleeps on a `Condvar` under a `Mutex` that guards no data, counting itself as a sleeper under
that lock before it reads the generation. An advance writes the generation before it reads the count
of sleepers, and takes the lock to wake every sleeper only when the count is not zero; all four
accesses are sequentially consistent, so either the sleeper reads the new generation or the advance
wakes it. Waking every sleeper at each advance costs spurious wake-ups and needs no choice of which
one to wake. A `notify` waiting at its limit waits the same way.

`Dispatcher::fail` sets the failure flag and advances the generation: every claim from then answers
`Failed`, and every waiter wakes. A worker thread holds the handle `Dispatcher::worker` returns for
as long as it claims, and dropping that handle while the thread panics calls `fail`, so no worker
waits for a package the panicking one claimed and never acknowledged. A dispatcher method refuses a
caller that breaks the protocol through one check, which calls `fail` before it panics, so the run
fails with or without a worker handle. That includes a pipeline the dispatcher does not have. The
debug-build assertions on a breaker's morsels and on a `Pushes` finishing through its own dispatcher
panic without failing the run. After a failure, `acknowledge` and `finish` record nothing, and
`notify` returns at once.

Every claim reads the generation and writes the `claimed` counter of the pipeline it takes from, and
an acknowledgement writes `acknowledged`, so those cache lines move between the cores that claim
from one pipeline.

A claim hands out a finish only when no package anywhere is claimable, so a pipeline ready to finish
waits behind the packages of every other pipeline, which delays its reader when the reader
is on the run's longest path. A reader starts on the first push of a pipeline it reads, which lands
after that pipeline's first consume, unless that pipeline pushes only at its finish
(`pushes_while_consuming`).

## Tile Operators

Each `TileOperator` is a static (compile-time) node in the dataflow graph. It knows its output
[`Tiling`] and can instantiate a live `TileProducer` via `subscribe`. Operators are constructed
during compilation; producers are created on demand at runtime.

### Operator identity and the graph the inspector reads

Production operators carry an `OperatorBase` with a construction-time `NodeId` and output tiling.
Operator and expression ids use the same counter; provenance attribution is specified in
[Operator conversion](../ccl/design/provenance.md#operator-conversion).

`OperatorGraph` supplies the inspector's `post-conversion` pane. `BoundarySession::into_graph`
walks from program outputs through `TileOperator::visit_inputs`, emitting each identified operator
once in depth-first postorder. A visited-id set terminates shared paths and cycles. Operators
without ids, including test doubles, are neither emitted nor traversed. Conversion records sink
identities with `record_sink`; the walk adds each recorded sink and its output edge.

`compile_program` walks newly constructed operators before subscribing them. Subscription takes
`CycleSlot` contents and store inputs, so a later walk cannot recover those edges. Reused operators
that were already subscribed expose only the inputs they still hold. The implementation is in
`operator_graph.rs`.

`visit_inputs` is required on every operator. The graph walk and the default `TileOperator::inspect`
implementation both read it; an omitted input can remove an edge or subtree from both. Its callback
borrows each target only for the call, permitting inputs held behind `RefCell`, including fan inputs
and `CycleSlot` contents. `inspect_annotation` supplies non-input metadata such as a constant's
value or variant tag.

Edges are stored on consumers and point to their inputs, opposite the direction of dataflow and
notifications. They describe held operator inputs, not necessarily distinct runtime subscriptions:
a fan slot can retain an edge after a sibling has subscribed the shared input. In dataflow terms,
an inputless operator has in-degree zero and a sink has out-degree zero.

| Edge property | Meaning |
|---|---|
| `Value` | Exclusively owned input, held in a `Box`. These edges form an ownership forest. |
| `Share` | A fan slot's reference to its fan input. Several slots may name the same input. |
| `Value { deferred: true }` | Input wired through a `CycleSlot` after its consumer was constructed. Ownership remains exclusive. |
| Role | Named field, vector position, or store key. These remain distinct even when their display labels match. |

`OperatorGraph::walk_starts` derives the ownership roots: recorded nodes targeted by no `Value`
edge. Sinks and shared fan inputs qualify. In debug and test builds, `assert_graph_invariants`
checks that every edge targets a recorded node, each node has at most one incoming `Value` edge,
and every node is reachable from these roots through `Value` edges. Exclusive ownership and
root reachability exclude value-edge cycles. The checks do not detect operators absent from the
recorded graph.

The default `TileOperator::inspect` recursively follows only `Value` edges. It omits shared inputs
and needs no cycle guard under the forest invariant. `FanOutSlot` overrides this method: its primary
slot descends into the shared input, and other slots render as reference leaves.
Deferred edges identify late wiring; removing them breaks cycles in the complete graph for layout.
This is separate from the value-edge forest:
`Share` denotes shared ownership whether or not that edge participates in a cycle.

`CycleSlot` holds an operator during construction, not runtime values. Its clones share one cell.
The caller fills it once, the graph walk borrows it through `peek`, and subscription consumes it
through `take`. An empty `take` cannot distinguish a never-filled slot from an already-taken one;
the subscribing caller must reject either case when it requires an input. Each setter closure is
`FnOnce`, but separate setters can be obtained; a debug assertion rejects filling an occupied cell.

A data source is not a graph node. `IterateExtent` enumerates its domain and registers scheduler
wake-ups; `MapResultWithSource` reads values at supplied keys. A source lookup descends from an
iteration of that source, since inference admits no literal source-domain key. The invariant is
pinned by `a_source_read_descends_from_an_iteration_of_that_source` in
`tests/it/inspector_goldens.rs`. Neither operator adds an edge to the source itself.
`source_nodes` derives source-to-iteration ids from the current graph's iteration-domain tilings.

[A node on the wire](../inspector_model/design.md#a-node-on-the-wire) owns serialization. Operator
nodes include a label, tiling, and input edges; boundary nodes have no tiling. Walk roots are
derived from the edges on both sides of the wire rather than serialized separately.

### Operator catalog

| Operator | Input Tiling(s) | Output Tiling | Description |
|---|---|---|---|
| `Constant` | None | `Scalar` from `Constant::new`, `DataFunction(domain → Scalar(codomain))` from `Constant::from_bindings`, any tiling from `Constant::collection` | Produces a fixed tile. Which of the two a bindings table is cannot be read off the value: in function position it is one value the consumer applies (a list literal's table), and as a collection it is what a map iterates. Every operator below derives its tiling from its input's, so the choice decides whether a map transforms the table or each of its outputs — and the call site states it. |
| `IterateExtent` | None | `DataFunction(extent → Scalar(extent))` | Enumerates all values in an `Extent`, producing an identity-mapping function (domain = codomain = extent). Holds no input, so it is the root a data source is read from: it registers a wake-up against each source its extent reaches (`Extent::for_each_source`), and its tiling names them. |
| `MapResultWithSource` | `DataFunction(DataSourceDomain → Scalar(DataSourceDomain))` | `DataFunction(DataSourceDomain → Scalar)` | Looks up each key of a data-source domain via `DataSourceDomainExtentImpl::get` to produce a function from keys to their output values.  Built with paths (`MapResultWithSource::projecting`, from `Source(name, paths)`: an empty list reads the whole value), it returns the leaf at the one path, or the tuple of the leaves in the order named, and its output extent is that of the leaf or tuple. |
| `Zip` | `N` inputs of `DataFunction(shared_extent → *)` tilings |  `DataFunction(shared_domain → Record(_0, … _N))` | Merges N function operators that share a domain into one function whose codomain is a Record Tiling of all their codomains. Prefer the free `zip_arms_at` factory at op-conversion call sites: it dispatches to `Zip` (function-tiled arms) or `MakeRecord` (scalar arms) based on the compiled arms' tilings, since the same CCL-level `zip` maps to either tile shape depending on upstream `input`. |
| `MakeRecord` | `N` inputs at any tilings | `Record(name: input's own tiling, …)` | Builds a product value ([A product value is a record of tiles](#a-product-value-is-a-record-of-tiles)). Pulls every operand whole, and forwards each field's release to that field's operand. |
| `MapResult` | Function: any tiling of type `A → B`<br>Data: any tiling whose deepest codomain is `Scalar(A)` | The data's levels, then the function's below the one applied, over the function's codomain | Applies a function to the data's **deepest codomain**, element-wise. Application consumes the function's outermost level, and whatever sits below that level becomes further levels of the output, because a tile holds one flat level list. So a one-level function leaves the data's shape alone and changes only its deepest codomain, while the two-level lookup a keyed collection presents contributes its inner level: a collection of keys yields one group per key, and a `Scalar` key yields just that key's group — the single-key lookup `groupby(c, k)(v)`, one level shallower because the scalar contributes none of its own. A key absent from a *settled* grouping is the empty group; absent from an unsettled one it is simply not answered yet, which the function's `domain_predicate` distinguishes. Construction asserts that the function's domain extent includes the data's value extent, with one exception: a `UInt` or range value extent at a `0..𝑛` domain, the erasure of a refined `UInt` or range that inference proved inside the range. A row whose key the function has not answered is **withheld** — dropped from the output, and its outermost-level owner subtracted from the output's `domain_predicate` — and answered on a later pull. The **data** input tracks the consumer's release; the **function** operand is re-read whole on every pull, so it is released only on a universal release. |
| `MapResultToConst` | `DataFunction(extent → *)` | `DataFunction(extent → C)`, `C` the constant's tiling | Replaces each value of a function input at the level op-conversion states with the same constant (or zips it in, per its mode), preserving the levels above it. A value at that level may itself be a collection, which the constant replaces or pairs with whole. A scalar constant must be present (terminal) before it can be broadcast: a still-absent one (e.g. a scalar read from a sibling induction loop that has not yet converged) yields an empty, non-terminal output rather than fabricating a value for the unknown positions. A collection constant streams: each row holds what has arrived of it and is left open until it is complete, and the constant is released once everything is. |
| `RecordWrap` | `DataFunction(… → T)` | `DataFunction(… → Record(name: T))` | The values of the input at one level as a one-field record, keeping the input's keys: `Zip` with one arm. `zip_arms_named_at` builds it for a record literal with one field over a collection; a lone scalar field is a `MakeRecord`. Forwards a release to the input, naming the field's part at its level. |
| `SelectField` | `Record{name: T, …}` | `T` | Hands back one field's tile, the eliminator for `MakeRecord`. Pulls the product whole, and releases what its consumer released of the field it selects and every other field whole (`guard_at_field`). |
| `Converse` | `DataFunction(domain → Scalar(codomain))` | `DataFunction(codomain → domain)` | Inverts a function operator: each codomain value maps to the list of domain values that produced it. |
| `Uncurry` | `A ⤇ B ⤇ C` | `{_0: A, _1: B} ⤇ C` | Flattens a collection of collections into one keyed by pairs: the two key extents pack into a record key and the values stand as they were. |
| `MapDomain` | `DataFunction(A → *)` | `DataFunction(A → Scalar(A))` | Replaces the codomain of a function with a copy of the domain values (identity codomain), producing an identity mapping from domain to itself. |
| `Filter` | Predicate: a function `A → bool`, or a collection over the input's levels down to some depth with `bool` beneath <br>Data: a collection holding at least the predicate's levels | Same as input | Keeps the entries the predicate maps to `true`, with their values. A function predicate is applied to the outermost keys. A collection predicate's innermost values are the mask over the keys at the level op-conversion states ([The level a node is converted at](#the-level-a-node-is-converted-at)), which is the predicate's innermost level, and `Tile::retain_keys` re-cuts that level's groups and leaves the levels above standing. Its mask is positional: an input holding nothing at that level passes through, and any other difference in count is refused. A deeper predicate filters the inner collections one outer key at a time: the survivors differ per key, which a correlated filter and a per-group filter (`sum([s.amount for s in g if s.qty > 2])`) produce. `filter_values` compiles to it, and under `map` it filters each element collection. A rejected key stays inside the region the output states complete, so a consumer's release of that region releases it from the input, and from the predicate when the predicate is a collection. An entry the predicate has not answered is withheld and stated incomplete (`Tile::withhold`). <br>TODO the function form can probably be replaced by Restrict |
| `Restrict` | Predicate: any tiling of type `A → bool` <br>Data: `DataFunction(A → *)` | Same as input | Filters a function tile by a boolean predicate: keeps only domain elements whose predicate evaluates to `true`. |
| `Aggregate` | Collection with values supported by the aggregate kind | `Aggregation` | Folds the collection's values into one accumulator; see [Aggregation and extraction](#aggregation-and-extraction). |
| `ExtractAggregate` | `Aggregation` | `Scalar` | Extracts a terminal result. Partial-result extraction is unsupported. |
| `MapAggregate` | Collection chain of at least two levels | Enclosing levels ending in `Aggregation` | Folds the innermost collection, preserving the levels above it. |
| `MapExtractAggregate` | Collection chain ending in `Aggregation` | Enclosing levels ending in the accumulator tiling | Extracts terminal results and removes innermost keys whose aggregates are not terminal. |
| `FanOut` | `*` | Same as input | Allows multiple operators to consume the output of the same operator. Each consumer subscribes via a `FanOut::slot()` handle; the fan-out forwards `get` requests and tracks the intersection of release guards across slots. Constructed via either `FanOut::new` (no cyclic-mode overhead — the common case) or `FanOut::new_cyclic` (for fan-outs whose slots feed back into their own input, e.g. a commit/induction store whose writer reads the store back before proposing, or a mutation-loop body whose other slot is wired to the cyclic prev-accumulator stream). Cyclic mode adds a per-pull tile-cache and a subscribe-in-progress flag so re-entrant subscribes / pulls skip redundant inner work and serve from the cached snapshot instead of re-entering the inner producer. |
| `Memo` | `*` | Same as input | Caches the output of an operator so it can be repeatedly read without recomputation. Releases each region as it takes delivery of it, so the input can clear its state; once the input is drained the cache is the sole source of the value. Until the input notifies again, release builds then skip the upstream pull, and a debug build probes the drained input once after it drains, so an input that answers with released data trips the release-contract check at the input; probing on every pull would re-read a shared subgraph once per path to it. After a notification of a region the pull reads, every build reads it: a drained input inside a loop's cycle delivers again where a round has it read again (`read_again`). A `Memo` keeps a dirty region of its input, which starts as everything and takes each region the input notifies (`Arrivals`): a pull outside the dirty region answers from the cache and no pull goes below, in every build, apart from that probe, and a pull inside it reads the input and removes what it read. A `Memo` is also a [pipeline breaker](#pipeline-breakers): a consuming memo answers from its cache and pulls nothing. |
| `ExtractFinal` | Collection source and optional default | Source codomain | Extracts the last live position's value after source completion; see [Final-value extraction](#final-value-extraction). |
| `UnionOperator` | N inputs of `DataFunction(dᵢ → 𝑇ᵢ)` tilings | `DataFunction(Union(d₀,…,dₙ₋₁) → Scalar(C'))`, or `DataFunction(Union(d₀,…,dₙ₋₁) → DataFunction(𝐵 → 𝑇))` for jagged rows | Merges N function operators into one. The domain is the discriminated union of the arms' domains, and the codomain is one the caller declares. The domain keeps the arms apart, and `final_or_default` dispatches on the arm a row came from. The codomain is the arms' join, because the arms are alternative values at one row. A union node is typed `D ⤇ V`, with `V` the join inference computed in the full type lattice, and op-conversion reads `V` off the node and passes its extent in. The operator does not join the operand tilings: `Extent`'s lattice has variant and range rules but no record rule, so it would join two arms at different record widths to an anonymous positional sum where the type is `{a: Int}`, a shape no row holds. Arms that agree on a tiling keep it, because a `Tiling` carries a layout (struct-of-arrays for a record) that an `Extent` cannot express. Arms whose codomains are collections over different domains, the rows of a jagged collection, merge at the bound `𝐵` the declared codomain gives their domains, beneath which they share the tiling `𝑇`, as a list literal of boxed rows has it (`OpConversionContext::witness_domain_extent`). Other arms whose codomain tilings differ must each fit in one column (`Tiling::is_scalar`: a `Scalar`, or a `Record` of such at any depth), and each is rebuilt as one column, keeping its own record fields, before the arms merge. A flat union (`new_flat`) collapses the arms' domain to the one they share whatever each row holds, a collection included. A realized conditional's legs are over different domains and disjoint only by their gates, so they flat-merge under the domain bound the sum's type declares (`new_flat_over`), which must include every leg's domain. Release is per arm: an incoming `Predicate::Union` guard splits into per-variant predicates, so one arm can be released in full while its siblings still produce. |
| `VariantWrap` | Payload: `Scalar(Pₜ)` or `DataFunction(D → Scalar(Pₜ))` | `Scalar(Union(P₀,…,Pₙ))` or `DataFunction(D → Scalar(Union))` | **Sum introduction — dual of `VariantProject`.** Wraps the payload under tag `tag`, so that arm holds the payload and every other arm is empty. Arms are keyed by [`FieldKey`], not by position: a tag's *position* is not stable under width subtyping (``{`b} <: {`a | `b}`` renumbers `b`), and an arm set is part of a union column's layout, so a position-keyed arm would need a renumbering coercion at every subsumption. A bare `Scalar` payload (a scalar `VariantCtor`) yields `Scalar(Union)`; a payload *stream* (a `VariantCtor` inside a lambda, `Builtin::VariantWrap(tag)`) is wrapped element-wise **preserving the domain** `D`, so the constructor composes as the RHS of a `≫`. Because the domain is preserved, a domain release forwards to the payload verbatim. A payload that is a collection is one value, held materialized in its arm's cell: an applied `VariantCtor` wraps its whole payload, and a composed one each row's. A cell cannot grow, so a row's cell is emitted once that row's collection is complete. |
| `VariantProject` | Scrutinee: `Scalar(Union(P₀,…,Pₙ))` or `DataFunction(D → Scalar(Union))` | `DataFunction(UInt → Scalar(Pᵢ))` for a bare scrutinee (implicit `0..N` keys), or `DataFunction(D → Scalar(Pᵢ))` for a stream scrutinee (the real `D` keys preserved) | **Sum elimination — the read-dual of `VariantWrap`.** Projects the arm named `tag` out of a tagged-union stream, *restricting to the sub-domain of rows carrying that tag* and yielding that arm's payload column, keyed by the original `UInt` position. A tag the scrutinee does not carry yields an **empty** projection rather than an error — that is what makes a width-subtype scrutinee, and so a `match` arm the scrutinee can never reach, inert instead of ill-formed. **Restrict and project are one op**: a [`UnionArm`] stores its rows alongside its payloads, so reading the arm *is* the tag restriction — there is no separate boolean `Restrict` step and no tag-discriminating `Predicate` (a domain-`Restrict` could not express it: the tag lives in the scrutinee's codomain, not its domain). Emitted by `lambda_elim` for a scrutinee-`Case`; consumed as a bare `Builtin::VariantProject(tag)` composed onto the fed scrutinee. |

### Aggregation and extraction

`Aggregate` folds a collection into one aggregation. `MapAggregate` folds the innermost collection
of a chain with at least two levels, leaving its enclosing levels intact. Both choose their
accumulator tiling through `AggregateKind::output_tiling`; construction fails if the kind does not
support the input values. The implementation is in `tile_operators/aggregate.rs`.

Each pull reads the input universally, compacts the returned tile, and accumulates its live values.
The producer releases the received tile's guard, captured before compaction so that it also covers
deleted rows. `Aggregate` marks its result terminal when the input's accumulated obsolete guard is
universal. An extremum without an identity emits an empty tile until its first element arrives;
completion without an element panics through `AggregateKind::no_extreme_of_nothing`. Otherwise it
re-emits the running accumulator until a universal output release, after which it returns empty
tiles and releases the input universally. Empty releases have no effect; partial releases of its
keyless aggregation are rejected.

`MapAggregate` stores one accumulator per complete parent path, not per final key alone: equal keys
under different parents identify different groups. A group's terminal flag is set when
`Tile::completion_at` covers its path. Completion at any enclosing level can complete the group;
the whole outer collection need not be complete. Output levels retain their respective input
completion predicates. Paths are sorted lexicographically to rebuild contiguous child runs, and
incomparable keys at the same level cause a panic. An extremum group without an identity is omitted
until it receives an element; completion of such an empty group panics.

A release removes every accumulator whose complete path it covers. Unreleased ancestor keys remain
in the output even when they no longer contain an accumulator. Input release is restated through
the unchanged enclosing levels with `through_shared_levels`, since an output accumulator replaces
an input collection. A universal release clears the accumulators and retained ancestor keys and
releases the input universally.

`ExtractAggregate` emits `AggregateKind::extract` only when its input has a terminal flag and that
flag is true. An empty aggregation tile is not a completed fold of an empty collection.
Construction with `only_terminal: false` is unsupported and panics. A universal output release
releases its input universally; an empty release has no effect.

`MapExtractAggregate` accepts a collection chain of any positive depth ending in an aggregation.
It replaces that aggregation with the extracted value and retains only the innermost keys whose
terminal flags are true. The enclosing levels remain intact. Releases pass through those shared
levels; a partial release of an extracted value does not release its input aggregation.

### Final-value extraction

`ExtractFinal` returns the last live position's value once its source collection is terminal. The
output tiling is the source codomain, which may itself be a collection. The current terminal
selection uses the last nondeleted row, not the greatest live key. Collection tiles do not require
key order, so this is an implementation gap for unsorted inputs, not a source precondition.
Induction histories use `StoreFinalRead` instead. The implementation is in
`tile_operators/extract_final.rs`.

Before source completion, extraction returns an empty tile. If a nonterminal delivery contains
live `UInt` keys with maximum 𝑚 greater than zero, it releases the source prefix through 𝑚 − 1 and
retains the maximum position. This key-value comparison agrees with the terminal row selection
only when the remaining rows are in key order. On a terminal delivery, it releases the source
universally. A live position supplies the result; if none remains, extraction pulls the default.
The default's extent must be included in the source codomain. `without_default` requires a source
that cannot finish empty, such as an exhaustive tag partition. Extraction panics if that requirement
is violated.

A collection-valued result retains the selected position's whole sub-tile. A collection default is
returned once terminal. Non-collection values are normalized through
`scalar_tile_to_column_value` and rebuilt at the declared output extent, preserving variant arms
absent from the selected value. Record layouts may differ between the source and default. A default
without a complete value yields an empty result.

Subscription attaches the consumer to the source. The default is subscribed eagerly with a no-op
consumer. This is a notification defect: if the source finishes empty before the default is ready,
the default's completion does not wake downstream readers. A `Memo` downstream can keep returning
its incomplete cached result without retrying extraction. Defaults are not required to be complete
at source completion. The default is pulled only for an empty terminal source and released
universally once it supplies the fallback. A cached result is re-emitted until a universal output
release. That release suppresses further emissions and releases both inputs universally.

### Pointwise functions

Pointwise functions are applied through `MapResult(input, Constant(FunctionDef))`, not standalone
operators. The variants are `BinOp(op)` over a `{_0, _1}` record column, `UnaryOp(op)` over one
column, `RecordField(f)` projecting a field, and `Scalar(program)` evaluating a fused chain.

#### Scalar programs

`ScalarProgram` in `scalar_expr.rs` is a straight-line instruction sequence. Instruction 𝑖 defines
slot 𝑖, and operands refer only to earlier slots. The last instruction produces the result.

| Instruction | Value |
|---|---|
| `Input { path }` | Input column, or a field path into it, of type `Int`, `UInt`, `String`, or `Bool` |
| `Const(value)` | One value of those types, repeated over the input rows |
| `Bin(op, a, b)` | Binary operation on slots `a` and `b` |
| `Un(op, a)` | Unary operation on slot `a` |
| `Record(fields)` | Record column with a slot per field, sorted by field name |

Operations consume scalar columns, never `Record` instructions. A `Record` is the last instruction
or a field of a later `Record`; nested records construct only the result. Record equality and
inequality are expanded during recognition: `Parser::operation` recursively compares the fields
selected by `binop::compared_fields`, joining results with `and` for `==` or `or` for `!=`. Operands
may be input records, constants, or products constructed by `zip`.

Repeated reads of an input field path share one `Input` instruction. References to an already
computed value reuse its slot, including when several `zip` arms read it. The parser does not merge
independently expressed equal computations. Failed recognition and output probes discard their
temporary instructions; field-name sorting makes record instruction order deterministic.
`ScalarProgram` equality compares these instruction sequences, not semantic equivalence.

`fuse_prefix` accepts input projections, but a projection of a computed product ends recognition.
Its eligible forms, operation-count threshold, and operator-conversion boundaries are specified in
[Element-wise chains](../ccl/design/optimization.md#element-wise-chains).

`ScalarProgram::eval` processes at most 1024 rows (`BLOCK_ROWS`) per block. Inputs and constants are
borrowed [column views](#column-views), with no scratch column. Each intermediate operation writes
a scratch column that is cleared and reused for the next block. The last instruction appends
directly to the output: an operation runs its kernel, and a record copies each field's block,
recursively for nested records. Output capacity for all input rows is reserved before evaluation.
Intermediate columns hold at most one block each rather than one column per full input. An empty
input still runs one zero-length block and produces a correctly typed empty output.

#### Column views

`View<T>` (`src/view.rs`) borrows either a slice or one value repeated over a specified length.
`ColumnView` (`types/column_view.rs`) wraps views of `Int`, `UInt`, `String`, or `Bool`. Record,
union, and `Units` columns have no view. Taking a view or subrange does not copy the operand into
another column. `ColumnValue::extend_from_view` copies a view into a column of the same element
type and panics on a type mismatch.

The binary kernels in `src/scalar_ops.rs` append results to caller-owned buffers and require equal
operand lengths. `apply_binop_views` truncates operands to their common prefix before dispatch;
`apply_unaryop_views` appends one result per operand row. The corresponding `*_column` entry points
accept `ColumnValue`s; `apply_binop_column` also handles record comparisons. With two constant
operands, a binary kernel computes the result once and repeats it. At zero length it does not
evaluate the operation, so an empty division by a constant zero does not fault.

### Sum compilation

**Value-selecting `Case` in a writer decision body** (a conditional induction write `if 𝑝: acc += a else: acc += b`, or a `with begin():` per-key routing merge — a gate that varies with the element at a site with **no visible iteration source**). `lambda_elim` compiles it to the same **union of domain-restricts** as every other value-`Case`, over the *fed* element stream: `⧺ᵢ (filter_values(π̂ᵢ) ≫ eᵢ)`, first-match `π̂ᵢ`. `filter_values` (`Builtin::FilterValues` → the `Filter` tile operator, input stream + predicate) is a **value-preserving** filter — unlike `Restrict` (which returns the domain identity `{D|p}⤇{D|p}` for a source a map re-indexes), it keeps each surviving element's value `V`, so `eᵢ` maps the kept elements directly and a **partial op** (`//`) in `eᵢ` runs only where its guard holds — never eagerly at a rejected position (the retired `Select` computed both arms and faulted on the off-path one). The arms filter the *same* fed stream disjointly (first-match), so their union is a **flat merge** (`UnionOperator::new_flat`): it stays on one domain extent (not a tagged `Extent::Union`) and reassembles the full column sorted by domain key, co-iterating with the decision record's sibling `commit`/`writes` fields. The key is the arm's domain *value*, not a position: reassembly needs only a total order (to restore the fed order) and equality (to catch two arms claiming one key), and both hold for any single collection's keys, since its domain is one `Extent`. A `UInt` position is the common case; a fed stream whose own index set is a coproduct — a conditional-element comprehension, whose `Copair` domain is `Variant({Index(i): {D | π̂ᵢ}})` — carries `Union { tag, inner }` keys, which `Value`'s order compares lexicographically by tag then payload. Keys that are *not* mutually comparable mean the arms were fed different domains, which is a copairing rather than a disjoint join, and `flat_merge` says so. The legs of a realized conditional are the one flat merge whose arms are over different domains: each leg is its arm over the arm's own domain, the first-match gates leave at most one holding rows, and the merged keys range over the bound the sum's type declares (`UnionOperator::new_flat_over`). A sourceless value-`Case` (a top-level ternary) still takes the `UIntRange(1)`-driver C-form + `final_or_default` (a tagged union dispatch); the writer-body case differs only in filtering the fed stream rather than a synthetic driver.

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
each of the binding's rows first (`lift_into_iteration`). A reference converted at a deeper curry
level than the binding's (`LetBinding::level`), inside a `strength_over` or `curry_over` its loop
body runs beneath, is spread the same way, over the keys of the reference's input, one level at a
time (`lift_into_level`).

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

### Applying a collection at a key

`apply` over `(key, collection)` rows converts to [`Lookup`], which reads each row's key in that
row's own collection. A collection is a data function, and `apply`'s type keeps the key inside
its domain, so the answer is the value at the key, not an option. A read of a dependent loop's
element has this shape: the element's value is its position read in the collection the loop's
source builds from the enclosing positions, `⟨𝑥.1, 𝑥.0 ▷ 𝐷⟩ ≫ apply`. Applying a compute
function stays unsupported, since a compute function has no compiled form as a value.

The rows stand at the level the node is converted at, and each row's collection is a level
beneath it, one run of keys per row. A row is answered as soon as its key arrives in its run,
because a value at a key never changes and no row waits for an absence to be decided, which
[`CheckedLookup`] does. A row whose key has not arrived is left out, and every level states the
input's completeness less that row's path, the rule `CheckedLookup` applies to a key it has not
decided. An input that is complete answers every row, and `Lookup` fails loudly where one does
not. The answer keeps the input's keys at every level above the rows, so a release passes
through to the input, each row's collection going with its row.

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
