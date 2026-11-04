# Projections that name a path

Status: accepted. Stages 1 to 4 are built. The decisions are listed under [Decisions](#decisions),
and the work lands in the [stages](#stages) below.

A projection names the part of a producer's tile a pull asks for, and a push names the region a
pipeline breaker decided (`src/interpreter/design-operators.md`, "Projection guards"). This note
specifies projections that name keys at any collection level, each under the path of keys above it,
the guard differences they need, and the stages that put them to use. A producer declares the levels
whose keys it restates (`TileProducer::restates`, a `Restates`), the outermost keys only by default,
and one that declares more reads its projection with `TileGuard::projection_for`. The `get` wrapper
of a debug build panics on a pull at a level a producer does not restate, and a push beneath the
outermost keys lands in its reader as a projection at its level (`Dispatcher::land_in`).

## What a dispatched run refuses

A loop nested in another runs in rounds of its own (`src/interpreter/design-operators.md`, "A loop
in rounds"), and a feed, a loop or a transaction over a live source runs dispatched
(`src/interpreter/design-operators.md`, "Running a compiled program"). The shapes a dispatched run
still refuses are listed there. Removing the scheduler removes pull mode, so each of them has to run
there first.

## Where a region crosses an operator

A region crosses an operator on four paths, and only three need a path.

| Path | What crosses | Needs a path |
| --- | --- | --- |
| Notification (`Consumer::notify`) | the keys that changed | no |
| Pull (`TileProducer::get`) | the region asked for | yes |
| Push (`Consumer::push`) and package | the region a breaker decided | yes |
| Release (`TileProducer::release`) | the region read no more | yes |

A notification only has to be sound: naming more than changed costs a read and loses nothing, so
a change at `(k, j)` is notified as the key `k`, or widened to `Everything`. A push names a region
its reader's pipeline consumes once in the run (`Pushes::record`), so a push of `k` for a change at
`(k, j)` would consume the row `k` at its first position. A pull at a package's region answers
that region and no more (`Tile::within`), and the breaker releases its input at what the answer
states, which a finish checks covers the package (`finish_with`).

Notifications go with the scheduler (the `TODO` on `Consumer::push`), so they need no change.

## Representation

A projection at level 𝑛 names keys of level 𝑛, each under the path of keys above it. Level 0 is
the outermost collection, and one variant spells every level:

```rust
pub enum Projection {
    Everything,
    Nothing,
    /// Keys of level `level`, beneath the paths `keys` qualifies them by.
    Keys { level: CurryLevel, keys: Predicate },
}
```

At level 0, `keys` names no enclosing path. Beneath it, `keys` is a predicate over whole paths,
spelled with `Predicate::Qualified`, which already names keys under enclosing paths
(`Predicate::exactly`, `contains_path`, `descend`). Its guard is the domain guard of `keys` wrapped
in a codomain guard per level above it (`CurryLevel::wrap_guard`). `Projection::of` reads that
guard back, and so does it read an `Or` of such guards at several levels.

Two projections at different levels meet at the deeper one: the keys `k` at level 0 are the paths
`(k, *)` at level 1, `Predicate::qualified(k, True)`. `intersect`, `minus` and `union` lift the
shallower side and combine the qualified predicates componentwise, which `Predicate` already does
for `Qualified` (`Componentwise::Qualified`). A result that admits whole keys of a level above
normalizes back to that level, so level 0 stays the spelling of an outermost region. The lift is
exact because a codomain guard naming every key beneath a key names that key: a release of it drops
the key (`a_codomain_release_drops_only_the_keys_it_names_whole`).

`Tile::restrict_to` cuts at level 𝑛: it keeps the rows of level 𝑛 whose path the predicate admits,
and a key above where an admitted path passes through it. A statement beneath level 𝑛 is
qualified by the paths kept (`within_paths`). A statement above level 𝑛 keeps the keys whose every
path the predicate admits, which the arms of the projection's guard name above level 𝑛, and states
the rest of what it said at level 𝑛, cut to the predicate. `Tile::within` checks the same paths.

## Differences of nested guards

`guard_minus` (`tile_operators/mod.rs`) takes the difference of two guards of a collection's keys
at any levels as their projections differ. A breaker holding the keys `k` and released up to the
path `(k, j)` holds a guard with arms at two levels, `TileGuard::Or` of the keys not released and
the paths of row `k` past `j`:

```
held      = Domain(k ∈ {0, 1})
released  = Codomain(Domain(Qualified { enclosing: k = 0, here: j ≤ 1 }))
held − released = Or [ Domain(k = 1), Codomain(Domain(Qualified { enclosing: k = 0, here: j > 1 })) ]
```

The arm `(0, j > 1)` is empty where row 0 has no position past 1, which the guard alone does not
say. `TileGuard::closed_over`, which also closes a guard against a tagged union's tags, drops the
arm where its level's extent is a finite range of positions none of which it names, so over rows
of positions `0..2` the difference is `Domain(k = 1)`. `BreakingProducer::final_guard` closes its
difference over the producer's tiling. A level of any other extent closes no arm, and a row there
is held no more once a release names it whole. Closing drops an empty arm and does not lift an arm
naming every position of its row to the key above.

A release can also carry an arm of cells beneath keys. A selector releases every field but its own
at every path (`guard_at_field`, `fan.rs`), and a `FanOut` releases the meet of its readers'
releases, which keeps an arm of the fields one reader skipped beneath the keys another released
whole. `guard_minus` takes the arms of keys out as projections. Where every other arm is a codomain
guard naming nothing of what the arms of keys leave, the difference is that region, and
`guard_minus` panics on any other arm:

```
held      = Domain(True)
released  = Or [ Domain(k = 0), Codomain(Record { _0: ∅, _1: Domain(Qualified { enclosing: k = 0, here: True }) }) ]
held − released = Domain(k ≠ 0)
```

An arm of cells that names part of what is left leaves a record guard beneath the held keys, which
is no region of keys, and `guard_minus` panics on it. A push names a region of keys
(`Dispatcher::land_in` reads it with `Projection::of`), so a breaker's final guard is its held keys
less the keys its readers released whole (`keys_released_whole`, `BreakingProducer::final_guard`).
A key some of whose cells a reader released stays held, and the push names it. `SelectField`
restates every level above the record: a selector pulled at a path leaves the inner loop's drive
holding the other fields' cells of the path released, the drive's push names the path, and the
selector takes its field there (`a_condition_in_a_loop_nested_over_rows`).

A round pushes per position, so it needs the difference, where a push at a finish only names the
breaker's whole held region.

`Pushes::record`, `Queue::append_unqueued` and the finish's release check (`finish_with`) compute
their regions with `guard_minus`, `union` and `intersect` over `TileGuard`, so they take nested
regions.

## Operator rows

Each row of the table under "Projection guards" in `design-operators.md` gains what the operator
does with a projection at level 𝑛 > 0. The rows fall into five kinds:

| Kind | Operators | A projection at level 𝑛 |
| --- | --- | --- |
| Keeps every level's keys | `MapResultWithSource`, `Filter` (with a collection predicate, the levels down to the masked one), `Restrict`, `MapDomain`, `VariantProject`, `VariantIs`, `Memo`, `FanOutSlot`, `IterateExtent`, `MapAggregate`, `MapExtractAggregate` (the levels of its input, not those of a `Sole` collection beneath them) | pulls each keyed input at the same projection and cuts its answer to it |
| Keeps the keys above its level | `MapResult` (keyed input), `MapResultToConst`, `RecordWrap`, `Zip`, `VariantWrap`, `SelectField` over a stream of records, `Product` | pulls each keyed input at a projection above its level and refuses one at or beneath it, or, for `Product`, pulls both sides at the rows above its paired level and cuts the pairs |
| Shifts levels | `Uncurry`, `Converse` beneath standing levels, a nested store's read | restates the projection by the levels it adds or removes |
| Reads whole and cuts | `PermuteRecordDomain`, `FlattenTupleDomain`, `SelectField` over a product, `CheckedLookup`'s collection, `UnionOperator` | reads its input whole and cuts the answer at level 𝑛 |
| No keys beneath | `Aggregate`, `ExtractAggregate`, `ExtractFinal`, `MakeRecord`, `Constant` scalar | refuses, as it refuses keys today |

An operator that keeps its input's keys above its own level and computes the values beneath them
refuses a projection at or beneath that level (`Restates::Above`): those keys are inside the values
it computes. The outer side of `Product` has no paired level, so `Product` declares
`Restates::Every`, pulls both sides at the rows above that level that a projection's paths run
through (`Projection::above`), and cuts the pairs after.

`Memo` is the operator whose state depends on the algebra: its `dirty` region and its cache's cut
are projection arithmetic (`MemoProducer::get_impl`), which `Projection` does at every level.

The induction drive emits a position only where the pull's projection names its whole path
(`InductionDriverProducer::step`). A drive and a store are pulled beneath their outermost keys only
in a round of a nested loop, so their rows land with the nested scope.

A push is restated by the consumer an operator chooses at subscribe time, not by the operator:
`Forwarding` keeps the region, `Widening` widens it to `Everything`, and `Tagging` puts it under an
arm's tag (`scheduler.rs`). A nested region passes `Forwarding` as it is and `Widening` as
`Everything`. `Tagging` tags its outermost key: the enclosing component of `keys` goes under the
tag. An operator that shifts levels and keeps keys has to restate a nested push by the shift instead
of passing it on, so it gets a consumer of its own.

## The planner

A loop nested in another runs as a scope inside the outer loop's scope, queued a row of its store
per outer round: the inner scope's rounds are the positions `(k, j)` of row `k` the inner drive
emits, and a round at the row closes it.

The planner refuses a nested loop where an operator its rounds pull beneath the outermost keys
restates no projection there (`Planner::refusal_of_nested`), and the program runs in pull mode. It
composes the levels along each path from an inner pipeline's breaker: `TileProducer::restates` says
what an operator accepts, and `TileProducer::input_level` the level it pulls each input at. There is
no folded execution. No program of the differential suite is refused this way
(`tests/it/dispatch_refused.txt`).

A live source's arrivals are notified at the outermost keys of the pipeline that stands for the
range, or that pipeline reads its input whole once the source yields everything
(`LivePipeline::poll`): no arrival is notified beneath the outermost keys. A feed of a collection
read from a live source is keyed by the sink's one row, so its arrivals reach the pipeline above the
source widened, and that pipeline reads its input whole.

## Stages

1. The algebra: `Projection::Keys` at a level, its `of`, `guard`, `intersect`, `minus` and `union`;
   `Tile::restrict_to` and `Tile::within` at a level; `guard_minus` with arms at several levels and
   their closing against a row's extent. Unit tests over the algebra only.
2. The rows of the operators a nested loop's body pulls at a path: `MapResult`,
   `MapResultToConst`, `Zip`, `RecordWrap`, `VariantWrap`, `Product`, `FanOutSlot` and `Memo`,
   each declaring the levels it restates (`TileProducer::restates`).
   Each with a test that a pull at a projection of paths answers what a pull at `Everything` cut
   to it answers.
3. The nested scope in the planner, refused where an operator its rounds pull restates no nested
   projection (`TileProducer::input_level`), with the rows of the induction drive, the stores and
   their reads, and the nested-loop programs of the differential suite running in rounds.
4. Live sources, once a dispatched run notifies them: a feed of a map over a source, read whole once
   the source yields everything; a loop over a source, flat or nested; and a transaction over one,
   whose store pushes the commit ticks each consume decides.
5. The remaining rows, the operators a refused nested loop's rounds pull among them, then the
   scheduler's removal (`src/interpreter/design-operators.md`, "Running a compiled program").

## Decisions

- One variant spells a projection at every level: `Keys { level, keys }`, with level 0 the
  outermost collection.
- A round pushes per position, so the guard algebra has a difference of nested guards rather than
  pushing only at a finish.
- A difference closes an arm against the extent of the row it names, so an arm that names no
  position of its row reads as `Nothing`.
- A nested loop whose rounds pull an operator with no nested row is refused and runs in pull mode;
  no loop folds into the scope around it.
- `MapResultToConst` widens every push from its constant: a reader takes a row whose constant
  streams once the constant is complete, and the constant's keys do not stream beneath the row.
- A transaction store pushes the commit ticks each consume decides, so a feed inside a transaction
  streams.
