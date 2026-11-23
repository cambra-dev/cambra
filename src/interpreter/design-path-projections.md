# Projections that name a path

A projection names the part of a producer's tile a pull asks for, and a push names the region a
pipeline breaker decided (`src/interpreter/design-operators.md`, "Projection guards"). This note
specifies projections that name keys at any collection level, each under the path of keys above it,
and the guard differences they need. A producer declares the levels whose keys it restates
(`TileProducer::restates`, a `Restates`), the outermost keys only by default, and one that declares
more reads its projection with `TileGuard::projection_for`. The `get` wrapper of a debug build
panics on a pull at a level a producer does not restate, and a push beneath the outermost keys lands
in its reader as a projection at its level (`Dispatcher::land_in`).

## Where a region crosses an operator

A region crosses an operator through reads, notifications and releases.

| Path | What crosses | Needs a path |
| --- | --- | --- |
| Pull (`TileProducer::get`) | the region asked for | yes |
| Notification (`Consumer::notify`) and package | the region a breaker decided | yes |
| Release (`TileProducer::release`) | the region read no more | yes |

`Consumer::notify` marks cached reads dirty and forwards the region through the dispatcher routes.
A dispatcher notification names a region its reader's pipeline consumes once in the run
(`Pushes::record`), so notifying `k` for a decided position at `(k, j)` would consume the row `k`
at its first position. A pull at a package's region answers
that region and no more (`Tile::within`), and the breaker releases its input at what the answer
states, which a finish checks covers the package (`finish_with`).

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
the key.

`Tile::restrict_to` cuts at level 𝑛: it keeps the rows of level 𝑛 whose path the predicate admits,
and a key above where an admitted path passes through it. A statement beneath level 𝑛 is
qualified by the paths kept (`within_paths`). A statement above level 𝑛 keeps the keys whose every
path the predicate admits, which the arms of the projection's guard name above level 𝑛, and states
the rest of what it said at level 𝑛, cut to the predicate. `Tile::within` checks the same paths,
and checks that every statement lies within what the cut leaves stated.

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
less the keys its readers released whole (`keys_released_whole`, `BreakingProducer::final_guard`). A
key some of whose cells a reader released stays held, and the push names it. `SelectField` restates
every level above the record: a selector pulled at a path leaves the inner loop's drive holding the
other fields' cells of the path released, the drive's push names the path, and the selector takes
its field there.

A breaker's held region can also carry an arm of cells beneath rows still open. Taking keys of
the outermost level out of it keeps the cells beneath every other key: each enclosing path the arm
names loses the released keys, and an arm named under every path is qualified by the rest
(`minus_outermost_keys`). The difference is spelled for cells one level beneath the keys, named
under one qualification and with no `Or`; any other arm reads no single outermost key, and
`cells_outside_keys` panics on it. So does a release of keys beneath the outermost level:

```
held      = Or [ Domain(k > 1), Codomain(Record { _0: Qualified { enclosing: k ∈ {0, 1}, here: True }, … }) ]
released  = Domain(k = 0)
held − released = Or [ Domain(k > 1), Codomain(Record { _0: Qualified { enclosing: k = 1, here: True }, … }) ]
```

Whether a release covers a guard needs no difference (`guard_covers`): with an arm of cells, only
its keys released whole cover, so a key whose every cell is released one arm at a time counts as
not covered, and a read of it answers nothing.

A round pushes per position, so it needs the difference, where a push at a finish only names the
breaker's whole held region.

`Pushes::record`, `Queue::append` and the finish's release check (`finish_with`) compute
their regions with `guard_minus`, `union` and `intersect` over `TileGuard`, so they take nested
regions.

## Operator rows

The [projection table](design-operators.md#projection-guards) specifies each operator's supported
levels and input projections. `TileProducer::restates` declares those levels; `input_level` describes
how a supported output level maps to each input.

## The planner

A loop nested in another runs as a scope inside the outer loop's scope, queued a row of its store
per outer round: the inner scope's rounds are the positions `(k, j)` of row `k` the inner drive
emits, and a round at the row closes it.

A round of a nested loop pulls each operator beneath the outermost keys at a level it restates,
and the planner asserts it (`Planner::unrestated_in_rounds`). The check composes the levels along
each path from an inner pipeline's breaker: `TileProducer::restates` says what an operator accepts,
and `TileProducer::input_level` the level it pulls each input at.

An operator may pull an input above the round's level, at the nearest level that input restates
(`Projection::restated_by`), and declares that level (`Restates::nearest`); `Uncurry` and
`UnionOperator` do. The wider read is cut to the round's paths after. A `Memo` beneath it on a
path to a recurrence slot caches positions of later rounds from the store's snapshot, and reads them
again before the store's next step
([A store as a breaker](design-operators.md#a-store-as-a-breaker)).

A live source's arrivals are notified as the region they restate at the entry of the pipeline that
stands for the range, at any level (`LivePipeline::poll`). A feed of a collection read from a live
source is keyed by the sink's one row, so its arrivals reach the pipeline above the source widened,
as every key of its input.
