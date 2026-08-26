# CLAUDE.md
This file provides guidance to Claude Code (claude.ai/code) when working with code in this directory.

The interpreter implements Cambra's runtime according to the operational
semantics in [`docs/operational-semantics/summary.md`](/docs/operational-semantics/summary.md)
(with full formalism in [`semantics.md`](/docs/operational-semantics/semantics.md)).
Per-operator specifications live in [`design-operators.md`](./design-operators.md);
keep that doc in sync with code changes.


## Core invariant: data flows between operators as Tiles, nothing else

Every operator-to-operator handoff goes through the `TileProducer` /
`TileConsumer` protocol — `subscribe` → `get` → `release`, exchanging
[`Tile`] values along the way.  There are no side channels: no shared
caches read by name, no input ports that bypass `get`, no closures that
capture upstream state directly.  If two operators need to communicate,
they communicate by one calling `get` on the other and receiving a
[`Tile`].

Concretely:

- Adding a new way for an operator to read from another (e.g., "the body
  reads the prev-acc directly from a `Rc<RefCell<...>>` instead of
  through `get`") is a violation, even if it works on the test cases at
  hand.  Cyclic graphs go through `FanOut::new_cyclic` and the
  re-entrancy machinery on `FanOutShared` — see [`FanOutReentrancy`]'s
  docs for the contract — but the data on the wire is still a [`Tile`].
  A cyclic pull is served the fan's cached snapshot rather than
  re-entering the inner producer, which is why such a cycle advances one
  step per outer pull.
- Constructor-time wiring (a [`CycleSlot`], filled through its
  `setter` once the rest of the cycle exists) passes `TileOperator`
  handles, not raw values.  The operator graph is static; values flow
  through it at `get` time.
- Side effects (I/O, sinks, notifications) live at the boundary —
  `compile_program` wires a `SinkConsumer` to the final operator, and
  `Scheduler::check_for_notifications` drives them.  Operators
  themselves only manipulate tiles.

If you find yourself reaching for a back-channel to avoid a tile
shape that's awkward to express, fix the tile shape instead.


## Core invariant: known data inside a Tile is immutable

A Tile only ever **grows monotonically** — the progress order from the
semantics doc.  The only way to remove data is `release()`, which is a
declaration that the consumer doesn't need that region anymore;
producers may then `compact` (drop the data), but they may never *change*
a value at a known position.

Concretely:

- A producer that has emitted value `v` at domain position `d` cannot
  emit a different value at `d` later.  Recomputing because "the
  upstream changed" is not a thing — upstream tiles only grow.
- `Tile::merge` is `⊕` from the semantics: it combines disjoint
  information.  Merging the same position twice with different values
  is a bug.  Merging the same position with the *same* value is
  allowed if you can't easily avoid it (idempotent), but prefer
  releasing before re-emitting if you find yourself doing this.
- `release` is the *only* operation that shrinks a tile.  It removes
  data from the producer's view (and the consumer's), but the
  consumer has already extracted whatever value it needed before
  calling `release`.  Released regions can be reclaimed via
  compaction; un-released regions stay live.
- Mutating fields of a tile in place during `get_impl` is fine *before*
  returning the tile — that's just constructing the value to emit.
  Once a tile leaves a producer, the values inside it are part of the
  consumer's monotonic state and can't be retroactively changed.

The "known portion" framing matters for cached / shared paths
(`FanOut`, `Memo`, the cyclic-mode cache in `FanOutShared`): a cached
tile is a snapshot of values that have already been emitted, so it is
safe to clone, share, and serve from.  A re-entrant pull that serves
the cache is *not* observing a stale-but-currently-changing tile; it
is observing the most recent committed snapshot, which is correct by
the monotonicity invariant.


## General Instructions

### Workflow
When changing operator semantics, surface area, or tile shape, update
[`design-operators.md`](./design-operators.md) — it is the runtime
counterpart of `ccl/design/optimization.md` and the operator-spec entry
point for new readers.  If a change crosses the CCL ↔ interpreter
boundary (e.g., a new `Builtin` that maps to a new tile operator),
update both `design-operators.md` and `ccl/design/optimization.md`.

When in doubt about the protocol, consult the formal definitions in
[`semantics.md`](/docs/operational-semantics/semantics.md) rather than
inferring from existing code
