# Operational Semantics: Overview

See also:
- [semantics.md](semantics.md) — formal definitions of tilings, guards, and operators
- [example.md](example.md) — end-to-end worked example
- [deprecation.md](deprecation.md) — transition from yield guards
- [src/interpreter/design-operators.md](/src/interpreter/design-operators.md) — per-operator specifications
- [brainstorm/guards-and-separation-algebras.md](brainstorm/guards-and-separation-algebras.md) — historical brainstorm

---

## The Model

Every term in a Cambra program has a **type**. Each type has a corresponding **extent** — the plain
set of final values the term can take on (e.g. the set of integers for `Int`, or the set of total
functions from `T` to `U` for the type `T ⇒ U`). The extent has no algebraic structure; it is
simply the space of possible answers.

To compute the actual value of a term, Cambra uses a **tiling** — a progress algebra that describes
all possible intermediate operational states on the way to that value. Each element of a tiling is
called a **tile**. Tiles can be combined when they cover non-overlapping parts of the computation;
the combination is always uniquely determined. There are no inverses: combining tiles only ever
adds information. This gives tiles a natural progress order — one tile is smaller than another if
the larger one can be obtained by combining it with additional tiles.

The state of a running Cambra program assigns a tile to each term. Every term starts at `⊥`
(bottom) — zero information. As execution proceeds, tiles grow monotonically: each term's tile is
**extended** by combining it with new tiles produced by its dependencies. A program terminates
when no tile can be extended further.

A **guard** identifies a subtiling — a downward-closed, combination-closed subset of a tiling's
tiles. Guards are the mechanism by which operators decompose tiles: the `split` operation takes a
tile and a guard and returns the portion of the tile inside the guard's subtiling together with the
complementary portion outside it. Guards appear in three roles at runtime:

- **Projection guard** — passed to `get()` to request only a portion of a producer's tile.
- **Intent guard** — registered at `subscribe()` time, bounding the full subtiling a consumer
  will ever need.
- **Obsolete guard** — passed to `release()` to declare that a subtiling is no longer needed,
  allowing the producer to reclaim resources via compaction.

An **operator** is the runtime counterpart of a CCL function `f : T ⇒ U`. It maps tiles of
`Tiling(T)` to tiles of `Tiling(U)` monotonically, and its behavior on terminal inputs must match
`f`'s denotational semantics. Operators that are homomorphisms can stream — each new input tile is
independently transformed and combined into the output. Operators can also terminate early,
producing a terminal output before their input is complete. When consumers release portions of an
operator's output, the operator may **compact** the released portion into a summary, retaining
enough information to produce correct future output without keeping the full tile history.

The three terms to keep distinct:

- **Extent**: the set of possible final values — no algebraic structure.
- **Tiling**: the progress algebra — tiles, `⊕`, `⊥`, and the progress order.
- **Tile**: a single element of a tiling — the runtime state of a term at a given moment.

Guards operate on tilings (structural decomposition). Value predicates are expressed as operators
and interact with guards only indirectly, through terminal results feeding into domain restrictions
on enclosing function tilings.
