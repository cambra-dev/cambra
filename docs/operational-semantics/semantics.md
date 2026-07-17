# Operational Semantics: Formal Details

See also:
- [summary.md](summary.md) — high-level overview of the model
- [src/interpreter/design-operators.md](/src/interpreter/design-operators.md) — per-operator specifications

---

## 1. Tilings

Each type has a **tiling** — an algebraic structure describing all possible operational states
during computation of a value of that type. Each state is called a **tile**. Tiles can be
combined when they cover non-overlapping parts of the computation, and the result is always
uniquely determined. There are no inverses: combining tiles only adds information, never removes
it. This gives tiles a natural **progress order**: one tile is smaller than another if the
larger one can be obtained by combining it with additional tiles.

### Formal Definition

A _Progress Algebra_, which we colloquially call a "tiling", is a set
(elements of which we call "tiles") equipped with:

1. A **partial binary operation** `⊕ : Tile × Tile ⇀ Tile`. This operation combines information;
   it is defined only for *compatible* pairs — pairs whose information does not contradict or
   overlap. `⊕` is commutative and associative (wherever it is defined).
2. An **identity element** `⊥`, representing zero information. `x ⊕ ⊥ = x` for all tiles `x`.
3. **Positivity**: if `x ⊕ y = ⊥` then `x = ⊥` and `y = ⊥`. Only the empty tile combines
   to give the empty tile; there are no "inverses."

These axioms induce the **progress preorder**: `x ≤ y` iff `∃h. x ⊕ h = y`. Reflexivity
follows from the identity axiom (`x ⊕ ⊥ = x`), and transitivity from associativity. A tile
with more information is larger. Computation proceeds upward through this preorder.

When we have tiles `u ≤ t`, we say that _`u` is a sub-tile of `t`_. This builds on the intuition
that smaller tiles can be combined with other tiles to form larger tiles. If we have
`u ⊕ v = t`, we say that _`u` and `v` decompose `t`_.

### Termination and Extraction

A tile is **terminal** iff no tiles in the tiling are larger than it in the progress order.
Equivalently, `t` is terminal iff there exists no tile `u` such that `t ⊕ u` is defined and `u ≠ ⊥`.

Given an extent `E` and a tiling `T`, we say **`T` is a tiling for elements of `E`** iff there exists a
bijection between the terminal elements of `T` and `E`. This bijection **extracts** tiles into values,
or **injects** values into the tiling.

### Instances

**Scalar terms** (e.g., `Int`, `Bool`): The tiling is `{⊥} ∪ T`, where `T` is the
carrier set of the type. `x ⊕ y` is defined iff at least one of `x`, `y` is `⊥`; combining two
concrete values is incompatible (a scalar can take on only one value). A scalar tile is therefore
determined in a single step: from `⊥` to its terminal value.

**Function terms** (e.g., `T ⇒ U`): The tiling is the set of partial functions `T ⇀ U`.
`f ⊕ g` is defined iff the domains of `f` and `g` are disjoint; the result is their union.
Function tiles can be determined incrementally, with each new tile covering a disjoint portion
of the domain. Partial function tiles are terminal when they are total.

**Aggregate terms** (e.g. `sum(f)`, `max(f)`, where `f: I ⇒ T`):
An aggregate operator takes a function tiling (`I ⇀ T`) as input and produces tiles in a
tiling specific to the aggregation. For `sum`, the tiling is `Count × Sum`; for `max`,
`Count × Max` (see Section 2, Unsplittable Tilings). Each increment of the input function
tiling is translated into a tile of the aggregate tiling, and the aggregate's running state
is their `⊕`-combination. These aggregate tilings are typically unsplittable — they support
only the trivial guard algebra. This means projection guards cannot request a portion of the running
aggregate, and obsolete guards can only release the entirety of the aggregate.

---

## 2. Guards

A **guard** is a predicate that identifies a **subtiling**—that is, a subset of tiles that is
both **downward-closed** and **⊕-closed**. Concretely:

1. **Downward-closed**: if tile `y` is in the guard and `x ≤ y`, then `x` is in the guard.
   Computing a tile always requires first computing everything below it in the progress order,
   so a guard identifies not just specific tiles, but all intermediate tiles in their
   determination.
2. **⊕-closed**: if tiles `a` and `b` are in the guard and `a ⊕ b` is defined, then `a ⊕ b` is
   in the guard. This ensures that `split` (see below) is well-defined.

A subtiling is a tiling in its own right — it inherits the progress algebra axioms from the
ambient tiling, and its progress order is faithfully embedded (downward-closure ensures no
intermediate tiles are missing). We write `t ∈ g` as shorthand for "tile `t` is in the subtiling
denoted by guard `g`."

A specific algebra of predicates that can select subtilings of a tiling is called a
**guard algebra** of that tiling. The choice of guard algebra for a tiling is not unique, and is
made by the compiler/interpreter.

**Closure under intersection, not union:** subtilings can be intersected freely, which means that
many guard algebras can support an efficient intersection operation. However,
⊕-closure means that the union of two subtilings is not
necessarily a subtiling: if `a ∈ G₁` and `b ∈ G₂` with
`a ⊕ b` defined, `a ⊕ b` need not be in either guard.

### The `split` Operation

Guards enable an operation that splits a tile into one piece that's inside the guard's subtiling,
and another outside.

Formally, given `tiling : Tiling` and `guardAlg: GuardAlgebra(tiling)`:

```
split : {tile : tiling.Tile, g: guardAlg.Guard} ⇒ {inside : tiling.Tile, outside : tiling.Tile}
```

This operation finds `inside` and `outside` such that `inside ⊕ outside ≡ tile` and
`inside ∈ g`, where `inside` is the greatest element of `{a ∈ g : a ≤ tile}` and `outside`
is the unique complement.

`split` is the primary way that guards interact with tilings.

### Split-Determinism

For `split` to be well-defined, two things must hold for every guard `g` in the algebra and
every tile `t` in the tiling:

1. **Unique inside**: the set `{a ∈ g : a ≤ t}` has a greatest element.
2. **Unique outside**: the decomposition `inside ⊕ outside = t` has exactly one solution
   for `outside`.

A guard algebra satisfying both conditions is **split-determinate**. This is the fundamental
requirement on a guard algebra — without it, `split` is ambiguous and the producer/consumer
protocol cannot function.

Every tiling admits at least one split-determinate guard algebra: the **trivial guard algebra**
`{nothing, everything}`, where `nothing = {⊥}` selects only the identity and `everything`
selects the whole tiling. For these guards, `split` is immediate:
`split(t, nothing) = (⊥, t)` and `split(t, everything) = (t, ⊥)`.

The richness of the guard algebra a tiling can support depends on the tiling's algebraic
properties. Some tilings support only the trivial guard algebra; others support arbitrarily
rich guard algebras. This is not a deficiency of the tiling — it reflects the inherent
splittability of the type's operational structure.

### Universal Split-Determinism

Two optional properties of a progress algebra, when both present, guarantee that _any_ guard
algebra is split-determinate. We call this **universal split-determinism**.

**Cancellativity**: if `x ⊕ z = y ⊕ z` then `x = y`. This guarantees unique complements:
once you know a sub-tile `inside` and the whole tile `t`, the complement `outside` is uniquely
determined. Cancellativity also strengthens the progress preorder into a partial order
(antisymmetry follows from cancellativity together with positivity). With cancellativity, a
progress algebra is a [separation algebra](https://en.wikipedia.org/wiki/Separation_logic)
(a.k.a. cancellative partial commutative monoid).

**Sub-tile meet**: for any tiles `a, b ≤ t`, the greatest common sub-tile `a ∧ b` exists
(the greatest `s` with `s ≤ a` and `s ≤ b`). This guarantees unique insides: the greatest
element of `{a ∈ g : a ≤ t}` always exists, for any guard `g`.

**Lattice structure.** Together with cancellativity and positivity, the sub-tile meet implies
that the sub-tiles of any tile `t` form a **distributive lattice**. The lattice operations
`∧` (meet) and `∨` (join) are *not* `⊕` — they are total, idempotent operations on the poset
of sub-tiles, whereas `⊕` is partial and never idempotent (except at `⊥`). The join is
constructed by de-duplicating the shared part before combining: `a ∨ b = a ⊕ b'`, where
`b = (a ∧ b) ⊕ b'` strips out the part of `b` already in `a`. (`⊕` coincides with `∨` only
when `a ∧ b = ⊥`, i.e., when the sub-tiles are disjoint.) Distributivity —
`a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)` — means overlapping with a union equals the union of the
overlaps. Sub-tiles decompose into independent parcels that combine without entanglement.

**Proof that these conditions imply universal split-determinism.** Cancellativity gives unique
outside (condition 2) immediately. For unique inside (condition 1), we show any two candidates
have an upper bound in the guard.

Given `a, b ∈ g` with `a ≤ tile` and `b ≤ tile`, the sub-tile meet gives `s = a ∧ b`, and
cancellativity yields unique `a', b'` with `a = s ⊕ a'` and `b = s ⊕ b'`. We claim
`a' ∧ b' = ⊥`: any common sub-tile `w` of `a'` and `b'` satisfies `s ⊕ w ≤ a` and
`s ⊕ w ≤ b` (hence `s ⊕ w ≤ s`), giving `w = ⊥` by cancellativity and positivity.

Let `c = a ⊕ b'` (equivalently `s ⊕ a' ⊕ b'` — the join `a ∨ b` in the sub-tile lattice
of `tile`). Then:

- `c ≤ tile`: `b' ∧ a = ⊥` by the same argument (any common sub-tile of `b'` and `a` is
  `≤ a ∧ b = s`, but `s ∧ b' = ⊥`), so disjoint compatibility gives `a ⊕ b' ≤ tile`.
- `a ≤ c` (by definition) and `b ≤ c` (since `s ⊕ b' ≤ s ⊕ a' ⊕ b'`).
- `c ∈ g`: `b' ≤ b ∈ g`, so `b' ∈ g` by downward-closure; then `a ⊕ b' ∈ g` by ⊕-closure.

By induction, every finite set of candidates has an upper bound in `g`, so a greatest element
exists. ∎

⊕-closure is also **necessary** for split-determinism: if `a, b ∈ g` and `a ⊕ b` is defined,
then `split(a ⊕ b, g)` must return `(a ⊕ b, ⊥)` (since `a ⊕ b` is the largest element
`≤` itself in `g`), which requires `a ⊕ b ∈ g`.

**Which tilings have these properties?** Function tilings (`T ⇀ U`) have both cancellativity
and sub-tile meet, and so support any guard algebra. Scalar tilings (`{⊥} ∪ T`) also have
both.

### Unsplittable Tilings

Tilings which are only split determinate over the trivial guard algebra can still be interesting.
Being "unsplittable" just means that part of the information can't be thrown out without affecting
the overall computation.


**`Count × Sum`:** This tiling has carrier `{(0, 0)} ∪ {(n, s) : 1 ≤ n ≤ N, s ∈ ℤ}`, with
`(n₁, s₁) ⊕ (n₂, s₂) = (n₁ + n₂, s₁ + s₂)` when `n₁ + n₂ ≤ N`. This tiling is
cancellative but lacks sub-tile meet: `(2, 3)` and `(2, 5)` are both `≤ (N, 10)`, but their
lower bounds include all `(1, s)` for `s ∈ ℤ` with no greatest element.

However, the **only subtilings** of this tiling are `{⊥}` and the whole tiling. The proof:
suppose a subtiling `S` contains some `(1, s)`. By ⊕-closure, `(1, s) ⊕ (1, s) = (2, 2s) ∈ S`.
By downward-closure from `(2, 2s)`: since `(1, s') ≤ (2, 2s)` for all `s'` (the sum dimension
is unconstrained when the count is strictly less), all `(1, s') ∈ S`. By ⊕-closure and
induction, all tiles are in `S`. Therefore the only split-determinate guard algebra is the
trivial one — and this is the correct characterization: a sum accumulates opaquely, with no
useful intermediate decomposition.

**`Count × Max`:** This tiling has carrier `{(0, -∞)} ∪ {(n, m) : 1 ≤ n ≤ N, m ∈ ℤ}`, with
`(n₁, m₁) ⊕ (n₂, m₂) = (n₁ + n₂, max(m₁, m₂))` when `n₁ + n₂ ≤ N`. This tiling is
**not cancellative** (`(1, 5) ⊕ (1, 3) = (2, 5) = (1, 5) ⊕ (1, 4)`), and lacks sub-tile meet.
Just like `Count × Sum`, `Count × Max` only supports the trivial guard algebra.

These count-augmented carriers are the formal tilings that justify monotonicity and early termination. The runtime realizes an aggregate tiling as `Tiling::Aggregation { kind, accumulator }` with a `terminal` flag standing in for `count == N`, rather than storing an explicit count.



### Kinds of Guards

Guards appear in the producer/consumer protocol in the following roles:

**Projection guard**: passed to `get()` to decompose a tile via `split`. The producer returns only
the portion of its tile inside the projection guard's subtiling. Every interaction between a consumer
and a producer's tile is mediated by a projection guard, even if the tiling only supports the trivial
guard algebra — in which case the filter is always `everything` (return the whole tile) or
`nothing`.

**Intent guard**: a projection guard that persists across the lifetime of a subscription. A consumer registers its
intent guard at `subscribe()` time, declaring the full subtiling it will ever need. The intent
guard is an upper bound on future projection guards: the subtiling of any projection guard passed to
a subsequent `get()` will be intersected with the intent guard. For example, `Domain(D)` on a
function tiling restricts the consumer to mappings over `D`.

NOTE: Because unions of subtilings are not necessarily subtilings, intent guards
from multiple consumers may not be freely combinable. There may be guard algebras for which separate
state must be maintained for each consumer. For concrete guard algebras like `Domain(D)` in
function tilings, union does work (`Domain(D₁) ∪ Domain(D₂) = Domain(D₁ ∪ D₂)`, which is
⊕-closed), but the general story needs further investigation.

**Obsolete guard**: declares that a subtiling is no longer needed. Once all consumers have
released a subtiling, the producer may **compact** the portion of its tile inside of the
subtiling (see Section 3, Compaction) and reclaim resources. The obsolete guard must be a guard (not merely
a set of tiles) because `split` is required to separate the obsolete portion from the
still-relevant portion. For example, a consumer may release a subset of a function's domain
after processing the corresponding mappings and checkpointing the result. Another example:
when joining two streams of temporal data, a consumer might release old data from both streams
once it has been processed.

### Why Extent Predicates Are Not Guards

Consider `f : {0, 1} ⇀ ℤ` with the extent predicate `f(0) + f(1) > 100`. The downward
closure of terminal tiles satisfying this predicate includes `{0 ↦ 60}` (a sub-tile of
`{0 ↦ 60, 1 ↦ 50}`, which has sum 110) and `{1 ↦ 30}` (a sub-tile of `{0 ↦ 80, 1 ↦ 30}`,
which has sum 110). But `{0 ↦ 60} ⊕ {1 ↦ 30} = {0 ↦ 60, 1 ↦ 30}`, which has sum 90 and
is not in the set. The set is not ⊕-closed, so it is not a subtiling and cannot be a guard.

This is not a technicality — it reflects a real semantic issue. Whether a predicate on a
function's values holds depends on _which_ combination of inputs is present, not just on the
individual mappings. Guards decompose tiles structurally; extent predicates constrain values.
These are fundamentally different operations.

---

## 3. Operators

Sections 1–2 define the operational structures: tilings give types their progress algebra,
and guards give tilings their decomposition structure. This section connects these operational
structures to the denotational world of CCL. Types, terms, and functions each have an
operational counterpart — and the bridge between them is the **operator**.

### Denotational–Operational Correspondence

Each CCL type `T` has a corresponding tiling `Tiling(T)`, chosen by the compiler. Each term of
type `T` is computed as a tile in `Tiling(T)` — starting at `⊥` and growing monotonically until
it reaches a terminal tile.

Type constructors compose tilings in the expected way: a function type `T ⇒ U` uses the
partial-function tiling `T ⇀ U` over the extent of `T` and the tiling for `U`; a record type
would use a product-like tiling over its fields.

A CCL function `f : T ⇒ U` corresponds to a function between tiles,
`op : Tiling(T).Tile → Tiling(U).Tile`, called an **operator**. Operators are the operational
counterpart of denotational functions — they describe how to compute output tiles from input
tiles.

### The Operator Contract

An operator `op` corresponding to a CCL function `f : T ⇒ U` must satisfy two properties:

**Monotonicity**: `a ≤ b` implies `op(a) ≤ op(b)`. This encodes causality — more input
information can only lead to more (or equal) output information. An operator never "retracts"
progress it has already made.

**Correctness**: `op` is correct for `f` iff it commutes with the terminal bijection:
`∀ t : T . inject(f(t)) = op(inject(t))`. When the operator receives a terminal input, it
must produce the correct terminal output. Behavior on non-terminal tiles is constrained only
by monotonicity — the operator may output `⊥` until the input is terminal, or it may produce
useful intermediate tiles.

### Streaming via Homomorphisms

An operator that is also a **homomorphism** — `op(a ⊕ b) = op(a) ⊕ op(b)` — can process
input tiles incrementally as they arrive, without waiting for the input to become terminal.
Each new tile contributed to the input is independently transformed and combined into the
output, enabling streaming and pipelining. Correctness (the terminal-bijection condition)
guarantees that a homomorphism also **preserves terminality**: when the input reaches a
terminal tile, the output is terminal too, so the stream concludes.

*Example — function composition*: given a scalar function `g : B ⇒ C` and a function term
`f : A ⇒ B` with tiling `A ⇀ B`, the operator for `g ∘ f` maps each partial-function tile
`{a₁ ↦ b₁, …}` to `{a₁ ↦ g(b₁), …}`. This preserves disjoint-domain union, so it is a
homomorphism. Each new mapping of `f` is immediately transformed — no buffering needed.

*Example — projection*: for a product or record tiling, projecting to one component is a
homomorphism. Each increment of the record tile yields an increment of the projected
component.

### Early Termination

Some operators can produce a **terminal output from a non-terminal input** — the operator
determines its output is final before the input is complete. Early termination is independent
of streaming: it depends only on the operator being monotone and the output tiling having
the right structure. A non-streaming early-terminating operator is **repeatedly applied** to
the evolving input tile, **replacing** its previous output each time (not `⊕`-combining),
until the output becomes terminal.

Consider `sum(f) < 100` for `f : I ⇒ ℕ` and `|I|` bounded:

- `sum` is a tiling homomorphism from `I ⇀ ℕ` to `Count_N × Sum_ℕ`: each new mapping
  increments the count and adds to the running sum, up to `N` elements. Because `sum` is a
  homomorphism, it can stream — each new partial-function tile from `f` is independently
  transformed into a `Count_N × Sum_ℕ` tile and combined into the running aggregate.
- `< 100` is a monotone operator from `Count_N × Sum_ℕ` to `{⊥, true, false}`, but it is
  **not** a homomorphism — we cannot stream partial results into it. Instead, each time
  `sum` produces a new intermediate tile (enabled by `sum`'s homomorphism property), `< 100`
  is **re-applied** to the updated `Count_N × Sum_ℕ` state. Because partial sums of
  non-negative integers are non-decreasing, a fact that is encoded into the `Count_N × Sum_ℕ`
  tiling and is therefore usable by the `_<_` operator, once the running sum reaches 100 the
  `_<_` operator produces terminal `false` — without waiting for `f` to complete.
- The benefit comes from the combination: `sum`'s streaming feeds incremental updates to
  `< 100`'s repeated application, giving `< 100` the opportunity to terminate early at each
  step.

### Extent Predicates as Operators

Extent predicates — predicates on the final values of tiles (see Section 2, "Why Extent
Predicates Are Not Guards") — are expressed as **operators** in the CCL program, not as
guards. A predicate operator has the scalar tiling `{⊥, true, false}`.
The predicate only filters values when used as a refinement of the domain of a function.

Extent predicates compose with the guard system through two mechanisms:

1. **Standard domain guards propagating the consequence.** A terminal result from a predicate
   operator feeds into domain restrictions on enclosing function tilings via `Domain` guards.
   The function guard algebra suffices to do this filtering.
2. **Operators producing terminal results from non-terminal inputs.** The `< 100` operator
   on a non-decreasing sum can determine its output before its input is complete. This is a
   semantic property of the specific operator, not an algebraic property of the guard system.

### Compaction

Streaming and early termination describe how operators produce output. Compaction describes
how operators manage their *internal state* — specifically, how they reclaim resources when
consumers declare that a portion of their output is no longer needed.

When a consumer calls `release(obsolete_guard)`, it declares that it will never again request
tiles in the released subtiling. Once **all** consumers have released a subtiling, the operator
may reclaim the resources serving it. The simplest strategy is to discard the released tiles
entirely. But operators that need to track progress — to check terminality, to produce correct
future outputs — must retain a summary. This summarize-and-reclaim operation is **compaction**.

#### Mechanics

The operator's current tile decomposes as `obsolete ⊕ relevant`, where `obsolete` is in the
released subtiling and `relevant` is in the still-active subtiling. Split-determinism of the
guard algebra (Section 2) guarantees this decomposition is unique. The operator replaces the
full tile with `(compact(obsolete), relevant)`, where `compact` maps tiles of the source
tiling into tiles of a simpler **summary tiling**. The summary tiling is a progress algebra
in its own right, but is typically simpler: it may lack cancellativity or sub-tile meet, and
its guard algebra may be trivial. This is expected — the summary only needs to support the
queries that the operator actually performs on compacted state.

Concretely, when all consumers have released:

1. Compute `released`, the intersection of the obsolete guards from every consumer.
2. Call `split(relevant, released)` to obtain `obsolete_new ⊕ relevant_new`.
3. Compute `compact(obsolete_old) ⊕ compact(obsolete_new)` in the summary tiling, storing it
   alongside `relevant_new`.
4. Discard `obsolete_new` and the old `relevant`.

Compaction is **irreversible**: once applied, the original tile cannot be recovered. This is
safe precisely because all consumers have declared they no longer need it.

#### Requirements

An operator's compact map `compact : T → C` (from the source tiling into the summary
tiling) must satisfy:

1. **Homomorphism**: `compact(x ⊕ y) = compact(x) ⊕ compact(y)` for all compatible `x, y`,
   and `compact(⊥) = ⊥`. This ensures compaction can be applied incrementally — each newly
   released tile is compacted independently and combined with the running summary.
2. **Faithfulness at identity**: `compact(t) = ⊥` implies `t = ⊥`. Only the empty tile
   compacts to the empty summary. This prevents the operator from losing track of progress.
3. **Terminality preservation**: if `t` is terminal in `T`, then `compact(t)` is terminal
   in `C`.
4. **Terminality reflection**: if `compact(t)` is terminal in `C`, then `t` is terminal
   in `T`.

Properties 3–4 together ensure that termination can be checked on the compact representation:
`is_terminal(o ⊕ r) = is_terminal(compact(o) ⊕ compact(r))` for all compatible tiles `o`
and `r`.

Beyond these structural properties, the operator must guarantee **semantic sufficiency**: its
future output tiles must be a function of `compact(obsolete)` and `relevant` alone, not of
`obsolete` itself. This is a per-operator guarantee — it cannot be stated generically because
it depends on what the operator computes.

Note that this combination of properties implies that a compacting operator may never be able to
actually produce a terminal tile. This is by design: compaction is only useful when no one ever _needs_
the full terminal tile, all at the same time. Instead, all of the information in the terminal tile
is produced incrementally by splitting out subtiles. Semantic sufficiency ensures that the producer acts
_as if_ it had retained full tiles all along, but without being forced to retain the resources
implied.

#### Granularity

Compaction operates at the granularity of the guard algebra: the `split` operation can only
separate tiles along boundaries the guard algebra can express. If a tiling only supports the
trivial guard algebra (Section 2), the only possible splits are `(⊥, tile)` and `(tile, ⊥)` —
all or nothing. Operators over unsplittable tilings cannot partially compact, and that is fine:
their tiles are inherently atomic and must be retained in full until no consumer needs them.

#### Example: MVCC Key-Value Stores

Multi-Version Concurrency Control (MVCC) — as used in databases like PostgreSQL — illustrates
a compaction strategy for a versioned key-value operator. The source tiling is
`K × Version ⇀ V`: partial functions indexed by both key and version number, with `⊕`
defined for tiles whose `(key, version)` domains are disjoint.

Multiple consumers (transactions) may hold interest in different version ranges simultaneously.
When a consumer finishes reading old versions, it signals an obsolete guard on
`Domain({(k, v) | v < T})`. Once **all** consumers have released versions before `T`, the
operator compacts:

```
compact(f)(k) = (f(k, v_max), v_max)   where v_max = max{v | (k, v) ∈ dom(f)}
```

This maps each key to its latest value and version — a compaction from
`(K × Version ⇀ V, ⊕)` into the summary tiling `(K ⇀ V × Version, ∨)`, where `∨`
picks the higher-versioned entry per key. Because the version space is unbounded, `∨` is total
and neither the source nor summary tiling has terminal elements — termination is driven
by the transaction lifecycle, not the algebra. The compacted summary retains enough information
to correctly merge with future updates (via the retained version number) without storing the
full version history.

Semantic sufficiency is satisfied for any downstream operator that only needs the current
state of each key — which is the common case. Operators that require full version history
would use a different, less aggressive compaction strategy.

This is exactly what database vacuum does: old row versions are reclaimed once no active
transaction can read them, i.e., once all consumers have released their interest.
