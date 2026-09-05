# Collections

Cambra's surface language (CHL) has lists, arrays, sets and maps. The IR has one collection
primitive: a **data function** `𝐷 ⤇ 𝑉`, a function whose domain is the data
([type-inference.md, 4.6 Data vs compute functions](type-inference.md#46-data-vs-compute-functions)).
This document gives each surface type — those four spellings and the abstract `Collection(𝑇)`
— as that one primitive over a different domain, and says how each compiles.

What a program writes, and what each collection type means to it, is
[chl-spec, Direction: collection types](../../../docs/chl-spec.md#63-direction-collection-types-decided).
Start there if the question is about the language rather than the checker;
[The six collection types](#the-six-collection-types) below is the same list with its
domains.

The type-level machinery is the sum — a data function carrying its Σ binders — and the
[`TypeKind`] classifying the types each binder ranges over, specified in
[type-inference.md, Subtyping for sums](type-inference.md#subtyping-for-sums). Each
collection type is a Σ whose witness ranges over one **kind**, and this document says which
kind each one picks. "Kind" throughout means that `TypeKind`, never the collection type
itself; a witness is a binder, and the kind classifies the types it ranges over rather than
the binder.

The kind tells four of the five apart: `Array(𝑛, 𝑇)` is a bare data function over
one range, `List(𝑇)` a Σ over `UIntRanges`, `Collection(𝑇)` a Σ over `Type`. `Set(𝐾)` and
`Map(𝐾, 𝑉)` share the `SubtypesOf(𝐾)` kind and its key parameter, differing only in a codomain
that is `unit` for one, so the operation layer has nothing to dispatch on between them.
[Telling `Set` and `Map` apart](#telling-set-and-map-apart-open) is the open part.

> **What is built.** Everything in this document is implemented unless it is tagged
> `[Planned]` (e.g. the operation layer). Where a `[Planned]` feature has an interim
> behavior in today's code, that is tagged `[Interim]`.

## The six collection types

With `𝐷` a witness domain and `𝑛` a length:

- **`Array(𝑛, 𝑇)`** = `[0, 𝑛) ⤇ 𝑇` — domain `UIntRange(n)`, length *static*.
  Ordered. Lookup `arr[𝑖] : 𝑇` — total, because the bound `{𝑖 | 𝑖 < 𝑛}` is
  statically dischargeable. This is the shape the compiler builds for a list
  literal today.
- **`List(𝑇)`** = `Σ (𝐷 : UIntRanges). 𝐷 ⤇ 𝑇` — *some* index range, which one not
  necessarily known statically. Ordered. Lookup `lst[𝑖] : Option(𝑇)` — the bound is not
  statically dischargeable, so lookup is partial. The length is the witness domain's size,
  so `len` is its first projection rather than a stored field.
- **`Set(𝐾)`** = `Σ (𝐷 : SubtypesOf(𝐾)). 𝐷 ⤇ unit` — a key domain with trivial codomain;
  the domain is the payload. Unordered. Membership `𝑒 in 𝑠` discharges `𝑒`'s
  presence in the domain.
- **`Map(𝐾, 𝑉)`** = `Σ (𝐷 : SubtypesOf(𝐾)). 𝐷 ⤇ 𝑉` — a key domain; a *concrete* one's keys are
  typed `{𝑘: 𝐾 | 𝑘 ▷ (𝑚 ▷ collection_contains)}`. Unordered. Lookup `𝑚[𝑘] : Option(𝑉)` in
  general, `: 𝑉` when presence discharges (see
  [Lookup](#lookup-membership-discharge)). Membership `𝑘 in 𝑚`.
- **`FullMap(𝐾, 𝑉)`** = `(𝑘: 𝐾) ⤇ 𝑉` — a value for **every** key of `𝐾`, so the key set is
  readable from the type and `𝑚[𝑘] : 𝑉` needs no proof. Unordered. `𝑉` may depend on `𝑘`,
  which is why `groupby` returns one and no `Map` describes it
  ([`groupby`'s exact type](#groupbys-exact-type)). Totality is claimed rather than checked:
  nothing verifies the annotation against whatever built the map.
- **`Collection(𝑇)`** = `Σ (𝐷 : Type). 𝐷 ⤇ 𝑇` — the witness ranges over *every*
  domain; the domain rides along **in the value** (retained, not sealed — a
  domain-generic consumer holds it abstract). Unordered. The ⊤ of the kind order, and
  nothing more: keyed-ness lives in `SubtypesOf(𝐾)`, so `Collection(𝐾)` is not
  load-bearing for `Map`/`Set`.

  This is the type that needs a **runtime** witness, since iterating a `Collection(𝑇)`
  parameter has no static domain to read
  ([Compiling a conditional collection](#compiling-a-conditional-collection)).

Four of the six are sums over the named kind, and every rule they obey is the general Σ
rule at that kind — entry by a term, subtyping, and consumption
([type-inference.md, Subtyping for sums](type-inference.md#subtyping-for-sums)). `Array` and
`FullMap` are the two that are not: their domains are written in the type, so they need no
witness, and each is the unboxed form of the sum below it in the list. Crossing from either
to its sum is `box`, and that `box` is where the domain stops being available to reason
with.

## The collection type is declared, not read off the shape

Which side of `𝐷 ⤇ 𝑉` holds the payload is not fixed by the shape. `Set(𝐾)` iterates its
**keys** (the domain); `List(𝑇)` iterates its **values** (the codomain) — opposite sides
of the same function — and `Map(UInt, 𝑉)` and a filtered `List` can share a shape while one
must iterate entries and the other values. So which side is the payload is a fact about
the collection's *type*, and operations (`Iterable`, `Index`, `Membership`, `Ordering` —
[Operations](#operations-how-the-trait-layer-is-realized-planned)) dispatch on the declared
type rather than reading it back from the function. For the same reason **"keyed-ness" is not
a primitive**: there is no structural keyed property, only a per-type choice of what
`for ... in` surfaces.

Subtyping is the other axis and reads the shape as usual — `box(arr) <: List(𝑇) <:
Collection(𝑇)`, each edge the ordinary Σ rule at that kind
([type-inference.md, The Σ rule](type-inference.md#the-σ-rule)) — so the two axes do
not coincide: a `Set(𝐾)` is structurally a collection of `unit` and iterates `𝐾`.

## Telling `Set` and `Map` apart [Open]

`Set(𝐾)` and `Map(𝐾, unit)` are the same type, so nothing in [`Type`] distinguishes them and
no operation can dispatch between them. How to fix that is undecided; what follows records
the candidate and the questions it has to answer, not a decision.

The candidate is a **nominal type**: `Set` and `Map`, and only those two, become declared
type constructors with the `type` strength of
[chl-spec, Direction: term/type syntax split](../../../docs/chl-spec.md#61-direction-termtype-syntax-split-decided),
distinct from a structural `=` alias. The other three need nothing, since the kind already
discriminates a bare range `Fun` (`Array`), `UIntRanges` (`List`) and `Type` (`Collection`).

Three questions have to be answered together, and each has consequences outside this
document:

- **Whether the constructor wraps the Σ or abbreviates it.** A `Map` that elaborates to
  `Σ (𝐷 : SubtypesOf(𝐾)). 𝐷 ⤇ 𝑉` and vanishes is structural again, and `Set` is `Map` again.
  Trait dispatch matching the constructor requires the wrapping form, which makes `Set` and
  `Map` known nominal names rather than ordinary library declarations.
- **Whether `Map(𝐾, 𝑉) <: Collection(𝑉)` holds.** Structurally the edge falls out of the
  existing rule: `Σ (𝐷 : SubtypesOf(𝐾)). 𝐷 ⤇ 𝑉` has a kind contained in `Type`, so widening to
  `Collection(𝑉)` is the ordinary Σ rule. Nominally the edge is what a declared type
  constructor exists to withhold, and reaching `Collection(𝑉)` takes the explicit
  `values(m)`. `Array <: List <: Collection` is untouched either way. The answer decides
  what rejects `sum(m)` — a missing edge, or the iteration element (see
  [Views](#operations-how-the-trait-layer-is-realized-planned)).
- **The variance of `𝐾` and `𝑉` in `Map(𝐾, 𝑉)`.** A structural Σ reads variance off its
  body; a declared constructor states it once per parameter.

Nothing in [`Type`] carries a collection type constructor today, so none of this is an
implemented property.

**Until this is settled** `for ... in` binds the codomain for every collection type, because
key and entry iteration is exactly the `Set`-versus-`Map` distinction. If the operation
layer is needed first, the interim to reach for is **uniform entry iteration**: a `Set`'s
entry is `(𝐾, unit)` and the projection to `𝐾` is lossless, so `Map` gets correct entry
iteration without the distinction existing. That is surface-visible — `for k in s` would
bind a pair — so it is a spec decision, not a silent one.

## Representation: the key domain is the key morphism's image

A concrete keyed collection's domain is `{𝐾 | __elem ▷ (𝑚 ▷ collection_contains)}` — the
keys its key morphism `𝑚` produces.

**Naming the morphism is what makes membership provable.** A domain that said only "the keys
of this collection" would have no introduction rule: nothing could produce a value at it
except a term already stamped there, so `𝑚[𝑘] : 𝑉` would be unprovable by construction
rather than for want of a rule — and refinements relate by structural predicate equality
rather than implication, so there is no entailment step for a proof to land in instead.
Naming it supplies the rule: a key produced by `𝑚` is a key of the collection `𝑚` keys.

Naming a term is also what fixes when two key domains are the *same* domain: refinements
compare by structural predicate equality, so two domains agree exactly when they name the
same morphism term. That is a fact about terms rather than about collections — a domain
naming a parameter is one type over every collection that parameter is bound to, and
distinct spellings of one collection (a `let`-bound source and its inlined literal) are
distinct domains. Membership therefore reads "in the image of *this* morphism", under
whatever the morphism's free variables are bound to where the fact is used.

**A join of two keyed collections over different sources is not supported.** Their group
domains conflict, `box` does not help, and what the sum would need is a witness ranging over
both key domains.

[`Type::SharedHole`] equates the refinement's base with the morphism's codomain. The
builtin's scheme relates those two positions without equating them — `__elem` is *applied*
to the characteristic predicate, so the application contributes a lower bound only, and a
key type contradicting the morphism's would join with it rather than conflict.

## Operations: how the trait layer is realized [Planned]

> The **user-facing semantics** of `for`-in, `[]` / `[]?`, `in`, and ordering —
> what each collection type binds and returns — are specified in the spec
> ([chl-spec §3.9](../../../docs/chl-spec.md#39-subscript-and-attribute-access),
> [§4.6](../../../docs/chl-spec.md#46-for--iteration),
> [§6.3](../../../docs/chl-spec.md#63-direction-collection-types-decided)),
> not here. This section
> is the **implementation design**: how those operations dispatch on the
> collection's type and reuse the machinery below.

Each collection type carries its own instance of `Iterable`, `Index`, `Membership` and
`Ordering`, dispatched on the declared type ([The collection type is
declared](#the-collection-type-is-declared-not-read-off-the-shape)). Traits are a future
mechanism (typeclasses resolved by the given/`using`/`summon` solver,
[chl-spec §8](../../../docs/chl-spec.md#8-mutability-transactions-and-feeds)); until then
each operation is a built-in dispatch on the type, and when traits land these built-ins
become the per-type standard-library instances with no semantic change. Everything here is
[Planned].

- **Iteration (`Iterable`).** `for`-in binds what the type's `Iterable` instance
  yields — values (`List`/`Array`/`Collection`), keys (`Set`), or `(key, value)`
  entries (`Map`). Because that is chosen by the collection type, which is known only
  after inference, the binding **cannot be fixed at lowering** (pre-inference); it
  is resolved at **coalesce**, once the node's type is known — the
  same hook a [kinding constraint](type-inference.md#an-unresolved-candidate-becomes-a-kinding-edge)
  is discharged at. The loop encoding already threads the domain element as
  `__iter_record` (`comprehension.rs`), so binding the domain, the codomain, or both is a
  choice of *which* slot to bind, not a materialization.
  **[Interim]:** today the loop binds the codomain unconditionally (a map iterates
  values, as `groupby` results do); the per-type element choice is the [Planned]
  work and only *adds* cases — it does not change the tuple-binder form.
- **Lookup.** The two operators `[]` (proven) / `[]?` (optional) are the surface;
  their single shared mechanic is one domain-membership refinement that either
  discharges (`: 𝑇`) or does not (`: Option(𝑇)`).
- **Membership (`in`).** `Map`/`Set`'s instance tests the domain, `List`/`Collection`'s
  the codomain (Python semantics). A key-membership guard refines the key (`if k in
  m` ⟹ `k` carries the domain-membership proof), which is what a proven `[]` needs.
  **How** membership is expressed in the representation is an *implementation detail*
  of `Map`'s instance, **not** a type-level keyed marker.
- **Order.** Sequentiality is deduced from loop-carried dependencies and ordering
  is supplied as an `Ord` given, never fabricated. A positional domain (`UIntRange`, `Txn`,
  an induction domain) is totally ordered by construction, so `Array` and `List` are
  ordered; a keyed or opaque domain carries no order and an order-dependent operation over
  one needs an `Ord[𝐾]` instance rather than a fabricated one.
- **Views (`keys` / `values` / `items`).** `Map`'s projection operations, each a
  **lazy view** — no copy: `keys(m) : Collection(𝐾)` (the key set), `values(m) :
  Collection(𝑉)` (the map's own function), `items(m) : Collection({𝐾, 𝑉})`
  (`𝑘 ↦ (𝑘, 𝑚(𝑘))`). Turning a `Map` into a `Collection(𝑉)` is a **re-pairing**
  (project the key set, re-introduce over domain `{𝑘 | 𝑘 ∈ keys}`) — runtime-free,
  since `m` already carries its keys as its domain. `values(m)` is nonetheless the form to
  write, because `for x in m` binds entries while `for x in (m : Collection(𝑉))`
  binds values, and the explicit projection is what makes which one is meant
  visible — matching [chl-spec §6.3](../../../docs/chl-spec.md#63-direction-collection-types-decided).
  What *enforces* that turns on the open subtyping question ([Telling `Set` and `Map`
  apart](#telling-set-and-map-apart-open)). Structurally the `Map <: Collection(𝑉)` edge
  holds today, ⊤ absorbing every kind, and `sum(m)` is then rejected once `sum` lowers
  through iteration, because a `Map` yields `(𝐾, 𝑉)` entries and entries cannot be summed.
  Withholding that edge is what a declared type constructor would be for. Until either
  lands, `sum(m)` means `sum(values(m))`.

## Consuming a keyed collection: discharge, not point-free compose

A `groupby`'s per-key group `{𝑖 | key(𝑖) == 𝑘} ⤇ 𝑉` has a **dependent** codomain, so
anything consuming it must not let `𝑘` escape into the consumer, which is bound outside
`𝑘`'s scope. Cambra **discharges** the binder rather than packing it under an existential,
and can always do so because it controls every composition it emits — there is no surface
compose operator.

So a consumption lowers η-expanded: `producer ≫ consumer ⤳ λ 𝑥 → consumer(producer(𝑥))`,
where `producer(𝑥)` is a dependent application substituting `𝑥` for the key binder. A
comprehension is already in that form. A bare point-free `keyed ≫ collapse` is never
emitted — its consumer's parameter would resolve with `𝑘` free, which the scope check
rejects — and a `debug_assert` in `coalesce_node`'s `Compose` arm holds the invariant: no
`Compose` morphism's codomain may reference that morphism's own Pi binder.

## Lookup: membership discharge

> **[Planned]** — `c[k]` lowers as the lookup `c(k)`, but no rule discharges the index's
> membership, so it is a type error at the `Apply` for every index. The surface operators are
> specified in [chl-spec §3.9](../../../docs/chl-spec.md#39-subscript-and-attribute-access);
> this is the mechanic that decides which one type-checks.

Lookup is uniform across ranges and keys: `𝑐[𝑥]` is well-typed when `𝑥`'s type proves
`𝑥 ∈ dom(𝑐)`, and its totality is *whether that proof discharges*. Membership rides on the
**element's** type, not the collection's, so iterating a collection's own domain hands the
proof over and `m[k]` is total there, while a key from outside carries no proof and takes
the checked `m[k]?`. The range case is the same rule at a different domain: `arr[𝑖] : 𝑇`
where `{𝑖 | 𝑖 < 𝑛}` discharges, `lst[𝑖]? : Option(𝑇)` where it cannot. One mechanic covers
all four collection types rather than one per type.

### Prerequisite: the proof has to survive being consumed

Two routes produce a key carrying a collection's key domain, and only one of them works.

**Applying the key morphism** is direct: `(c ≫ key)(𝑖)` is a key of the collection
`c ≫ key` keys, because that is what `{𝑘 | 𝑘 ▷ ((c ≫ key) ▷ collection_contains)}` says.
This is what makes `for o in orders: g[key(o)]` provable, and it is what naming the
morphism bought — an opaque domain admits no such rule.

**Iterating the collection** does not, and the gap is in consumption rather than in the
surface. Consuming a sum deliberately presents the sum `σ` rather than the refined domain,
so that the witness cannot escape into the consumer's result; an iterated key is therefore
a consumed sum's witness, and the membership has nothing to discharge against. The
apparatus is there — `𝑘 : σ` alongside `𝑚 : σ` is the pairing a discharge needs — but which
shape closes it is open, and it lands before the `[]` / `[]?` surface rather than with it.

## `groupby`'s exact type

For `c: 𝐼 ⤇ 𝐴` and `key: 𝐴 → 𝐾`:

```
groupby(c, key) : (𝑘: {𝐾 | 𝑘 ▷ ((c ≫ key) ▷ collection_contains)}) ⤇ ({𝑖: 𝐼 | key(c(𝑖)) == 𝑘} ⤇ 𝐴)
```

The outer domain is *this* group-by's present keys, so it is not confusable with any other
collection's, and it is the group-by's own keys rather than all of `𝐾` because a data
function's domain is its data — a domain of `𝐾` would claim one row per inhabitant. The
codomain is the group, and it **depends on `𝑘`**.

That dependency decides what the type is: a [`FullMap`](#the-six-collection-types), not a
`Map`, since a `Map(𝐾, 𝑉)` holds one `𝑉` with no binder for the group to name. No
annotation or consumer converts one into the other, so a group-by is consumed at the type
it has.

### Lowering realization: the key binder states its domain

Lowering emits, with the inner group a cast:

```
groupby(c, key)  ⟶  λ (__gb_k : {𝐾 | __elem ▷ ((c ≫ key) ▷ collection_contains)}) → cast(λ __gb_i → __gb_i ▷ c, {𝐼 | key(c(__elem)) == __gb_k} ⤇ 𝐴)
```

which enters `Map(𝐾, …)` by the Σ rule once `box` has made it a one-candidate sum. Two
things say what it is: the binder is declared at the present-key domain
(`present_key_domain`), and a `data_fun(_, _)` annotation on the lambda stamps `Data` onto
the arrow. Nothing derives the kind from the key domain, which is scalar.

**`Converse` discharges the present-key domain.** Planning rebuilds the site as
`converse ≫ map`, and the two halves are typed at different domains: the key-extraction
morphism `c ≫ key` yields plain keys and is typed at the bare `𝐾`, while the partition
`Converse` builds holds exactly the keys that occur and is stamped at the present-key
domain. One key type serving both roles either rejects the extraction or understates the
partition.

The predicate rides to op-conversion on **types**, never as a term. Point-free compilation
applies to the predicates planning reifies into a `Restrict`, and this one it never
reaches — a membership evaluation would be a keyed lookup or an `x in s` filter, neither of
which exists.

### Constructor lowering: runtime `groupby` now, constant-folding later

The re-keying constructors are the first surface (before the `[k -> v]` sugar and
annotation-driven implicit insertion). Their **value construction is a runtime
`groupby`** on the key projection ([chl-spec
§3.11](../../../docs/chl-spec.md#311-list-tuple-record-literals)): `map([𝑘𝑣…])` groups the pairs by
`.0` and collapses each group to its `.1`; `set([𝑒…])` groups by the element,
codomain `unit`; `list([𝑒…])` keeps the positional domain (`Array` widened to
`List`). The result is the keyed Σ (`Map`/`Set`) or `List`.

Two consequences are **deferred to a future constant-folding pass**, recorded
here so the shortcut is explicit:

- **Compile-time construction.** A literal argument has statically-known keys, so
  the ideal is to build the sealed keyed tile at compile time rather than run a
  `groupby` over a constant. Cambra has no constant-folding today; when it lands,
  folding a re-keying over a constant collection *is* the compile-time
  construction, with no literal-detection special-case (the fold either succeeds
  on constant inputs or falls through to the runtime operator).
- **Duplicate-key error timing.** The spec makes a duplicate key in a map
  *literal* a *compile-time* error
  ([§3.11](../../../docs/chl-spec.md#311-list-tuple-record-literals)). At runtime, a duplicate produces a
  non-singleton group, which `map`'s `sole` collapse **rejects at run time** (that
  is its whole point) — so the error is *enforced*, just later than the spec wants.
  Moving it to compile time needs the key *values*, which only a constant fold
  has; so the compile-time-ness (not the enforcement) rides on constant-folding.
  (`set` has no `sole`, so duplicates there are absorbed by the group — set
  semantics — no error either way.)

#### `sole` is an `Option`-accumulator aggregate

`sole : (𝐷 ⤇ 𝐴) ⇒ 𝐴` is an ordinary [`AggregateKind`] (`Sole`) reusing the
aggregation framework — per-key accumulator, fold, extract. Its accumulator law is
`Option(𝐴)`'s: identity `none`, and the partial monoid where combining two `some`
values faults, two elements under one key being the duplicate. `Sum` and `Max` have
total monoids for accumulators, so `Sole` is the first partial one.

The fault is raised in `accumulate`, which is the only one of the three that sees a
single group. Under `MapAggregate` a fold receives one key's slice at a time, so a
length bound there is a bound on a group; `extract` instead runs on a column holding
one accumulated value per key, whose length is the key count, so it cannot check a
group's size and is the identity.

Two realization details separate `sole` from the scalar aggregates. Both follow from
`map`'s codomain; `set`'s `unit` codomain needs neither.

- **Presence is out-of-band.** `Sum` and `Max` carry an in-band identity (`0`, `MIN`)
  and `sole` has none, any element being a valid value. So `none` is the empty
  accumulator column and `some` a column of length one, and `initial_accumulator`
  builds the empty column from the extent rather than a value of the element type.
- **`sole` folds a structured codomain.** Each group's codomain in `map` is the pair
  `(𝐾, 𝑉)`, so the fold takes the sole *row* of a tuple-valued group where `Sum`
  takes a scalar column. This needs no per-shape code: `ColumnValue::select_indices`
  and `ColumnValue::append` both recurse through a record column, so one group folds
  by the same two calls whether its elements are pairs or scalars.

#### Runtime realization: nothing new for construction + value iteration

A keyed collection is **already a first-class runtime tile**: `groupby`'s
`λ 𝑘 → cast(…)` eliminates to a Pi-const source that planning recognizes as
`Converse` (see [Lowering realization](#lowering-realization-the-key-binder-states-its-domain)),
and `Converse` emits a `CurriedFunction` tile whose outer domain column *is* the
present keys. The `map`/`set` codomain map runs over that
`Converse` (as the group-consuming body of a comprehension-shaped iteration; see
[Consuming a keyed
collection](#consuming-a-keyed-collection-discharge-not-point-free-compose) for why
it is not a bare `Compose`). So construction and **value-iteration** consumption (`for v in m`)
reuse the existing operator set with **no new `Domain` and no hash store**. A keyed domain
dispatching `extent_of` to a hash store is for *lookup* (`𝑚[𝑘]`), which arrives with that
feature — not for immutable construction.

`set([𝑒…])` lowers to the group-by on an identity key, collapsed by the terminal
aggregate [`AggregateKind::Drain`] — `(𝐷 ⤇ 𝛾) ⇒ unit`, accumulator `Units(1)`,
`accumulate` a no-op — folding each key's group (of ≥ 1 duplicate elements) to the
one `unit` a `Set` holds. `set([1,2,2,3])` produces the sealed keyed tile over keys
`{1, 2, 3}`. `map([𝑘𝑣…])` is the same shape at the `Sole` collapse
([`lower_rekeyed`] builds both), so `map([(1, 10), (2, 20)])` produces the sealed
keyed tile carrying `10` and `20`.

Neither constructor compiles over a literal whose elements share **one** singleton
type. The element type stays that singleton (`Int@1`) where the key domain's base
widens to `Int`, and the two meet at the cast as a domain conflict, so `set([1])` and
`map([(1, 10)])` are rejected where `set([1, 2])` and `map([(1, 10), (2, 20)])`
compile (`test_rekeying_over_a_singleton_literal`). The single-entry seed a mutable
map wants is that shape.

Where a keyed collection value is and is not **driven** is a planning property, not
a constructor one, and the boundary is narrower than it looks. Planning inserts the
driving `iterate` at a *chain head*, so a `set(…)` reaches the runtime when it is
the program tail (`set([1,2,3])`), when it is a bare `groupby(…)`
(`a_bare_groupby_tail_is_driven`), or when it is let-bound and then consumed
(`s = set([…])` … `[k for k in s]`). What fails is a keyed collection **nested as
the source of another comprehension** (`[1 for k in set([1,2,3])]`), which surfaces as
*"list literal reached op-conversion without an input"*: the underlying source is never
given an iteration site. `test_undriven_keyed_collection` records it, and fixing it is a
planning change rather than part of the constructor surface. Separately, a keyed collection
cannot yet **yield its keys under iteration** — the deferred `items` view above, itself
blocked on the
[kind-representation question](#the-collection-type-is-declared-not-read-off-the-shape).

## Keyed entry needs the key domain written down at lowering

An entry term runs a membership predicate on the entering side, so it decides at
constraint-emission time only for a domain that is already concrete, and otherwise becomes
a kinding constraint on the domain variable. Whether a producer satisfies that is not a
property of the collection type but of whether lowering wrote the domain down. So the rule
for every re-keying producer is: **stamp your own key binder with the present-key domain**
`{𝐾 | __elem ▷ (𝑚 ▷ collection_contains)}`
([Representation](#representation-the-key-domain-is-the-key-morphisms-image)). Get
it wrong and the failure is an `AnnotationMismatch` on the Σ witness rather than anything
naming the cause, because the gate had nothing concrete to test.

A re-keying producer knows its key image syntactically, so it needs no deferred obligation
of the kind a comprehension's range domain takes. One comes due for a producer whose key
domain is unknowable until coalesce — a map comprehension, a keyed feed — and none exists
today.

## Iterating a `Set`/`Map` binds the codomain, not the keys [Interim]

`for g in groupby(xs, key)` binds `g` to the **codomain** — each group, not each key. The
semantic decision is made and kind-directed
([chl-spec §4.6](../../../docs/chl-spec.md#46-for--iteration)); what blocks it is narrower
than the operation layer being unbuilt. The element choice has to distinguish `Set` from
`Map`, and those are currently the same type, so there is nothing to dispatch on
([Telling `Set` and `Map` apart](#telling-set-and-map-apart-open)).


## Compiling a conditional collection

```
c: Bool = True
sum(box([1, 2]) if c else box([1, 2, 3]))
```

The arms' domains are `[0, 1]` and `[0, 2]`, so the `Case` types as
`Σ (𝜎 : [[0, 1], [0, 2]]). 𝜎 ⤇ Int` — one collection over a domain the branch picks
([type-inference.md, The domain join needs `box`](type-inference.md#the-domain-join-needs-box)).
Nothing reads a witness off a value at runtime, so that type on its own gives `sum` no
extent to iterate.

**Realization** replaces the Σ with a term that has one. The `Case` becomes the gated union
`⧺ᵢ (armᵢ | π̂ᵢ)` over the same domains, each leg gated by the path condition its `if`/`elif`
compiled to. The gates are exclusive and exhaustive, so exactly one leg is non-empty and the
union's extent is the domain the witness selected — which is what makes the union and the Σ
the same collection. It runs in planning (`planning/conditionals.rs`) and asserts its
pre-realization type rather than relating the two by a typing rule
([type-inference.md, Planning asserts the type it
replaces](type-inference.md#planning-asserts-the-type-it-replaces)).

**A conditional collection is the only Σ-typed term the runtime can currently evaluate.**
Its candidates are statically enumerable and the gates pick one. Every other Σ — a
`Collection(𝑇)` whose producer is not statically known, a collection in a `Mut` register or
crossing a source boundary — waits on a runtime witness that does not exist yet, and a Σ
that reaches op-conversion with no concrete domain has no extent and is reported as a
compiler bug.

**One realization per site, at the node whose type carries the choice**: the outermost `Σ`
binding the witness. Arms sharing a domain form no Σ at all, and substituting the arm for
the conditional at the site leaves the arm.

### Realization instantiates the witness inside the predicate

Realization substitutes one candidate for the witness at the site, and the predicate of a
consumer's filter is one of the places that witness occurs: a domain refinement's predicate
holds its own read of the source, and that read names the witness. So the leg is gated
twice, by its path condition `π̂ᵢ` and by `𝑝` with `armᵢ` in place of the source
(`read_the_arm_instead` in `src/ccl/planning/conditionals.rs`). Both gates are the one
substitution reaching two occurrences.

This is β, not a pushdown. Nothing weighs running the filter inside the leg against running
it after the union: a leg is the site with the witness instantiated, and an occurrence left
uninstantiated names a witness that no longer exists. A cost model has nothing to decide
here, and no ordering of the two gates is available to choose between.

The instantiated form is also the only expressible one. A predicate may name a plain arm,
but it may not name the gated union: reading the union needs the `iterate`/`restrict`
markers a predicate is forbidden to contain. Substituting `armᵢ` puts the read somewhere a
predicate is allowed to be.

Over a product domain the predicate holds one read per position, and each is instantiated
with the arm its own position chose. What the read's index ranges over does not identify the
position: two conditionals over the same candidate domains state the same kind. The element
position the source is applied to does, and the predicate spells those positions in the
site's own binders ([type-inference.md, The index is named at the domain
position](type-inference.md#the-index-is-named-at-the-domain-position)) — so a source is
matched by the sum's kind and the index reading it together.

**So a `let`-bound conditional is copied to each consumer.** Realization needs the `Case`
below the site, because a leg *is* the site with the `Case` replaced by one arm; a binding
precedes its body in scope, so a `Case` left there is above every site that reads it. The
site then names a witness no term has materialized, and op-conversion rejects the domain.
The copy is also what lets each consumer's substitution differ: two consumers filtering one
conditional instantiate the same witness into two different predicates, which one set of
legs cannot hold.

Only an **undetermined** witness is copied — a kind naming more than one candidate. A
determined one has no realization to feed, since the candidate is already its domain and the
erasure removes the binder where it stands; copying it duplicates the arms and puts a `box`
inside each consumer, where the erasure reaches the term but not every type that named it. A
runtime witness would remove the need for the copy, by letting one materialized union serve
several consumers; until that exists the copy is the only compiling form. It would also make
this substitution one choice among several rather than the only expressible form — the point
at which the duplication becomes a cost question instead of an obligation.

### A site's witnesses are compiled together

Two conditional generators in one comprehension put two sums over one product domain —
`Σ (𝜎₄ : 𝐾₄). Σ (𝜎₇ : 𝐾₇). ((𝜎₄, 𝜎₇) ⤇ 𝑉)` — and that is one site with two choices on it,
not a site within a site. So the legs are the **tuples** of arms, gated by the conjunction
of their path conditions and indexed by the product of their domains: the same finite-Σ ≡
gated-union isomorphism, stated for a product of witnesses. It is flat, which is what
`Expr::copair` already is, flattening a nested copairing into its operands.

Compiling the two one at a time instead leaves a union where a generator reads its
collection at a projected index (`π₀ ≫ coll`), and a union there is a **fed** copairing,
which op-conversion has no form for: its arms are over distinct index sets, so they cannot
flat-merge onto the one domain the input carries.

The gap is not particular to conditionals.
`sum([x + y for x in ([1, 2] ++ [3, 4]) for y in [10, 20]])` reaches the same rejection, and
the `let`-bound spelling of it reaches runtime instead and fails in
`ColumnValue::transform_by_map`, which has no union-key case — the
`a_union_generator_beside_a_second_generator` test in
`tests/compilation_pipeline/scalars_collections.rs`. Compiling a site's witnesses together
is what keeps every generator's domain a plain range, so no union is ever read at an index.
A tagged fed copairing, demultiplexing the input by tag and re-tagging each arm's output, is
what would let the legs be per conditional rather than per arm tuple.

A site therefore **names** its witness rather than being it: beside a second generator the
index is a product, so the filter rides `{(𝜎, 𝐷) | 𝑝}` and every rule keyed on the witness
matches a *mention* of it rather than the whole domain. Reading the whole domain makes the
product a silently different case, which emits the site's chain a second time over a witness
that has no extent.
