# Collections

Cambra's surface language (CHL) has lists, arrays, sets and maps. The runtime has one
collection primitive: a **data function** `𝐷 ⤇ 𝑉`, a function whose domain is the data
([type-inference.md, 4.6 Data vs compute functions](type-inference.md#46-data-vs-compute-functions)).
This document is how the five collection types those four spellings and the abstract
`Collection(𝑇)` name are that one primitive over different domains, and how they compile.

What a program writes, and what each collection type means to it, is
[chl-spec, Direction: collection types](../../../docs/chl-spec.md#63-direction-collection-types-decided).
Start there if the question is about the language rather than the checker;
[The five collection types](#the-five-collection-types) below is the same list with its
domains.

The type-level machinery is `Type::Sigma` and its witness kinds, specified in
[type-inference.md, Subtyping for sums](type-inference.md#subtyping-for-sums). A collection
type is a Σ over a witness **kind**, and this document says which kind each surface type
picks.

The **kind axis** is the part still open, and only for one pair. The witness kind already
tells four of the five apart: `Array(𝑛, 𝑇)` is a bare data function over one range,
`List(𝑇)` a Σ over `UIntRanges`, `Collection(𝑇)` a Σ over `Any`. `Set(𝐾)` and `Map(𝐾, 𝑉)`
are the pair it cannot, sharing the `Keyed(𝐾)` kind and its key parameter and differing
only in a codomain that is `unit` for one — so the operation layer has nothing to dispatch
on between them.

> **What is built.** A mechanism's section arrives in the branch that implements it, so a
> section being here means its mechanism is built unless it is tagged `[Planned]` — which
> the operation layer is, throughout. Where a `[Planned]` feature has an interim behavior in
> today's code, that is tagged `[Interim]`: an unfinished state on the path to the design,
> not a shim to remove.

## The kind is declared, not read off the shape

Which side of `𝐷 ⤇ 𝑉` holds the payload is not fixed by the shape. `Set(𝐾)` iterates its
**keys** (the domain); `List(𝑇)` iterates its **values** (the codomain) — opposite sides
of the same arrow — and `Map(UInt, 𝑉)` and a filtered `List` can share a shape while one
must iterate entries and the other values. So which side is the payload is a fact about
the collection's *kind*, and operations (`Iterable`, `Index`, `Membership`, `Ordering` —
[Operations](#operations-how-the-trait-layer-is-realized-planned)) dispatch on the
declared kind rather than reading it back from the arrow. For the same reason
**"keyed-ness" is not a primitive**: there is no structural keyed property, only a
per-kind choice of what `for`-in surfaces.

Subtyping is the other axis and reads the shape as usual — `box(arr) <: List(𝑇) <:
Collection(𝑇)`, each edge the ordinary Σ-width rule at that kind
([type-inference.md, The width rule](type-inference.md#the-width-rule)) — so the two axes do
not coincide: a `Set(𝐾)` is structurally a collection of `unit` and iterates `𝐾`.

> **Tentative — the ambiguous pair gets a nominal type.** `Set` and `Map`, and only
> those two, become **nominal type heads** — the `type` strength of
> [chl-spec, Direction: term/type syntax split](../../../docs/chl-spec.md#61-direction-termtype-syntax-split-decided),
> distinct from a structural `=` alias — landing when nominal types do. The other three
> kinds need nothing: the witness kind already discriminates a bare range `Fun`
> (`Array`), `UIntRanges` (`List`), `Keyed(𝐾)` (`Set`/`Map`) and `Any` (`Collection`),
> so `Set` versus `Map` is the one pair it cannot tell apart — they share a kind and its
> key parameter and differ only in a codomain that is `unit` for one. A nominal head
> makes that difference readable from the type, where `{𝐾 | tok} ⤇ unit` cannot say it.
> Nothing in [`Type`] carries a collection kind today, so this states an intent rather
> than an implemented property.
>
> Three consequences:
>
> - **The head wraps the Σ rather than abbreviating it.** A `Map` that elaborates to
>   `Σ (𝐷: Keyed(𝐾)). 𝐷 ⤇ 𝑉` and vanishes is structural again, and `Set` is `Map` again.
>   Trait dispatch matches the head, so `Set` and `Map` are known nominal names rather
>   than ordinary library declarations.
> - **Only the lateral relation becomes a decision.** `Array <: List <: Collection` is
>   untouched. Width-to-top survives for the nominal pair without a declared edge:
>   widening to `Collection(𝑉)` forgets which head it had, and the head's content
>   `Σ (𝐷: Keyed(𝐾)). 𝐷 ⤇ 𝑉` has a kind contained in `Any`, so the edge falls out of the
>   existing rule. What has to be stated is one rule — a nominal collection head is a
>   subtype of its content — plus the head's parameter variance, once per constructor.
> - **The head's compact representation cannot be an [`AtomKey`].** `AtomKey` is a
>   discrete set: reflexive arms only, atoms merge by union, and two shapes at one
>   position is a collision. Because a head widens by being forgotten, two different
>   heads meeting at one position join through their content rather than colliding, so a
>   tag alongside the existing `fun` slot that the join drops is likely sufficient. If a
>   full slot is needed, the shape to copy is [`Type::History`] — a fixed-arity
>   constructor with type children and its own slot merged componentwise, differing in
>   that `history_slot` recurses invariantly. Deciding between the two belongs to
>   designing nominal types.
>
> **Sequencing.** This is a prerequisite for key and entry iteration, which is the
> `Set`-versus-`Map` distinction, so until it lands `for`-in binds the codomain for every
> kind.
> If nominal types land after the operation layer is needed, the interim to reach for is
> **uniform entry iteration**: a `Set`'s entry is `(𝐾, unit)` and the projection to `𝐾` is
> lossless, so `Map` gets correct entry iteration without the distinction existing. That
> is surface-visible — `for k in s` would bind a pair — so it is a spec decision, not a
> silent one.

## The five collection types

With `𝐷` a witness domain and `𝑛` a length:

- **`Array(𝑛, 𝑇)`** = `[0, 𝑛) ⤇ 𝑇` — domain `UIntRange(n)`, length *static*.
  Ordered. Lookup `arr[𝑖] : 𝑇` — total, because the bound `{𝑖 | 𝑖 < 𝑛}` is
  statically dischargeable. This is the shape the compiler builds for a list
  literal today.
- **`List(𝑇)`** = `Σ (𝐷: UIntRanges). 𝐷 ⤇ 𝑇` — *some* index range, which one not
  known statically. Ordered. Lookup `lst[𝑖] : Option(𝑇)` — the bound is not
  statically dischargeable, so lookup is partial. The length is the witness domain's size,
  so `len` is its first projection rather than a stored field.
- **`Set(𝐾)`** = `Σ (𝐷: Keyed(𝐾)). 𝐷 ⤇ unit` — a key domain with trivial codomain;
  the domain *is* the payload. Unordered. Membership `𝑒 in 𝑠` discharges `𝑒`'s
  presence in the domain.
- **`Map(𝐾, 𝑉)`** = `Σ (𝐷: Keyed(𝐾)). 𝐷 ⤇ 𝑉` — a key domain. Unordered. Lookup
  `𝑚[𝑘] : Option(𝑉)` in general, `: 𝑉` when presence discharges. Membership `𝑘 in 𝑚`.
- **`Collection(𝑇)`** = `Σ (𝐷: Any). 𝐷 ⤇ 𝑇` — the witness ranges over *every*
  domain; the domain rides along **in the value** (retained, not sealed — a
  domain-generic consumer holds it abstract). Unordered. The ⊤ of the kind order, and
  nothing more: keyed-ness lives in `Keyed(𝐾)`, so `Collection(𝐾)` is not
  load-bearing for `Map`/`Set`.

  This is the type that needs a **runtime** witness, since iterating a `Collection(𝑇)`
  parameter has no static domain to read
  ([Realizing a conditional collection](#realizing-a-conditional-collection)).

Each is a `Type::Sigma` over the named kind, and every rule they obey is the general Σ
rule at that kind — entry by a term, width, and consumption
([type-inference.md, Subtyping for sums](type-inference.md#subtyping-for-sums)). Only
`Array` is not a sum: its domain is one concrete range, so it needs no witness.

## Operations: how the trait layer is realized [Planned]

> The **user-facing semantics** of `for`-in, `[]` / `[]?`, `in`, and ordering —
> what each collection kind binds and returns — are specified in the spec
> ([chl-spec §3.9](../../../docs/chl-spec.md#39-subscript-and-attribute-access),
> [§4.6](../../../docs/chl-spec.md#46-for--iteration),
> [§6.3](../../../docs/chl-spec.md#63-direction-collection-types-decided)),
> not here. This section
> is the **implementation design**: how those operations dispatch on the
> collection's type and reuse the machinery below.

Each kind carries its own instance of `Iterable`, `Index`, `Membership` and `Ordering`,
dispatched on the declared kind ([The kind is
declared](#the-kind-is-declared-not-read-off-the-shape)). Traits are a future mechanism
(typeclasses resolved by the given/`using`/`summon` solver,
[chl-spec §8](../../../docs/chl-spec.md#8-mutability-transactions-and-feeds)); until then
each operation is a built-in dispatch on the kind, and when traits land these built-ins
become the per-kind standard-library instances with no semantic change. Everything here is
[Planned].

- **Iteration (`Iterable`).** `for`-in binds what the kind's `Iterable` instance
  yields — values (`List`/`Array`/`Collection`), keys (`Set`), or `(key, value)`
  entries (`Map`). Because that is chosen by the kind, and the kind is known only
  after inference, the binding **cannot be fixed at lowering** (pre-inference); it
  is resolved at **coalesce**, once the node's type (hence kind) is known — the
  same hook a [kinding constraint](type-inference.md#what-the-kind-level-needs-from-the-solver)
  is discharged at. The realization is cheap: the loop encoding already threads the domain
  element as `__iter_record` (`comprehension.rs`), so binding the domain, the
  codomain, or both is a choice of *which* slot to bind, not a materialization.
  **[Interim]:** today the loop binds the codomain unconditionally (a map iterates
  values, as `groupby` results do); the per-kind element choice is the [Planned]
  work and only *adds* cases — it does not change the tuple-binder form.
- **Lookup.** The two operators `[]` (proven) / `[]?` (optional) are the surface;
  their single shared mechanic is one domain-membership refinement that either
  discharges (`: 𝑇`) or does not (`: Option(𝑇)`).
- **Membership (`in`).** `Map`/`Set`'s instance tests the domain, `List`/`Collection`'s
  the codomain (Python semantics). A key-membership guard refines the key (`if k in
  m` ⟹ `k` carries the domain-membership proof), which is what a proven `[]` needs.
  **How** membership is expressed in the representation is an *implementation detail*
  of `Map`'s instance, **not** a type-level keyed marker — the nominal kind is the
  marker.
- **Order.** Sequentiality is deduced from loop-carried dependencies and ordering
  is supplied as an `Ord` given, never fabricated. A positional domain (`UIntRange`, `Txn`,
  an induction domain) is totally ordered by construction, so `Array` and `List` are
  ordered; a keyed or opaque domain carries no order and an order-dependent operation over
  one needs an `Ord[𝐾]` instance rather than a fabricated one.
- **Views (`keys` / `values` / `items`).** `Map`'s projection operations, each a
  **lazy view** — no copy: `keys(m) : Collection(𝐾)` (the key set), `values(m) :
  Collection(𝑉)` (the map's own arrow), `items(m) : Collection((𝐾, 𝑉))`
  (`𝑘 ↦ (𝑘, 𝑚(𝑘))`). Turning a `Map` into a `Collection(𝑉)` is a **re-pairing**
  (project the key set, re-introduce over domain `{𝑘 | 𝑘 ∈ keys}`) — runtime-free,
  since `m` already carries its keys as its domain. `values(m)` is nonetheless the form to
  write, because `for x in m` binds entries while `for x in (m : Collection(𝑉))`
  binds values, and the explicit projection is what makes which one is meant
  visible — matching [chl-spec §6.3](../../../docs/chl-spec.md#63-direction-collection-types-decided).
  What *enforces* that is the **iteration element**, not a withheld subtyping edge:
  the implicit `Map <: Collection(𝑉)` edge holds (⊤ absorbs every kind), and
  `sum(m)` is rejected once `sum` lowers through iteration, because a `Map` yields
  `(𝐾, 𝑉)` entries and entries cannot be summed. Until then `sum(m)` means
  `sum(values(m))`, and the per-kind iteration element is what changes that.

## Realizing a conditional collection

**Realization** replaces a conditional collection's Σ with a term the runtime can drive. A
`Case` typed `Σ 𝐷 ∈ {𝐷ᵢ}. 𝐷 ⤇ 𝑉` becomes the gated union `⧺ᵢ (armᵢ | π̂ᵢ)` over the same
domains, each leg gated by the path condition its `if`/`elif` compiled to. The gates are
exclusive and exhaustive, so exactly one leg is non-empty and the union's extent is the
domain the witness selected — which is what makes the union and the Σ the same collection.
It runs in planning (`planning/conditionals.rs`) and asserts its pre-realization type
rather than relating the two by a typing rule ([type-inference.md, Realization asserts
rather than rewrites](type-inference.md#realization-asserts-rather-than-rewrites)).

**This is the only Σ the compiler can remove**, and therefore the only one that compiles.
Nothing reads a witness off a value at runtime, so a Σ that reaches op-conversion with no
concrete domain has no extent and is reported as a compiler bug. A conditional collection
escapes that because its candidates are statically enumerable and the gates pick one; every
other Σ — a `Collection(𝑇)` whose producer is not statically known, a collection in a `Mut`
register or crossing a source boundary — waits on a runtime witness that does not exist yet.

**One realization per site, at the node whose type carries the choice**: the outermost `Σ`
binding the witness. Arms sharing a domain form no Σ at all, and substituting the arm for
the conditional at the site leaves the arm.

### A restricting consumer's filter moves into the legs

A consumer that filters the collection leaves the filter on the witness —
`Σ 𝜎 ∈ 𝐾. ({𝜎 | 𝑝} ⤇ 𝑉)` — and the consumer can do nothing with it, having no extent for a
witness. Realization can: inside leg 𝑖 the collection *is* `armᵢ`, so the leg is gated
twice, by its path condition `π̂ᵢ` and by `𝑝` rewritten to read that arm.

The rewrite is what makes the filter expressible. A predicate may name a plain arm, but it
may not name the gated union: reading the union needs the `iterate`/`restrict` markers that
a predicate is forbidden to contain. Rewriting `𝑝` against `armᵢ` puts it somewhere a
predicate is allowed to be.

**So a restricted conditional is copied to each consumer that restricts it.** The legs carry
one consumer's demand, so a `let`-bound conditional filtered by two consumers needs two sets
of legs. Planning copies the conditional into each restricting consumer and drops the
binding, which also puts the `Case` back below the site that restricts it — a binding
precedes its body in scope, so no traversal order reaches the demand first. An unrestricted
conditional owes nothing and stays shared. The price is one union per restricting consumer;
a runtime witness would let one materialized union serve several.

### A site's witnesses are realized together

Two conditional generators in one comprehension put two sums over one product domain —
`Σ 𝜎₄ ∈ 𝐾₄. Σ 𝜎₇ ∈ 𝐾₇. ((𝜎₄, 𝜎₇) ⤇ 𝑉)` — and that is one site with two choices on it, not
a site within a site. So the legs are the **tuples** of arms, gated by the conjunction of
their path conditions and indexed by the product of their domains: the same finite-Σ ≡
gated-union isomorphism, stated for a product of witnesses. It is flat, which is what
`Expr::collection_union` already is.

Realizing the two one at a time instead nests the unions, and the nesting is wrong in the
term rather than only in the type: a leg's gate rides as a refinement on its domain, and the
term-level `restrict` is emitted only where that domain heads an iteration. The inner union
is not an iteration site, so wrapping it drops the outer gate — two legs are live where
exactly one may be, and the answer double-counts.

A site therefore **names** its witness rather than being it: beside a second generator the
index is a product, so the filter rides `{(𝜎, 𝐷) | 𝑝}` and every rule keyed on the witness
matches a *mention* of it rather than the whole domain. Reading the whole domain makes the
product a silently different case, which emits the site's chain a second time over a witness
that has no extent.
