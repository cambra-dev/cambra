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
> A section tagged `[Decided]` records a choice among alternatives, so its
> mechanism is built and the section says why this one and not the others.

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

`Set(𝐾)` and `Map(𝐾, unit)` are related by no arm, being one type today. Under the nominal
direction that relation becomes a declaration, and it is the only edge nominality turns
into a decision — widening to `Collection(𝑉)` still holds for both, because widening
forgets the head.

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
> makes that difference readable from the type; a `Keyed(𝐾)` domain paired with a `unit`
> codomain cannot say it.
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
- **`Map(𝐾, 𝑉)`** = `Σ (𝐷: Keyed(𝐾)). 𝐷 ⤇ 𝑉` — a key domain; a *concrete* one's keys are
  typed `{𝑘: 𝐾 | 𝑘 ▷ (𝑚 ▷ collection_contains)}`. Unordered. Lookup `𝑚[𝑘] : Option(𝑉)` in
  general, `: 𝑉` when presence discharges (see
  [Lookup](#lookup-membership-discharge)). Membership `𝑘 in 𝑚`.
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

## `FullMap` is the unboxed map

`FullMap(𝐾, 𝑉)` is the dependent data function `(𝑘: 𝐾) ⤇ 𝑉`, not a sum. Its key set is
`𝐾`, readable from the type, so a lookup needs no proof of presence and answers `𝑉`
([chl-spec, Direction: collection types](../../../docs/chl-spec.md#63-direction-collection-types-decided)).
`Map(𝐾, 𝑉)` is what remains after forgetting which key set: a Σ over `Keyed(𝐾)`, whose
witness stands where the key set was. Crossing from a `FullMap` to a `Map` is therefore
`box`, and that `box` is where the key type stops being available to reason with.

This is the type `groupby` returns. Its domain is the present-key domain
`{𝐾 | 𝑘 ▷ ((c ≫ key) ▷ collection_contains)}` and its codomain names the key binder, which
is `(𝑘: 𝐾) ⤇ 𝑉[𝑘]`. So the constructor is not a new shape; `Type::full_map_of` names a
shape the checker already builds, and `Map(𝐾, 𝑉)` cannot describe it at any spelling —
entry is `box`, and `𝑉` is one type with no binder for the dependent group to name.

**Totality is claimed, not checked.** A `FullMap(Int, 𝑉)` asserts a value for every `Int`,
and nothing verifies that against whatever built the map. What that obligation should be is
open in the spec — a literal must cover the domain, and a domain that grows must extend the
map. Until it is settled, an annotation is a promise the checker propagates.

### Annotating a group-by waits on `keys`

A `groupby` satisfies `FullMap(_, _)` and no narrower annotation, because a data
function's domain is invariant: `FullMap(Int, _)` demands the bare key type where the
collection carries the present-key refinement. Writing that refinement means naming the key
morphism's image at the surface, which is `keys` — a `[Planned]` operation
([Operations](#operations-how-the-trait-layer-is-realized-planned)). The elided form is not
a workaround for a missing rule; it states that the checker knows the key set and the
surface cannot spell it. `FullMap({𝐾 | 𝑝}, 𝑉)` is writable whenever the key type is refined
against something other than the map itself, which is how the north-star `storefront`
declares `inventory` over its catalog's keys.

### The total lookup waits on refinement introduction

A lookup on a `FullMap` needs no presence proof, and no program reaches that rule yet.
Nothing type-theoretic stands in the way: the argument edge already relates refinements in
the dropping direction, and what a proven lookup needs is the other one — a key produced by
the key morphism from an element of the source *acquires*
`{𝐾 | 𝑘 ▷ ((c ≫ key) ▷ collection_contains)}`, since that predicate says which keys the
morphism produces. `g[x]` for `x` in the source, `g[key(x)]`, and `g[r.a]` are one situation
and are rejected alike, pinned by `a_key_from_the_source_does_not_yet_carry_its_key_domain`.
The rule is the direct route in
[Prerequisite: the proof has to survive being consumed](#prerequisite-the-proof-has-to-survive-being-consumed).

A range domain reaches the same wall by a different road: `Array(𝑛, 𝑇)` is already a
`FullMap` over `[0, 𝑛)`, and `arr[𝑖]` fails because `UIntRange` is a primitive relating only
by equality rather than an index type carrying a bound
([Lookup: membership discharge](#lookup-membership-discharge)).

So the annotation works and neither lookup does. With the key elided a `FullMap` is
satisfied by a producer's own domain, as a binding and as a parameter
(`full_map_annotations_are_satisfiable`). Writing an unrefined base type instead claims a
value for every element of it, which nothing constructs — that is a property of the key
type, not of the form.

### No nominal head yet

Nothing distinguishes a `FullMap` from any other dependent data function, so every data
function satisfies a `FullMap` annotation. Under the nominal direction only a declared one
would ([The kind is declared](#the-kind-is-declared-not-read-off-the-shape)), so today's
annotation is wider than its successor. Two constraints keep that direction open: `FullMap`
is not the way to spell "any data function", and no rule may recover FullMap-ness from the
arrow's shape. The name exists so a head has one place to attach.

## Representation: the key domain is the key morphism's image [Decided]

Because operations dispatch on the kind rather than on the arrow, the *representation* of
a keyed collection's key set is a free internal choice — unobservable at the type level,
carrying no semantic weight of its own. Of the candidates considered, the
**characteristic-predicate** form won: `Map(𝐾,𝑉) = Σ (𝐷: Keyed(𝐾)). 𝐷 ⤇ 𝑉`, where a
concrete `𝐷` is `{𝑘 | 𝑘 ▷ (𝑚 ▷ collection_contains)}` — the keys the key morphism `𝑚`
produces.

**The predicate is transparent, and that is what makes membership provable.** An *opaque*
per-site token has no introduction form: nothing can produce a value at the domain it
names except a term already stamped there, so `𝑚[𝑘] : 𝑉` is unprovable by construction
rather than for want of a rule. Refinement subtyping compounds this — refinements relate
by structural predicate equality, never implication — so there is no entailment step for a
proof to land in. Naming the morphism supplies the introduction rule that was missing: a
key produced by `𝑚` is a key of the collection `𝑚` keys.

The asymmetry this removes is the one the older design left standing. `groupby`'s codomain
already names both terms — `{𝑖: 𝐼 | key(c(𝑖)) == 𝑘}` — and works, so "a producer in a
type" was never the cost being avoided; only the *domain* refused to say what the codomain
said. What a term in the type does cost is that type identity compares terms, and the
substitution that keeps them current is the ordinary type walk (`Subst::rewrite_type`),
which reaches a predicate wherever it rides.

`keys(m)` is the data function's domain projection either way — the key set is its carried
domain, and enumerability comes from the `⤇`, not the witness.

### Why a refinement, and not an atom or a token

A concrete keyed domain is `{𝐾 | __elem ▷ ((c ≫ key) ▷ collection_contains)}`, and the
representation was traced rather than guessed.

- A nominal domain **atom** cannot work: [`AtomKey`] is a *discrete* set — only reflexive
  arms exist for the nominal leaves, atoms merge by set union, and coalesce rejects ≥ 2
  shapes at a position. A nominal `KeyDom(id, Int) <: Int` edge would need polarity-aware
  atom subsumption that does not exist, and it would break at the first `k + 1`.
- A **refinement** works for free: `Type::Refinement(inner, r)` compacts by recursing into
  `inner`, so the base's atom lands in `atoms` while `r` rides a separate width-subtyped
  list (positive intersects, negative unions). So `{𝐾 | __elem ▷ (𝑚 ▷ collection_contains)}`
  and `𝐾` both contribute the base atom — no collision — and join to `𝐾`. The predicate
  sits in the **function** position of the ordinary `__elem ▷ p` shape, so
  `fn_of_bare_predicate` fast-paths it and predicate compilation round-trips with no
  special case.
- An **opaque per-site token** is cheaper — identity is an integer comparison, and no term
  rides in the type — but it has no introduction form, so proven lookup is unprovable by
  construction rather than for want of a rule.

[`Type::SharedHole`] equates the refinement's base with the **morphism's** codomain: the
scheme relates those two positions but does not equate them ([The key type is pinned, not
bounded](#the-key-type-is-pinned-not-bounded)), and the annotation carrying the hole is the
one the chain needs for its kind anyway. `debug_assert_no_unexecutable_atoms` names the
invariant that keeps the predicate type-level: a key-domain atom never reaches
op-conversion as a term.

## Key-domain identity is the key morphism (load-bearing)

**Two keyed collections have the same key domain exactly when they name the same key
morphism.** That is the property which keeps a join of two distinct maps *escapable*: two maps `𝑚₁, 𝑚₂ : Map(𝐾, 𝑉)` built from different sources have the same
*surface type* but **distinct key domains** `𝐷ₘ₁ ≠ 𝐷ₘ₂`, so a join `𝑚₁ if 𝑐 else 𝑚₂` is
representable as `Σ (𝐷 ∈ {𝐷ₘ₁, 𝐷ₘ₂}). 𝐷 ⤇ 𝑉` and a membership proof against `𝐷ₘ₁` is
never confusable with one against `𝐷ₘ₂`.

The failure mode this rules out is a *shared, anonymous* key domain — one leaf for all
maps. Under that, two maps are indistinguishable types, a join silently picks one domain
and drops the other's rows, and a lookup proof from one map wrongly discharges against
another. That is unrecoverable: identity cannot be retrofitted onto values already
conflated, which is why it has to be decided before anything discharges a key rather than
as a later refinement.

Two corners follow from this and stay open. A **join of two distinct maps** —
`𝑚₁ if 𝑐 else 𝑚₂` — has each map's membership predicate closing over its own value, so two
discharge substitutions meet at one coalescing variable and `bridge_holder_gap` hits its
panic tripwire; `box` is most of the answer, since the two then carry distinct witnesses and
the candidates stay separate, and what remains is consuming one. And a **dependent
collection under an exact annotation** reports a compiler bug: `groupby`'s value type names
the key binder, `Map(𝐾, 𝑉)` has one `𝑉` with no binder to name, so
`g: Map(Int, _) = groupby(…)` fills `𝑉` from the initializer and captures `__gb_k`. The
bounded form `g <: Map(Int, _)` leaves `g` its own type and is unaffected; what is missing
is the diagnosis, not a rule.

Identity is therefore **structural, not per-site**: re-keying one source by one key
function twice yields one key domain, and a proof drawn from either discharges against the
other. A per-creation-site token separates those two as well, conflating "distinct
collections" with "distinct expressions" — every membership fact becomes local to the
expression that produced it. The runtime needs no identity, distinct maps being distinct
hash stores, so this is a compile-time-only obligation.

**What `Keyed` adds to the kind system: a parameter.** `Enumerated` *lists* its
candidates and `UIntRanges` *describes* its, so containment against either is a
decidable question about one kind. `Keyed(𝐾)` carries a **type parameter**, and
relating two types is subtyping's job — so containment does not decide it, it emits
the pair as an obligation the width arm discharges invariantly through the solver.
Emitting rather than testing is also what lets an open key type be *pinned* by the
kind it meets, which is what makes `Map(_, 𝑉)` inferable.

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

## Consuming a keyed collection: discharge, not point-free compose

A `groupby`'s per-key group `{𝑖 | key(𝑖) == 𝑘} ⤇ 𝑉` is a **dependent** codomain: its
domain refinement names the key binder `𝑘`. Anything that consumes it — a rollup over
the groups, a group collapse, `(key, value)` entry-iteration — must not let `𝑘` escape
into the consumer, which is bound outside `𝑘`'s scope.

There are two ways to stop a bound variable escaping its scope: **discharge** it
(substitute an in-scope value — a dependent application,
[§4.5](type-inference.md#45-dependent-refinements-via-pi-types)) or **abstract** it
(pack it under an existential witness). Cambra discharges, and can always do so
because it controls every composition it emits — there is no surface compose
operator, so a point-free `producer ≫ consumer` is only ever a lowering choice. When
the producer is a keyed collection, the choice is the **η-expanded** form
`producer ≫ consumer  ⤳  λ 𝑥 → consumer(producer(𝑥))`. Here `producer(𝑥)` is a
dependent application: it substitutes `𝑥` for the key binder, so the group is
`{𝑖 | key(𝑖) == 𝑥} ⤇ 𝑉` with `𝑥` bound by the fresh `λ 𝑥`, in scope for the consumer.
A comprehension (`[… for key -> g in …]`) is already in this form. A **bare**
point-free `keyed ≫ collapse` is never emitted: its consumer's parameter would
resolve to `{𝑖 | key(𝑖) == 𝑘} ⤇ 𝑉` with `𝑘` free — the scope escape inference rejects.

This is discharge, not a sealed existential: no `Σ`-witness is introduced for the
group and no later pass erases one. The η-expanded shape stays well-typed through the
**whole** pipeline — inference (the application binds `𝑥`); lambda elimination (the
`groupby` eliminates to a *dependent* `const(cast) ≫ collapse`, whose key binder
rides the compose's own Pi arrow — the dependent-morphism handling in `emit_compose` /
`coalesce_node` keeps it there and matches it structurally); and planning
(restructured to the per-key `converse ≫ map ≫ collapse`). At no stage is the group a
point-free chain input carrying a free binder. A `debug_assert` in `coalesce_node`'s
`Compose` arm enforces the invariant: no `Compose` morphism's codomain may reference
that morphism's own Pi binder.

The `Collection` Σ witness (the domain) still matters for *other* questions — e.g.
rejecting an unsound `Σ <: Fun` consumption, which is what presenting the sum itself
as the consumed domain is for — but consuming a `groupby` group is not one of them:
discharge resolves it with no witness at all.

## Lookup: membership discharge

> **[Planned]** — no lookup path exists today. `c[k]` lowers as the lookup `c(k)`
> (`lower_subscript`), but no rule discharges the index's membership, so it is a type
> error at the `Apply` for every index. The surface operators — proven `c[k] : 𝑇`
> and checked `c[k]? : Option(𝑇)` — are specified in
> [chl-spec §3.9](../../../docs/chl-spec.md#39-subscript-and-attribute-access). This section is the **discharge
> mechanic** they rest on: the single rule that decides which one type-checks.

Lookup is uniform across ranges and keys: `𝑐[𝑥]` is well-typed when `𝑥`'s type
proves `𝑥 ∈ dom(𝑐)`, and its result totality is *whether that proof
discharges*.

- Membership rides on the **element's** type, not the collection's. Iterating a
  collection's own domain hands you the proof:

  ```
  m : {k: K | k ▷ (m ▷ collection_contains)} ⤇ V
  for (k, v) in m:          # k : {k: K | k ▷ (m ▷ collection_contains)}
      m[k]                  # : V        — membership discharges → TOTAL
  ```

- A key from outside carries no proof, so the **proven** operator `m[k]` is a
  type error; the **checked** operator `m[k]?` returns an option:

  ```
  m[req.body.sku]           # type error — membership cannot discharge; use m[…]?
  m[req.body.sku]?          # : Option(V) — the checked operator
  ```

The range case is the same rule: `arr[𝑖]` is `: 𝑇` when `{𝑖 | 𝑖 < 𝑛}` discharges (an
`Array` index, a comprehension index), and `lst[𝑖]?` is `: Option(𝑇)` where the bound
cannot be discharged (a `List` of unknown length, where bare `lst[𝑖]` is a type error).
So one discharge mechanic covers all four kinds rather than one per kind.

`Option` is the tagged variant `some(𝑣) | none`, matched with `match`, over the existing
`Variant` / `VariantProject` / `VariantWrap` CCL nodes. The surface `match` / `some` /
`none` are shared with `txn_kv` and are not collection-specific.

### Prerequisite: the proof has to survive being consumed

Two routes produce a key carrying a collection's key domain, and they need different
things.

**Applying the key morphism** is direct: `𝑖 : 𝐼` gives `(c ≫ key)(𝑖)` a key of the
collection `c ≫ key` keys, because that is what the domain
`{𝑘 | 𝑘 ▷ ((c ≫ key) ▷ collection_contains)}` says. This is the rule that makes the
motivating program — `for o in orders: g[key(o)]` — provable, and it needs no change to
consumption. It is what naming the morphism bought: an opaque domain has no such rule, and
none could be added, since nothing relates a key to a predicate that says only "the keys
of this collection".

**Iterating the collection itself** is the harder one, and the rule above is stated
against it: the **sealed** keyed collection, where the key's type literally reads
`{𝑘: 𝐾 | 𝑘 ▷ (𝑚 ▷ collection_contains)}`. That is not the form a consumer sees. Consuming
a sum deliberately **does not** present the refined domain: it presents the sum `σ` itself,
precisely so the witness binder cannot escape into the consumer's result (a `map`'s result
domain must not mention a binder with no enclosing Σ — see the `Σ <: Fun` arm in
`constrain.rs`). So after opening, an iterated key is a consumed sum's witness, not a
membership-refined `𝐾`, so the membership has nothing to discharge *against*.

This is a real gap, not a detail of the surface syntax, and it is what the second route
has to settle. The apparatus for it is already there: the presented domain
*is* the whole consumed Σ, so it is identity-bearing — `𝑘 : σ` together with `𝑚 : σ` is
exactly the pairing a discharge needs (*this* key came from *that* map). Two shapes
are then possible and the choice is open: teach the discharge to relate a key typed at
the named `σ` to `σ`'s own membership refinement, or have the consuming rule present a domain
that keeps the refinement *and* binds the witness once for both the key and the
collection (a proper consumption binding both components rather than naming
per-use). Either way it lands before, not with, the `[]` / `[]?` surface.

## `groupby` is a `Map`

For `c: 𝐼 ⤇ 𝐴` and `key: 𝐴 → 𝐾`, the **exact type** of a group-by is a keyed
collection from present keys to their groups:

```
groupby(c, key) : (𝑘: {𝐾 | 𝑘 ▷ ((c ≫ key) ▷ collection_contains)}) ⤇ ({𝑖: 𝐼 | key(c(𝑖)) == 𝑘} ⤇ 𝐴)
                ≡ "a dependent Map(𝐾, group(𝑘))"
```

— the outer domain is *this* group-by's present-key domain, the keys its key morphism
`c ≫ key` produces (so it injects into `Map(𝐾, _)` by kind containment, and is not
confusable with any other collection's keys); the codomain is the group, the
sub-collection of `c` whose key is `𝑘`. The codomain **depends on `𝑘`**, so this is a
*dependent* keyed collection — a generalization of the non-dependent surface `Map(𝐾, 𝑉)`.

**Precise inferred type, non-dependent surface, bridged by the entry term.** The surface
`Map(𝐾, 𝑉)` stays non-dependent (fixed `𝑉`). `groupby`'s precise dependent type is only
ever *inferred*, never annotated, and **injects into** `Map(𝐾, Collection(𝐴))` on
annotation or uniform consumption — each dependent group `{𝑖 | key==𝑘} ⤇ 𝐴` injects into
`Collection(𝐴)` (any data function does). So precision flows where it is produced
(groupby → its immediate consumer) and abstracts at the surface, the two coexisting
through the existing entry term — no dependent `Map` constructor is forced on every map.
The one bill this defers is **dependent lookup** (`m[𝑘] : 𝑉(𝑘)`), which comes due only
when lookup is built.

**This is a fix, not new behavior.** The previous inferred type for
`groupby([1, 2, 3], \x -> x // 2)` was

```
(__gb_k: Int) ⤇ ({[0, 2] | __elem ▷ [1, 2, 3] ▷ (λ x : Int → x // 2) == __gb_k} ⤇ Int)
```

— a **`Data`** arrow, correctly, but over **all of `Int`** rather than over the present
keys. Lowering stamps the kind by provenance (`lower::exprs`, the `data_fun` annotation),
so the kind was right and the domain was the defect: a data function's domain is its data,
so that type claims one row per inhabitant of `Int`. The claim propagated — the rollup
`[sum(v) for v in g]` inferred `Int ⤇ Int`, a collection over every integer — and it
compiled only because planning recovers the real extent from the group-by's source instead
of from the type. `g(99)` at an absent key type-checked and evaluated to the empty group,
the same imprecision seen from the term side.

The dependent codomain `{𝑖 | key==𝑘} ⤇ 𝐴` is already present and handled by the
[dependent-application machinery](type-inference.md#5-ccl-specific-inference-rules). The
fix retains it and changes only the outer **domain**, from all of `𝐾` to this group-by's
own present-key domain, which makes the type a keyed Σ — a `Map`. Absent-key lookup then
goes through `g[𝑘]?` ([Lookup](#lookup-membership-discharge)) rather than through a total
function, so the empty group is an `Option` the program handles rather than a row the type
never had.

### Lowering realization: the key binder states its domain

Lowering builds the keyed Σ, and the term it builds is well-formed at every compilation
stage — no free variables, valid before and after inference. Two things say what `groupby`
is.

**The binder's domain is the present-key domain**
([Representation](#representation-the-key-domain-is-the-key-morphisms-image-decided)):
`__gb_k` is
declared at `{𝐾 | __elem ▷ ((c ≫ key) ▷ collection_contains)}` (`present_key_domain` in
`lower/exprs.rs`).

**The kind is provenance.** A `data_fun(_, _)` annotation on the lambda makes `emit_node`
stamp `Data` onto the arrow `emit_lambda` builds — an arrow that already carries the
binder and this domain. No term crosses `⇒` to `⤇`, and nothing derives the kind from the
key domain, which is scalar.

So lowering emits, with the inner group a cast as before:

```
groupby(c, key)  ⟶  λ (__gb_k : {𝐾 | __elem ▷ ((c ≫ key) ▷ collection_contains)}) → cast(λ __gb_i → __gb_i ▷ c, {𝐼 | key(c(__elem)) == __gb_k} ⤇ 𝐴)
```

which enters `Map(𝐾, …)` by Σ-width once `box` has made it a one-candidate sum.

**`Converse` discharges the present-key domain.** Planning recognizes the pointful site
and rebuilds it as `converse ≫ map` (`convert_groupby_pointful`). The two halves are typed
at different domains, and that split is what lets the rebuilt term's type say what the
term does: the key-extraction morphism `c ≫ key` yields plain keys, so it is typed at the
bare `𝐾`, while the partition `Converse` builds holds exactly the keys that occur, so it
is stamped at the present-key domain. One key type serving both roles either rejects the
extraction or understates the partition.

The predicate rides through to op-conversion on **types**, never as a term, and its
morphism stays pointful: point-free compilation applies to the predicates planning reifies
into a `Restrict`, and this one it never reaches. `insert_iterate_markers` skips a
key-domain layer when it reifies a domain refinement into one, and
`debug_assert_no_unexecutable_atoms` asserts at the planning→op-conversion boundary that
no `collection_contains` reached the term spine.

**Invariant — no iteration markers inside predicates.** A predicate that reads a
collection at the element (`__elem ▷ src ▷ 𝑓`, what a filter lowers to) holds a term that
also lives in the term tree, where planning wraps it in `iterate` markers; a move-site
discharge of a `let`-bound source into the predicate would otherwise drag those markers
into the type, where they make `simplify` churn (nested-`Compose` vs `flatten_compose`)
and diverge from inference's pre-marker copy. So the term→type substitution boundary
strips the neutral `iterate` marker (`ccl_utils::strip_iterate_markers`), keeping
predicates marker-free; a `restrict` marker (a filtered source in a membership predicate —
a future `𝑥 in filtered_coll`) is *not* stripped and is caught loudly by a debug assert
rather than silently mis-compiled. This is a general `Subst`/`simplify` invariant,
exercised by any predicate carrying a collection, not a group-by special-case.

Everything else follows: the `storefront` `/stats` rollup

```
[key -> sum([o.price for o in g]) for key -> g in groupby(paid, \o -> o.sku)]
```

is "iterate a map's `(key, value)` entries, build a new map". Under the
[Interim](#iterating-a-setmap-binds-the-codomain-not-the-keys-interim) iteration binds the
**codomain** for every kind, so `for v in m` gives `v: 𝑉` exactly as iterating `groupby`'s
result binds each group, and the key is not handed over. Recovering the key alongside the
value — the `key -> g` entry binding the `/stats` rollup needs — is the
[`items` view](#operations-how-the-trait-layer-is-realized-planned), which reads a data
function `𝐴 ⤇ 𝐵` as `𝐴 ⤇ (𝐴 ⤇ 𝐵)`: each key mapped to its singleton entry, so iterating
that yields entries from which both key and value project. `items` is **deferred**; value
iteration is the near-term consumption path.

#### The key type is pinned, not bounded

[`Builtin::CollectionContains`]'s scheme `∀ι κ. (ι ⤇ κ) ⇒ (κ ⇒ Bool)` shares `κ` between
the morphism's codomain and the predicate's domain, and that relation is not enough on its
own. `__elem` binds at the refinement's base and is **applied** to the characteristic
predicate, so the application contributes `base <: κ` — a lower bound. A key type
contradicting the morphism's then joins with it rather than conflicting, and
`g <: Map(String, _)` over `Int` keys is accepted, with the disagreement surfacing only in
the post-emission narrowing audit (`verify_narrowing_is_complete`). One
[`Type::SharedHole`] states the equality the application cannot
(`keyed_entry_checks_the_annotated_key_type` pins the elided-value spelling, the one that
reaches this obligation rather than failing on the value edge first).

### A type-embedded predicate is typed where its binder is emitted

A predicate embedded in a *parameter* annotation is typed by `emit_lambda`, in the
**enclosing** scope — before the parameter binds, because the predicate's terms may
reference outer bindings. `groupby`'s key binder is the case that needs it: its domain
names the collection and key function, neither of which lowering holds a type for. It
holds only the [`Type::SharedHole`] equating the key type across the two positions that
must agree. Only *node* annotations re-infer an embedded predicate
(`emit_annotation_predicates`), so a `Hole`-typed predicate would strand unresolved
`Infer`s at the [post-inference check](type-inference.md#the-post-inference-check-shared-rules).
An annotation on a `Map`/`Set` carries no predicate at all, the domain's obligation being
the witness kind, so nothing is embedded there to resolve.

### A collection-consuming UDF inlines because it is a capability

`λ c → sum(c)` is `FunKind::Compute`, so it beta-reduces at each concrete call site,
monomorphizing the abstract `Σ`/`Collection` parameter to the argument's concrete
domain — the resolution op-conversion needs. The inline decision is therefore the
function's *kind* (`inline::should_inline`) and not the shape of its domain: a `groupby`
is a `Data` arrow, which a shape test reads as a non-iterable domain and goes on inlining.

## Keyed entry needs the key domain written down at lowering

An entry term runs a *membership predicate* on the entering side — is this domain a range,
is it a membership refinement? — so it decides at constraint-emission time only for a
domain that is already concrete, and otherwise becomes a kinding constraint on the domain
variable. Whether a producer satisfies that is **not** a property of the collection kind;
it is a property of whether lowering wrote the domain down:

```
x <: List(Int)   = box([y+1 for y in [1, 2, 3]])  # ✅ range domain ?N at emit; resolved at coalesce
m <: Map(Int, _) = box(groupby(xs, key))          # ✅ key domain written onto `__gb_k` by lowering
```

The `box` is the entry itself and the bound is what leaves `m` its own type, so neither
carries the domain question these lines are about. What the elided `_` avoids is a second,
unrelated rejection: a group is a bare data function, and naming `Collection(𝑉)` there asks
it to enter another sum. A `FullMap` is absent from this list because it is not a sum and
has no entry to check ([`FullMap` is the unboxed map](#fullmap-is-the-unboxed-map)).

So the rule for every re-keying producer is: **stamp your own key binder with the
present-key domain** `{𝐾 | __elem ▷ (𝑚 ▷ collection_contains)}`
([Representation](#representation-the-key-domain-is-the-key-morphisms-image-decided)).
Get it wrong and the failure is a confusing `AnnotationMismatch` on the Σ witness rather
than anything naming the real cause, because the gate had nothing concrete to test.

**Why not a deferred obligation, as `List` uses?** The `List` arm genuinely needs one: a
comprehension's *range* domain is the domain coalesce independently resolves it to, and
constraining it at emit collides with that resolution (see
[What `box` checks against a collection type, and
solver](type-inference.md#what-the-kind-level-needs-from-the-solver)).
A re-keying producer is different — it *knows its own key-image syntactically*, so there
is nothing to wait for. A kinding constraint already carries *which* kind to check, so the
keyed case needs no extension of the mechanism, only the keyed kind itself; it comes due
for a producer whose key domain is genuinely unknowable until coalesce — a map
comprehension, a keyed feed. No producer that exists today is in that position.

## Iterating a `Set`/`Map` binds the codomain, not the keys [Interim]

`for g in groupby(xs, key)` binds `g` to the collection's **codomain** — each group, not
each key. The *semantic* decision is made — the `Iterable` element is kind-directed
(`Set` → key, `Map` → `(𝐾, 𝑉)` entry, `Collection`/`List` → value;
[chl-spec §4.6](../../../docs/chl-spec.md#46-for--iteration)) — and its realization is
[Operations](#operations-how-the-trait-layer-is-realized-planned).

What blocks it is narrower than "the operation layer is unbuilt": the element choice needs
to distinguish `Set` from `Map`, and those are currently the *same type*, so there is
nothing to dispatch on. This section is therefore the record of two things at once — the
**[Interim]** codomain-only binding, and the fact that lifting it depends on the
[kind-representation question](#the-kind-is-declared-not-read-off-the-shape), not merely
on writing the trait instances.

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
