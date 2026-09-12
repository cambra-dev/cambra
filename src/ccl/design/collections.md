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
[type-inference.md, Subtyping for sums](type-inference.md#subtyping-for-sums). Throughout,
**kind** means that `TypeKind` and never the collection type itself; a witness is a binder,
and the kind classifies the types it ranges over rather than the binder.

`Set(𝐾)` and `Map(𝐾, 𝑉)` are the one pair the kind does not separate: they share the
`SubtypesOf(𝐾)` kind and its key parameter, differing only in a codomain that is `unit` for
one, so the operation layer has nothing to dispatch on between them.
[Telling `Set` and `Map` apart](#telling-set-and-map-apart-open) is the open part.

> **What is built.** Everything in this document is implemented unless it is tagged
> `[Planned]` (e.g. the operation layer). Where a `[Planned]` feature has an interim
> behavior in today's code, that is tagged `[Interim]`; a section whose operators are partly
> built is tagged `[Partly implemented]`.

## The six collection types

With `𝐷` a witness domain and `𝑛` a length. Each entry gives the type's semantics rather
than its status: which lookups type-check today is in
[Lookup: membership discharge](#lookup-membership-discharge), and `in` is [Planned] with the
rest of the [operation layer](#operations-how-the-trait-layer-dispatches-planned).

- **`Array(𝑛, 𝑇)`** = `[0, 𝑛) ⤇ 𝑇` — domain `UIntRange(n)`, length static.
  Ordered. Lookup `arr[𝑖] : 𝑇` is total, the index bound being static. This is the shape the
  compiler builds for a list literal today.
- **`List(𝑇)`** = `Σ (𝐷 : UIntRanges). 𝐷 ⤇ 𝑇` — some index range, which one not
  necessarily known statically. Ordered. The range is not static, so nothing proves an index
  present and the lookup is the checked `lst[𝑖]? : Option(𝑇)`. The length is the witness
  domain's size, so `len` is its first projection rather than a stored field.
- **`Set(𝐾)`** = `Σ (𝐷 : SubtypesOf(𝐾)). 𝐷 ⤇ unit` — a key domain with trivial codomain;
  the domain is the payload. Unordered. Membership `𝑒 in 𝑠` discharges `𝑒`'s
  presence in the domain.
- **`Map(𝐾, 𝑉)`** = `Σ (𝐷 : SubtypesOf(𝐾)). 𝐷 ⤇ 𝑉` — a key domain; a concrete one's keys are
  typed `{𝑘: 𝐾 | 𝑘 ▷ (𝑚 ▷ collection_contains)}`
  ([The key domain is the key morphism's image](#the-key-domain-is-the-key-morphisms-image)).
  Unordered. Lookup `𝑚[𝑘] : 𝑉` where the key's type proves it present, `𝑚[𝑘]? : Option(𝑉)`
  where nothing does. Membership `𝑘 in 𝑚`.
- **`FullMap(𝐾, 𝑉)`** = `(𝑘: 𝐾) ⤇ 𝑉` — a value for **every** key of `𝐾`, so the key set is
  readable from the type and `𝑚[𝑘] : 𝑉` needs no proof. Unordered. `𝑉` may depend on `𝑘`,
  which is why `groupby` returns one and no `Map` describes it
  ([`groupby`'s exact type](#groupbys-exact-type)). **Totality is claimed rather than checked
  where the key is elided [Interim]**: `FullMap(_, 𝑉)` asks only for a data function, so a list
  literal satisfies it (`full_map_annotations_are_satisfiable`). A *written* key is an ordinary
  obligation on an invariant domain, which is why `FullMap(Int, 𝑉)` is uninhabited — no producer
  has an unrefined `Int` domain (`full_map_lookup_needs_no_presence_proof`). What would let a
  group-by carry one is a surface spelling for the present-key domain, which is the same gap
  `keys(…)` names below.
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

## The empty literal names no element type

`[]` is typed `[0, 0) ⤇ 𝛼`, with `𝛼` left for whatever demands an element type: an annotation on
the binding it seeds (`xs: List(Int) = box([])`), an operator that reads an element, or a join
with a collection that names one.

With nothing demanding one, `𝛼` is pinned to `unit`. The empty literal denotes the function with
no positions, so no program reads a value out of it, and `unit` is what this type language has for
a value carrying no information — there is no uninhabited type
([chl-spec, 6.6 The empty product is unit](../../../docs/chl-spec.md#66-the-empty-product-is-unit)).
`pin_empty_list_element` makes the choice after the constraints are in, on the rule an unreachable
`Case` arm's payload takes
([type-inference.md, An unobservable arm payload is pinned to what its uses require](type-inference.md#an-unobservable-arm-payload-is-pinned-to-what-its-uses-require)).

Emptiness is the premise the pin rests on, not a stand-in for "no value reached the element type".
A non-empty literal whose elements are themselves undetermined — `\x -> [x, x]`, never called —
has a value-free element type too, and there the variable is a type parameter the program left
ambiguous; pinning it would accept a program that has no type.

### The empty collection has no key morphism

`map([])` and `set([])` are rejected. A re-keying reads its key domain off the key morphism's
image ([The key domain is the key morphism's image](#the-key-domain-is-the-key-morphisms-image)),
and with no elements there is no image, so nothing names the key.

The pin does not supply one either. The re-keyed literal is copied into the key domain's
refinement predicate, `Clone` leaves the copy its own inference variables, and a pin inside a
predicate would answer for the copy while the original stays free — so it declines there
(`CoalesceCtx`'s `in_predicate`). Both constructors reject an empty literal as an unresolved
inference variable.

`empty_map()` is the spelling that works, because it is not a re-keying. Its type is
`Σ (σ : SubtypesOf(𝐾)). σ ⤇ 𝑉` with both parameters open, stated by the term rather than derived
from entries it does not have, and a `Map(𝐾, 𝑉)` or `Set(𝐾)` annotation pins them:

```python
cart: Mut(Map(String, Int), Txn) := empty_map()
```

**It is a sum without `box`.** Every other collection enters one through `box`, whose candidate
position is invariant and so pins to the argument's own type
([type-inference.md, Only a term builds a sum](type-inference.md#only-a-term-builds-a-sum)). A
collection with no entries has no such type to offer — `box([])` against `Map(String, 𝑉)` collides
on the domain, the empty index range `[0, 0)` being a `UIntRanges` domain rather than a key one —
so the term names the sum itself and lets the annotation choose the witness.

**The annotation is the only source.** A keyed write states its obligation on the value it writes,
not on the collection's key type, so writes and reads leave both parameters open; an unannotated
`empty_map()` is an unresolved-variable error. `Set(𝐾)` needs no separate term, being `Map(𝐾, unit)`
([Telling `Set` and `Map` apart](#telling-set-and-map-apart-open)) — the annotation's codomain is
what distinguishes the two readings.

At runtime it is one empty tile whose domain and codomain columns are born at the annotated types,
built from the type because no entry exists to read them off.

## The collection type is declared, not read off the shape

Which side of `𝐷 ⤇ 𝑉` holds the payload is not fixed by the shape. `Set(𝐾)` iterates its
**keys** (the domain); `List(𝑇)` iterates its **values** (the codomain) — opposite sides
of the same function — and `Map(UInt, 𝑉)` and a filtered `List` can share a shape while one
must iterate entries and the other values. So which side is the payload is a fact about
the collection's *type*, and operations (`Iterable`, `Index`, `Membership`, `Ordering` —
[Operations](#operations-how-the-trait-layer-dispatches-planned)) dispatch on the declared
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
  [Views](#operations-how-the-trait-layer-dispatches-planned)).
- **The variance of `𝐾` and `𝑉` in `Map(𝐾, 𝑉)`.** A structural Σ reads variance off its
  body; a declared constructor states it once per parameter.

Nothing in [`Type`] carries a collection type constructor today, so none of this is an
implemented property.

**Until this is settled** a *name* binder binds the codomain for every collection type, so
`for g in groupby(xs, key)` binds each group rather than each key. The spec's choice is
kind-directed ([chl-spec §4.6](../../../docs/chl-spec.md#46-for--iteration)), so what blocks
it is the missing `Set`/`Map` distinction rather than the unbuilt operation layer: key and
entry iteration is exactly that distinction.

A **two-tuple binder** is the interim, and it is built — see
[Entry iteration `for k -> v in m` [Partly implemented]](#entry-iteration-for-k---v-in-m-partly-implemented)
below. It is the **uniform entry iteration** this section previously proposed — a `Set`'s
entry is `(𝐾, unit)` and the projection to `𝐾` is lossless, so `Map` gets correct entry
iteration without the distinction existing — with the one change that makes it cost nothing:
the binder's *arity* selects, not the collection's type. The proposal as written made every
keyed binder bind a pair, which changes what `for k in s` means and so needed a spec
decision; selecting on arity leaves every name binder reading exactly as it read before, and
only `for k -> v in m` asks for the entry.

## Entry iteration `for k -> v in m` [Partly implemented]

A two-tuple binder — `for k -> v in m`, or the parenthesised `for (k, v) in m` the pair
arrow is sugar for — takes the **entry**. It lowers (`src/ccl/lower/entries.rs`) to

```text
λ __iter_record → __iter_record ▷ (m ▷ map_domain) ▷ (λ k → let v = m[k] in body)
```

— the source is the collection's *keys*, and the value comes back through the proven lookup
that key's own domain discharges ([Lookup: membership discharge](#lookup-membership-discharge)).

**The source has to be the collection's keys, and that is the whole design.** Two shapes are
more obvious and both fail for one reason. Binding the key to the iteration position the
encoding already has — `λ i → let k = i in i ▷ m ▷ …` — and re-viewing the source as entry
pairs — `λ k → (k, k ▷ m)`, which lambda elimination turns into the fanout `⟨id, m⟩` — leave
a site that is not *iteration-bearing* (`src/ccl/planning/iterate.rs`), so planning sources
it from the site's domain **type**: a chain-head `iterate` over the domain's unrefined base,
plus one `restrict` per refinement. For a keyed collection that base is the bare key type,
which names no extent, and the refinement is a `collection_contains` membership term that is
carried and never executed. `map_domain` is in the iteration-internalising group, so a site
headed by one is sourced from the collection and planning adds nothing. [`Builtin::MapDomain`]
accordingly gained an [`OperatorSchemes`] entry — `∀δ ε. (δ ⤇ ε) ⇒ (δ ⤇ δ)`, the argument a
*consumer's* collection so a sum satisfies it — where before it was minted only by join
planning, which stamps its own type.

**What works today**: a `map(…)` or `set(…)` source, with a scalar key, read or unread, in
comprehension position — including inside a `with begin():` block over a collection the block
does not own. Pinned in `tests/compilation_pipeline/comprehensions.rs`. **Statement position**
(`for k -> v in m:`) lowers through the same binder and then meets the wall a *name* binder
meets there: a `for` with an accumulator is an induction loop, whose source must be indexed by
iteration position, and a keyed collection's positions are its keys.

**What does not, and why** — each pinned in the same file, and each blocked *upstream of the
binder*, which lowers identically in all of them:

- **A compound key** (`for (a, t) -> q in cart`). Projecting a key whose type is a
  present-key domain over a tuple leaves the component types undetermined. Not the binder:
  a hand-written `k.0` fails the same way.
- **An annotated `Map(𝐾, 𝑉)`**, i.e. a sum. The keys of a sum are the keys of whichever
  candidate the witness picked, so the key binder lands on the witness and collides with the
  `𝐾` the annotation names. This is consuming a sum at its witness, open with the sum rules.
- **A `groupby` result**, which the storefront rollup
  `[k -> agg(g) for k -> g in groupby(c, key)]` needs. A group's codomain depends on its key
  ([`groupby`'s exact type](#groupbys-exact-type)), and re-viewing at the keys carries that
  dependency out of its binder's scope.
- **A list literal.** `map_domain` compiles its argument with no upstream input, and a bare
  list literal is an iteration site planning only sources when something downstream asks.
  Entry iteration over a list is the index/value pair and is well-defined; what is missing is
  planning seeding a combinator's collection argument.
- **A second generator** beside an entry-iterating one: the two readings of the collection
  acquire different domain refinements, and a data domain is invariant.
- **A filter** (`for k -> v in m if …`). Not entry iteration at all — the same comprehension
  with a name binder fails identically, because the restrict chain planning builds for the
  filter also tries to compile the domain's carried `collection_contains`.
- **A transactional map's snapshot**, the shape every storefront/demo entry-iteration site
  takes. A `Mut(…)` never derefs to the collection inside it at a function position; the
  name-binder case fails on the same program. Reading a transactional collection as a
  collection is unbuilt; `src/ccl/design/mutability.md` is where that work lands.

## `groupby`'s exact type

For `c: 𝐼 ⤇ 𝐴` and `key: 𝐴 → 𝐾`:

```
groupby(c, key) : (𝑘: {𝐾 | 𝑘 ▷ ((c ≫ key) ▷ collection_contains)}) ⤇ ({𝑖: 𝐼 | key(c(𝑖)) == 𝑘} ⤇ 𝐴)
```

The outer domain is this group-by's present keys and no other collection's, and it is the
group-by's own keys rather than all of `𝐾` because a data function's domain is its data — a
domain of `𝐾` would claim one row per inhabitant. The codomain is the group, and it **depends
on `𝑘`**.

That dependency decides what the type is: a [`FullMap`](#the-six-collection-types), not a
`Map`, since a `Map(𝐾, 𝑉)` holds one `𝑉` with no binder for the group to name. No
annotation or consumer converts one into the other, so a group-by is consumed at the type
it has. A checked lookup answers at the key, the binder discharging to the key term
([The checked lookup `𝑐[𝑘]?`](#the-checked-lookup-𝑐𝑘)); what it cannot do is
materialize, a group being a collection.

### The key domain is the key morphism's image

A key domain is spelled as the image of a named morphism term:
`{𝐾 | __elem ▷ (𝑚 ▷ collection_contains)}` is the keys `𝑚` produces.
`present_key_domain` in `src/ccl/lower/exprs.rs` builds every one, so a domain of this shape
came from a re-keying producer.

**Naming the morphism is what makes membership provable.** A domain that said only "the keys
of this collection" would have no introduction rule: nothing could produce a value at it
except a term already stamped there, so `𝑚[𝑘] : 𝑉` would be unprovable by construction
rather than for want of a rule — and refinements relate by structural predicate equality
rather than implication, so there is no entailment step for a proof to land in instead.
Naming it supplies the rule: a key produced by `𝑚` is a key of the collection `𝑚` keys.

**That is the current answer, and implication is what retires it.** Reasoning about refinements
by implication rather than by structural equality is planned and unbuilt
([type-inference.md, Roadmap and Current Prototype
Status](type-inference.md#roadmap-and-current-prototype-status)). With it, an opaque named key
set — "the keys of this collection", carrying no producer — is dischargeable from an axiom, and
it wins on every count that decides between the two: it is smaller, it is independent of how the
producer is spelled, and it keeps a producer out of a type. So the transparent form is what the
absence of an entailment step forces, and the opaque form is its successor.

**A product keys a collection like any other type.** A key domain is the morphism's image
whatever the morphism produces, and the group predicate compares two keys — so what a key
type owes is equality, which a tuple or record satisfies componentwise
([type-inference.md, A product is answered off the table](type-inference.md#a-product-is-answered-off-the-table)).
The runtime holds a product key as one `Records` column and a computed one as a column per
field, and the lookup pivots the second into the first, so both sides of a search are one
value.

**Naming a term is also what fixes domain identity.** Refinements compare by structural
predicate equality, so two key domains are the same domain exactly when they name the same
morphism term. That is a fact about terms rather than about collections — a domain naming a
parameter is one type over every collection that parameter is bound to, and two spellings of
one collection (a `let`-bound source and its inlined literal) are two domains. Membership
therefore reads "in the image of the morphism named here", under whatever the morphism's free
variables are bound to where the fact is used.

Implication does not close that gap, because the obligation the two spellings need is the
definition `c = [1,1,2]` rather than an entailment between predicates over values. Relating them
is canonicalization work, and nothing does it today.

Two things follow from naming a term at all. A key domain embeds its whole producer, so the type
grows with the producer and shows up wherever the key type does. And a type's identity now rests
on a term's, which is the same identity-by-shape exposure the Σ rule's `𝜌` substitution has
([type-inference.md, What checks each
premise](type-inference.md#what-checks-each-premise)).

**Every re-keying producer stamps its own key binder, at lowering.** An entry term runs a
membership predicate on the entering side, so it decides at constraint-emission time only for
a domain that is already concrete, and otherwise becomes a
[kinding edge](type-inference.md#an-unresolved-candidate-becomes-a-kinding-edge) on the domain
variable. Whether a producer satisfies that is a fact about whether lowering wrote the domain
down rather than about the collection type. Get it wrong and the failure is an
`AnnotationMismatch` on the Σ witness rather than anything naming the cause, because the gate
had nothing concrete to test.

**`Converse` discharges the present-key domain.** Planning rebuilds the site as
`converse ≫ map`, and the two halves are typed at different domains: the key-extraction
morphism `c ≫ key` yields plain keys and is typed at the bare `𝐾`, while the partition
`Converse` builds holds exactly the keys that occur and is stamped at the present-key
domain. One key type serving both roles either rejects the extraction or understates the
partition.

The predicate rides to op-conversion on **types**, never as a term. Point-free compilation
applies to the predicates planning reifies into a `Restrict`, and this one it never
reaches — a membership evaluation would be a keyed lookup or an `x in s` filter, neither of
which exists. Compilation is the identity on it besides: `fn_of_bare_predicate` returns `f`
verbatim from a bare `__elem ▷ f`, which is the form a key domain is born in, so the morphism
inside it is never rewritten. That is what keeps one collection's key domain to one spelling —
a morphism point-freed at one position and pointful at another would be two structurally
unequal domains, and the membership fact would stop transferring between them.

### Constructor lowering: runtime `groupby` now, constant-folding later

The re-keying constructors are the first surface (before the `[k -> v]` sugar and
annotation-driven implicit insertion). Their **value construction is a runtime
`groupby`** on the key projection ([chl-spec
§3.11](../../../docs/chl-spec.md#311-list-tuple-record-literals)): `map([𝑘𝑣…])` groups the pairs by
`.0` and collapses each group with `Sole` to its `.1`; `set([𝑒…])` groups by the element and
collapses with the terminal `Drain` to the one `unit` a `Set` holds; `list([𝑒…])` keeps the
positional domain (`Array` widened to `List`). The result is the `Map`/`Set` Σ or `List`, and
[`lower_rekeyed`] builds both re-keyings.

Two consequences are **deferred to a constant fold that reaches collections**, recorded here
so the shortcut is explicit. Planning's fold (`src/ccl/planning/const_fold.rs`) stops at the
scalar. It evaluates a closed scalar computation, so a literal's elements are constant and
the re-keying over them stays a runtime `groupby`.

- **Compile-time construction.** A literal argument has statically-known keys, so
  the ideal is to build the sealed keyed tile at compile time rather than run a
  `groupby` over a constant. Folding a re-keying over a constant collection *is* the
  compile-time construction, with no literal-detection special-case (the fold either
  succeeds on constant inputs or falls through to the runtime operator).
- **Duplicate-key error timing.** The spec makes a duplicate key in a map
  *literal* a *compile-time* error
  ([§3.11](../../../docs/chl-spec.md#311-list-tuple-record-literals)). At runtime, a duplicate produces a
  non-singleton group, which `map`'s `sole` collapse **rejects at run time** (that
  is its whole point) — so the error is *enforced*, just later than the spec wants.
  Moving it to compile time needs the key *values*, which only a fold over the
  collection has; so the compile-time-ness (not the enforcement) rides on that fold.

**The collapse aggregate is the whole difference between absorbing a duplicate and
faulting on one.** `set([1,2,2,3])` and `map([(1,10),(1,20)])` are one [`lower_rekeyed`] over
one input condition, a repeated key, and the constructors pick different aggregates to
collapse the group. `Drain` is total, so a group of any size yields the one `unit` a `Set`
holds; `Sole` is partial, and a group of two has no value to yield
([`AggregateKind::is_partial`]). A set absorbing duplicates is set semantics, so both
answers are right, and neither is a property of the key.

#### A duplicate key is a process fault today

`Sole`'s rejection is an `assert!` in `AggregateKind::accumulate`, and the engine has no
channel for a fault raised by a query's **data**. Every other assertion in the tile
operators is about a shape no pass should have produced, where stopping is right. This one
is decided by user values, so one duplicate key fails every request the process is serving
rather than the one that carried it.

What it should become is a fault the failing query reports. That is a runtime channel and
not a change to this check: the alternative to the assertion is silent corruption, so the
assertion stays until the channel exists.

Literals are not the boundary. A map comprehension `[k -> v for …]` reads as a `Map` exactly
as a map literal does
([chl-spec §3.12](../../../docs/chl-spec.md#312-comprehensions)),
and [`lower_rekeyed`] is the one shape both re-keyings take, so a map built from request data
inherits the fault on the same path unless the comprehension's lowering decides otherwise.
The comprehension is decided as surface and unimplemented, so that decision is still open.

## Operations: how the trait layer dispatches [Planned]

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
- **Lookup.** The two operators `[]` (proven, `: 𝑇`) and `[]?` (optional, `: Option(𝑇)`)
  share one mechanic, the domain-membership refinement: `[]` requires it to discharge and is
  a type error otherwise, `[]?` decides it at runtime instead.
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

## Lookup: membership discharge

> **[Partly implemented]** — the two surface operators, proven `c[k] : 𝑇` and checked
> `c[k]? : Option(𝑇)`, are specified in
> [chl-spec §3.9](../../../docs/chl-spec.md#39-subscript-and-attribute-access). Both types
> today for a `Map` or `Set` whose type is known at the lookup, and `c[k]` does not yet
> discharge the key's membership — see [The proven lookup `𝑐[𝑘]`](#the-proven-lookup-𝑐𝑘).

The two forms are one rule. Both take the collection's key type off the collection, relate
the key to it, and read the codomain at the key; what separates them is how the answer is
presented, and a `LookupForm` is the whole of that difference. Lowering emits one shape for
both — `(𝑐, 𝑘) ▷ lookup`, tupled — `emit_lookup` types both, `simplify`'s partial-lookup
rule rewrites both, and one tile operator answers both.

### The checked lookup `𝑐[𝑘]?`

`𝑐[𝑘]?` is its own total operation, answering `Option(𝑉)` for any key. A collection is a
total function on its own domain and says nothing about keys outside it, so neither half of
the operation is a reading: the typing rule cannot be an application, and the operator has
to search.

**The rule**, four steps in `emit_lookup`:

1. **Take the key domain, the key binder and the codomain off the collection**
   (`keyed_access_types`). An abstract `Map(𝐾, 𝑉)` is a Σ over `SubtypesOf(𝐾)`, so the sum
   is instantiated at `𝐾` by the ordinary Σ rule; a concrete `Map` is already the function.
2. **Substitute the key term for the key binder** in the codomain (`keyed_value_at`), so a
   group-by's `𝑔[𝑘]` answers the group refined at `𝑘`
   (`a_key_dependent_lookup_discharges_the_key_binder`).
3. **Require the key's type below the key domain's base**, the membership refinement peeled
   off (`keyed_access_value`).
4. **Answer** step 2's value as the form says — `Option` of it here — and stamp the builtin
   with the pair it is applied to and that result, so later passes read one type off the
   node.

Step 3 is the whole of the key's obligation, and it is what an application cannot express.
An application requires its argument to lie in the function's domain, and a checked lookup
is reached exactly where that is unknown, so typing it as one would first have to relax
`𝑐`'s domain — and a collection type with its domain relaxed is a type no value has.
Peeling the refinement instead leaves the key owing `𝐾` and nothing more, which is right
because the refinement is what says which keys are present, and deciding presence is the
operator's job at runtime.

**Not an application, typed where applications are.** The category is a claim about the
rule and not about the term: lowering emits `(𝑐, 𝑘) ▷ lookup?`, an ordinary application of
a builtin, so `emit_apply` is where the node arrives and the rule is reached by intercepting
it there. Giving the rule its own emission path would mean giving `𝑐[𝑘]?` its own
`TypedExprNode`, which buys nothing the interception does not: the four steps above run
whole, and no application rule runs on the way past. A scheme is what cannot express it —
a scheme would have to name the key type, only a `SubtypesOf(𝐾)` kind states one, and every
concrete collection would then need an entry term first, which only a typed pass can decide
to insert.

Step 3 is an edge in one direction, and that is load-bearing. Relating the key and the
collection's keys to a common supertype — the literal reading of `SubtypesOf` — is satisfied
by any join, so a `String` key against an `Int`-keyed map would widen the key type rather
than fail (`a_checked_lookup_is_not_an_application`).

Step 2 is sound because step 3 asks nothing of the key beyond `𝐾`. `𝑘` is only maybe
present, and the substituted type stands for any key of the key type, denoting the empty
group where the key is absent — `` `none `` against `` `some `` of an empty group is what
distinguishes the two cases. The binder's declared domain is where the binder was
introduced, not something the key has to satisfy.

[`Builtin::CollectionContains`] is the same rule one payload lighter — `∀ι κ. (ι ⤇ κ) ⇒
(κ ⇒ Bool)`, a runtime-decided question behind a total function. It names the key set
`{𝐾 | __elem ▷ (𝑚 ▷ collection_contains)}` at the type level and is never executed; `𝑐[𝑘]?`
answers the same question with the value instead of a tag.

**The operator.** Lowering emits `(𝑐, 𝑘) ▷ lookup?`, which op-conversion compiles to a
[`Lookup`] taking the collection and the key as separate sources: it searches the
collection's domain for the key and emits `` `some(𝑐(𝑘)) `` or `` `none ``.

**Absence is decided, not read off an empty tile.** An empty tile means "no rows known
here", which covers both a key genuinely absent and a producer that has not converged.
Answering `` `none `` from emptiness would make the tag a function of how far the source had
run rather than of the collection's value, so the same lookup on a live source would answer
`` `none `` and later `` `some `` — and a live source is the ordinary case here. Terminality
is therefore the **readiness** condition: [`Lookup`] withholds until the domain is decided,
and only then answers `` `none ``.

**A lookup on an unpinned live domain never decides absence.** Terminality stands in for
"the domain has a definite value", and a live feed has one only where something pins it —
a filter against `txn.current_time()`, or a store read inside `with begin():`. Neither
terminates, so the present condition withholds `` `none `` from both, and a lookup over a
bare live feed withholds it forever. The condition a pin would state, and why unboundedness
is the wrong predicate for it, is
[chl-spec §3.9](../../../docs/chl-spec.md#39-subscript-and-attribute-access).

Emission computes step 2's discharge; a check reads it back off the operator's stamped type
rather than re-running it. Planning compiles a refinement's predicate to point-free form,
and compilation records the binder's type on the `const` minted to carry it — a place
substituting the binder's occurrence does not reach — so a discharge re-run after planning
builds a term emission never produced (`Typing::keyed_value_at`).

The operator's domain is a pair, so it never produces a function value. Its point-free form
is a morphism from a zip, `⟨𝑐, 𝑘⟩ ≫ lookup?`, and a collection reaches that zip two ways:

- **One collection for the whole iteration**, its leg closed in the loop binder.
  `simplify`'s partial-lookup rule rewrites `⟨const(𝑐), 𝑔⟩ ≫ lookup?` to
  `𝑔 ≫ (𝑐 ▷ curry(lookup?))`, and op-conversion compiles that partial application to a
  collection read once with every key answered against it. The rewrite is not an
  optimization: a streamed collection cannot be replicated into every row, because
  broadcasting copies a single present value and a collection is a tile.
- **One collection per position**, where the leg is a projection of the row. A mutable
  collection's mutable variable read inside a transaction is the only producer: `transact_phase`
  applies the writer body to a snapshot tuple, so the mutable variable arrives as `.n` of that tuple
  and no eta-reduction makes it closed again. Each row's cell is one materialized map value,
  and the lookup searches that value's bindings.

**A collection-valued answer does not materialize.** A group-by's rows are themselves
collections, so the answer would carry a collection, and nothing materializes one there.
Op-conversion rejects that shape by name, on the collection rather than on the answer, so
both forms fail alike (`a_group_valued_lookup_is_rejected_by_name`). It is also the case
where presence and emptiness genuinely differ: a `Map(𝐾, Collection(𝑉))` can store an empty
collection at a present key.

### The proven lookup `𝑐[𝑘]`

`𝑐[𝑘]` answers `𝑉` at any key, and faults the process where the key is absent.

**The key's obligation is the checked lookup's [Interim].** Step 3 of the rule above is the
whole of it — the key owes the collection's key base, membership peeled off — so a key that
cannot be shown present type-checks, and the operator reaches a decided absence with nothing
to answer. A `` `none `` is a value of a type this form does not have, so the process faults
(`a_proven_lookup_on_an_absent_key_faults`). Every other step is shared, including the key
binder's discharge, so `𝑚[𝑘]` names the same value type read, written, or checked.

The specified rule makes an unprovable key a compile-time error instead
([chl-spec §3.9](../../../docs/chl-spec.md#39-subscript-and-attribute-access)), and what it
waits on is a key that carries its collection's key domain — the gap
[Prerequisite: the proof has to survive being consumed](#prerequisite-the-proof-has-to-survive-being-consumed)
states. Until then the obligation is not gone, only moved: the **call** spelling `𝑐(𝑘)` is
still an application and still demands the index lie in the domain
(`a_key_from_the_source_does_not_yet_carry_its_key_domain`), so the two spellings the spec
calls one operation have parted company for as long as this lasts.

### Prerequisite: the proof has to survive being consumed

Two routes produce a key carrying a collection's key domain, and only one of them works.

**Applying the key morphism** is direct: `(c ≫ key)(𝑖)` is a key of the collection
`c ≫ key` keys, because that is what `{𝑘 | 𝑘 ▷ ((c ≫ key) ▷ collection_contains)}` says.
This is what makes `for o in orders: g[key(o)]` provable, and it is what naming the
morphism bought — an opaque domain admits no such rule.

**Iterating the collection** does not, and the gap is in consumption rather than in the
surface. Consuming a sum presents the sum `σ` rather than the refined domain, so that the
witness cannot escape into the consumer's result; an iterated key is therefore a consumed
sum's witness, and the membership has nothing to discharge against. The apparatus is there —
`𝑘 : σ` alongside `𝑚 : σ` is the pairing a discharge needs — but which shape closes it is
open. Closing it is what retires the interim rule in
[The proven lookup `𝑐[𝑘]`](#the-proven-lookup-𝑐𝑘).

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
`Collection(𝑇)` whose producer is not statically known, a collection in a mutable variable
or crossing a source boundary — waits on a runtime witness that does not exist yet, and a Σ
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
here, and no ordering of the two gates is available to choose between. The duplication the
same substitution forces stands on the same ground, and stays an obligation until a runtime
witness exists ([A `let`-bound conditional is copied to each
consumer](#a-let-bound-conditional-is-copied-to-each-consumer)).

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

#### A `let`-bound conditional is copied to each consumer

Realization needs the `Case` below the site, because a leg is the site with the `Case`
replaced by one arm; a binding precedes its body in scope, so a `Case` left there is above
every site that reads it. The site then names a witness no term has materialized, and
op-conversion rejects the domain. The copy is also what lets each consumer's substitution
differ: two consumers filtering one conditional instantiate the same witness into two
different predicates, which one set of legs cannot hold.

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
