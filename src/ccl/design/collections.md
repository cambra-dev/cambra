# Collections

Cambra's surface language (CHL) has lists, arrays, sets and maps. The IR has one collection
primitive: a **data function** `𝐷 ⤇ 𝑉`, a function whose domain is the data
([type-inference.md, 4.6 Data vs compute functions](type-inference.md#46-data-vs-compute-functions)).
This document gives each surface type — those four spellings and the abstract `Collection(𝑇)`
— as that one primitive over a different domain, and says how each compiles.

What a program writes, and what each collection type means to it, is
[chl-spec, Direction: collection types](../../../docs/chl-spec.md#63-direction-collection-types-decided).
Start there if the question is about the language rather than the checker;
[The five collection types](#the-five-collection-types) below is the same list with its
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

## The five collection types

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
- **`Map(𝐾, 𝑉)`** = `Σ (𝐷 : SubtypesOf(𝐾)). 𝐷 ⤇ 𝑉` — a key domain. Unordered. Lookup
  `𝑚[𝑘] : Option(𝑉)` in general, `: 𝑉` when presence discharges. Membership `𝑘 in 𝑚`.
- **`Collection(𝑇)`** = `Σ (𝐷 : Type). 𝐷 ⤇ 𝑇` — the witness ranges over *every*
  domain; the domain rides along **in the value** (retained, not sealed — a
  domain-generic consumer holds it abstract). Unordered. The ⊤ of the kind order, and
  nothing more: keyed-ness lives in `SubtypesOf(𝐾)`, so `Collection(𝐾)` is not
  load-bearing for `Map`/`Set`.

  This is the type that needs a **runtime** witness, since iterating a `Collection(𝑇)`
  parameter has no static domain to read
  ([Compiling a conditional collection](#compiling-a-conditional-collection)).

Each is a sum over the named kind, and every rule they obey is the general Σ
rule at that kind — entry by a term, subtyping, and consumption
([type-inference.md, Subtyping for sums](type-inference.md#subtyping-for-sums)). Only
`Array` is not a sum: its domain is one concrete range, so it needs no witness.

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

**Until this is settled** `for ... in` binds the codomain for every collection type, because
key and entry iteration is exactly the `Set`-versus-`Map` distinction. If the operation
layer is needed first, the interim to reach for is **uniform entry iteration**: a `Set`'s
entry is `(𝐾, unit)` and the projection to `𝐾` is lossless, so `Map` gets correct entry
iteration without the distinction existing. That is surface-visible — `for k in s` would
bind a pair — so it is a spec decision, not a silent one.

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
  What *enforces* that depends on the open subtyping question
  ([Telling `Set` and `Map` apart](#telling-set-and-map-apart-open)): with the Σ edge
  to `Collection(𝑉)` present, `sum(m)` is rejected only once `sum` lowers through
  iteration, because a `Map` yields `(𝐾, 𝑉)` entries and entries cannot be summed; without
  it, `sum(m)` has no edge to take. Until either lands `sum(m)` means `sum(values(m))`.

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

Planning (`planning/conditionals.rs`) replaces it with the gated union `⧺ᵢ (armᵢ | π̂ᵢ)` over
the same domains, each leg gated by the path condition its `if`/`elif` compiled to. The
gates are exclusive and exhaustive, so exactly one leg is non-empty and the union's extent
is the domain the witness selected — which is what makes the union and the Σ the same
collection. The pass asserts the type it is replacing rather than relating the two by a
typing rule ([type-inference.md, Planning asserts the type it
replaces](type-inference.md#planning-asserts-the-type-it-replaces)).

**A conditional collection is the only Σ-typed term the runtime can currently evaluate.**
Its candidates are statically enumerable and the gates pick one. Every other Σ — a
`Collection(𝑇)` whose producer is not statically known, a collection in a `Mut` register or
crossing a source boundary — waits on a runtime witness that does not exist yet, and a Σ
that reaches op-conversion with no concrete domain has no extent and is reported as a
compiler bug.

**One union per site, at the node whose type carries the choice**: the outermost `Σ`
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
