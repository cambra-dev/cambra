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

## The domain family

A data function's domain has several species. Today three exist; this
design adds the fourth (keyed) and makes a fifth (the Σ witness) fully live.
The organizing distinction is **positional vs. content-addressed** and
**static vs. opaque**:

| Domain | Positional? | Domain known | Element type | Ordered |
|---|---|---|---|---|
| `UIntRange(n)` | yes | static (`usize`) | `{𝑖: UInt \| 𝑖 < 𝑛}` | yes |
| `source(name)` / `Txn` / `ChanDom` | by arrival | opaque | positions | arrival only |
| **key domain** *(new)* | no | opaque | the keys that occur | no |
| **Σ witness `𝐷`** *(activated)* | inherits `𝐷` | opaque, kind-classified | inherits `𝐷` | inherits `𝐷` |

The last two rows are **one primitive**, the Σ witness classified by a kind
([type-inference.md, The wired witness kinds](type-inference.md#the-wired-witness-kinds)).
A key domain is a `Keyed(𝐾)` member; the ≥ 2 control-flow join is an `Enumerated` witness;
a `List`'s is a `UIntRanges` member.

## The five collection types

With `𝐷` a witness domain and `𝑛` a length:

- **`Array(𝑛, 𝑇)`** = `[0, 𝑛) ⤇ 𝑇` — domain `UIntRange(n)`, length *static*.
  Ordered. Lookup `arr[𝑖] : 𝑇` — total, because the bound `{𝑖 | 𝑖 < 𝑛}` is
  statically dischargeable. This is the shape the compiler builds for a list
  literal today.
- **`List(𝑇)`** = `Σ (𝐷: UIntRanges). 𝐷 ⤇ 𝑇` — *some* index range, which one not
  known statically. Ordered. Lookup `lst[𝑖] : Option(𝑇)` — the bound is not
  statically dischargeable, so lookup is partial.
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
  parameter has no static domain to read ([Future work](#future-work)).

Each is a `Type::Sigma` over the named kind, and every rule they obey is the general Σ
rule at that kind — entry by a term, width, and consumption
([type-inference.md, Subtyping for sums](type-inference.md#subtyping-for-sums)). Only
`Array` is not a sum: its domain is one concrete range, so it needs no witness.

## What `box` checks against a collection type, and when

`box` forms the dependent pair `(𝐷, body)` for `List(𝑇) = Σ (𝐷: UIntRanges). 𝐷 ⤇ 𝑇` from a
concrete `𝐷 ⤇ 𝑇`, and succeeds iff the concrete domain is a **member of the kind** — for
`UIntRanges`, iff it is a `UIntRange`.
Membership is a predicate on the domain's shape rather than a constraint that records a
bound.

This is a Σ (dependent **sum**), not an ∃ (existential): the witness is retained and
projectable rather than sealed. A list's length rides in the value — it is the domain's
size, so `len` is the first projection — and the same holds for a keyed domain, where
`keys` is a `Map`/`Set`'s first projection. The witness is already present in the runtime
`SealedFunction`, so the pairing copies nothing.

Which collection is boxed decides when that predicate can run. A **literal**'s domain is
already a concrete `UIntRange`, so it runs at emission. A **computed** collection — a
comprehension — has a domain that is still an inference variable there, so the membership is
recorded as a kinding constraint and discharged once the shape exists
([type-inference.md, What the kind level needs from the solver](type-inference.md#what-the-kind-level-needs-from-the-solver)).
Read at a collection, that discharge is: a range discharges, and a source or a membership
refinement is a mismatch, reported as the collection-annotation error it is.

It has to live on the *variable* rather than be re-checked from the syntax later because
no annotation is left on the tree by then: monomorphization rebuilds the `let` and drops
`user_annotation`, the binding becoming an anonymous `__mono`.

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
  same hook a [kinding constraint](#what-box-checks-against-a-collection-type-and-when) is
  discharged at. The realization is cheap: the loop encoding already threads the domain
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
  `sum(values(m))`; see step 3 of the [Implementation
  roadmap](#implementation-roadmap).

## Compilation

Collections add one planning phase, **realization**, and otherwise extend the existing
lowering, inference, and planning surfaces.

- **lower** (`ccl/lower/`) — map literals `[k -> v]` (today `Unsupported`),
  `set(…)` / `list(…)` / `map(…)` constructors, `(𝑘, 𝑣)` entry-iteration binders, and
  keyed-feed `𝑐[𝑘] = 𝑣` / `𝑐[𝑘] := 𝑣`. Subscript already lowers as lookup; what it
  needs is the discharge.
- **infer** (`ccl/infer/`) — a lookup emits a key-presence obligation and discharges
  it against the collection's own key domain (total) or falls back to `Option`
  (partial); `groupby`'s result type unifies with `Map` (mostly *deleting*
  special-casing).
- **constrain** (`ccl/infer/solver/constrain.rs`) — finish domain invariance modulo
  refinements ([type-inference.md, Data domains are
  invariant](type-inference.md#data-domains-are-invariant)); everything else reuses the
  refinement-width and Σ-width arms.
- **planning** (`ccl/planning/`) — `extent_of` dispatches a keyed domain to a
  hash store and a range to a dense array; `restrict` / `FilterValues` already
  lower a domain refinement; the mutable-map store is the existing keyed MVCC
  store with a dynamic key column.

### Realizing a conditional collection

**Realization** turns a conditional collection from the type its arms joined to into the
term the runtime can drive: a `Case` typed `Σ 𝐷 ∈ 𝐾. 𝐷 ⤇ 𝑉` becomes the gated union
`⧺ᵢ (armᵢ | π̂ᵢ)` over the same domains, gated by the branch predicates the `if`/`elif`
compiled to. Exactly one gate passes, so the union's extent is the selected domain, which
is what makes the two the same collection. It runs in planning
(`planning/conditionals.rs`) and asserts its pre-realization type rather than relating the
two by a typing rule ([type-inference.md, Realization asserts rather than
rewrites](type-inference.md#realization-asserts-rather-than-rewrites)).

**Realization is demand-directed, so a restricted conditional is copied to each
consumer.** A consuming site's filter rides the witness — `Σ 𝜎 ∈ 𝐾. ({𝜎 | 𝑝} ⤇ 𝑉)` —
and the site can do nothing with it, having no extent for a witness. Realization can:
inside leg 𝑖 the conditional is `armᵢ`, so the leg is gated twice, by its path
condition `π̂ᵢ` and by `𝑝` rewritten to read that arm. Rewriting is what makes the fact
sayable — a predicate may hold a plain arm but not a gated union, which needs the
`iterate`/`restrict` a predicate is forbidden.

The legs therefore carry one consumer's demand, and a `let`-bound conditional consumed
twice has one set of legs and two demands. So planning copies a conditional to each
consumer that restricts it and drops the binding, which also puts the `Case` back below
the site that restricts it — a binding precedes its body by scope, so no traversal order
reaches the demand first. An unrestricted conditional owes nothing and stays shared. The
price is a union per restricting consumer; a runtime witness would let one materialized
union serve several, by moving the filter back to the consumer.

A site **names** its witness rather than being it: iterated beside a second generator
the index is a product, so the same filter rides `{(𝜎, 𝐷) | 𝑝}`. Every rule keyed on
the witness a domain names therefore matches a *mention* — which witness owes the
restriction, and whether a site whose restriction was discharged into the legs still
owes a `restrict`. Reading only the whole domain makes the product a silently different
case: the second question answered wrongly emits the site's chain a second time, over a
witness that has no extent.

**A site's witnesses are realized together, so its legs are the combinations.** Two
conditional generators nest two sums over one product domain —
`Σ 𝜎₄ ∈ 𝐾₄. Σ 𝜎₇ ∈ 𝐾₇. ((𝜎₄, 𝜎₇) ⤇ 𝑉)` — and that is one site with two choices on it,
not a site within a site. Realizing them one at a time nests the unions, and a nested
union is wrong in the term rather than only in the type it records: a leg's gate is
carried as a refinement on its domain, and the term-level `restrict` is emitted only
where that domain heads an iteration, so wrapping the inner union — not an iteration
site — drops the outer gate. Two legs are then live where exactly one may be, and the
answer double-counts.

So the legs are the tuples of arms, gated by the conjunction of their path conditions
and indexed by the product of their domains. This is the finite-Σ ≡ gated-union
isomorphism stated for a product of witnesses rather than for one, and it is flat, which
is what the term already is — `Expr::collection_union` flattens, so a one-at-a-time
realization also disagrees with its own term about the tags.

There is **one realization**, at the node whose type carries the choice: the outermost
`Σ` binding the witness, or the `Case` itself when the arms share a domain and no type
above mentions the choice at all. That second case is degenerate rather than separate —
one choice, and substituting the arm for the conditional at the site leaves the arm.
Realizing at the site is also what retires a restriction *map*: the site that placed the
restriction is the site being copied, so the filter is already inside the leg, and there
is nothing to carry down from an ancestor.

## Implementation roadmap

The order to build the rest in, and why that order. A step names what it unblocks and what it depends on; the
design is the section it links to.

> **A step-0 obligation.** It is cheap now and unrecoverable later, so it gates the
> steps rather than sitting inside one.
>
> - **Decide how a collection kind is represented** — tentatively the witness kind for
>   four of the five, with `Set`/`Map` as nominal type heads landing with nominal types
>   ([The kind is declared](#the-kind-is-declared-not-read-off-the-shape)).
>   Step 3 dispatches every operation on it. If nominal types trail the operation layer,
>   take the uniform-entry-iteration interim named there rather than encoding `Set` vs
>   `Map` somewhere it will have to be removed from.

1. **Finish the Σ-as-kinds rework** ([type-inference.md, Where the pairing search
   runs](type-inference.md#where-the-pairing-search-runs)). What remains is the **keyed**
   kind, which makes the keyed discharge plain kind containment rather than a rule of its
   own, so it precedes every step below that dispatches on a key.

2. **Restore direct group-by key application; then lookup discharge and `Option`.** Two
   halves of one mechanic, and the first is a regression fix: `groupby`'s honest keyed
   type makes `g(k)` at a bare key a type error, and it must, since an arbitrary key is
   not known to be present. A test asserting a bare key succeeding is therefore restated
   against the checked operator, never re-enabled. The surface pair `𝑐[𝑘]` / `𝑐[𝑘]?` and
   `Option` over the existing `Variant` nodes sit on top.

3. **The operation layer** ([Operations](#operations-how-the-trait-layer-is-realized-planned)).
   Gated on step 0's kind decision. Pins the `storefront` `/stats` rollup, which needs
   entry iteration, and lifts the codomain-only iteration every kind gets today. It is
   also what makes `sum(m)` an error rather than `sum(values(m))`
   ([Views](#operations-how-the-trait-layer-is-realized-planned)).

4. **Keyed entry under an invariant domain.** The subtyping arm is done
   ([type-inference.md, Data domains are
   invariant](type-inference.md#data-domains-are-invariant)), so what is left is the
   explicit `Cast` its consequence requires.
   Land it before refined keyed domains, not after: a keyed Σ's body domain is the nullary
   [`Type::WitnessRef`] on both sides, so the whole domain content sits in the kind, where
   containment checks the key domain's shape and stops. The moment a keyed domain carries
   a second refinement — a restricted map, a filtered key set — nothing compares it and the
   missing guard becomes a live refinement-acquisition hole.

5. **The Σ layer as the general rule.** Three mechanisms, in this order, each
   independently landable
   ([type-inference.md, Deliberately incomplete
   here](type-inference.md#deliberately-incomplete-here) is the gap list they close):
   a **kind lattice** over [`TypeKind`] with membership split out as a per-kind predicate;
   the **pairing search** `∀ 𝑑 ∈ 𝐾₀. ∃ 𝑒 ∈ 𝐾₁`, whose precondition is ground candidates
   rather than a particular time; and **consuming a sum at a domain-preserving consumer**
   by every route — inline, `let`-bound, and through a UDF parameter — with a filtered one
   restricting the witness, which [realization](#realizing-a-conditional-collection)
   discharges into the legs.

6. **The rest of the constructor surface.** Map literals `[k -> v]`, `list()`,
   `map()`, general `𝑚[𝑘]` subscript lowering, and keyed entry for a collection whose key
   domain is only concrete after coalesce. Also the one planning change that lets a keyed
   collection be driven as a nested comprehension source and as a bare `groupby` tail.

`storefront` is the composition test, red until steps 1–2 plus the HTTP library (a
separate design) land.

## Future work

- **The runtime witness.** The load-bearing item, and the one the others reduce to.
  Nothing today can read a witness off a value
  ([type-inference.md, A sum on the left](type-inference.md#a-sum-on-the-left-forget-the-witness-or-name-it)
  is what a Σ value is). Consuming a sum means projecting it and dispatching, so a
  `Collection(𝑇)` parameter cannot be iterated: there is no static domain to recover,
  which is the whole content of the annotation. [`extent_of`] maps a *type* to an
  `Extent`; the witness needs the treatment `Type::DataSource` already gets, resolving
  to `Extent::DataSourceDomain` — a handle to the domain as it exists at runtime. So
  the witness joins the family of opaque domains rather than founding one.

  `Collection(𝑇)` is the general case and the conditional collection is the special one.
  The conditional collection is the single Σ that does not need a runtime witness: its
  candidates are statically enumerable and its realization is the gate fan-out
  `⧺ᵢ (xsᵢ | π̂ᵢ)`, whose extent already is the selected domain because the unselected legs
  are empty. Realization performs that union after inference and asserts the
  pre-realization type, so nothing has to relate the tagged union to the sum by a typing
  rule.

  **What forces it is producer-visibility, not abstraction.** An abstract *parameter*
  never forces it: inlining beta-reduces the UDF, so the consumer is reunited with a
  concrete producer whatever the type says. (An exact `Collection(𝑇)` annotation keeps
  the type abstract and inlining keeps the graph concrete, so the two are independent;
  the bounded form `a <: Collection(𝑇)` monomorphizes the type as well.) What no
  call-site instantiation
  resolves is a producer that is not statically known at all: a collection in a `Mut`
  register, one crossing a source boundary, a recursive function, or a collection
  stored inside another collection.

  Where a sum would strand is enumerable rather than speculative, because
  [`extent_of`] has no `Type::Sigma` arm and its catch-all is a loud "compiler bug"
  error. The paths that convert a *type* rather than deriving from an input operator
  are: the `Builtin::Iterate` source domain, a loop's iteration extent, a store key's
  init value, and a transaction item / reply tap. Aggregation is **not** among them —
  `apply_aggregate` wraps its input operator and never consults the node's type. So
  the two families that break are **iteration** and **storage**, and consumption by
  aggregation is already safe.

  It also unblocks a **live** witness — one referenced by an element-membership
  predicate and so kept by the keep-iff-referenced filter — which `lambda_elim` and
  planning must handle instead of a witness that is always `None`. That is [roadmap step
  4](#implementation-roadmap) regardless.

- **A mutable keyed collection has no type yet.** A keyed collection carries its key
  domain *in* its type, so a point write that inserts a key changes that type, and
  `Mut[Map(𝐾, 𝑉), Txn]` fixes one key domain for the register's whole history. Modelling
  `store[𝑘] := 𝑣` needs a value type whose key domain varies over the sequencing domain,
  which is a dependency the history model does not have. The compound registers of
  [mutability.md](mutability.md) are the static-key special case and do not generalize on
  their own.
