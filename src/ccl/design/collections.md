# Collections

Cambra's surface language (CHL) has lists, arrays, sets, maps, and dicts. The
runtime has one collection primitive: a **data function** `𝐷 ⤇ 𝑉` — a function
whose domain *is* the data, distinguished from a compute function
`𝐷 ⇒ 𝑉` (a capability) by its [`FunKind`](type-inference.md#46-data-vs-compute-functions).
This document explains how the surface collection types are all *the same
primitive over different domains*, what the one genuinely new type-level idea
is (a **referenceable opaque domain** — the dormant Σ
witness), how lookup, ordering, feeds, and mutation follow from the domain's
shape, and how the whole thing compiles.

It builds directly on the mutability/conditionals stack: `FunKind`, the Σ
domain-join, refined domains, and kind-aware subtyping ([type-inference.md
§4.6](type-inference.md#46-data-vs-compute-functions)) are
the substrate, and mutable collections are the keyed generalization of the
compound (tuple/record) registers that stack introduced.

> **Implementation status.** This document is the **complete design of record**
> for collections, frontloaded here at the base of the collection stack
> (`collections-design` → `collection-constructors` → `groupby-keyed-collection`
> → `map-set-constructors`) so it reads end-to-end. Because it is frontloaded,
> **[Status](#status) is the one place status is recorded** — every branch of the
> stack updates that table as it lands a row, so the table is true at whichever
> branch you have checked out. A section carries an inline `[Planned]` tag only
> when it is planned across the *whole* stack (the operation layer, ordering,
> mutable / deferred / recursive collections); anything whose status **flips**
> between branches — the five types, the Σ arms, the constructors —
> is recorded in the table and nowhere else. Restating a flipping status in prose
> is precisely how this document rotted before.
>
> Where a [Planned] feature has an *interim* behavior in today's code (e.g.
> iterating a map yields values, not entries), that is called out inline as
> **[Interim]** — an unfinished state on the path to the design, not a shim to remove.

## The idea in one line

**One representation; the kind axis is a decided direction with a tentative
representation.** Every collection is represented by a single primitive — a data
function `𝐷 ⤇ 𝑉`. The surface kinds `List`, `Array`, `Set`, `Map`, and
`Collection` are *meant* to be distinct, each with its own operations, and that
is the decided direction ([Two axes](#two-axes-representation-vs-kind-decided-direction-representation-tentative)).
How a kind is represented is *tentatively* settled — the witness kind for four of them, a
**nominal head** for the ambiguous pair — and today it is not represented at all:
`Array(𝑛, 𝑇)` and `List(𝑇)` share the range representation `[0,𝑛) ⤇ 𝑇`, `Set(𝐾)` and
`Map(𝐾, 𝑉)` will share the `Keyed(𝐾)` witness kind, with `Set(𝐾)` *literally*
`Map(𝐾, unit)`. So the operation layer has nothing to dispatch on yet.

### Two axes: representation vs kind [Decided direction; representation tentative]

Two surfaces; conflating them is the trap this design avoids.

- **Representation — structural.** The data function `𝐷 ⤇ 𝑉`. *Subtyping and
  coercion* live here (`Array → List → Collection`), as the terms that build a sum /
  re-pairings the solver realizes ([Subtyping](#subtyping)), and it is what
  op-conversion compiles. Shared across kinds.
- **Kind — plus operations — traits.** `List`/`Array`/`Set`/`Map`/`Collection`
  are meant to be distinct heads, each carrying its own instance of `Iterable`,
  `Index`, `Membership`, and `Ordering`
  ([Operations](#operations-how-the-trait-layer-is-realized-planned)), dispatched
  on the *declared* kind — never read back from the representation's shape.

**Why the kind should not be read off the shape.** Which side of `𝐷 ⤇ 𝑉` is the
*payload* is not fixed by the shape. `Set(𝐾) = Σ (𝐷: Keyed(𝐾)). 𝐷 ⤇ unit` iterates
its **keys** (the domain); `List(𝑇)` iterates its **values** (the codomain) — opposite sides
of the same arrow — and `Map(UInt, V)` vs. a filtered `List` can share a shape
yet must iterate entries vs. values. "Which side is the payload" is therefore a
fact about the *kind*, not something the arrow can be asked. This is also why
**"keyed-ness" is not a primitive**: there is no structural "keyed" property, only
a per-kind choice of what `for`-in surfaces (see
[Operations](#operations-how-the-trait-layer-is-realized-planned)).

> **Tentative — the ambiguous pair gets a nominal type.** `Set` and `Map` — and only
> those two — become **nominal type heads** (the `type` strength of
> [chl-spec, Direction: term/type syntax split](../../../docs/chl-spec.md#61-direction-termtype-syntax-split-decided), distinct
> from a structural `=` alias), landing when nominal types do. Tentative rather than
> settled, but it is what this design expects to go with absent a new argument. The other
> three kinds need nothing: their domains already differ, so the witness kind discriminates
> them and they stay structural.
>
> Nothing in [`Type`] carries a collection kind today, so the paragraph above states an
> *intent*, not an implemented property. The **witness kind** already discriminates four
> of the five on its own — a bare range `Fun` (`Array`), `UIntRanges` (`List`),
> `Keyed(𝐾)` (`Set`/`Map`), and `Any` (`Collection`) — so the one genuinely ambiguous
> pair is **`Set` vs `Map`**, which share a kind *and* its key parameter, differing only
> in a codomain that is `unit` for one.
>
> **Why nominal, and not the kind.** A nominal head *restores decidability*: whether a
> value is a set of keys or a map to units becomes readable from the type, where
> `{𝐾 | tok} ⤇ unit` cannot say. That is the property which decides how much solver
> machinery a classifier costs — see [type-inference.md, What would change the
> answer](type-inference.md#what-would-change-the-answer) — and it is why a nominal head
> beats both alternatives rather than merely differing from them: putting the
> distinction in the **kind** would leave membership undecidable *and* leave positions
> that must infer it, forcing a kind inference variable; a bare **provenance stamp**
> avoids the variable but tracks the reading alongside the type instead of in it. A
> nominal head needs no variable *because* the head is the evidence.
>
> It is also the same conclusion this section reaches on its own terms: `Set` is not a
> different *domain shape* from `Map`, it is a different **reading** of the same shape,
> and a nominal type is exactly a reading. `Keyed(𝐾)` is unaffected and still earns its
> place — it classifies the *domain* (a key domain, not a range), which is orthogonal to
> which side of the arrow is the payload.
>
> **What it costs.** Less than it first appears — the second bullet is the one that
> shrank on inspection, and the third has a precedent for going wrong here:
>
> - **The head must wrap the Σ, not abbreviate it.** If `Map` elaborates to
>   `Σ (𝐷: Keyed(𝐾)). 𝐷 ⤇ 𝑉` and vanishes, the types are structural again and `Set` is
>   `Map` again. That is precisely the `type`-versus-`=` distinction, so the mechanism is
>   right — but trait dispatch has to match the head, which means `Set`/`Map` are
>   *known* nominal names rather than ordinary library declarations.
> - **Only the *lateral* relation becomes a decision.** Nominality is needed to keep
>   `Set` and `Map` apart from *each other*, and that is all it is needed for — the
>   witness kind already discriminates the other three, so `Array`, `List` and
>   `Collection` stay structural and `Array <: List <: Collection` is untouched.
>
>   Width-to-top survives for the nominal pair too, and not by a declared edge:
>   widening to `Collection(𝑉)` **forgets** which head you had, and forgetting is what
>   widening *is*. The head's content is `Σ (𝐷: Keyed(𝐾)). 𝐷 ⤇ 𝑉`, whose kind is
>   contained in `Any` because ⊤ absorbs, so the edge falls out of the existing rule
>   rather than needing a row. What has to be stated is one rule for the mechanism — a
>   nominal collection head is a subtype of its content — plus the head's **parameter
>   variance**, once per constructor. Neither is per-edge.
>
>   So the only genuinely new *choice* is `Set(𝐾)` versus `Map(𝐾, unit)`, which is
>   exactly the choice nominality exists to make explicit. And it does not move
>   `sum(m)`: that rejection belongs to the *iteration element*, a fact about the element
>   type rather than about any edge (step 3 of the
>   [Implementation roadmap](#implementation-roadmap)).
> - **The head needs a compact representation, and it cannot be an [`AtomKey`].**
>   `AtomKey` is a *discrete* set — only reflexive arms, atoms merge by union, two shapes
>   at one position is a collision — which is exactly why the nominal key-domain *atom*
>   failed and became a refinement instead
>   ([Implementation roadmap](#implementation-roadmap)).
>
>   How much is needed follows from the upward transparency above. Because a head widens
>   by being *forgotten*, the join of two different heads at one position is their
>   content's join — `Collection`-ward — rather than a collision, so a **tag alongside
>   the existing `fun` slot that the join drops** is likely sufficient, and a full slot
>   with per-parameter polar recursion is likely not needed. If it turns out to be, the
>   shape to copy is [`Type::History`]: a fixed-arity constructor with type children and
>   its own `history_slot` merged componentwise, differing in that `history_slot`
>   recurses invariantly. Deciding between the two is part of designing nominal types,
>   not settled here.
>
> **Sequencing.** Settling it is a prerequisite for the operation layer — specifically
> for key/entry iteration, which is exactly the `Set`-vs-`Map` distinction — so until
> then `for`-in binds the codomain for every kind ([Interim], see
> [Iterating a `Set`/`Map`](#iterating-a-setmap-binds-the-codomain-not-the-keys-interim)).
> If nominal types land *after* the operation layer is needed, the interim to reach for
> is **uniform entry iteration**: a `Set`'s entry is `(𝐾, unit)` and the projection to
> `𝐾` is lossless, so `Map` gets correct entry iteration without the distinction
> existing. That is surface-visible (`for k in s` would bind a pair), so it is a spec
> decision, not a silent one.

## Status

**The single status surface for this design.** Every other section states
*design* and tags itself `[Implemented]` / `[Planned]` against this table; each
branch of the collection stack flips its own rows as it lands them, so the table
is accurate at whichever branch you are reading. A `[Planned]` row's **Branch**
column names the branch that *will* land it.

| Capability | Status | Branch |
|---|---|---|
| `FunKind` (`⇒`/`⤇`), kind-aware subtyping, conditional-collection Σ | Implemented | `conditionals-sigma-types` |
| value-`Case` compilation (gated partition / fan-out) | Implemented | `conditionals-value-case-compilation` |
| `Array(𝑛, 𝑇)` / `List(𝑇)` annotations; `List` as the `UIntRanges` **type**-witness Σ, with its own term, consumption, and width | Implemented | `collections-design` |
| one carrier **per constructor** — a `sigma` slot holding the witness kind ([`CompactWitnessKind`]: listed candidates or a described kind), a `fun` slot holding one ordinary domain, and coalesce asserting the latter | Implemented | `collections-design` |
| `List` **entry** with an *inferred* domain, as a kinding constraint on the domain variable ([`InferBounds::kinds`]) | Implemented | `collections-design` |
| the Σ-width **pairing search** `∀ 𝑑 ∈ 𝐾₀. ∃ 𝑒 ∈ 𝐾₁` over ground candidates, codomain edge emitted once ([`KindObligations::pairing`]) | Implemented | `collections-design` |
| a data-function join keeps its **candidates** — alternatives accumulate at either polarity, demands still narrow ([`CompactFun::merge`]) | Implemented — this is the *implicit* formation `box` replaces | `collections-design` |
| Consuming a sum at a **domain-preserving** consumer, in any constraint order — a variable's collection-shaped lower bounds denote the sum, so the join is read when its outgoing edge is drawn; a restriction rides the witness | Implemented | `collections-design` |
| a sum's **candidates** as an invariant position (two-way extrusion proxies), so an arm whose domain is *inferred* — any comprehension arm — joins like a written one | Implemented | `collections-design` |
| a use of a **lambda parameter** falling back to the parameter slot where the bare read has no answer, so a **UDF-call** arm joins through the bound graph | Implemented | `collections-design` |
| `Collection(𝑇)` (`TypeKind::Any`): its own term, consumption, width-to-top from every *sum* kind (⊤ absorbs structurally; a bare `𝐷 ⤇ 𝑉` is not below it) | Planned | `collection-constructors` |
| `Map` / `Set` / `Dict` annotations as the `Keyed(𝐾)` witness **kind** | Planned | `collection-constructors` |
| kind **parameters** (a `Keyed` kind's key type) related invariantly through the solver, not tested by containment | Planned | `collection-constructors` |
| a **shared hole** ([`Type::SharedHole`]) — one annotation type var written at two lowering sites | Planned | `groupby-keyed-collection` |
| the keyed **discharge** — keyed term / consumption / width, as kind containment | Planned | `groupby-keyed-collection` |
| `groupby` infers the keyed `Map` type; kind-based inlining | Planned | `groupby-keyed-collection` |
| the *concrete* keyed domain `{𝐾 \| __elem ▷ keydom#id}` and its [`Builtin::KeyDom`] token; per-site key-domain identity | Planned | `groupby-keyed-collection` |
| keyed entry into a nominal `Map`/`Set` (`groupby → Map`, `set(…) → Set`) | Planned | `groupby-keyed-collection` / `map-set-constructors` |
| `set(…)` values (group-by + [`AggregateKind::Drain`]) | Planned | `map-set-constructors` |
| the general deferred keyed gate (a producer whose key domain is only concrete after coalesce) | Planned | — |
| direct group-by key application `g(k)` | Works (via `groupby`'s imprecise total type) | — |
| how a collection *kind* (`Set` vs `Map`) is represented — decided as **provenance**, like `FunKind` | Planned | — |
| driving a keyed collection as a *nested* comprehension source, and a bare `groupby` tail | Planned | — |
| the operation layer: iteration element, `[]`/`[]?`, `in`, ordering, `keys`/`values`/`items` | Planned | — |
| domain invariance modulo refinements (the one new subtyping arm) | Planned | — |
| lookup discharge + `Option` | Planned | — |
| mutable / deferred / recursive keyed collections | Planned | — |
| `box` as the **sole** way into a sum — `𝑇 <: Σ` removed from subtyping, so a join forms no sum ([type-inference.md, Only a term builds a sum](type-inference.md#only-a-term-builds-a-sum)) | Implemented | `collections-design` |
| the Σ **carrier** — a `sigma` slot beside `fun`, with the merge laws derived from width and consumption rather than chosen ([type-inference.md, How a sum flows through the solver](type-inference.md#how-a-sum-flows-through-the-solver)) | Implemented | `collections-design` |
| **naming the witness** — the consumer typed under a named witness carrying its range, bound at materialization ([type-inference.md, Consuming a sum: naming the witness](type-inference.md#consuming-a-sum-naming-the-witness)) | Implemented | `collections-design` |
| realization asserting its pre-realization type ([`TypedExprNode::Realize`]) rather than rewriting every enclosing mention of it | Implemented | `collections-design` |
| the **runtime witness** — a Σ value as a pair, with [`extent_of`] reading a domain off a *value*; retires the gated-partition re-typing arms and unblocks iterating a `Collection(𝑇)` | Planned | — |

### Realization notes

Three mechanisms behind the `[Implemented]` rows that are not obvious from the
rules, recorded because each was arrived at the hard way.

- **A domain refinement inside a type must be built *typed*, not `Hole`.** Only
  *node* annotations re-infer embedded predicates (`emit_annotation_predicates`); a
  *parameter* or *let* annotation does not, so a `Hole`-typed predicate on a
  non-discharged (parameter) collection strands unresolved `Infer`s at the
  post-inference wall. Both places this bites are now structured to avoid it rather
  than to work around it: an **annotation** carries no predicate at all (what the domain
  must satisfy is carried by the witness kind, so there is nothing to embed), and a
  **concrete** keyed domain's key token is
  stamped typed where it is minted — `keydom#id : 𝐾 ⇒ Bool` over the site's shared
  hole. That is why the token's type names the key: not decoration, but the thing
  that keeps a type-embedded predicate resolvable.
- **A collection-consuming UDF inlines because it is a capability.** `λ c →
  sum(c)` is `FunKind::Compute`, so it beta-reduces at each concrete call site,
  monomorphizing the abstract `Σ`/`Collection` parameter to the argument's
  concrete domain — the resolution op-conversion needs. Making the inline
  decision the function's *kind* (`inline::should_inline`) **replaces** the
  type-shape `is_iterable_domain` heuristic, the same anti-pattern as the retired
  `has_enumerable_extent`. The switch had to land with `groupby-keyed-collection`:
  only there is a `groupby` a `Data` arrow, which the old shape heuristic would have
  gone on inlining as a non-iterable domain.
- **Realization is demand-directed, so a restricted conditional is copied to each
  consumer.** A consuming site's filter rides the witness — `Σ 𝜎 ∈ 𝐾. ({𝜎 | 𝑝} ⤇ 𝑉)` —
  and the site can do nothing with it, having no extent for a witness. Realization can:
  inside leg 𝑖 the conditional *is* `armᵢ`, so the leg is gated twice, by its path
  condition `π̂ᵢ` and by `𝑝` rewritten to read that arm. Rewriting is what makes the fact
  *sayable* — a predicate may hold a plain arm but not a gated union, which needs the
  `iterate`/`restrict` a predicate is forbidden.

  The legs therefore carry one consumer's demand, and a `let`-bound conditional consumed
  twice has one set of legs and two. So planning copies a conditional to each consumer
  that restricts it and drops the binding, which also puts the `Case` back *below* the
  site that restricts it — a binding precedes its body by scope, so no traversal order
  reaches the demand first. An unrestricted conditional owes nothing and stays shared.
  The price is a union per restricting consumer; the runtime witness is what would let
  one materialized union serve several, by moving the filter back to the consumer.

  A site **names** its witness rather than being it: iterated beside a second generator
  the index is a product, so the same filter rides `{(𝜎, 𝐷) | 𝑝}`. Every rule keyed on
  "the witness this domain names" therefore matches a *mention* — which witness owes the
  restriction, and whether a site whose restriction was discharged into the legs still
  owes a `restrict`. Reading only the whole domain makes the product a silently different
  case: the second question answered wrongly emits the site's chain a second time, over a
  witness that has no extent.

- **A site's witnesses are realized together, so its legs are the combinations.** Two
  conditional generators nest two sums over one product domain —
  `Σ 𝜎₄ ∈ 𝐾₄. Σ 𝜎₇ ∈ 𝐾₇. ((𝜎₄, 𝜎₇) ⤇ 𝑉)` — and that is one site with two choices on it,
  not a site within a site. Realizing them one at a time nests the unions, and a nested
  union is wrong in the **term**, not merely in the type it records: a leg's gate is
  carried as a refinement on its domain, and the term-level `restrict` is emitted only
  where that domain heads an iteration, so wrapping the inner union — not an iteration
  site — drops the outer gate silently. Two legs are then live where exactly one may be,
  and the answer double-counts.

  So the legs are the tuples of arms, gated by the conjunction of their path conditions
  and indexed by the product of their domains. This is the same finite-Σ ≡ gated-union
  isomorphism stated for a product of witnesses rather than for one, and it is *flat*,
  which is what the term already is — `Expr::collection_union` flattens, so a
  one-at-a-time realization also disagrees with its own term about the tags.

  There is **one realization**, at the node whose type carries the choice: the outermost
  `Σ` binding the witness, or the `Case` itself when the arms share a domain and no type
  above mentions the choice at all. That second case is degenerate rather than separate —
  one choice, and substituting the arm for the conditional at the site leaves the arm.
  Realizing at the site is also what retires a restriction *map*: the site that placed the
  restriction is the site being copied, so the filter is already inside the leg, and there
  is nothing to carry down from an ancestor.

The rest of this document is the design of record for every row above.

### Injecting a domain that has no shape yet

The term that builds a sum forms the dependent pair `(𝐷, body)` for
`List(𝑇) = Σ (𝐷: UIntRanges). 𝐷 ⤇ 𝑇` from a concrete `𝐷 ⤇ 𝑇`. It succeeds iff the
concrete domain is a **member of the kind** — for `UIntRanges`, iff it is a
`UIntRange`. That is a *membership predicate on the domain's shape*, **not** a subtype
constraint that records a bound. The distinction is load-bearing given how the
MLsub-style solver works.

(A kind that carries a **parameter** is the one exception, and it proves the rule:
`Keyed(𝐾)`'s key type cannot be checked by inspection, so containment hands it back
as an obligation the width arm *does* discharge as a constraint. Shape is checked;
parameters are related. See [Representation](#representation-the-key-domain-is-opaque-decided).)

This is a Σ (dependent **sum**), not an ∃ (existential): the witness is
**retained and projectable**, not sealed. The list's length rides in the value
(it *is* the domain's size — `len` is the first projection `π₁`), so
Building a sum pairs a witness that is already present in the runtime
`SealedFunction` — the pairing copies nothing (runtime-free). The same holds for
the keyed domain (`keys` = `π₁` of a `Map`/`Set`).

- A **literal**'s domain is a concrete `UIntRange` already at constraint-emission
  time, so the predicate runs immediately in `TypeKind::contains`
  (`solver/constrain.rs`).
- A **computed** collection — a comprehension, `set`, or `groupby` — has a
  domain that is still an inference *variable* at emit time; it resolves to a
  concrete domain (`[0, 𝑘)`, `source(…)`, a key domain) only at
  coalesce. The predicate cannot run yet, and it must not be *forced* into a
  subtyping constraint: demanding `domain <: [0, 𝑛)` adds that as an upper
  bound on the domain variable, which then collides with the domain coalesce
  independently resolves it to (`[0, 𝑘]`) — "Incompatible upper bounds".

What the second case needs is a constraint of a **different kind**, not a deferred
check. "Whatever this variable resolves to must inhabit 𝐾" is not a relation to any
type — no 𝑇 has `α <: 𝑇` iff `α` is a range — so it is recorded as a **kinding
constraint** on the variable, in a third slot beside its lower and upper bounds
([`InferBounds::kinds`]). From there it takes the route every other constraint on a
variable takes: compaction folds it into the position the variable contributes to, and
coalesce discharges it against the type that position materializes to. A range
discharges; a source or membership refinement is a mismatch, reported as the
collection-annotation error it is.

Nothing is left over afterwards, and that is checked rather than assumed: post-coalesce
there is no constraint graph to emit into, so `contains_ground` — the same containment
under the discharge available without a graph — requires the residue to be empty. A
variable still shapeless at that point is one that never resolved, which is a genuine
failure. Sharing `contains_ground` with the compact-domain lattice is what keeps the two
ground discharges from drifting apart from the Σ-width rule they must agree with.

Two things follow, and both simplify the design rather than complicate it. First, a
candidate is undecidable **only** when it is a bare variable — any other head is already
readable by the predicate, so `{[0, 𝑘) | 𝑝}` is a `Refinement` and therefore not a
`UIntRange` no matter what 𝑘 becomes. The constraint attaches to variables, never to
arbitrary types. Second, because the constraint carries types it has the same level
exposure as a bound: `extrude` and `freshen_above` carry it, or a scope boundary
launders it away and every use site of a generalized definition silently type-checks
([type-inference.md, What the kind level needs from the
solver](type-inference.md#what-the-kind-level-needs-from-the-solver)).

There is no annotation left on the tree to re-check against by then — monomorphization
rebuilds the `let` and drops `user_annotation` (the binding becomes an anonymous
`__mono`) — which is why the requirement has to live on the *variable* rather than be
recovered later from the syntax. A keyed producer needs no separate mechanism for the
common case (lowering writes its key domain down, so the shape is already concrete); the
general unresolved keyed case reuses this one unchanged.

## The domain family

A data function's domain has several species. Today three exist; this
design adds the fourth (keyed) and makes a fifth (the Σ witness) fully live.
The organizing distinction is **positional vs. content-addressed** and
**static vs. opaque**:

| Domain | Positional? | Domain known | Element type | Ordered |
|---|---|---|---|---|
| `UIntRange(n)` | yes | static (`usize`) | `{𝑖: UInt \| 𝑖 < 𝑛}` | yes |
| `source(name)` / `Txn` / `ChanDom` | by arrival | opaque | positions | arrival only |
| **key domain** *(new)* | no | opaque, per-site | `{𝑘: 𝐾 \| 𝑘 ▷ keydom#id}` | no |
| **Σ witness `𝐷`** *(activated)* | inherits `𝐷` | opaque, kind-classified | inherits `𝐷` | inherits `𝐷` |

The last two rows are **one primitive**: a *referenceable opaque domain* — a domain
that is (a) opaque (no static enumeration), (b) identified rather than enumerated,
and (c) usable as the domain of a data function. That is verbatim what the Σ
**witness** apparatus provides: the witness is a *type*, classified by a
[`TypeKind`], and a concrete domain is a member of that kind. A key domain is a
`Keyed(𝐾)` member, named by an opaque per-site token; the ≥ 2 control-flow join is
an `Enumerated` witness (a sum of domains); a `List`'s is a `UIntRanges` member.
This design *activated* it. See
[The referenceable opaque domain](#the-referenceable-opaque-domain).

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
- **`Map(𝐾, 𝑉)`** = `Σ (𝐷: Keyed(𝐾)). 𝐷 ⤇ 𝑉` — a key domain; a *concrete* one's keys
  are typed `{𝑘: 𝐾 | 𝑘 ▷ keydom#id}`. Unordered. Lookup `𝑚[𝑘] : Option(𝑉)` in
  general, `: 𝑉` when presence discharges (see
  [Lookup](#lookup-membership-discharge)). Membership `𝑘 in 𝑚`.
- **`Collection(𝑇)`** = `Σ (𝐷: Any). 𝐷 ⤇ 𝑇` — the witness ranges over *every*
  domain; the domain rides along **in the value** (retained, not sealed — a
  domain-generic consumer holds it abstract). Unordered. The ⊤ of the kind order, and
  nothing more: keyed-ness lives in `Keyed(𝐾)`, so `Collection(𝐾)` is *not*
  load-bearing for `Map`/`Set` (the key-set-witness design that made it so was
  rejected — see [The referenceable opaque
  domain](#the-referenceable-opaque-domain)).

  This is the type that most needs the witness to be **real at runtime**, and the
  reason is one line of user code: iterating a `Collection(𝑇)` parameter has to find
  the actual domain, and there is no static one to read. Every other collection type
  can be, and today is, served by a domain recovered from its *static* type. That
  makes `Collection(𝑇)` the general case and the conditional collection the special
  one, not the other way round — see [Future work](#future-work).

`Dict(𝐾, 𝑉)` is the surface spelling of `Map(𝐾, 𝑉)`; there is no separate type.

## The referenceable opaque domain

The one new type-level idea. A data function may quantify its domain over a
**witness** `𝑛`, whose members it does not statically know but can *name
and refine*:

- **Σ join (sum, ≥ 2 choices)** — the existing use, from control-flow merges:
  `Σ 𝑛 ∈ {𝐷₀, 𝐷₁}. 𝑛 ⤇ 𝑉`. Already materialized by coalesce; the witness
  `name` is stripped today because no predicate references it.
- **List runtime length (single range witness)** — `Σ 𝑛. [0, 𝑛) ⤇ 𝑇`, `𝑛` an
  opaque `Nat`. The codomain does not reference `𝑛`, but the *element* type of
  the domain does (`{𝑖 | 𝑖 < 𝑛}`), which is what makes lookup partial.
- **Map / Set keyed domain** — `Σ (𝐷: Keyed(𝐾)). 𝐷 ⤇ 𝑉`, over the kind of *every*
  key domain on 𝐾. The annotation is the abstract map: it says "keyed by 𝐾"
  without naming which keys.

**Representation — a witness *kind*, not a value and not a new leaf.** Every
witness is a **type**, classified by a [`TypeKind`], and a keyed collection is
`Type::Sigma` over `TypeKind::Keyed(𝐾)`:

```
Map(𝐾, 𝑉) = Σ (𝐷: Keyed(𝐾)). 𝐷 ⤇ 𝑉
Set(𝐾)    = Σ (𝐷: Keyed(𝐾)). 𝐷 ⤇ unit
List(𝑇)   = Σ (𝐷: UIntRanges). 𝐷 ⤇ 𝑇
```

The three lines are the same shape with a different kind, which is the whole
point: `Map` needs no rule of its own, only a kind. Subtyping is the [single Σ
rule](type-inference.md#46-data-vs-compute-functions)
— kind containment plus body subtyping — and a concrete keyed collection reaches
`Map(𝐾, 𝑉)` by that same rule, once `box` has made it a one-candidate sum.

A **concrete** keyed collection is what the kind ranges over: one specific key
domain, written `{𝑘: 𝐾 | 𝑘 ▷ keydom#id}` where [`Builtin::KeyDom`] is an **opaque
per-site token**. The token says "the keys of *this* collection" and nothing more;
`keydom#id : 𝐾 ⇒ Bool` is the characteristic function of that domain, and there is
no way to look inside it.

**Why a token rather than a term.** The alternative — and the earlier design — put
the key *set* in the type: `{𝑘: 𝐾 | 𝑘 ∈ 𝐸}` over a `Collection(𝐾)`-typed witness
`𝐸`, with `𝐸` instantiated to the producer's inlined key-image term `c ≫ key`. That
worked, and what it cost is instructive:

- A whole **term lived inside a type**, and after planning compiled it to
  point-free form, a compiled operator graph did. Type identity became structural
  comparison of that graph.
- The term was there **only to carry a type**. The `∈` atom is never executed; its
  second argument existed so a shared-variable scheme `∀κ. (κ, Collection(κ)) → Bool`
  could link the key type to the producer. That is a type-level identity smuggled
  through a term, which is what [`Type::SharedHole`] now states directly.
- The witness needed a type describing "the 𝐾s this map has", and `Set(𝐾)` would
  regress (a `Set` is itself keyed). `Collection(𝐾)` bottomed it out — a real
  resolution, but only because the key-set had to be a *value* at all.

With the token, identity is a `KeyDomId` comparison, the key type is pinned at the
producer, and `Keyed(𝐾)` is a kind like any other. `Collection(𝐾)` remains as the
`TypeKind::Any` top, no longer load-bearing for keyed-ness.

**What `Keyed` adds to the kind system: a parameter.** `Enumerated` *lists* its
candidates and `UIntRanges` *describes* its, so containment against either is a
decidable question about one kind. `Keyed(𝐾)` carries a **type parameter**, and
relating two types is subtyping's job — so containment does not decide it, it emits
the pair as an obligation the width arm discharges invariantly through the solver.
Emitting rather than testing is also what lets an open key type be *pinned* by the
kind it meets, which is what makes `Map(_, 𝑉)` inferable.

### Witness identity is minted at creation (load-bearing)

**Every concrete keyed collection's domain carries a fresh, per-site identity,
minted where the collection is created** — a map literal, a `groupby`, a feed-built
map each mint a distinct [`KeyDomId`], the way `ChanDom` mints a distinct channel
per `defer`. This is not a detail; it is the property that keeps the
[domain-join corner](#future-work) *escapable*. Two maps `𝑚₁, 𝑚₂ : Map(𝐾, 𝑉)`
have the same *surface type* but **distinct key domains** `𝐷ₘ₁ ≠ 𝐷ₘ₂`, so a join
`𝑚₁ if 𝑐 else 𝑚₂` is representable as `Σ (𝐷 ∈ {𝐷ₘ₁, 𝐷ₘ₂}). 𝐷 ⤇ 𝑉` and a
membership proof against `𝐷ₘ₁` is never confusable with one against `𝐷ₘ₂`.

The failure mode this rules out: a *shared, anonymous* key domain — one `KeyDom`
leaf for all maps. Under that, two maps would be indistinguishable types, a join
would silently pick one domain and drop the other's rows, and a lookup proof from
one map would wrongly discharge against another. That is unrecoverable — you cannot
retrofit identity onto values that were already conflated, which is why this is a
**step-0 obligation** (see [roadmap](#implementation-roadmap)) rather than a later
refinement.

It costs nothing: it is how `ChanDom` / `DataSource` already work, and the token
carries it directly (`key_domains_are_per_creation_site` pins it). Worth noting what
changed — before the token, this property held only *incidentally*, because the
domain embedded the producer's key-image term and two producers happened to build
different terms. Identity is now the mechanism rather than a side effect of term
inequality, so the domain-join corner stays a localized future solver change
rather than a representational dead end. The runtime needs no identity — distinct
maps are distinct hash stores — so this is a compile-time-only obligation.

## Operations: how the trait layer is realized [Planned]

> The **user-facing semantics** of `for`-in, `[]` / `[]?`, `in`, and ordering —
> what each collection kind binds and returns — are specified in the spec
> ([chl-spec §3.9](../../../docs/chl-spec.md#39-subscript-and-attribute-access),
> [§4.6](../../../docs/chl-spec.md#46-for--iteration),
> [§6.3](../../../docs/chl-spec.md#63-direction-collections-as-functions-decided)),
> not here. This section
> is the **implementation design**: how those operations dispatch on the
> collection's type and reuse the machinery below.

Operations are **trait**-dispatched **on the collection's nominal kind** —
`List`/`Array`/`Set`/`Map`/`Collection` are distinct type heads, and each carries
its own instance of `Iterable`, `Index`, `Membership`, and `Ordering`. Dispatch is
on the *declared* kind, **never** read back from the representation's domain/
codomain shape — that derivation is brittle (a `Map(UInt, V)` and a filtered
`List` share a shape but not their operations; see
[Two axes](#two-axes-representation-vs-kind-decided-direction-representation-tentative)). Traits are a future mechanism
(typeclasses resolved by the given/`using`/`summon` solver,
[chl-spec §8](../../../docs/chl-spec.md#8-mutability-transactions-and-feeds)); until then each operation is a
**built-in dispatch on the kind**, and when traits land these built-ins *become*
the per-kind standard-library instances with no semantic change. Everything here
is [Planned].

**"Keyed-ness" is not a primitive.** There is no structural "keyed" property to
test: every collection is a function of its domain, so the domain elements are
always the keys in the only sense that exists. What differs per kind is **which
side of `𝐷 ⤇ 𝑉` is the payload** — the codomain (`List`/`Array`/`Collection`), the
domain (`Set`), or both (`Map`). That is precisely the `Iterable` instance,
selected by the nominal kind, not inferred from the arrow.

- **Iteration (`Iterable`).** `for`-in binds what the kind's `Iterable` instance
  yields — values (`List`/`Array`/`Collection`), keys (`Set`), or `(key, value)`
  entries (`Map`). Because that is chosen by the kind, and the kind is known only
  after inference, the binding **cannot be fixed at lowering** (pre-inference); it
  is resolved at **coalesce**, once the node's type (hence kind) is known — the
  same hook a [kinding constraint](#injecting-a-domain-that-has-no-shape-yet)
  is discharged at. The realization is cheap: the loop encoding already threads the domain
  element as `__iter_record` (`comprehension.rs`), so binding the domain, the
  codomain, or both is a choice of *which* slot to bind, not a materialization.
  **[Interim]:** today the loop binds the codomain unconditionally (a map iterates
  values, as `groupby` results do); the per-kind element choice is the [Planned]
  work and only *adds* cases — it does not change the tuple-binder form.
- **Lookup.** The two operators `[]` (proven) / `[]?` (optional) are the surface;
  their single shared mechanic — a domain-membership refinement that either
  discharges (`: 𝑇`) or does not (`: Option(𝑇)`) — is
  [Lookup: membership discharge](#lookup-membership-discharge) below.
- **Membership (`in`).** `Map`/`Set`'s instance tests the domain, `List`/`Collection`'s
  the codomain (Python semantics). A key-membership guard refines the key (`if k in
  m` ⟹ `k` carries the domain-membership proof), which is what a proven `[]` needs.
  **How** membership is expressed in the representation is an *implementation detail*
  of `Map`'s instance, **not** a type-level keyed marker — the nominal kind is the
  marker. It is settled: an opaque `𝐾 ⇒ Bool` key token applied `𝑘 ▷ keydom#id` (see
  [Representation](#representation-the-key-domain-is-opaque-decided)).
- **Order.** Sequentiality is deduced from loop-carried dependencies and ordering
  is supplied as an `Ord` given, never fabricated — [Ordering](#ordering) below.
- **Views (`keys` / `values` / `items`).** `Map`'s projection operations, each a
  **lazy view** — no copy: `keys(m) : Collection(𝐾)` (the key set), `values(m) :
  Collection(𝑉)` (the map's own arrow), `items(m) : Collection((𝐾, 𝑉))`
  (`𝑘 ↦ (𝑘, 𝑚(𝑘))`). Turning a `Map` into a `Collection(𝑉)` is a **re-pairing**
  (project the key set, re-introduce over domain `{𝑘 | 𝑘 ∈ keys}`) — a perfectly
  a good way into a sum, runtime-free (`m` already carries its keys as its domain),
  *not* a fundamental obstacle. `values(m)` is nonetheless the form a user should
  write, because `for x in m` binds entries while `for x in (m : Collection(𝑉))`
  binds values, and the explicit projection is what makes which one is meant
  visible — matching [chl-spec §6.3](../../../docs/chl-spec.md#63-direction-collections-as-functions-decided).
  What *enforces* that is the **iteration element**, not a withheld subtyping edge:
  the implicit `Map <: Collection(𝑉)` edge holds (⊤ absorbs every kind), and
  `sum(m)` is rejected once `sum` lowers through iteration, because a `Map` yields
  `(𝐾, 𝑉)` entries and entries cannot be summed. Until then `sum(m)` means
  `sum(values(m))`; see step 3 of the [Implementation
  roadmap](#implementation-roadmap). (Whether `keys` is literally the Σ's first
  projection or the data function's domain projection depends on the representation —
  see the note below.)

### Representation: the key domain is opaque [Decided]

Because operations dispatch on the kind rather than on the arrow, the
*representation* of a keyed collection's key set is a free internal choice —
unobservable at the type level, carrying no semantic weight of its own. Of the two
candidates considered, the **characteristic-predicate** form won, in its opaque
variant: `Map(𝐾,𝑉) = Σ (𝐷: Keyed(𝐾)). 𝐷 ⤇ 𝑉`, where a concrete `𝐷` is
`{𝑘 | 𝑘 ▷ keydom#id}` — a domain refined by ordinary application of an **opaque**
`𝐾 ⇒ Bool` token.

The rejected alternative was the **key-set witness**:
`Σ (𝐸: Collection(𝐾)). {𝑘 | 𝑘 ∈ 𝐸} ⤇ 𝑉`, the domain refined by an `∈` atom over a
nested `Collection` Σ. It works, and it is what was built first; the reasons it lost
are in [The referenceable opaque domain](#the-referenceable-opaque-domain) above —
chiefly that the witness had to be a *value*, so the type ended up carrying a term
that existed only to carry a type.

Choosing the *opaque* predicate over a transparent one is the second half of the
decision, and it is what makes `keys(m)` and identity behave. A transparent
predicate (`{𝑘 | ∃ 𝑖. key(c(𝑖)) == 𝑘}`, `groupby`'s natural refinement) would put the
producer back in the type and need an ∃ the language does not have. An opaque token
says only "the keys of this collection", which is exactly the information the type
layer needs: enough to distinguish two maps, never enough to require evaluating
anything. `keys(m)` is the data function's domain projection either way — the key set
is its carried domain, and enumerability comes from the `⤇`, not the witness.

## Lookup: membership discharge

> **[Planned]** — no lookup path exists today (surface subscript is
> integer-literal tuple projection). The surface operators — proven `c[k] : 𝑇`
> and checked `c[k]? : Option(𝑇)` — are specified in
> [chl-spec §3.9](../../../docs/chl-spec.md#39-subscript-and-attribute-access). This section is the **discharge
> mechanic** they rest on: the single rule that decides which one type-checks.

Lookup is uniform across ranges and keys: `𝑐[𝑥]` is well-typed when `𝑥`'s type
proves `𝑥 ∈ dom(𝑐)`, and its result totality is *whether that proof
discharges*.

- Membership rides on the **element's** type, not the collection's. Iterating a
  collection's own domain hands you the proof:

  ```
  m : E ⤇ V
  for (k, v) in m:          # k : {k: K | k ∈ E}
      m[k]                  # : V        — k ∈ E discharges → TOTAL
  ```

- A key from outside carries no proof, so the **proven** operator `m[k]` is a
  type error; the **checked** operator `m[k]?` returns an option:

  ```
  m[req.body.sku]           # type error — cannot discharge k ∈ E; use m[…]?
  m[req.body.sku]?          # : Option(V) — the checked operator
  ```

This is the same rule the range case wants: `arr[𝑖]` is `: 𝑇` when `{𝑖 | 𝑖 <
𝑛}` discharges (an `Array` index, a comprehension index), and `lst[𝑖]?` is `:
Option(𝑇)` where the bound cannot be discharged (`List`, unknown length — bare
`lst[𝑖]` there is a type error). One discharge mechanic covers Array/List and
Set/Map — `arr[i]:T` / `lst[i]?:Option(T)` and `m[k]:V` / `m[k]?:Option(V)` are
the *same* split on whether the domain-membership refinement discharges, spelled
with the two operators `[]` / `[]?` ([chl-spec §3.9](../../../docs/chl-spec.md#39-subscript-and-attribute-access)).
(Neither lookup path exists today — surface subscript is integer-literal tuple
projection — so this is new, but it is a single mechanic, not one per collection
kind.)

`Option` is the tagged variant `some(𝑣) | none`, matched with `match` — the
`Variant` / `VariantProject` / `VariantWrap` CCL nodes the conditionals stack
landed. The surface `match` / `some` / `none` are shared with `txn_kv` and are
not collection-specific.

### Prerequisite: the proof has to survive being consumed

The rule above is stated against the **sealed** keyed collection, where the key's
type literally reads `{𝑘: 𝐾 | 𝑘 ▷ keydom#id}`, naming the collection's key domain. That is
not the form a consumer sees. Consuming a sum deliberately **does not** present the
refined domain: it presents the sum `σ` itself, precisely so the witness binder cannot
escape into the consumer's result (a `map`'s result domain must not mention a binder
with no enclosing Σ — see the `Σ <: Fun` arm in `constrain.rs`). So after opening, an
iterated key is a consumed sum's witness, not a membership-refined `𝐾`, and `𝑘 ∈ 𝐸` has nothing
to discharge *against*.

This is a real gap, not a detail of the surface syntax, and it is the first thing
lookup has to settle. The apparatus for it is already there: the presented domain
*is* the whole consumed Σ, so it is identity-bearing — `𝑘 : σ` together with `𝑚 : σ` is
exactly the pairing a discharge needs (*this* key came from *that* map). Two shapes
are then possible and the choice is open: teach the discharge to relate a key typed at
the named `σ` to `σ`'s own membership refinement, or have the consuming rule present a domain
that keeps the refinement *and* binds the witness once for both the key and the
collection (a proper consumption binding both components rather than naming
per-use). Either way it lands before, not with, the `[]` / `[]?` surface.

## Ordering

> **[Planned]** — the `Ord` given and ordered operations are designed, not built.
> User-facing ordering rules (unordered/parallel `for`-in, sequentiality) are in
> [chl-spec §4.6](../../../docs/chl-spec.md#46-for--iteration).

Ordering is **derived from the domain species, not stored** — no per-collection
ordering flag.

- **Positional / sequencing domains** (`UIntRange`, `Txn`, induction /
  `source` domains) are totally ordered by construction — the mutability model
  already relies on this ("each sequencing domain is a total order"). Ordered
  operations (positional index, first/last, ordered folds) work directly. So
  `Array` and `List` are ordered because their domain is a range.
- **Keyed / opaque domains** (`Set`, `Map`, `Collection`) carry no intrinsic
  order. An order-dependent operation over them requires an `Ord[𝐾]`
  **given** — supplied through the same contextual-parameter mechanism the spec
  gives `Transaction` ([chl-spec §8](../../../docs/chl-spec.md#8-mutability-transactions-and-feeds)). No order is
  fabricated for an unordered domain; the operation simply does not typecheck
  without the instance.

This reuses infrastructure that exists (sequencing-domain order) or is already
designed (the given/typeclass solver), and matches the spec's decision
([chl-spec §3](../../../docs/chl-spec.md#3-expression-semantics),
[§6.3](../../../docs/chl-spec.md#63-direction-collections-as-functions-decided)): `Array`/`List` ordered,
`Set`/`Map`/`Collection` unordered-with-explicit-ordering.

## Subtyping

Collection subtyping *is* data-function subtyping; the arms are those in
[type-inference.md §4.6](type-inference.md#46-data-vs-compute-functions),
most already implemented.

- **`Data <: Compute`** — a collection used as a capability upcasts; a
  `Compute <: Data` is rejected (a capability where a collection is demanded is
  silent row-loss). Landed.
- **Codomain covariance** — `𝐷 ⤇ 𝑉₀ <: 𝐷 ⤇ 𝑉₁` when `𝑉₀ <: 𝑉₁`. Landed.
- **`Array <: List` is not an edge.** Only a term builds a sum
  ([type-inference.md, Introduction is a
  term](type-inference.md#only-a-term-builds-a-sum)), so an array reaches a `List(𝑇)`
  by being boxed: `box(arr) <: List(𝑇)`, discharged by ordinary Σ-width — the listing
  `{[0, 𝑛) ⤇ 𝑇}` against the description `UIntRanges`, which picks the array's own
  domain as the witness. The membership test that width runs
  — `[0, 𝑛) ∈ UIntRanges` — is what keeps a *filtered* range out, since a
  `Refinement` is not a `UIntRange` and domain invariance leaves width no other
  candidate to choose. The guard is reached through the ordinary rule rather than
  written twice.
- **Refinement width on the domain** — `{𝑘: 𝐾 | 𝑝 ∧ 𝑞} ⤇ 𝑉 <: {𝑘: 𝐾 | 𝑝} ⤇ 𝑉`:
  a more-constrained-key map (a sub-map, a `restrict`ed collection) is a
  subtype. Landed (the refinement-width arm).
- **Width to the top** — `Σ <: Collection(𝑉)`: the `TypeKind::Any` witness admits
  every domain, so any lhs witness kind is contained in it and width reduces to
  codomain covariance. `Collection(𝑉)` is therefore the top **of the sums** — `List`,
  `Map`, `Set` and a boxed collection all widen to it, keyed lhs included, because ⊤
  absorbs structurally rather than by a row per kind and a `Map(𝐾, 𝑉)` genuinely *is*
  a data function with codomain `𝑉`.

  It is **not** a top of the whole collection lattice: a bare `𝐷 ⤇ 𝑉` is not below it,
  because that edge would build a sum. This is the one place the explicit-`box`
  decision is felt in ordinary code — an array or a comprehension result reaches a
  `Collection(𝑉)` parameter by being boxed. It has to be that way round: a structural
  top is an upper bound of *every* pair of data functions, so keeping the edge would
  make every collection join succeed silently and widen maximally, which is the
  behaviour `box` exists to surface.

  The reason to write `values(m)` anyway, and what rejects `sum(m)`, is the iteration
  element rather than this edge (see
  [Views](#operations-how-the-trait-layer-is-realized-planned) and
  [chl-spec §6.3](../../../docs/chl-spec.md#63-direction-collections-as-functions-decided)).
- **`Set(𝐾)` vs `Map(𝐾, unit)`** — no subtyping arm relates them, because with the
  kind unrepresented they are the *same type* — a set constructor delegates to the map
  one. Under the [tentative
  direction](#two-axes-representation-vs-kind-decided-direction-representation-tentative)
  they become distinct **nominal heads**, and the relation between them (if any) is then
  a deliberate declaration rather than a structural accident. That is the *only* edge
  nominality turns into a decision: the width-to-top edge above still holds for both,
  because widening forgets the head.
- **Domain invariance** — inherited, not work to do. A data function's domain
  relates only to itself, in both halves: a wider or narrower base is rejected
  because ranges compare by equality, and *neither* refinement direction holds
  ([type-inference.md, Data domains are
  invariant](type-inference.md#data-domains-are-invariant)). Two consequences the
  collection types must be designed against, since an earlier sketch of this
  section assumed the opposite of the first:
  - A *filtered* collection `{[0,𝑛] | 𝑝} ⤇ 𝑉` does **not** flow where `[0,𝑛] ⤇ 𝑉`
    is declared. Dropping a domain refinement looks sound — [`extent_of`] strips
    refinements anyway, so it is invisible to iteration — but it is not sound for a
    consumer that discharges membership, which is exactly what a keyed lookup does:
    a filtered list keeps the source's index numbering, so the coarsened type
    licenses proving `1 ∈ [0, 2]` while the `Filter` may have removed index 1.
  - A collection cannot **acquire** a domain refinement by subsumption either, so
    keyed entry needs the explicit
    [`Cast`](ir.md#cast--explicit-refinement-acquisition) rather than an implicit
    edge.

## Deferred keyed collections

> **[Planned].**

A collection can be *defined incrementally* — declared, then contributed to from
elsewhere in the program (`𝑐 << 𝑒`, `𝑐[𝑘] = 𝑣`), the way a `Feed` is. The
critical decision here is **what type such a thing has**, and it is *not*
`Feed[Set(𝐾)]` / `Feed[Map(𝐾, 𝑉)]`.

**No sequencing layer for unordered collections.** A `Feed[𝑉]`
(`Type::History { kind: Append }`) is a function over a *contribution /
sequencing domain* — it exists to remember *which* contribution a value came
from, i.e. to keep a stream's positions (or a bag's duplicates) distinct. A
`Set` / `Map` is **unordered and deduplicated**: the sequence of writes is not
observable, so there is nothing to track. Wrapping it as `Feed[Set(𝐾)]` =
`𝐷 ⤇ Set(𝐾)` imposes an extra `𝐷 ⤇` function layer that the
semantics never uses. So a deferred keyed collection is exposed as **the
collection type itself** — `Set(𝐾)` / `Map(𝐾, 𝑉)`, i.e. one arrow over a key
domain, contributed *directly into that domain*, with no contribution domain.

**Write permission is a type-level distinction (open vs. closed).** Whether a
collection may still receive contributions is carried in its type, exactly as
feed-ability and mutability are ([chl-spec §6.2](../../../docs/chl-spec.md#62-non-purity-as-type-wrappers),
"impurity is a type wrapper"): the write operator demands the open type, and a
closed binding does not have it.

- An **open / deferred** keyed collection is `Type::History { kind: Append }`
  *during inference and checking* — the same feedability marker feeds use. A
  keyed collection declared without an initializer (`reach_feed: Set({src,
  dst})`) mints an open key domain (the keyed, element-typed instance of the
  channel-flavored `ChanDom` a `defer()` already mints) under that marker.
- A **closed / immutable** collection — a `set([…])` literal, or any `= {…}`
  initializer — is a plain `Fun { kind: Data }`, no `History` marker.
- `𝑐 << 𝑒` / `𝑐[𝑘] = 𝑣` **requires** the target to be `History { Append }`
  (open). So `m: Map(Int, Int) = [1 -> 2, 4 -> 5]` binds `m` at plain
  `Fun { Data }`, and `m[3] = 7` is a **type error** — the same mechanism that
  rejects `x = 5; x << 3`. An already-defined immutable collection cannot be
  extended, by construction.

**This does not reintroduce a wrapper layer** — that is the whole point of the
keyed domain. A *bag* feed's `History { Append }` has a *separate anonymous
contribution index* as its domain (`𝐷 ⤇ 𝑉`), because a multiset must hold
duplicates. A *keyed* collection's `History { Append }` has **its own key domain
`𝐷` as the domain**, so `History { Append, domain: 𝐷, value: 𝑉 }` and the closed
`𝐷 ⤇ 𝑉` are the *same arrow* — the marker tags the domain's open-ness, it does
not wrap the collection in a second `𝐷 ⤇` function. Like every `History`, it is
transient: `channelize` erases the marker and closes the domain (resolving the
open `ChanDom`-flavored domain to its concrete value), leaving a plain
`Fun { Data }`. So the open/closed distinction is present precisely when the
checker needs it — when it must accept or reject a write — and gone by planning.

**Merge law by collection kind.** Contributions combine by the collection's
lattice join — set union (`Set`), keyed define / last-write-wins (`Map`) — which
is **idempotent / order-insensitive**, which is *why* no sequencing domain is
needed. The well-formedness condition ([chl-spec
§6.3](../../../docs/chl-spec.md#63-direction-collections-as-functions-decided):
"multiple out-of-line definitions don't overlap") is that two defines at one key `𝑘` conflict unless
the merge is idempotent (`Set`) or last-write-wins (`Map`). Contrast a **bag
feed** (`orders: Feed({…})`, `ledger: Feed({…})`) — a multiset with no key, no
dedup — which *does* need the anonymous contribution index to hold duplicates
and stays `Feed[𝑉]` = `𝐷 ⤇ 𝑉`. So the fork is keyed/unordered/idempotent →
bare collection type, no sequencing; unkeyed/multiset → `Feed` with an index.

Surface forms, all direct-into-domain (no `Feed` layer):

- **`resps[req.id] = 𝑣`** (`txn_kv`, `storefront`) — the response collection is
  `Map(RequestId, Response)`, keyed by the request id; the assignment defines it
  at key `req.id`. This *is* the existing "`http_serve` pairs each response with
  its request by shared domain" contract ([chl-spec
  §7.4](../../../docs/chl-spec.md#74-sources)), now explicit: the pairing
  is keyed, not sequenced. `channelize` routes the contribution to key `req.id`.
- **`reach_feed << 𝑒` where `reach_feed: Set(…)`** (`reachability`) — codomain
  `unit`, the key domain *is* the payload, merge idempotent set union.

Collections and feeds are still the one `𝐷 ⤇ 𝑉` object; the difference from the
bag-feed case is that a keyed, unordered, idempotent collection needs neither a
sequencing domain nor a `Feed` wrapper — it is contributed straight into its own
key domain.

## Recursive keyed collections (fixpoint)

> **Status: model specified here; the fixpoint engine is deferred** (a roadmap
> item, north-star `reachability`).

`reachability` feeds `reach_feed` from a loop *over `reach_feed` itself* — a
transitive closure. This is a **recursively-defined keyed collection**, and its
well-foundedness is *different in kind* from every recurrence
[mutability.md](mutability.md) handles:

- Those cycles are well-founded by **causal position-decrease**: a `get_prev_*`
  reads strictly-earlier positions of a sequencing domain. mutability.md states
  *"an append feed carries no carry-forward, so channels never close a causal
  cycle"* — true for the output feeds it considered, but `reach_feed`'s self-feed
  closes a cycle through its **whole value**, which the causal check would reject
  (the "non-causal cycle → compile error" row of `plan_loops`).
- A recursive keyed collection is instead well-founded by **monotone convergence
  on a bounded lattice**: each round adds elements, the collection's join is
  idempotent, so the sequence increases monotonically to a **least fixpoint** in
  finitely many steps (semi-naive Datalog evaluation).

**Keyedness is the enabling condition for recursion.** The fixpoint converges
*because* the collection is a lattice with an idempotent join — a `Set`/`Map`.
A plain multiset `Feed` (bag) has no idempotent join, so a recursive bag feed
diverges: this is exactly why `reachability`'s own comment says a `List` "would
be multiset semantics… and never terminate." So "how a deferred keyed
collection works" is not only about routing one write — the keyed (dedup /
lattice) merge law is *what makes deferred definition safe to make recursive*.
The `rec` set-comprehension form in the same program is the immutable dual of
the same fixpoint.

**Two well-foundedness rules for `LetRec`.** The `LetRec` node is already
general enough ([mutability.md](mutability.md#letrec): "recursively-defined
collections… all target the same node"); what it needs is a **second**
admissible cycle shape beside causal-decrease:

- *causal* — every cycle crosses a `get_prev_*` accessor (position strictly
  decreases). The existing rule, for overwrite/sequenced histories.
- *monotone-lattice* — every cycle's binding is a lattice-valued collection
  (`Set`/`Map`) whose recursive references are **monotone** (union / insert, no
  removal), so the group has a least fixpoint. The new rule, for recursive keyed
  collections.

**Reconciliation with the causality claim.** mutability.md's "feeds never close
a causal cycle" is not contradicted — it is *scoped*: an *unordered, idempotent*
collection closes a cycle that is well-founded by lattice monotonicity rather
than causal decrease, a discipline the mutability model does not use (its feeds
are outputs, not recursive lattice accumulators). The two disciplines are
disjoint and both live under `LetRec`.

**Engine (deferred).** The monotone-lattice cycle needs a **fixpoint-iteration
engine** — semi-naive evaluation to convergence — as a third loop-planning
pattern beside `InductionStore` and the commit operator. Specifying it (delta
maintenance, convergence detection on the bounded lattice, stratification) is
out of scope here; recorded as a roadmap item with `reachability` as its
north-star. Until it lands a recursive keyed collection is rejected (the
`plan_loops` non-causal-cycle error), not silently mishandled.

## Mutable collections

> **[Planned].**

A mutable collection is a register whose *value type is a collection*:
`inventory: Mut[Map(𝐾, 𝑉), Txn]`, written `inventory[𝑘] := 𝑒`. It is the
**keyed generalization of the compound (tuple/record) registers** the stack
already carries: a compound register's write set is keyed by *static* fields
(`{𝑘₁: 𝑉₁, …}`); a mutable map's write set is keyed by *runtime* `𝐾` values.

The engine already stores this shape. The commit operator's store is an MVCC
log `Txn ⤇ (Key ⤇ Value)` ([mutability.md](mutability.md#the-runtime-engines)),
and a multi-variable atomic block already produces one shared record `{time,
writes: {𝑘₁: 𝑉₁, …}}` per commit with a **per-key view** through which each
variable's history reads. A mutable map is that store with the field-key set
made dynamic:

- **Point mutation** `store[𝑘] := 𝑣` is a point-write to a register of history
  `Txn ⇒ Map(𝐾, 𝑉)`; the per-key view `get_prev_txn` searches per `(register, 𝑘)`.
  The static compound case is the special case where the key set is a fixed record
  shape.
- **Global mutation** `store := 𝑚` (replacing the whole collection register with a
  new collection value) is the ordinary whole-register write — the register's
  value type is a collection, so it rides the existing `Mut[Coll, Txn] := …`
  compound-register write at the whole-value level, no per-key view. The two
  compose: a global write establishes a new key-set generation, point writes
  amend it. (Whole-collection-value writes are not yet exercised e2e — a
  verification item, not new engine work.)
- **Dynamic-key write-sets** are the genuinely new engine bit: the commit
  record's `writes` column is `𝐾 ⤇ 𝑉`, not a fixed `Record`, so the per-key
  view is parameterized by a runtime key.
- **Refinement discharge at the write site.** `Mut[Map(𝐾, {𝑞: Int | 𝑞 ≥ 0}),
  Txn]` (`nonneg_inventory`, `storefront`): each `store[𝑘] := 𝑒` must discharge
  the value refinement — the `stock >= qty` guard is what proves `𝑞 ≥ 0` on the
  committing branch. This is refinement discharge at a `MutWrite`, the write-site
  dual of the boundary-assert lifting in `discount_contract`.

Everything else — the causal `LetRec`, the commit-decision variant, the
per-key carry-forward — is the compound-register machinery unchanged.

## `groupby` is a `Map`

For `c: 𝐼 ⤇ 𝐴` and `key: 𝐴 → 𝐾`, the **exact type** of a group-by is a keyed
collection from present keys to their groups:

```
groupby(c, key) : (𝑘: {𝐾 | 𝑘 ▷ keydom#id}) ⤇ ({𝑖: 𝐼 | key(c(𝑖)) == 𝑘} ⤇ 𝐴)
                ≡ "a dependent Map(𝐾, group(𝑘))"
```

— the outer domain is *this* group-by's present-key domain, named by its own
[`KeyDom`](`Builtin::KeyDom`) token (so it injects into `Map(𝐾, _)` by kind
containment, and is not confusable with any other collection's keys); the codomain
is the group, the sub-collection of `c` whose key is `𝑘`. The codomain **depends on `𝑘`** (the
group's domain is `𝑘`-specific), so this is a *dependent* keyed collection — a
generalization of the non-dependent surface `Map(𝐾, 𝑉)`.

**Precise inferred type, non-dependent surface, bridged by the entry term.** The
surface `Map(𝐾, 𝑉)` stays non-dependent (fixed `𝑉`). `groupby`'s precise
dependent type is only ever *inferred*, never annotated, and **injects into**
`Map(𝐾, Collection(𝐴))` on annotation or uniform consumption — each dependent
group `{𝑖 | key==𝑘} ⤇ 𝐴` injects into `Collection(𝐴)` (any data function does).
So precision flows where it is produced (groupby → its immediate consumer) and
abstracts at the surface, the two coexisting through the existing entry term — no
dependent `Map` constructor is forced on every map. The one bill this defers is
**dependent lookup** (`m[𝑘] : 𝑉(𝑘)`), which comes due only when lookup is built.

**This is a fix, not new behavior.** `groupby` today mis-types its result as
`(𝑘: 𝐾) ⇒ (…)` — a **Compute** function **total over all of `𝐾`** (every key
yields a possibly-empty group). It "works" only because every consumer
immediately *eliminates* it and planning materializes just the present keys, so
the imprecise type never surfaces — until you try to hold a group-by as a
first-class value (a `Map`), where it infers as `𝐾 ⇒ …` instead of the keyed Σ.
The dependent codomain `{𝑖 | key==𝑘} ⤇ 𝐴` is **already present today** (handled by
the [dependent-application machinery](type-inference.md#5-ccl-specific-inference-rules)); the fix retains it and changes only the
*outer* arrow from `(𝑘) ⇒` (Compute, total) to the keyed Σ (Data, finite present
keys). See [type-inference.md
§4.6](type-inference.md#46-data-vs-compute-functions).

### Lowering realization: the key binder states its domain

Lowering builds the keyed Σ, and the term it builds is well-formed at every compilation
stage — no free variables, valid before and after inference. Two things say what
`groupby` is.

**The binder's domain is the present-key domain.** `__gb_k` is declared at
`{𝐾 | __elem ▷ keydom#id}`, where [`Builtin::KeyDom`] is an opaque per-site token stamped
`𝐾 ⇒ Bool`. It says "the keys of this collection" and nothing more. Nothing inside an
opaque refinement can pin `𝐾`, so the key type arrives from outside: one
[`Type::SharedHole`] written into both the binder's domain and `key_fn`'s codomain
annotation states that those two positions agree, which is the claim lowering can make
and neither type can yet.

**The kind is provenance.** A `data_fun(_, _)` annotation on the lambda makes `emit_node`
stamp `Data` onto the arrow `emit_lambda` builds — an arrow that already carries the
binder and this domain. No term crosses `⇒` to `⤇`, and nothing derives the kind from the
key domain, which is scalar.

So lowering emits, with the inner group a cast as before:

```
groupby(c, key)  ⟶  λ (__gb_k : {𝐾 | __elem ▷ keydom#id}) → cast(λ __gb_i → __gb_i ▷ c, {𝐼 | key(c(__elem)) == __gb_k} ⤇ 𝐴)
```

which infers as `{𝐾 | __elem ▷ keydom#id} ⤇ ({𝐼 | key(c(__elem)) == __gb_k} ⤇ 𝐴)` and
enters `Map(𝐾, …)` by Σ-width once `box` has made it a one-candidate sum.

**`Converse` discharges the token.** Planning recognizes the pointful site and rebuilds it
as `converse ≫ map` (`convert_groupby_pointful`). The two halves are typed at different
domains, and that split is what lets the rebuilt term's type say what the term does: the
key-extraction morphism `c ≫ key` yields plain keys, so it is typed at the bare `𝐾`, while
the partition `Converse` builds holds exactly the keys that occur, so it is stamped at the
present-key domain. One key type serving both roles either rejects the extraction or
understates the partition.

The token rides through to op-conversion on **types**, never as a term. Planning compiles
surviving predicates to point-free form, so a `keydom` atom appears in post-planning types;
what does not happen is a `Restrict`. `insert_iterate_markers` skips a key-domain layer
when it reifies a domain refinement into one, and `debug_assert_no_unexecutable_atoms`
asserts at the planning→op-conversion boundary that no token reached the term spine.

**Invariant — no iteration markers inside predicates.** A predicate that reads a
collection at the element (`__elem ▷ src ▷ 𝑓`, what a filter lowers to) holds a term that
also lives in the term tree, where planning wraps it in `iterate` markers; a move-site
discharge of a `let`-bound source into the predicate would otherwise drag those markers
into the type, where they make `simplify` churn (nested-`Compose` vs `flatten_compose`)
and diverge from inference's pre-marker copy. So the term→type substitution boundary strips the
neutral `iterate` marker (`ccl_utils::strip_iterate_markers`), keeping predicates
marker-free; a `restrict` marker (a filtered source in a membership predicate — a
future `𝑥 in filtered_coll`) is *not* stripped and is caught loudly by a debug
assert rather than silently mis-compiled. This is a general `Subst`/`simplify`
invariant, exercised by any predicate carrying a collection, not a group-by
special-case.

Everything else follows: the `storefront` `/stats` rollup

```
[key -> sum([o.price for o in g]) for key -> g in groupby(paid, \o -> o.sku)]
```

is "iterate a map's `(key, value)` entries, build a new map". **Iteration alone
does not hand you the key.** A keyed collection is a `Collection` in its
*codomain*: `Map(𝐾, 𝑉) <: Collection(𝑉)`, and iterating any collection binds the
loop variable to the **codomain** — `for v in m` gives `v: 𝑉`, exactly as
iterating `groupby`'s result today binds each *group*. Recovering the key
alongside the value (`key -> g` / `(k, v)` entry binding, and hence the `/stats`
rollup above) needs a user-level **`entries` built-in** that views a data
function `𝐴 ⤇ 𝐵` as `𝐴 ⤇ (𝐴 ⤇ 𝐵)` — each key mapped to its singleton entry, so
iterating *that* yields entries from which both key and value project. `entries`
is **deferred**; value iteration is the near-term consumption path.

The `map`/`set` constructors are `groupby` + a **codomain map** (the group
collapse), which preserves the keyed domain:

```
set([e…])      = groupby(xs, id) ≫ (λ g → unit)            : Map(𝐾, unit) = Set(𝐾)
map([(k,v)…])  = groupby(ps, .0) ≫ (λ g → g ▷ sole ▷ .1)   : Map(𝐾, 𝑉)
```

where `sole` is the pick-the-one-element (error if more than one) aggregate. The
codomain map *conceptually* leaves the key domain untouched and rewrites only the
codomain `𝑉 → 𝑊`, landing at `{𝐾 | 𝑘 ▷ keydom#id} ⤇ 𝑊` — `Set(𝐾)` (`𝑊 = unit`) or
`Map(𝐾, 𝑉)`. The collapse is lowered
as the η-expanded discharge shape ([Consuming a keyed
collection](#consuming-a-keyed-collection-discharge-not-point-free-compose)), which
types and compiles end-to-end. One gap remains: the result infers at the correct
**Data** (`⤇`) kind but does not yet *inject* into a nominal `Set`/`Map` annotation,
which needs the keyed-`Σ` witness discharge (open issue below).

### Consuming a keyed collection: discharge, not point-free compose

A `groupby`'s per-key group `{𝑖 | key(𝑖) == 𝑘} ⤇ 𝑉` is a **dependent** codomain: its
domain refinement names the key binder `𝑘`. Anything that consumes it — the
`groupby(…) ≫ (λ entry → …)` rollup above, a `set`/`map` collapse, `(key, value)`
entry-iteration — must not let `𝑘` escape into the consumer, which is bound outside
`𝑘`'s scope.

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
A comprehension (`[… for key -> g in …]`) is already in this form; the `set`/`map`
constructors emit it directly (`λ __iter → __iter ▷ keyed ▷ collapse`). A **bare**
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

Because discharge introduces `𝑥` for its own sake, the group-collapse `collapse` need
not itself *consume* the group **for scope-safety** — `keyed(𝑥)`'s type names `𝑥`, bound
by `λ 𝑥`, whatever `collapse` does. It must nonetheless consume it for a different
reason: **planning drives a source through its consumer.** Replacing `set`'s `Drain`
with a group-ignoring `λ 𝑔 → unit` still type-checks (no scope violation — verified),
but the group-by source is then never driven and the underlying list literal reaches
op-conversion with no `iterate` before it. So the consuming collapse is load-bearing at
*two* levels, neither of them the type checker: it deduplicates each key's group to the
one `unit` a `Set` holds, and it is what makes the collection get materialized at all.

The `Collection` Σ witness (the domain) still matters for *other* questions — e.g.
rejecting an unsound `Σ <: Fun` consumption, which is what presenting the sum itself
as the consumed domain is for — but consuming a `groupby` group is not one of them:
discharge resolves it with no witness at all.

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
aggregation *framework* (per-key accumulator, fold, extract). Its accumulator is
logically `Option(𝐴)`: identity `none`, and the merge law is the *partial* monoid
where combining two `some` values is a **run-time error** (two elements for one
key — the duplicate). `extract` errors on `none` (an empty group, which a
`groupby`-produced group never is, so this arm is a defensive invariant rather
than a reachable path for `map`). So the duplicate-key rejection is `some ⊕ some`
and the collapse's well-formedness is the `none`-extract guard — both fall out of
the accumulator law. (Contrast `Sum`/`Max`, whose accumulators are total
monoids.)

Two realization details distinguish `sole` from the scalar aggregates and are
designed with `map` (not `set`, whose `unit` codomain needs no `sole`):

- **Presence is out-of-band.** `Sum`/`Max` carry an in-band identity (`0`,
  `MIN`); `sole` has none — any element is a valid value — so `none`/`some` is
  tracked by accumulator *presence* (an empty vs. length-1 column), not a
  sentinel value. A populated per-key accumulator is always length 1, so the
  cross-tile merge path (`Tile::merge`) sees `some ⊕ some` and errors, as intended.
- **`sole` folds a structured codomain.** In `map`, each group's codomain is the
  pair `(𝐾, 𝑉)`, so `sole` picks the sole *row* of a record/tuple-valued group,
  not a scalar column — a wider shape than the scalar `ColumnValue` fold `Sum`
  uses.

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
reuse the existing operator set with **no new `Domain` and no hash store**. The
"keyed domain → hash store" dispatch that [Compilation](#compilation) anticipates
is for *lookup* (`𝑚[𝑘]`) and *mutable* maps, which arrive with those features —
not for immutable construction.

`set([𝑒…])` lowers to the group-by on an identity key, collapsed by the terminal
aggregate [`AggregateKind::Drain`] — `(𝐷 ⤇ 𝛾) ⇒ unit`, accumulator `Units(1)`,
`accumulate` a no-op — folding each key's group (of ≥ 1 duplicate elements) to the
one `unit` a `Set` holds. `set([1,2,2,3])` produces the sealed keyed tile over keys
`{1, 2, 3}`. `map`/`sole` are the remaining constructor work.

Where a keyed collection value is and is not **driven** is a planning property, not
a constructor one, and the boundary is narrower than it looks. Planning inserts the
driving `iterate` at a *chain head*, so a `set(…)` reaches the runtime when it is
the program tail (`set([1,2,3])`) or is let-bound and then consumed
(`s = set([…])` … `[k for k in s]`). What fails is a keyed collection **nested as
the source of another comprehension** (`[1 for k in set([1,2,3])]`) and a **bare
`groupby(…)`** — both surface as *"list literal reached op-conversion without an
input"*, the underlying source never having been given an iteration site. Fixing
that is one planning change covering both; it is not part of the constructor
surface, and the two shapes are pinned by the `#[ignore]`d
`test_undriven_keyed_collection` (`tests/compilation_pipeline/joins_aggregates_groupby.rs`). Separately, a keyed collection cannot yet **yield its keys under
iteration** — the deferred `entries` built-in above, itself blocked on the
[kind-representation question](#two-axes-representation-vs-kind-decided-direction-representation-tentative).

## Keyed entry needs the key domain written down at lowering

An entry term runs a *membership predicate* on the entering side — is this domain
a range, is it a membership refinement? — so it decides at constraint-emission time only
for a domain that is already concrete, and otherwise becomes a kinding constraint on the
domain variable. Whether a producer
satisfies that is **not** a property of the collection kind; it is a property of
whether lowering wrote the domain down:

```
x: List(Int) = [y+1 for y in [1, 2, 3]]          # ✅ range domain ?N at emit; deferred, realized at coalesce
m: Map(Int, Collection(Int)) = groupby(xs, key)  # ✅ key domain written onto `__gb_k` by lowering
x: Set(Int)  = set([1, 2, 3])                    # ✅ same, written onto the constructor's iteration binder
```

So the rule for every re-keying producer is: **stamp your own key binder with the
present-key domain** `{𝐾 | __elem ∈ (c ≫ key)}` (`present_key_domain` in
`lower/exprs.rs`). `groupby` does it for `__gb_k`; `set` does it for its iteration
binder. Get it wrong and the failure is a confusing `AnnotationMismatch` on the Σ
witness rather than anything that names the real cause, because the gate silently
had nothing concrete to test.

**Why not a deferred obligation, as `List` uses?** The `List` arm genuinely needs
one: a comprehension's *range* domain is the domain coalesce independently resolves
it to, and constraining it at emit collides with that resolution (see
[Injecting a domain that has no shape yet](#injecting-a-domain-that-has-no-shape-yet)).
A re-keying producer is different — it *knows its own key-image syntactically*, so there
is nothing to wait for. A kinding constraint already carries *which* kind to check, so
the keyed case needs no extension of the mechanism, only the keyed kind itself; it comes
due for a producer whose key domain is genuinely unknowable until coalesce — a map
comprehension, a keyed feed. No producer that exists today is in that position.

## Iterating a `Set`/`Map` binds the codomain, not the keys [Interim]

`for k in set(xs)` binds `k` to the collection's **codomain** (`unit` for a `Set`),
so `sum([k for k in set([1,2,3])])` fails (`Aggregate: expected Unit, found Int`).
The *semantic* decision is made — the `Iterable` element is kind-directed (`Set` →
key, `Map` → `(𝐾, 𝑉)` entry, `Collection`/`List` → value;
[chl-spec §4.6](../../../docs/chl-spec.md#46-for--iteration)) — and its realization is
[Operations](#operations-how-the-trait-layer-is-realized-planned).

What actually blocks it is narrower than "the operation layer is unbuilt": the
element choice needs to distinguish `Set` from `Map`, and those are currently the
*same type*, so there is nothing to dispatch on. This section is therefore the
record of two things at once — the **[Interim]** codomain-only binding, and the fact
that lifting it depends on the
[kind-representation question](#two-axes-representation-vs-kind-decided-direction-representation-tentative),
not merely on writing the trait instances. The entry key's membership proof is what
makes a subsequent `m[k]` a *proven* lookup ([Lookup](#lookup-membership-discharge)).

## Compilation

Collections need no new pass; they extend the existing lowering, inference, and
planning surfaces.

- **lower** (`ccl/lower/`) — map literals `[k -> v]` (today `Unsupported`,
  `lower/mod.rs`), general `𝑚[𝑘]` subscript (today integer-literal tuple
  projection only), `set(…)` / `list(…)` constructors, `(𝑘, 𝑣)` entry-iteration
  binders, keyed-feed `𝑐[𝑘] = 𝑣` / `𝑐[𝑘] := 𝑣`.
- **infer** (`ccl/infer/`) — a lookup emits a key-presence obligation and discharges
  it against the collection's own key domain (total) or falls back to `Option`
  (partial); `groupby`'s result type unifies with `Map` (mostly *deleting*
  special-casing).
- **constrain** (`ccl/infer/solver/constrain.rs`) — finish domain-invariance
  modulo refinements (the one new arm); everything else reuses the refinement-width
  and Σ-width arms.
- **planning** (`ccl/planning/`) — `extent_of` dispatches a keyed domain to a
  hash store and a range to a dense array; `restrict` / `FilterValues` already
  lower a domain refinement; the mutable-map store is the existing keyed MVCC
  store with a dynamic key column.

## Implementation roadmap

[Status](#status) records what is built. This section is the **order** to build the rest
in, and why that order — nothing else. A step names what it unblocks and what it depends
on; it does not restate a capability's status, name the tests a branch turns off, or carry
design a section above already holds. Each of those is what rotted this section before,
and each has a home: the table, the branch, and the section respectively.

> **Two step-0 obligations.** Both are cheap now and unrecoverable later, so they
> gate the steps rather than sitting inside one.
>
> - **Per-collection key-domain identity, minted at creation** — see [Witness identity
>   is minted at creation](#witness-identity-is-minted-at-creation-load-bearing). A
>   shared anonymous key domain would let one map's membership proof discharge
>   against another's, and identity cannot be retrofitted onto values already
>   conflated. Discharged by giving each creation site its own key domain, so two maps
>   built separately never share one.
> - **Decide how a collection kind is represented** — **tentatively decided**: the
>   witness kind carries four of the five, and `Set`/`Map` — the pair it cannot
>   discriminate — become **nominal type heads**, landing with nominal types
>   ([Two axes](#two-axes-representation-vs-kind-decided-direction-representation-tentative)
>   states why and what it costs). Step 2 dispatches every operation on it, and `Set` vs
>   `Map` is not expressible until it lands — so if nominal types trail the operation
>   layer, take the uniform-entry-iteration interim named there rather than encoding the
>   distinction somewhere it will have to be removed from.

1. **Finish the Σ-as-kinds rework.** Every witness is a *type* classified by a **kind**,
   so Σ subtyping is kind containment plus the body edge — the general union rule, with its
   `∃` discharged as a search over ground candidates ([type-inference.md, Where the pairing
   search runs](type-inference.md#where-the-pairing-search-runs)). What remains is the
   **keyed** kind, which makes the keyed discharge plain kind containment rather than a rule
   of its own, so it precedes every step below that dispatches on a key. The representation
   it uses is [Representation: the key domain is
   opaque](#representation-the-key-domain-is-opaque-decided).

2. **Restore direct group-by key application; then lookup discharge + `Option`.** Two
   halves of one mechanic, and the first is a *regression fix*: `groupby`'s honest keyed type
   makes `g(k)` at a bare key a type error, and it must, since an arbitrary key is not known
   to be present — the whole content of [Lookup](#lookup-membership-discharge). A test
   asserting a bare key succeeding is therefore **restated** against the checked operator,
   never re-enabled. The prerequisite is [making the membership proof survive being
   consumed](#prerequisite-the-proof-has-to-survive-being-consumed); the surface pair `𝑐[𝑘]` /
   `𝑐[𝑘]?` and `Option` over the existing `Variant` nodes (shared with `txn_kv`) sit directly on
   top.

3. **The operation layer.** The per-kind iteration element (`Set` → key, `Map` →
   `(𝐾, 𝑉)` entry), membership `in`, the `keys` / `values` / `items` views, and the
   `Ord[𝐾]` given that an ordered operation over an unordered domain requires — all
   as [Operations](#operations-how-the-trait-layer-is-realized-planned) describes.
   Gated on step 0's kind decision. Pins the `storefront` `/stats` rollup, which
   needs entry iteration, and lifts the
   [codomain-only-iteration Interim](#iterating-a-setmap-binds-the-codomain-not-the-keys-interim).

   It is also what makes `sum(m)` an error. Width-to-top admits a keyed lhs — ⊤
   absorbs every kind — so nothing in the type layer distinguishes a user writing
   `sum(m)` from lowering consuming a `groupby` per key, and a kind row that tried
   would be answering a question about the iteration element one layer down. Once
   `sum` lowers as `sum([x for x in m])` the rejection comes from the element itself:
   a `Map` yields `(𝐾, 𝑉)` entries, and entries cannot be summed. Until then
   `sum(m)` means `sum(values(m))`
   (`test_keyed_collection_widens_to_collection_like_any_other`).
4. **Keyed entry under an invariant domain.** The subtyping arm is done — a data
   domain relates only to itself, both halves ([type-inference.md, Data domains are
   invariant](type-inference.md#data-domains-are-invariant)) — so what is left is not
   the guard but its consequence: acquisition is gone as an implicit edge, and keyed
   entry must name the refinement it adds through an explicit
   [`Cast`](ir.md#cast--explicit-refinement-acquisition). Its urgency is worth stating precisely: a keyed Σ's *body* domain is
   the nullary [`Type::WitnessRef`] on both sides, so body subtyping compares nothing
   about the domain — the whole domain content sits in the **kind**, where
   containment checks the key token's *shape* and relates the key type, and stops
   there. That is sound only while the shape is canonical. The moment a keyed domain
   carries a *second* refinement (`{𝑘 | 𝑘 ∈ 𝐸 ∧ valid(𝑘)}` — a restricted map, a
   filtered key set), nothing compares it and the missing guard becomes a live
   refinement-acquisition hole. Land it before, not after, refined keyed domains.

   Because a Σ pairing is discharged by ordinary body subtyping, this step *is* the
   Σ-level refinement question too — there is no separate candidate rule to write.
5. **The Σ layer as the general rule.** Three mechanisms, in this order, each
   independently landable ([type-inference.md, Deliberately incomplete
   here](type-inference.md#deliberately-incomplete-here) is the gap list they close):

   1. **A kind lattice** — `<:`, `⊔`, `⊓` over [`TypeKind`], with `Any` as ⊤ by
      structure; membership split out as a per-kind predicate on a type. Fills
      `join_witness_kinds`' missing `Described ⊔ Described`, and retires the `(Keyed, Any)`
      row to the iteration-element layer (step 3).
   2. **The pairing search** — `∀ 𝑑 ∈ 𝐾₀. ∃ 𝑒 ∈ 𝐾₁`, with the codomain edge emitted once
      and the domain edge per pairing. The precondition is ground candidates,
      not a particular time: a ground comparison records no bounds, so a failed attempt
      leaves no trace and the choice is confluent. That holds at emission today, so the
      search runs inline and needs no deferral channel; it moves late only when formation
      does (step 3). `Enumerated`/`Enumerated` cannot record a *pending* candidate the way
      a described kind can, because a disjunction is not a constraint — so an unresolved
      candidate keeps only the `𝑒 = 𝑑` instance.

      It does **not** fold in the hand-rolled gated-partition pairing, and the reason is
      structural rather than pending: that site checks a *bijection* between legs and
      fibers, with a covariant per-leg edge, because a partition must cover exactly;
      Σ-width is one-directional with a contravariant domain edge. See
      [type-inference.md, Where the pairing search
      runs](type-inference.md#where-the-pairing-search-runs).
   3. **Consuming a sum at a domain-preserving consumer.** A conditional
      collection survives a comprehension by every route — inline, `let`-bound, and through
      a UDF parameter — all yielding `Σ 𝐷 ∈ {[0, 1], [0, 2]}. 𝐷 ⤇ Int`, and a filtered one
      restricts the **witness**, `Σ 𝜎 ∈ {[0, 1], [0, 2]}. ({𝜎 | 𝑝} ⤇ Int)`, which
      realization discharges into the legs (see [Realization
      notes](#realization-notes)).

      *Not* by forming the Σ earlier — that was an earlier reading of this step and it is
      wrong; a conditional whose arms are both parameters proves no syntactic rule can
      replace the join. What was actually wrong is where the join was **taken**. Closing a
      variable's collection-shaped lower bounds against a consumer's demand one at a time
      computes the candidates' *meet* on the contravariant domain edge, because two data
      functions with distinct domains have no `Fun` least upper bound. The rule is instead
      about the variable: one whose lower bounds range over two or more distinct domains
      **denotes** the sum over them, so the sum flows along its outgoing edge once. A
      function upper bound then meets the consuming arm and a variable upper bound
      carries the join onward, so constraint order is irrelevant and nothing has to be
      retracted.

      Four supporting pieces: the constraint-time join is a **union of listings**, which is all
      that reaches it — compaction's `join_witness_kinds` additionally orders across kinds, which is
      reachable only there, so the two are not one law at two representations; the join reads *collection shapes*, so an
      already-joined Σ arriving as a lower bound contributes its witness kind whole, which is
      the associativity law that flattens nested conditionals; consumption presents the **sum
      itself** for every witness kind, so compaction's re-pairing closes the round trip
      instead of a tagged union leaking into the result; and a sum's **candidates** are an
      invariant position, so they cross a level boundary through two-way proxies
      (`extrude_invariant`) rather than a polar one-way approximation that inherits whichever
      side the polarity picked. That last one is what lets an arm whose domain is *inferred*
      — any comprehension arm — join like a literal one. See [type-inference.md, A variable's
      lower bounds are one value](type-inference.md#a-variables-lower-bounds-are-one-value).

      A **UDF-call** arm is closed by the *solver* rather than by the join: the join declines a
      bare variable, and the arm's collection reaches the join variable transitively as an
      ordinary lower bound. What had to be fixed for it was a reading — a use of a lambda
      parameter was coalesced standalone, losing the contravariant-domain context in which its
      candidates are alternatives.

      The *other* half of what this step used to claim — the join destroying candidates —
      holds as well: alternatives accumulate at either polarity while demands still narrow.
6. **The rest of the constructor surface.** Map/dict literals `[k -> v]`, `list()`,
   `map()` with the [`sole` aggregate](#sole-is-an-option-accumulator-aggregate),
   general `𝑚[𝑘]` subscript lowering, and the [keyed entry of an inferred-domain
   collection](#keyed-entry-needs-the-key-domain-written-down-at-lowering).
   Also the one planning change that lets a keyed collection be driven as a nested
   comprehension source and as a bare `groupby` tail.
7. **Mutable maps.** Dynamic-key write-sets + per-key `get_prev_txn` over runtime
   keys; refinement discharge at `store[𝑘] := 𝑒`. Sits directly on the compound
   (tuple/record) registers. Pins `nonneg_inventory`.
8. **Deferred keyed collections.** `reach_feed << 𝑒` and `resps[req.id] = 𝑣`
   contributed directly into an *open key domain* — the collection type is
   `Set(𝐾)` / `Map(𝐾, 𝑉)`, **no `Feed` wrapper and no sequencing domain** (see
   [Deferred keyed collections](#deferred-keyed-collections)); `channelize`
   closes the open domain. Pins `ledger_balance`'s feed side and the
   `http_serve` response pairing.
9. **Recursive keyed collections (fixpoint engine).** The second `LetRec`
   well-foundedness rule (monotone-lattice) and the semi-naive fixpoint engine
   (see [Recursive keyed collections](#recursive-keyed-collections-fixpoint)).
   Pins `reachability` (both the `rec` comprehension and the self-feed forms).
   The largest single step; deferred behind the rest.

`storefront` is the composition test, red until steps 1–2 plus the HTTP library (a
separate design) land.

## Future work

- **A dependent collection under an exact collection annotation reports a compiler
  bug.** `groupby`'s value type names the key binder, and `Map(𝐾, 𝑉)` has one `𝑉` with
  no binder to name — so `g: Map(Int, _) = groupby(…)` fills `𝑉` from the initializer
  and captures `__gb_k`, which the escape check reports as a scope violation labelled a
  compiler bug. It is an annotation error: the annotation cannot express the type. The
  bounded form `g <: Map(Int, _)` leaves `g` its own type and is unaffected. What is
  missing is the diagnosis, not a rule.

- **The runtime witness.** The load-bearing item, and the one the others reduce to.
  A Σ value is a **pair** — a concrete witness together with an element of the body at
  that witness ([type-inference.md, Introduction is a
  term](type-inference.md#only-a-term-builds-a-sum)) — and nothing today can read a
  witness off a value. Consuming a sum means projecting it and dispatching, so a
  `Collection(𝑇)` parameter cannot be iterated: there is no static domain to recover,
  which is the whole content of the annotation. [`extent_of`] maps a *type* to an
  `Extent`; the witness needs the treatment `Type::DataSource` already gets, resolving
  to `Extent::DataSourceDomain` — a handle to the domain as it exists at runtime. So
  the witness joins the family of opaque domains rather than founding one.

  Why this has stayed invisible: the conditional collection, the one Σ that is
  routinely built today, is the single case that does *not* need it. Its candidates
  are statically enumerable and its realization is the gate fan-out `⧺ᵢ (xsᵢ | π̂ᵢ)`,
  whose extent already *is* the selected domain because the unselected legs are empty.
  Realization performs that union *after* inference and asserts the pre-realization
  type, so nothing ever has to relate the tagged union to the sum by a typing rule. Reading
  the conditional collection as the model and `Collection(𝑇)` as an extension of it is
  backwards; `Collection(𝑇)` is the general case.

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
  planning must handle instead of the always-`None` dormant one. That is [roadmap step
  4](#implementation-roadmap) regardless.

- **The domain-join corner (O1/O4).** Two distinct maps meeting at a join (`𝑚₁ if 𝑐
  else 𝑚₂`, or returning / storing distinct maps). The membership predicate closes over
  the specific map value, so two distinct maps produce two distinct discharge
  substitutions; when they meet at one coalescing variable, `bridge_holder_gap` hits
  its panic tripwire (guarded loudly — never silently wrong).

  `box` is most of the answer. Written `box(𝑚₁) if 𝑐 else box(𝑚₂)`, the two maps carry
  distinct witnesses by [creation-site
  identity](#witness-identity-is-minted-at-creation-load-bearing), so the arms are
  `Σ 𝑇 ∈ {𝑀₁}. 𝑇` and `Σ 𝑇 ∈ {𝑀₂}. 𝑇` and their join is ordinary Σ-width — the
  candidates stay *separate*, and each keeps the discharge substitution belonging to
  its own map. There is no two-discharges-at-one-variable to resolve, because nothing
  ever merged them: the panic's cause was a join being asked to produce a single map
  type, and that join now has no answer to invent. Unboxed, it is a `JoinTypeError`
  naming both domains rather than a tripwire.

  What remains is consuming one — projecting the witness to pick the discharge — which is
  the runtime-witness item above. The earlier plan here was to form the Σ *at* the
  discharge level, mirroring the top-level join; that is the same implicit formation
  the design removed, so the corner is now a consequence of the witness rather than a
  separate mechanism.

  The tagged-variant escape hatch (`.MapA(𝑚₁) if 𝑐 else .MapB(𝑚₂)`, then `match`) is
  **superseded**: `box` is the anonymous version of exactly that, and it needs no
  declared tags and no `match` at the use site, since consumption distributes
  structurally.

  **Not on the critical path.** The north-star programs use *single* mutable maps and
  *single* registers (`nonneg_inventory`, `storefront`, `txn_kv`) — one witness
  identity each, never a distinct-map join — so the demos compile without it.
- **First-class collections of `Mut`.** `Mut` values are second-class
  (downward-only); a collection of registers needs the same index-types generality as
  the domain-join corner, so it lands with the runtime witness above.
- **Set/map algebra as refinement algebra** — union, intersection, difference as
  operations on the membership predicate. Falls out of the refinement algebra
  once the keyed domain is live; not committed as surface yet.
