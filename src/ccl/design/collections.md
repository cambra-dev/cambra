# Collections

CCL represents a collection as a data function `D ⤇ V`: the domain identifies its data positions,
and the codomain describes the value at each position. This reference owns the representation,
constructor lowering and checked-lookup implementation. The
[CHL collection reference](../../../docs/chl-spec.md#63-direction-collection-types-decided)
owns the source-language interface and its planned changes.

The current representation does not distinguish every planned surface collection type.
In particular, `Set(K)` and `Map(K, unit)` lower to the same type, and iteration currently
binds values for both. Proposed nominal distinctions and per-type operations are marked below.

A witness is a binder whose candidate domains are classified by a `TypeKind`. The general
rules are owned by [Subtyping for sums](type-inference.md#subtyping-for-sums); this document
specifies how the collection constructors use them.

## The six collection types

The annotation forms lower through `lower_type_application` in `lower/stmts.rs`:

| Annotation | CCL representation | Domain information |
|---|---|---|
| `Array(n, T)` | `UIntRange(n) ⤇ T` | A statically written length. `n` must be a non-negative integer literal representable as `usize`. |
| `List(T)` | `Σ (D : UIntRanges). D ⤇ T` | Some unsigned index range; the annotation does not name its length. |
| `Set(K)` | `Σ (D : SubtypesOf(K)). D ⤇ unit` | A subset of key type `K`, with unit values. |
| `Map(K, V)` | `Σ (D : SubtypesOf(K)). D ⤇ V` | A subset of key type `K` with values of type `V`. |
| `FullMap(K, V)` | `K ⤇ V` | The domain is `K` itself, not a sum witness. |
| `Collection(T)` | `Σ (D : Type). D ⤇ T` | An abstract domain without a narrower kind restriction. |

`Array` and `FullMap` have explicit domains. The other four are sums. Introducing a sum
requires a term such as `box`; a subtype constraint does not insert one. For example,
`box([1, 2])` can satisfy `List(Int)`, whereas the bare literal has a concrete range domain.
Widening an existing sum follows the kind/body relation, not a collection-specific coercion.

The abstract domain remains part of a collection value even when a consumer cannot name it
statically. `Collection`'s `Type` kind admits every domain kind, but does not supply a runtime
witness implementation; see
[Compiling a conditional collection](#compiling-a-conditional-collection).

`FullMap(_, V)` lets inference recover a producer's domain. A list literal can satisfy that
annotation; this does not give it an unrefined `Int` domain. Likewise, a group-by retains its
present-key domain. `full_map_annotations_are_satisfiable` and
`a_groupby_is_a_full_map_at_either_strength` cover annotation cases.
A `FullMap(Int, Int)` parameter can be type-checked with an integer subscript without establishing
that a tested concrete collection can inhabit the parameter type.

The table does not promise that every declared lookup or iteration interface is implemented.
Those boundaries are specified under [Lookup](#lookup-membership-discharge) and
[Operations](#operations-how-the-trait-layer-dispatches-planned).

## The empty literal names no element type

`[]` has an empty `UIntRange(0)` domain and an initially unresolved element type. An annotation,
an operator using an element or a join with a typed collection can constrain that element type.
With no requirements, it becomes `unit`. No element can be read from the empty domain, and the
type language has no uninhabited type; see
[The empty product is unit](../../../docs/chl-spec.md#66-the-empty-product-is-unit).

An empty literal whose element no value reaches is a pin site of
[An unobservable variable takes the type of its position](type-inference.md#an-unobservable-variable-takes-the-type-of-its-position).
The element takes the type of its position, so in `box([1]) if c else box([])` it takes the other
branch's element type, `{Int where _ == 1}`. With no answer from the position, it takes the arm
payload's fallback
([An unobservable arm payload is pinned to what its uses require](type-inference.md#an-unobservable-arm-payload-is-pinned-to-what-its-uses-require)).
The choice is constrained in both directions against the element variable, so bindings and
iteration targets that share it see the same choice. Choosing `unit` during emission would
instead conflict with later requirements for another element type.

Each walk pins the literals in its own tree, so a literal inside a generalized definition is
pinned once per use. `def f(x: Int): []` called as `xs: List(Int) = box(f(1))` gives that use's
element `Int`.

An empty literal can have incompatible use sites. Failure to satisfy all recorded bounds is
returned as a type error, not asserted as an internal invariant. The regression
`an_empty_literal_read_at_two_types_is_a_type_error` in
[the collection pipeline tests](../../../tests/it/compilation_pipeline/scalars_collections.rs)
covers conflicting `List(Int)` and `List(String)` annotations.

The pass selects syntactically empty `List` nodes, not every unresolved collection element type.
Emptiness is what makes the choice unobservable. A nonempty comprehension such as
`\x -> [x for z in [1, 2]]` leaves its element type ambiguous, and pinning it would accept a
program that has no type. The pinning pass walks expression children, not copies stored in
refinement predicate type slots.

### The empty collection has no key morphism [Interim]

`map([])` and `set([])` fail inference with an unresolved-variable error. Their key type is
derived from [the key morphism's image](#the-key-domain-is-the-key-morphisms-image), and the empty
source supplies no key value. The re-keying stores a copy of that source in a refinement
predicate; the term-only pinning pass does not choose the copied literal's element type.
`a_re_keying_constructor_rejects_an_empty_literal` also covers `box(map([]))` under an explicit
`Map(String, Int)` annotation.

`empty_map()` constructs a keyed sum without deriving a type from entries:
`Σ (σ : SubtypesOf(𝐾)). σ ⤇ 𝑉`. A `Map(𝐾, 𝑉)` annotation fixes its parameters. A `Set(𝐾)`
annotation also works because `Set(𝐾)` is represented as `Map(𝐾, unit)`.

```python
cart: Mut(Map(String, Int), Txn) := empty_map()
```

The builtin introduces the sum directly, without `box`. Boxing an empty list retains its
`UIntRanges` candidate domain rather than introducing a keyed `SubtypesOf(𝐾)` domain; see
[Only a term builds a sum](type-inference.md#only-a-term-builds-a-sum). Bare and let-bound
unannotated `empty_map()` calls leave unresolved parameters and are rejected.
Keyed writes check the key and value against the collection's existing types; they do not
replace the annotation that determines this empty constructor's parameters.

Operator conversion constructs an empty function value at the extent obtained from the
inferred type. No entry is available from which to recover its key or value types.
`an_empty_map_is_a_typed_empty_tile` checks the resulting empty tile.

`TypeKind` has no inference-variable form. Generalizing the empty constructor across kinds
would require a representation and inference rules for an unknown kind; this remains a proposal,
not an implemented replacement for `empty_map()`. The decided nominal `Set` and `Map` replace it
with the two values `Set::empty` and `Map::empty`; see
[Telling `Set` and `Map` apart](#telling-set-and-map-apart-decided).

## The collection type is declared, not read off the shape

The planned operation interface selects an iteration element by collection type: values for
arrays/lists/collections, keys for sets, and entries for maps. A function shape alone cannot
identify that intent. A set and a map with unit values have the same representation, and a
positional and a keyed collection can expose overlapping domain shapes.

Current loops bind the codomain unconditionally. The type-directed choice below is proposed
work, not a dispatch mechanism already implemented by the compiler. `Set` is a nominal builtin with
no edge to `Collection` ([Telling `Set` and `Map` apart](#telling-set-and-map-apart-decided)), so
its keys are reached through `keys` rather than through a structural reading of its values.

## Telling `Set` and `Map` apart [Decided]

`Type` has no nominal collection constructor distinguishing `Set(K)` from `Map(K, unit)` today.
The decision is that `Set`, `Map` and `FullMap` become **nominal builtins**: type constructors the
compiler declares, opaque as a `type` declaration is
([chl-spec, 6.8 Nominal types and methods [Decided]](../../../docs/chl-spec.md#68-nominal-types-and-methods-decided)),
with no constructors or `extract` a program can reach. `Array`, `List` and `Collection` stay
structural: the kind already tells a bare range `Fun`, `UIntRanges` and `Type` apart. `FullMap` is nominal
because it iterates entries as `Map` does, which a structural `(𝑘: 𝐾) ⤇ 𝑉` does not.

The three questions the decision answers:

- **The nominal constructor remains around the sum.** `Map(𝐾, 𝑉)` wraps
  `Σ (𝐷 : SubtypesOf(𝐾)). 𝐷 ⤇ 𝑉`, `Set(𝐾)` wraps `Σ (𝐷 : SubtypesOf(𝐾)). 𝐷 ⤇ unit`, and
  `FullMap(𝐾, 𝑉)` wraps `(𝑘: 𝐾) ⤇ 𝑉`. Inference resolves the builtin's operations on the
  name, and the first implementation erases it once they are resolved. Erasure is
  [open in the spec](../../../docs/chl-spec.md#a-nominal-type-is-opaque).
- **`Map(𝐾, 𝑉) <: Collection(𝑉)` does not hold**, and no edge leads from `Set` or `FullMap` to a
  structural type. A nominal type is related only to itself, so reaching a `Collection` takes
  the method `keys`, `values` or `items`, and `sum(m)` is rejected at the missing edge.
- **Variance is read off the wrapped representation**, as a declared type's is read off its
  constructors' parameter types.

`FullMap(𝐾, 𝑉)`'s second parameter is a family over the key, since `𝑉` may depend on `𝑘` for a
group-by. A nominal builtin's parameter therefore accepts a type family where a declared type's
parameter takes a type.

None of this is implemented. Current codomain iteration makes `for g in groupby(xs, key)` bind
groups. Uniform entry iteration is a possible interim design: a set entry would be `(K, unit)`
rather than `K`. That would change source-visible behavior and is not implemented here.

## `groupby`'s exact type

For `c: I ⤇ A` and `key: A ⇒ K`, lowering constructs:

```text
groupby(c, key) :
  (k: {K | k ▷ ((c ≫ key) ▷ collection_contains)})
    ⤇ ({i: I | key(c(i)) == k} ⤇ A)
```

The outer domain is this key morphism's image, not all inhabitants of `K`. Each output group
retains the source positions whose values have that key. The codomain depends on the outer key
binder. Both the outer function and the inner group are data functions.

This is an explicit-domain function, the `FullMap` representation, rather than a uniform
`Map(K, V)` abbreviation. An exact `FullMap(_, _)` annotation can preserve and consume the
group-by's type. Boxing it to satisfy a `Map` annotation does not establish equivalent behavior:
`a_consumed_boxed_map_annotation_escapes_its_scope` records an inference failure when that
boxed annotation is consumed. Bounded group-by annotation cases also have an open-bound
invariant failure in `a_consumed_bounded_keyed_annotation_records_an_open_bound`.
These are implementation limitations, not rules rejecting every group-by annotation.

A checked lookup substitutes its key into the dependent group type during inference.
The streamed collection-valued answer is rejected later at operator conversion; see
[The checked lookup](#the-checked-lookup-𝑐𝑘).

### The key domain is the key morphism's image

`present_key_domain` in `lower/exprs.rs` constructs
`{K | __elem ▷ ((c ≫ key) ▷ collection_contains)}`. The predicate retains the producer
morphism rather than an opaque key-set identifier. Its structural identity therefore depends
on the named term and its free references, not merely on the keys that term happens to produce.

The helper shares one `SharedHole` between the refinement base and the morphism's codomain.
Using only the builtin scheme would leave a one-way bound instead of establishing that identity.
`lower_groupby` returns the domain so re-keying consumers reuse both its key type and its
predicate allocation. Independently constructing a similar domain would create separately
inferred predicate copies.

The key domain is stamped during lowering. Delaying it until coalescing can leave a keyed-sum
entry constraint with an unresolved candidate rather than the concrete membership-bearing domain
it needs. General handling of unresolved candidates belongs to
[kinding edges](type-inference.md#an-unresolved-candidate-becomes-a-kinding-edge).

Key types must support equality. Products compare componentwise, and runtime lookup pivots
a computed product key into one value for comparison with stored product keys.
There is no requirement that keys be scalar base types.

`Converse` separates two domains during planning: the extraction morphism produces keys of
base type `K`, while its resulting partition is typed over the present-key domain. Using one
domain for both would impose membership on extraction or lose the partition's restriction.

The membership predicate can remain embedded in a type without becoming an executed membership
test. `fn_of_bare_predicate` returns `f` directly for a bare `__elem ▷ f` predicate.
An occurrence that remains in a type is not thereby a compiled runtime `CollectionContains`
operator. The compiler does not provide a surface `in` expression yet.

Producer-bearing domains expose two limitations:

- A producer term is embedded in the type, so its structure can appear at many type sites.
- Different spellings, such as a bound source and its inlined literal, need not reconcile.
  The [SMT fallback](type-inference.md#semantic-entailment-as-a-fallback) does not supply
  collection-membership axioms or a general producer-identity proof.

Naming the producer makes a membership-introduction rule expressible; it does not mean that
applying its key morphism already proves membership. The current rejection is recorded under
[Prerequisite](#prerequisite-the-proof-has-to-survive-being-consumed).

### Constructor lowering: runtime `groupby` now, constant-folding later

The implemented re-keying constructors return concrete data functions:

| Constructor | Key morphism | Group collapse | Result |
|---|---|---|---|
| `set(xs)` | Identity on an element | `Drain` | Present-key domain to `unit`. |
| `map(entries)` | First projection of a pair | `Sole`, then second projection | Present-key domain to the entry value. |

`lower_rekeyed` builds both. It retains the domain returned by `lower_groupby` and
eta-expands the application as `λ __iter_record → __iter_record ▷ keyed ▷ collapse`.
A bare composition would expose the dependent key binder in the collapse parameter's type.
The iteration lambda carries both the present-key domain and a data-function annotation;
the refinement and function-kind stamps serve different constraints.

The collapse must consume its group. For a set, replacing `Drain` with a function that ignores
the group would leave the source without the consumer through which planning assigns an iteration
site. Duplicate set elements are absorbed by the drain; duplicate map keys reach `Sole`.

Neither constructor inserts `box`. A sum annotation requires explicit boxing, for example
`m: Map(Int, Int) = box(map([1 -> 10, 2 -> 20]))`.
`list(...)` is not a surface builtin; use `box` to introduce a list sum.
Annotation-driven insertion of these constructors remains planned.

Planning's constant fold does not evaluate an entire re-keying collection. Its scalar folding
can prepare literal elements, but the group-by remains a runtime operation. A collection fold
could construct constant keyed values and diagnose duplicate literal keys earlier; that is a
proposal, not the current error stage.

#### A duplicate key is a process fault today

`AggregateKind::accumulate` asserts that a `Sole` group has at most one element.
`map([(1, 10), (1, 20)])` therefore compiles and panics while executing the duplicate group,
in both debug and no-assertions builds. The assertion is not a returned compile diagnostic or
an Option-valued lookup result.

The runtime has no query-data fault channel for this operation. The CLI host does not catch this
panic in its scheduler loop, so a duplicate key terminates the process and fails every request it
is serving. Replacing the assertion with an arbitrary winner would change map construction
semantics.
A query-local fault channel and compile-time checking of constant collections are separate work.

`set([1, 1])` instead consumes the repeated group with `Drain` and produces one key.
Explicit `map([k -> v for ...])` uses the same constructor path. Implicit re-keying selected
only by an annotation or lookup remains planned.
Literals are not the fault boundary: a map comprehension built from request data inherits this
process fault. The appropriate failure behavior for that case remains an open decision.

## Operations: how the trait layer dispatches [Planned]

The intended source interfaces are owned by
[collection types](../../../docs/chl-spec.md#63-direction-collection-types-decided),
[subscripts](../../../docs/chl-spec.md#39-subscript-and-attribute-access), and
[iteration](../../../docs/chl-spec.md#46-for--iteration).
This section records the proposed implementation strategy, not today's dispatch.

The proposal assigns per-type `Iterable`, `Index`, `Membership` and `Ordering` operations.
These collection interfaces are distinct from the solver's implemented arithmetic/comparison
trait tables. General contextual-parameter/typeclass resolution remains future work.

- `for x in c` places the requirement `Iterable(𝐶, Item=𝐸)` on `c`'s type and binds `x: 𝐸`
  ([chl-spec, 4.6 `for` — iteration](../../../docs/chl-spec.md#46-for--iteration)). The solver
  discharges it once `𝐶`'s head is known, as it discharges an operator's requirement, and a
  polymorphic `def` generalizes over it. The instances are built in: values for a structural
  collection, including every comprehension result; keys for `Set`; entries for `Map` and
  `FullMap`. A nominal type is related only to itself, so every producer of a value names the same
  head and the instance does not depend on where the value flows. The instance chooses which part
  of the existing iteration record to expose. Current lowering binds values and does not
  implement that dispatch.
- Optional lookup would decide membership at runtime; proven access would require a key
  refinement. The surface spellings are governed by the CHL reference, not duplicated here.
- Membership would test map/set domains and list/collection values. A key-membership guard
  would introduce the evidence required for proven lookup.
- `len(c)` places the built-in requirement `HasLen(𝐶)`
  ([chl-spec, Trait requirements](../../../docs/chl-spec.md#trait-requirements)). Each instance
  reads the size of the collection's domain: an `Array`'s static `𝑛`, a `List`'s witness range,
  the key count of a `Set`, `Map` or `FullMap`, and the position count of a `Collection`. A
  `FullMap`'s key type is a finite present-key domain, the only kind a producer constructs.
  Nothing implements it yet.
- Ordering would come from positional domains or an explicit ordering instance, rather than
  the incidental storage order of keyed data. Loop-carried dependencies and collection order
  remain distinct questions.
- The methods `keys`, `values` and `items` of `Map` and `FullMap`, and `keys` of `Set`, would
  expose lazy views without copying collection data. The nominal `Map` has no edge to
  `Collection(V)` ([Telling `Set` and `Map` apart](#telling-set-and-map-apart-decided)), so these
  views are the only route to one, and `sum(m)` is an error where `sum(m.values())` is not.
  Current value iteration permits `sum(m)` when the values support summation.

The suggested re-pairing of an existing keyed domain is a representation plan, not an implemented
runtime-free conversion API. No surface view constructor should be inferred from these names.

## Lookup: membership discharge

Current `c[k]` lowers as function application. It requires the key type to be below the
collection's domain. `c[k]?` is checked lookup: it requires a compatible key type but decides
presence at runtime and returns `Option`. The
[CHL reference](../../../docs/chl-spec.md#39-subscript-and-attribute-access) owns the planned
replacement spellings.

A `FullMap(K, V)` parameter with a key of type `K` satisfies ordinary application.
That typing rule does not construct a value at such a domain. A concrete keyed domain requires
its own membership evidence; a known source element does not currently acquire it automatically.
Range-domain list subscripts are also rejected in the tested integer-index cases.

### The checked lookup `𝑐[𝑘]?`

Lowering emits `(c, k) ▷ lookup?`. `emit_apply` intercepts that builtin application and uses
`emit_lookup_checked` rather than the ordinary collection-application rule:

1. `keyed_access_types` obtains the domain, optional key binder and codomain. For a sum,
   its first witness must have kind `SubtypesOf(K)`; the sum is instantiated at `K`.
   A concrete function supplies its own domain.
2. `Typing::keyed_value_at` substitutes the key term into a dependent codomain.
3. `keyed_access_value` constrains the key below the domain's base, peeling refinements.
4. The rule returns `Option` of the value type and stamps the builtin with the concrete
   pair-to-Option function type.

The key constraint is directional. Joining the lookup key and collection keys at a common
supertype would admit a wrong-base key by widening instead of rejecting it.

An exact `Map(K, V)` parameter exposes a usable type at emission. A bounded parameter can
still be unresolved there and is rejected; binding the collection locally or giving the
parameter an exact annotation can avoid that boundary. `checked_lookup_boundaries` also
covers tuple targets and range domains. A tuple is a product, not a collection lookup target.

Emission computes the dependent result once. Later type checks recover the payload from the
stamped operator type rather than substituting again into predicates that planning may have
converted to point-free form. A second discharge could produce a different embedded term.

#### Runtime readiness and answer shape

`CheckedLookup` accepts either separate collection/key sources or paired rows. It searches
a streamed collection's domain for each key. A present key can yield `some(value)` before the
whole collection terminates. A missing key yields `none` only when the collection tile is
terminal; otherwise the operator emits no answer for that key yet.

An empty nonterminal tile is not proof of absence. A bare live domain can therefore leave a
missing key unanswered indefinitely. A materialized `Value::Function` differs: its binding
list is complete once that value arrives, so absence can be answered immediately without waiting
for an enclosing stream to terminate. Transactional map reads can supply this materialized form.

The two compilation shapes are:

- A shared collection independent of the key iteration. `simplify` turns
  `⟨const(c), g⟩ ≫ lookup?` into `g ≫ (c ▷ curry(lookup?))` so the collection is read
  as a separate source instead of broadcast into every key row.
- Paired collection/key rows. A materialized map cell can vary by row; a streamed collection
  leg is searched as a shared tile. Runtime keys retain their own domain positions when only
  some rows have answers.

`reject_unanswerable_lookup_collection` accepts a one-level streamed function with a scalar
codomain, or a scalar containing one materialized function value. A streamed group-by has a
collection-valued codomain, so its checked lookup fails conversion even though inference
can type the dependent Option result. Materialized maps are not subject to that same
streamed-scalar-codomain restriction.

Runtime details and release behavior belong to `interpreter/tile_operators/lookup.rs`.
The collection docs do not promise query completion from an Option result type alone.

### Prerequisite: the proof has to survive being consumed

A key produced by a collection's key morphism should support membership in that producer's image.
The current compiler does not implement that introduction rule. The regression
`a_key_from_the_source_does_not_yet_carry_its_key_domain` rejects direct source elements,
applications of the key function and projected source fields. This is missing functionality,
not a decision that such keys must remain unusable.

A key whose type names a sum's witness through the sum's value is a member by its type; see
[Projecting a sum's witness](#projecting-a-sums-witness).

## Projecting a sum's witness

A sum `𝑐 : Σ (σ : 𝐾). 𝐷[σ] ⤇ 𝑉` is a pair of a witness and a collection over it, and it has the
pair's two projections:

- `σᵢ(𝑐)` is the `i`th witness, as a type, counting the sum's binders outermost first
  (`Type::WitnessProjection`). It is how a type outside the sum names `σ`, which no reference to
  `σ` can do outside the sum's own type.
- `unbox(𝑐)` is the collection, at the type `𝐷[σ ↦ σ₁(𝑐)] ⤇ 𝑉` (`Builtin::Unbox`).

`unbox` inverts `box`: `box` pairs a collection with the one candidate its domain is, and
`unbox(box(𝑥))` is `𝑥` over `σ₁(box(𝑥))`, which erasure rewrites to that candidate.

A projection is a candidate like any other: the domain of `𝑐` outside its type is `𝐷[σ ↦ σ₁(𝑐)]`,
built by the substitution realization and erasure already perform (`instantiate_witness`). So a
sum over `σ` has domain `σ₁(𝑐)`, a filtered one `{σ₁(𝑐) | 𝑞}`, and one over a product of two
binders `(σ₁(𝑐), σ₂(𝑐))`. A plain collection binds no witness and has no projection.

`σᵢ(𝑐)` holds the term `𝑐` as a refinement holds its predicate: shared by `Rc` and compared by
normal form. `𝑐`'s type carries the sum's binders, so the projection reads a witness's kind and
bound off its own term. It holds the binder's position rather than its id: inference renames a
sum's binders into each consumer's scope, and the term and the position stay the same. A type that
mentions `σᵢ(𝑥)` and leaves the binding of `𝑥` substitutes `𝑥`'s definition, as any type naming a
`let` binder does ([`let` binders and scope exit](type-inference.md#let-binders-and-scope-exit)).
Planning's erasure of a determined witness rewrites `σᵢ(𝑐)` to the candidate, and `unbox` of a
collection whose witness it erased to that collection. It reads the witness off the term the
projection quotes, under the id that term was typed with.

### Typing

`unbox` has no scheme. Its result type is the sum's body as a function of the witness, which a
scheme cannot quantify over, so each use carries a dependent type stamped for its argument's sum,
`(𝑐 : Σ (σ : 𝐾). 𝐷[σ] ⤇ 𝑉) ⇒ 𝐷[σ ↦ σ₁(𝑐)] ⤇ 𝑉` (`ty::unbox_type`), and the post-inference check
holds the stamp to that rule (`check_unbox`), as it does `strength_over`'s. Applying it discharges
`𝑐` to the argument. A key typed `σ₁(𝑐)` then applies to `unbox(𝑐)` as to any collection over that
domain. Two projections are equal when their positions are and their terms are equal by normal
form.

A witness with no key bound has no extent: one over `Type`, or over `Enumerated` candidates whose
key types differ. A consumer that needs the extent of a projection of one refuses it by name.

### A projection at runtime

A projection has no runtime representation of its own. A sum's value is a `Tile::DataFunction`
holding its keys in its domain column, and the extent of `σᵢ(𝑐)` is the `i`th witness's key bound
(`OpConversionContext::witness_domain_extent`). `unbox(𝑐)` is `𝑐`'s value tiled at that bound: a
one-leg flat merge where the value stands at its own domain, as a `[1, 2]` bound as a `List(Int)`
stands at `[0, 1]`, and `𝑐`'s operator where it already stands at the bound or is a collection
materialized into a value, which carries its keys. `unbox(𝑐)` carries
`𝑐`'s keys, so it is an iteration source exactly when `𝑐` is. No `IterateExtent` ranges over a
projected domain, since it would enumerate the whole bound.

### A `for` loop over a sum

`mut_elim` types the history of `for 𝑥 in 𝑐` over `𝑐`'s projected domain, and the body reads the
item as `__pos ▷ unbox(𝑐)`. The induction driver takes its positions from the source tile's keys,
as for a map source ([The store](../../interpreter/design-operators.md#the-store)).

A loop over an outer loop's element ranges over the projected domain of that element, so the
nested positions are a dependent tuple whose second component is `σ₁(𝑡(𝑥))` for the row `𝑡(𝑥)`
the outer position `𝑥` reads. Its keys at `𝑥` are the row's own:
`(λ 𝑥 → unbox(𝑡(𝑥))) ≫ map_domain` (`planning/correlated.rs`, `row_keys_family`).

## Compiling a conditional collection

```
c: Bool = True
sum(box([1, 2]) if c else box([1, 2, 3]))
```

The arms have domains `[0, 1]` and `[0, 2]`. The `Case` therefore has type
`Σ (𝜎 : [[0, 1], [0, 2]]). 𝜎 ⤇ Int`, retaining the selected arm's domain; see
[The domain join needs `box`](type-inference.md#the-domain-join-needs-box).

`planning/conditionals.rs` realizes a conditional collection as a union of restricted arms,
`⧺ᵢ (armᵢ | π̂ᵢ)`. Each restriction is the arm's first-match path condition. Exactly one
condition holds; only that leg can contribute rows, though the selected arm may itself be
empty. The union's tagged domain differs from the sum's domain, so `Realize` asserts the
original type rather than deriving it by subtyping. See
[Planning asserts the type it replaces](type-inference.md#planning-asserts-the-type-it-replaces).
At runtime the value is the leg holding rows, keyed by its own keys: op-conversion compiles a
`Realize` over a copairing as a flat merge at the key bound the sum's type declares
(`UnionOperator::new_flat_over`), so no key carries its leg's tag.

Planning can instead erase a determined witness or retain a materialized one. Erasure
removes the introduction and instantiates its type references. A materialized witness keeps
the `box`, and the value carries its keys. This supports `List(𝑇)` over `UIntRanges` and
`Map(𝐾, 𝑉)` over `SubtypesOf(𝐾)`: `extent_of` supplies a key bound, not an enumeration.
A determined row must also remain materialized when its enclosing position requires a sum.
The type-level erasure exceptions are specified in
[Witness erasure](type-inference.md#which-case-a-site-realizes-and-what-a-leg-instantiates).

A materialized collection still cannot supply an `IterateExtent` from its type alone.
The standalone `WitnessRef` case in `extent_of` rejects that use. A comprehension can
instead compose its generator with the collection, taking the keys from its values; see
[Sum-source generators](optimization.md#a-generator-over-a-sum-composes-with-its-source).

A `for` loop over a sum types its history over the source's domain; see
[A `for` loop over a sum](#a-for-loop-over-a-sum).

`erase_determined_boxes` decides whether to retain a row's introduction from the position it fills.
Inlining can move a let-bound row into a jagged literal position, where its box is preserved. A row
read from mutable storage has already had its determined witness erased. Such a bare row cannot fill
a sum-typed element position; `reject_rows_fixed_elsewhere` reports the mismatch.

Realization operates at a site whose type carries the witnesses and whose subtree contains
their conditionals. Unboxed arms sharing a domain need no sum; boxed arms sharing a domain
still have a one-candidate sum during inference. A same-domain boxed conditional is realized,
not erased: realization records its witness in `realized`, and `collapse_determined_sums`
preserves it so the `Realize` assertion retains its binder.

### A conditional chosen per row

A conditional whose condition reads a lambda's binder, a loop's or a comprehension's, chooses an
arm per row, and realization does not reach it. Lambda elimination compiles the `Case` in the
lambda's body as a fan-out of morphisms out of the row, `⊔ᵢ (filter_values(π̂ᵢ) ≫ (armᵢ ▷ const))`:
each leg keeps the rows whose gate holds and gives each of them its arm. The legs' union is a
disjoint join over the rows. A filter's predicate is planned as a lifted term
([Planning a lifted term](optimization.md#planning-a-lifted-term)), so a conditional in one reads
the element the same way.

With arms over one domain, every row's value is a collection over that domain. With boxed arms it is
a sum, and the union's codomain binds a witness per row. `erase_determined_boxes` reads that demand
through each leg: `walk_children_with_demand` hands a chain's last morphism the chain's codomain,
and the argument of `𝑥 ▷ const` the codomain it answers at every input, so each arm's `box` stays,
materialized as a jagged list literal's rows are. The iteration walk looks through a standing `box`
to give its argument an iteration source (`mark_component_source`).

At runtime the fed union merges rows whose values are collections. `UnionOperator` flattens the
arms' domain to the rows they share whatever their codomain holds, and arms whose rows have
different domains merge at the bound the node's type declares, as a list literal of boxed rows
does (`OpConversionContext::witness_domain_extent`).

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

Over a product domain, each predicate read is instantiated with its position's chosen arm.
Equal candidate kinds do not identify positions: two independent conditionals can have the
same kind. Source matching uses both the sum's kind and the index reading it. Predicate
type slots must use the site's binder names; see
[Binder resolution at materialization](type-inference.md#binder-resolution-at-materialization).

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
inside each consumer, where the erasure reaches the term but not every type that named it.
Materializing the conditional rather than realizing it would remove the copy, by letting one
value serve several consumers; planning realizes it, so the copy is the only compiling form. It
would also make this substitution one choice among several rather than the only expressible
form — the point at which the duplication becomes a cost question instead of an obligation.

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
`an_inline_union_generator_beside_a_second_generator` and
`a_let_bound_union_generator_beside_a_second_generator` tests in
`tests/it/compilation_pipeline/scalars_collections.rs`. Compiling a site's witnesses together
is what keeps every generator's domain a plain range, so no union is ever read at an index.
A tagged fed copairing, demultiplexing the input by tag and re-tagging each arm's output, is
what would let the legs be per conditional rather than per arm tuple.

A site therefore **names** its witness rather than being it: beside a second generator the
index is a product, so the filter rides `{(𝜎, 𝐷) | 𝑝}` and every rule keyed on the witness
matches a *mention* of it rather than the whole domain. Reading the whole domain makes the
product a silently different case, which emits the site's chain a second time over a witness
that has no extent.
