# Collections

CCL represents a collection as a data function `D ⤇ V`: the domain identifies its data positions,
and the codomain describes the value at each position. This reference owns the representation,
constructor lowering and checked-lookup implementation. The
[CHL collection reference](../../../docs/chl-spec.md#63-direction-collection-types-decided)
owns the source-language interface and its planned changes.

`Set`, `Map` and `FullMap` are nominal types declared in `std`. Their representations are data
functions, and their `Iterable` instances choose keys or entries as the iteration elements.
`Array`, `List` and `Collection` are structural collection types.

A witness is a binder whose candidate domains are classified by a `TypeKind`. The general
rules are owned by [Subtyping for sums](type-inference.md#subtyping-for-sums); this document
specifies how the collection constructors use them.

## Index range notation

`Type::UIntRange(n)` renders as `0..n`: the unsigned indices from zero up to, but not including,
`n`. The empty domain is `0..0`, and the domain holding only zero is `0..1`. The rendering has no
brackets, so a range domain never reads as a list literal: `0..3 ⤇ Int` is a collection of three
integers, and `[0, 3]` is a two-element list. These are rendered types, not CHL expressions; a
source annotation writes `Array(n, T)` for a collection over `0..n`.

A runtime `Extent::UIntRange` renders in the same notation. Released indices can leave several
intervals, rendered as `1..3 ∪ 5..8`. An interval holding `u64::MAX` renders with an inclusive
endpoint, `start..=end`, because its exclusive endpoint does not fit in `u64`. Interval
predicates (`src/interpreter/tiling/predicate.rs`) keep their bracket notation.

## The six collection types

`Array`, `List` and `Collection` lower through `lower_type_application` in `lower/stmts.rs`.
`Set`, `Map` and `FullMap` resolve to the nominal declarations in `std`:

| Annotation | CCL type or nominal representation | Domain information |
|---|---|---|
| `Array(n, T)` | `UIntRange(n) ⤇ T` | A statically written length. `n` must be a non-negative integer literal representable as `usize`. |
| `List(T)` | `Σ (D : UIntRanges). D ⤇ T` | Some unsigned index range; the annotation does not name its length. |
| `Set(K)` | Nominal, wrapping `Σ (D : SubtypesOf(K)). D ⤇ unit` | A subset of key type `K`, with unit values. |
| `Map(K, V)` | Nominal, wrapping `Σ (D : SubtypesOf(K)). D ⤇ V` | A subset of key type `K` with values of type `V`. |
| `FullMap(K, V)` | Nominal, wrapping `(k: K) ⤇ V(k)` | The domain is `K` itself, not a sum witness. |
| `Collection(T)` | `Σ (D : Type). D ⤇ T` | An abstract domain without a narrower kind restriction. |

`Array` has an explicit domain. `List` and `Collection` are sums. A sum requires a term such as
`box`; a subtype constraint does not insert one. For example, `box([1, 2])` can satisfy
`List(Int)`, whereas the bare literal has a concrete range domain. `Set` and `Map` wrap sums
that their constructors introduce internally. `FullMap` wraps an explicit-domain collection.
Widening a sum follows the kind/body relation.

The abstract domain remains part of a collection value even when a consumer cannot name it
statically. `Collection`'s `Type` kind admits every domain kind, but does not supply a runtime
witness implementation; see
[Compiling a conditional collection](#compiling-a-conditional-collection).

`FullMap(_, V)` lets inference recover a group-by's present-key domain, and only a group-by
satisfies it, since `groupby` is the only operation that builds a `FullMap`.
`only_a_group_by_satisfies_a_full_map_annotation` and
`a_groupby_is_a_full_map_at_either_strength` cover annotation cases.
A `FullMap(Int, Int)` parameter can be type-checked with a proven integer lookup `m[1]!` without
establishing that a tested concrete collection can inhabit the parameter type.

A data-function type `𝐷 |=> 𝑉` lowers to `(k: 𝐷) ⤇ 𝑉` under a fresh binder, as
the representation of `FullMap(𝐾, 𝑉)` does (`Type::full_map_of`), and its funkind follows its
domain:

- A bare `_` domain gets a funkind hole (`FunKind::data_hole`), which normalization replaces with
  a fresh data funkind at each occurrence, plain or a sum. A lowered annotation is cloned by every
  use of an alias, so the hole is a marker rather than a variable the uses would share.
- Any written domain, a type parameter included, gets a plain collection's funkind.
- An instance's associated type closes its funkind holes to a plain collection's
  (`close_kind_holes` in `lower/traits.rs`).

The table does not promise that every declared lookup or iteration interface is implemented.
Those boundaries are specified under [Lookup](#lookup-membership-discharge) and
[Operations](#operations-trait-dispatch).

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

### The empty collection's key type comes from its uses

`map([])` and `set([])` derive their key type from
[the key morphism's image](#the-key-domain-is-the-key-morphisms-image), and an empty source
supplies no key value, so the literal's element type is pinned as any empty literal's is. Two
things carry its uses to the pin:

- **One literal.** The group-by's expansion copies its collection into the key domain's predicate
  and the groups' refinement, and a copy in a predicate keeps its own variables, which the pin,
  walking terms only, never reaches. So A-normalization names a literal collection once
  (`anf`, the `GroupBy` arm), and every copy reads the one binding the pin decides.
- **The annotation's key type.** A `Set(𝐾)` or `Map(𝐾, 𝑉)` annotation relates the key domain to
  `SubtypesOf(𝐾)`. Membership adds an upper bound from which the empty element's type can be
  determined ([The type of a position](type-inference.md#the-type-of-a-position)).

`map`'s entry is declared a pair, so its element is the pair `(𝐾, 𝑉)`, and the pin decides each
component that no value reaches the same way. With no use, the element is unit, and a map's is
`(unit, unit)`.

### `empty_map()` [Interim]

`empty_map()` constructs an empty nominal map without deriving its types from entries:
`Map(𝐾, 𝑉)` around `Σ (σ : SubtypesOf(𝐾)). σ ⤇ 𝑉`. A `Map(𝐾, 𝑉)` annotation
fixes its parameters. A `Set(𝐾)` annotation is rejected: it names another nominal type.

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
[Telling `Set` and `Map` apart](#telling-set-and-map-apart).

## The collection type is declared, not read off the shape

`Iterable` selects an iteration element by collection type: values for structural collections,
keys for sets, and entries for maps and full maps. A function shape alone cannot identify that
intent. A set and a map with unit values have the same representation, while their nominal
identities select different instances. Loops and comprehensions call `Iterable::elements`;
they do not infer the intended collection type from the representation's shape.

## Telling `Set` and `Map` apart

The private constructors preserve each collection's identity. `Set` and `Map` obtain their
representations from `@Builtin`. Their payloads are sums over `SubtypesOf(K)`, with unit values
for `Set` and values of type `V` for `Map`. `FullMap` declares its constructor in CHL with
payload `(𝑘: 𝐾) ⤇ 𝑉(𝑘)`. Variance follows these payload types.

The constructor stays in the runtime value. An operation extracts the payload through a one-arm
`match`. The representation gives no subtyping relation to a structural collection. An entry
comprehension builds a structural collection from the values it selects.

### Keys and entries

A `Set` iterates its keys, and a `Map` or a `FullMap` its entries. `Iterable`'s `elements` of each
is its representation, taken out of the constructor, through `map_domain` for a `Set` and
`entries : (𝐷 ⤇ 𝑉) ⇒ (𝐷 ⤇ (𝐷, 𝑉))` for the other two. The `@Builtin` instances in `std` build that
term at coalescing (`apply_collection_primitive` in `infer/solve.rs`). A loop over a group-by binds
an entry, `for _ -> g in groupby(xs, key)`, and a loop over a map's values is `for _ -> v in m`.

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

This explicit-domain function is wrapped by `FullMap::new`. A `FullMap(_, _)` annotation,
exact or bounded, preserves and consumes the group-by's nominal type
(`a_keyed_annotation_compiles_and_runs`). A `Map(_, _)` annotation names another nominal type
and does not accept a group-by.

A checked lookup substitutes its key into the dependent group type during inference.
The streamed collection-valued answer is rejected later at operator conversion; see
[The checked lookup](#the-checked-lookup-𝑐𝑘).

### The key domain is the key morphism's image

`present_key_domain` in `comprehension.rs` constructs
`{K | __elem ▷ ((c ≫ key) ▷ collection_contains)}`, with `c ≫ key` indexed as a loop is, to
`λ __iter_record → __iter_record ▷ c ▷ key`, the key at each of `c`'s positions. The predicate retains the producer morphism rather than an opaque key-set identifier. Its structural identity therefore depends
on the named term and its free references, not merely on the keys that term happens to produce.

The helper shares one `SharedHole` between the refinement base and the morphism's codomain.
Using only the builtin scheme would leave a one-way bound instead of establishing that identity.
`expand_group_by` builds the domain once, and a re-keying constructor's iteration binder reuses
both its key type and its predicate allocation. Independently constructing a similar domain would
create separately inferred predicate copies.

The key domain is stamped before inference, when the group-by is expanded. Delaying it until coalescing can leave a keyed-sum
entry constraint with an unresolved candidate rather than the concrete membership-bearing domain
it needs. An unresolved candidate's membership is decided where it materializes
([Membership is decided at materialization](type-inference.md#membership-is-decided-at-materialization)).

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

An iteration site over a present-key domain enumerates the keys instead of testing membership:
its source is `𝑚 ▷ converse ▷ map_domain`, the image of the membership's collection `𝑚`, and the
domain's other refinements restrict it (`membership_keys` in `planning/iterate.rs`). A
comprehension whose element ignores the group reaches this, `[1 for _ -> g in groupby(xs, key)]` over
a list `xs`, or `[1 for v in ages]` over a map `ages`, since nothing applies the partition.

The source enumerates the domain level by level (`domain_keys` in `planning/iterate.rs`). A level
takes its keys from its membership when it has one and from its base otherwise, and its other
refinements restrict those keys. A product with a refined or projected component takes each
component's keys this way, broadcasts each later component's keys over the earlier ones with
`const`, and `uncurry`s them to the one level of tuple keys the domain states. A component reads
no other component, since a dependence is a dependent tuple, so the broadcast is exact. Over a map
`ages` with two entries, `[1 for v in ages for w in [1, 2]]` enumerates the two keys of `ages`
under each of two positions. A hash join's leaf iterates its arm's extent rather than its keys,
so a join with such a component is refused as an internal error (`extent_iteration` in
`planning/join.rs`).

Take `ages = map([("a", 1), ("b", 2)])`. The membership's collection `𝑚` is `ages ≫ key`, the
entries' key column `[0 ↦ "a", 1 ↦ "b"]`, and its image is `{"a", "b"}`, so `[1 for v in ages]`
iterates the two keys. The map `ages` itself is `["a" ↦ 1, "b" ↦ 2]`, whose image is the values
`{1, 2}`.

Producer-bearing domains expose two limitations:

- A producer term is embedded in the type, so its structure can appear at many type sites.
- Different spellings, such as a bound source and its inlined literal, need not reconcile.
  The [SMT fallback](type-inference.md#semantic-entailment-as-a-fallback) does not supply
  collection-membership axioms or a general producer-identity proof.

Naming the producer makes a membership-introduction rule expressible; it does not mean that
applying its key morphism already proves membership. The current rejection is recorded under
[Prerequisite](#prerequisite-the-proof-has-to-survive-being-consumed).

### Constructor lowering: runtime `groupby` now, constant-folding later

The re-keying constructors build concrete data functions before wrapping them:

| Constructor | Key morphism | Group collapse | Result |
|---|---|---|---|
| `set(xs)` | Identity on an element | `Drain` | Present-key domain to `unit`. |
| `map(entries)` | First projection of a pair | `Sole`, then second projection | Present-key domain to the entry value. |

Lowering keeps a `GroupBy` node until after A-normalization. Its expansion shares the normalized
source across the key predicate, group predicate, and group body. A-normalizing them independently
can introduce different binders for the same source, so inference cannot identify their predicates.
A collapse maps the groups under the same key domain.

The collapse must consume its group. For a set, replacing `Drain` with a function that ignores
the group would leave the source without the consumer through which planning assigns an iteration
site. Duplicate set elements are absorbed by the drain; duplicate map keys reach `Sole`.

Both constructors apply `box` to the re-keyed collection, then wrap the sum in the private
nominal constructor: `Set::rep` or `Map::rep`. Source writes
`m: Map(Int, Int) = map([1 -> 10, 2 -> 20])`. `groupby` instead wraps its explicit-domain result
in `FullMap::new` without boxing. `list(...)` is not a surface builtin; `box` introduces a
structural list sum. Annotation-driven insertion of re-keying constructors remains planned.

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

## Operations: trait dispatch

The implemented `Iterable` and `Indexable` interfaces are traits declared in `std`.
User-declared nominal types supply instances through ordinary trait declarations.
The compiler supplies the `@Builtin` instances for `Set`, `Map` and `FullMap`, and answers
structural collections directly through the collection rule.

`for x in c` calls `Iterable::elements(c)`, requires `Iterable(𝐶)` of `c`'s type, and binds `x`
to each value of `Elements`. A structural collection is its own `Elements`. A set exposes keys;
a map or full map exposes entries `(key, value)`. A generic definition retains the requirement.
See [A collection is answered off the table](type-inference.md#a-collection-is-answered-off-the-table).

Subscripts call `Indexable::entries`; [Lookup](#lookup-membership-discharge) specifies checked
and proven access. An entry comprehension such as `[v for _ -> v in m]` exposes a structural
collection of map values, so the proposed view methods are not its only possible interface.

Separate membership and ordering interfaces, and the lazy `keys`, `values` and `items` methods,
remain proposals. Membership would distinguish map/set keys from structural collection values.
Ordering would come from a positional domain or an ordering requirement, independently of
incidental keyed storage order. The source contracts are owned by
[collection types](../../../docs/chl-spec.md#63-direction-collection-types-decided),
[subscripts](../../../docs/chl-spec.md#39-subscript-and-attribute-access), and
[iteration](../../../docs/chl-spec.md#46-for--iteration).

## Lookup: membership discharge

A subscript reads its collection through `Indexable`, the `std` trait whose function `entries`
answers the collection as the function from each of its keys to the value there, of type
`Entries`. Lowering writes `c[k]` as `(c ▷ entries, k) ▷ lookup?` and `c[k]!` as
`k ▷ (c ▷ entries)`. A structural collection is its own `Entries`, by the collection rule, and
coalescing removes the call. `Set`, `Map` and `FullMap` have `@Builtin` instances whose `Entries`
is their representation, and coalescing replaces the call with the `match` that takes the
representation out of its constructor.

Where `c`'s type is known at the subscript, emission types `c ▷ entries` as that type's
`Entries` directly, since both lookup rules read the function's structure where they stand.
Where it is not, as for a parameter of an unannotated lambda, the call's obligation waits for
the type, and the proven lookup is typed against the call's result variable as an application
of an unknown function is. ANF leaves `c ▷ entries` in place over an atomic `c`, so the lookup
reads `c`'s own binding.

The proven lookup `c[k]!` is application of `c ▷ entries`. It requires the key type to be below
the collection's domain. `c[k]` is checked lookup: it requires a compatible key type but decides
presence at runtime and returns `Option`. The
[CHL reference](../../../docs/chl-spec.md#39-subscript-and-attribute-access) owns the spellings.
A direct call `c(k)` is application of `c` itself, so it reaches a structural collection only.

A `FullMap(K, V)` parameter with a key of type `K` satisfies ordinary application.
That typing rule does not construct a value at such a domain. A concrete keyed domain requires
its own membership evidence; a known source element does not currently acquire it automatically.
A list's proven lookup accepts a `UInt` key whose refinement entails the range bound, such as
`xs[int_to_uint(1)]!` over `0..3` (see
[Semantic entailment as a fallback](type-inference.md#semantic-entailment-as-a-fallback)).

### The checked lookup `𝑐[𝑘]`

Lowering emits `(c ▷ entries, k) ▷ lookup?`. `emit_apply` intercepts that builtin application
and uses `emit_lookup_checked` rather than the ordinary collection-application rule:

1. `keyed_access_types` obtains the domain, optional key binder and codomain. For a sum,
   its first witness must have kind `SubtypesOf(K)`; the sum is instantiated at `K`.
   A concrete function supplies its own domain.
2. `Typing::keyed_value_at` substitutes the key term into a dependent codomain.
3. `keyed_access_value` constrains the key below the domain's base, peeling refinements. The
   base of a range `0..𝑛` is `UInt`, so a list's checked lookup at a key outside the range types
   and answers `none`.
4. The rule returns `Option` of the value type and stamps the builtin with the concrete
   pair-to-Option function type.

The key constraint is directional. Joining the lookup key and collection keys at a common
supertype would admit a wrong-base key by widening instead of rejecting it.

An exact `Map(K, V)` parameter exposes a usable type at emission, and a bounded one
`m <: Map(K, V)` reaches the subscript's `Indexable` requirement from above, which a nominal
bound settles as a lower one does. `checked_lookup_boundaries` also
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
- `unbox(𝑐)` is the collection, at the type `(𝐷 ⤇ 𝑉)[σ ↦ σ₁(𝑐)]` (`Builtin::Unbox`), every
  binder of the sum read as its projection.

`unbox` inverts `box`: `box` pairs a collection with the one candidate its domain is, and
`unbox(box(𝑥))` is `𝑥` over `σ₁(box(𝑥))`, which erasure rewrites to that candidate.

A projection is a candidate like any other: the domain of `𝑐` outside its type is `𝐷[σ ↦ σ₁(𝑐)]`,
built by the substitution realization and erasure already perform (`instantiate_witness`). So a
sum over `σ` has domain `σ₁(𝑐)`, a filtered one `{σ₁(𝑐) | 𝑞}`, and one over a product of two
binders `(σ₁(𝑐), σ₂(𝑐))`. A plain collection binds no witness and has no projection.

The subscript counts the sum's binders, not its candidates, the term selects which value's witness
is meant, and nesting adds no positions. Two examples:

- **One binder, per row.** The jagged rows `box([box([1]), box([2, 3]), box([4, 5, 6])])` have
  type `Σ (τ : [0..3]). τ ⤇ Σ (σ : [0..1, 0..2, 0..3]). σ ⤇ Int`. Every row is a sum of its own,
  and its domain is `σ₁` of that row: `σ₁(box([1]))`, `σ₁(box([2, 3]))` and
  `σ₁(box([4, 5, 6]))`, which are `0..1`, `0..2` and `0..3` at runtime. A loop over the row
  `𝑡(𝑥)` at outer position `𝑥` ranges over `σ₁(𝑡(𝑥))`, whose keys are that row's own. The outer
  list is a separate sum with a `σ₁` of its own, whose one candidate is `0..3`.
- **Three binders, one value.** With `c : Bool`, the comprehension

  ```
  [x + y + z for x in (box([1]) if c else box([1, 2]))
             for y in (box([3]) if c else box([3, 4]))
             for z in (box([5]) if c else box([5, 6, 7]))]
  ```

  has type `Σ (σ : [0..1, 0..2]). Σ (τ : [0..1, 0..2]). Σ (υ : [0..1, 0..3]). (σ, τ, υ) ⤇ Int`:
  one collection over a tuple domain, with three witnesses. `Display` prints all three binders as
  `σ`; `CCL_SHOW_BINDERS=1` tells them apart. Outside its type the domain is
  `(σ₁(𝑐), σ₂(𝑐), σ₃(𝑐))`, and `σ₃(𝑐)` is the third generator's range: `0..1` when `c` holds and
  `0..3` otherwise.

`σᵢ(𝑐)` holds the term `𝑐` as a refinement holds its predicate: shared by `Rc` and compared by
normal form. `𝑐`'s type carries the sum's binders, so the projection reads a witness's kind and
bound off its own term. It holds the binder's position rather than its id: inference renames a
sum's binders into each consumer's scope, and the term and the position stay the same. A type that
mentions `σᵢ(𝑥)` and leaves the binding of `𝑥` substitutes `𝑥`'s definition, as any type naming a
`let` binder does ([`let` binders and scope exit](type-inference.md#let-binders-and-scope-exit)).
An elimination can know the sum before the term's type exposes it. `WitnessProjection::through`
saves the sum binders when their candidate types, including quoted type slots, contain no
inference variables. The saved sum has a unit codomain.
It is a type child in the projection's scope. Substitution, binder conversion,
freshening, coalescing and free-name checks reach it. Equality and hashing ignore both this type
and the term's type slots.

Realization rewrites `σᵢ(𝑐)` in a leg to the candidate the leg chose. It reads the witness off the
term the projection quotes, under the id that term was typed with.

### Typing

`unbox` has no scheme: its result type is the sum's body as a function of the witness, which a
scheme cannot quantify over. Inference types each use as an elimination
([An elimination reads a sum through a term](type-inference.md#an-elimination-reads-a-sum-through-a-term)),
and once every argument is settled the pipeline removes each `unbox` of a plain collection
(`drop_plain_unboxes` in `src/ccl/context.rs`). The post-inference check, which knows the
argument's sum, stamps `(𝑐 : Σ (σ : 𝐾). 𝐷[σ] ⤇ 𝑉) ⇒ 𝐷[σ ↦ σ₁(𝑐)] ⤇ 𝑉` (`ty::unbox_type`) and
holds it to that rule (`check_unbox`), as it does `strength_over`'s. Applying either type
discharges `𝑐` to the argument. A key typed `σ₁(𝑐)` then applies to `unbox(𝑐)` as to any
collection over that domain. Two projections are equal when their positions are and their terms
are equal by normal form.

A witness with no key bound has no extent: one over `Type`, or over `Enumerated` candidates whose
key types differ. A consumer that needs the extent of a projection of one refuses it by name.

### A projection at runtime

A projection has no runtime representation of its own. A sum's value is a `Tile::DataFunction`
holding its keys in its domain column, and the extent of `σᵢ(𝑐)` is the `i`th witness's key bound
(`OpConversionContext::witness_domain_extent`). `unbox(𝑐)` is `𝑐`'s value tiled at that bound: a
one-leg flat merge where the value stands at its own domain, as a `[1, 2]` bound as a `List(Int)`
stands at `0..2`, and `𝑐`'s operator where it already stands at the bound or is a collection
materialized into a value, which carries its keys. A witness over the universe, such as a
`Collection(𝑇)`'s, bounds no key type, so `unbox(𝑐)` is `𝑐`'s operator unchanged.
`unbox(𝑐)` carries `𝑐`'s keys, so it is an iteration source exactly when `𝑐` is. No
`IterateExtent` ranges over a projected domain, since it would enumerate the whole bound.

### A `for` loop over a sum

`mut_elim` types the history of `for 𝑥 in 𝑐` over `𝑐`'s projected domain, and the body reads the
item as `__pos ▷ unbox(𝑐)`. The induction driver takes its positions from the source tile's keys,
as for a map source ([The store](../../interpreter/design-operators.md#the-store)).

A source `𝑒` that is not a variable and reads nothing an enclosing loop binds or writes is bound
first, as `let __src = 𝑒 in for 𝑥 in __src` (`mut_elim::bind_sum_loop_sources`). The projection
quotes `__src`, and a pass rewriting `𝑒` rewrites the binding's definition. The binding stands
outside every enclosing loop, so the domain depends on no enclosing position. A source computed per
position of an enclosing loop is quoted as written.

A loop over an outer loop's element ranges over the projected domain of that element, so the
nested positions are a dependent tuple whose second component is `σ₁(𝑡(𝑥))` for the row `𝑡(𝑥)`
the outer position `𝑥` reads. Its keys at `𝑥` are the row's own:
`(λ 𝑥 → unbox(𝑡(𝑥))) ≫ map_domain` (`planning/correlated.rs`, `row_keys_family`).

## Compiling a conditional collection

```
c: Bool = True
sum(box([1, 2]) if c else box([1, 2, 3]))
```

The arms have domains `0..2` and `0..3`. The `Case` therefore has type
`Σ (𝜎 : [0..2, 0..3]). 𝜎 ⤇ Int`, retaining the selected arm's domain; see
[The domain join needs `box`](type-inference.md#the-domain-join-needs-box).

`planning/conditionals.rs` realizes a conditional collection as a union of restricted arms,
`⧺ᵢ (armᵢ | π̂ᵢ)`. Each restriction is the arm's first-match path condition. Exactly one
condition holds; only that leg can contribute rows, though the selected arm may itself be
empty. The union is a `Realized` node typed as the sum, each leg the sum's body at one candidate;
see [A realized conditional is typed as its sum](type-inference.md#a-realized-conditional-is-typed-as-its-sum).
At runtime the value is the leg holding rows, keyed by its own keys: op-conversion compiles it as
a flat merge at the key bound the sum's type declares (`UnionOperator::new_flat_over`), so no key
carries its leg's tag.

Every other sum is materialized: its `box` stays, and the value carries its keys. `box` is the
identity at runtime, since a collection carries its own domain, so a sum over one candidate
compiles to the operators its collection does. This supports `List(𝑇)` over `UIntRanges` and
`Map(𝐾, 𝑉)` over `SubtypesOf(𝐾)`: `extent_of` supplies a key bound, not an enumeration.
Iteration planning places an `iterate` beneath a standing `box`, and beneath `unbox(box(𝑥))`,
since an applied function's argument is a stream of its own (`planning::iterate::under_box`).

A materialized collection still cannot supply an `IterateExtent` from its type alone.
The standalone `WitnessRef` case in `extent_of` rejects that use. A comprehension can
instead compose its generator with the collection, taking the keys from its values; see
[Sum-source generators](optimization.md#a-generator-over-a-sum-composes-with-its-source).

A `for` loop over a sum types its history over the source's domain; see
[A `for` loop over a sum](#a-for-loop-over-a-sum).

A row a jagged list literal reads from a mutable variable does not compile: op-conversion converts
the literal as a constant, and takes a collection-valued element only written out as a list literal.

A conditional is realized where it stands. The `Case` is replaced in place by a `Realized` node
typed as the `Case` was, which keeps the `Case` as the term it stages. Every consumer reads the
conditional through `unbox`, over the projected domain `σ₁(𝑐)` of the `Case` term `𝑐`, so a
consumer's types quote the conditional rather than name its witness. The check after planning
rebuilds a consumer's result from the realized tree, and normal form reads the `Realized` node as
the `Case` it stages, so the rebuilt result equals the recorded one
([The check after planning reads planning's rewrites back](type-inference.md#the-check-after-planning-reads-plannings-rewrites-back)).
A `let`-bound conditional is realized once, in its binding, and its consumers share it.

Unboxed arms sharing a domain need no sum; boxed arms sharing a domain still have a
one-candidate sum. A same-domain boxed conditional is realized like any other, and the realized
conditional's type keeps its binder.

### A `match` selecting a collection

A `match` in value position whose arms are collections is a conditional collection. Lambda
elimination rewrites it to a guard `Case` and leaves it standing, as it leaves an `if` whose arms
are collections (`value_tag_case_to_guard_case`). Arm `𝑐ᵢ(𝑤ᵢ) → 𝑒ᵢ` becomes the guard
``𝑠 ▷ variant_is(`𝑐ᵢ)`` with body ``𝑒ᵢ[𝑤ᵢ ↦ 𝑠 ▷ variant_project(`𝑐ᵢ)]``. The tags are exhaustive,
so the last arm's guard is `true`. Planning realizes the result as it realizes any conditional
collection.

A `match` with one arm selects nothing, and lambda elimination binds its payload instead:
`match 𝑠 { 𝑐(𝑤) → 𝑒 }` is ``let 𝑤 = 𝑠 ▷ variant_project(`𝑐) in 𝑒``.

``variant_project(`𝑐)`` applied to one variant value, rather than to a collection of them, is the
payload: the collection itself where the payload is one. A value known to carry another tag holds
no rows of a collection payload, so that projection is the empty collection, complete. An unselected branch reads that projection, so its empty result completes the union.

### A conditional chosen per row

A conditional whose condition reads a loop's or a comprehension's variable chooses an arm for each
row:

```
for i in [1, 2]:
    out << sum([1, 2] if i > 1 else [3, 4])
```

Row `i = 1` takes `[3, 4]` and row `i = 2` takes `[1, 2]`, so the sink receives `7` and `3`.

Realization does not compile this conditional. The loop body is a lambda over the row, and lambda
elimination, which runs before planning, replaces the `Case` in it with one leg per arm:

```
⊔ᵢ (filter_values(π̂ᵢ) ≫ (armᵢ ▷ const))
```

A leg keeps the rows that pass its gate `π̂ᵢ`, the arm's first-match path condition, and gives
each of them its arm. Every row passes exactly one gate, so the union of the legs holds one value
per row.

A conditional in a filter's predicate compiles the same way, because the predicate is planned as a
lifted term ([Planning a lifted term](optimization.md#planning-a-lifted-term)):

```
out << sum([x for x in [1, 2, 3, 4, 5, 6, 7, 8] if x > sum([1, 2] if x > 4 else [3, 4])])
```

#### Boxed arms

Arms over one domain give every row a collection over that domain. Boxed arms over different
domains give each row a collection over the domain of the arm it selected:

```
for i in [1, 2]:
    out << sum(box([1, 2]) if i > 1 else box([3, 4, 5]))
```

Each row's value has type `Σ (σ : [0..2, 0..3]). σ ⤇ Int` and carries its own `σ`, so each
arm keeps its `box`, as every `box` does. A consumer that iterates a leg's arm finds the list
beneath the `box` (`mark_component_source`).

A loop over a conditional chosen per row reads it through `unbox`, so a type after the loop quotes
the conditional as written, `σ₁({ 𝑔(𝑥) → 𝑎; true → 𝑏 })`, while the tree holds its fan-out. Normal
form reads the fan-out applied to the row back as the `Case`, so the two compare equal
([Predicates are compared by normal form](type-inference.md#predicates-are-compared-by-normal-form)).
A-normalization binds the conditional ahead of the loop, and lambda elimination makes that binding
a collection over the enclosing positions. Nothing feeds a fan-out standing in a binding, so
planning puts an `iterate` over those positions in front of it (`iterate::is_iteration_bearing`).

#### At runtime

The legs are one stream of rows, split by their gates. `UnionOperator` merges them back into one
collection keyed by row, including where each row's value is a collection. Where boxed arms give
rows different domains, the merged collection keys each row's values by the bound the node's type
declares, the bound a list literal of boxed rows has
(`OpConversionContext::witness_domain_extent`).

### A leg is an arm

Each leg is one arm, gated by its first-match path condition `π̂ᵢ`. The arm's types are written at
the `Case`'s witness, which the leg instantiates with the arm's domain, in its refinement
predicates as well (`read_the_arm_instead` and `instantiate_witness_in_types` in
`src/ccl/planning/conditionals.rs`).

An arm typed `List(Int)` carries its domain in its value. A result over `UIntRanges` or
`SubtypesOf(𝐾)` can use `unbox` and the arm's domain projection. The result type supplies the
extent bound, and [checking the legs](type-inference.md#a-realized-conditional-is-typed-as-its-sum)
checks the projected domain for membership. For `Enumerated`, each candidate needs a leg with
a known domain. A nested conditional without such a domain stays for operator conversion.

Two conditional generators in one comprehension are two `Case`s, each realized where it stands.
The comprehension reads each source through `unbox`, so its domain is the product of their
projected domains, `(σ₁(𝑎), σ₁(𝑏))`, and each generator iterates the keys its realized source holds.
No union is read at a projected index.

