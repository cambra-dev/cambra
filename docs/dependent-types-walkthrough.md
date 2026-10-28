# Dependent types end to end

A walkthrough of how CCL types come to read terms (a group's key, a filter's predicate, an
outer loop's position) and of the rules that keep such types meaningful while the compiler
rewrites the program around them. Written for people who work on Cambra but have not worked
*inside* the dependent-type machinery.

This is a tour, not a specification. It describes the design as the docs on stack 313 state
it (draft PR #580 consolidates them), so some of what follows is not on `main` yet. The
documents it tours:

- `src/ccl/design/dependent-types.md`: the map. For each form it gives what binds, how a
  reference is stored, and what eliminates it.
- `src/ccl/design/type-inference.md` §4.5–4.8: Pi types and binder references, data vs
  compute functions, dependent sums, dependent tuples.
- `src/ccl/design/collections.md`: the collection types as sums, witness projections, and
  conditional collections.
- `src/ccl/design/type-parameters.md`, "Generalized types": what lambda lifting does to a
  type that names a binder.
- `src/ccl/design/ir.md`, "Every stored type is well-scoped": the one scoping rule.

Types below are written in the docs' notation and are often schematic. They are not
compiler dumps.

**The sections in one line each.** §1–2 cover why types read terms and the two ground rules
about collections. §3 lists the forms. §4–5 give the scoping rule and how a type spells a
binder. §6–7 cover inference under binders and what happens when a type leaves a binder's
scope. §8–9 are sums and dependent tuples. §10 is what lambda elimination does to all of
this. §11 walks the pipeline. §12 is the cheat sheet of invariants, worth keeping on screen
for questions.

---

## 1. Why a type has to read a term

CCL represents a collection as a **data function** `𝐷 ⤇ 𝑉`: the domain is the set of
positions that exist and the codomain is the value at each one. A callable function is a
**compute function** `𝐴 ⇒ 𝐵`. Once a collection is a function, the question "which keys does
this collection have?" is a question about a type, and programs answer it with values:

```
  groupby(c, key)                    the group at k holds the rows whose key is k
  [v for v in xs if v > r]           which rows exist depends on r
  r: List(Int) = box(…)              some length, but the type doesn't say which
  [x for xs in xss for x in xs]      the inner keys depend on which outer row
```

The first one is the canonical example. Lowering gives `groupby` this type:

```text
groupby(c, key) :
  (k : {K | k ▷ ((c ≫ key) ▷ collection_contains)})
    ⤇ ({i : I | key(c(i)) == k} ⤇ A)
```

Two things are going on here:

- The **codomain reads the binder `k`**: the inner collection's domain depends on which key
  you are at. This is a Pi type.
- The **domains are refinements whose predicates quote terms**: `c`, `key`, the comparison
  `== k`. A type holds a piece of the program.

A grouped collection displays like this:

```text
(k: Int) ⤇ ({[0, 2] | __elem ▷ xs ▷ key == k} ⤇ Int)
```

Every mechanism in this tour exists either to let a type say something like this or to keep
such a type true as the term it quotes is inlined, lifted, planned and compiled.

## 2. Two ground rules about collections

### Data and compute are different kinds of function

`FunKind` separates a data function (a collection) from a compute function (something you
call). Lowering decides the kind from the construct: lists, comprehensions, groupings and
unions are data, while lambdas and `def`s are compute, even a `def` that returns a
collection. A function-valued parameter can carry a **funkind variable** until an argument
pins it. Concrete `Data` and `Compute` are never related by subtyping, and a lost kind is a
rebuild error, never something to stamp back later.

### Data domains are invariant

A compute function's domain is contravariant, because a function that accepts more can stand
in for one that accepts less. A data function's domain is not an input contract. It is the
list of rows that exist. If it were contravariant, it would silently drop rows:

```
  [1, 2] if c else [1, 2, 3]

  contravariant:  join = [0, 1] ⤇ Int     sum(…) is 3 even when the else-arm ran
  invariant:      no join                 the conditional is rejected
```

So two collections over different domains that reach one variable meet as an **equation**,
which the solver draws as both edges. Two things follow, and they come back throughout the
tour:

- A program that wants "one of these two collections" has to say so with an explicit sum
  (§8).
- **A refinement on a collection's domain is data.** It decides which entries exist rather
  than stating a fact about a value already fixed (§10).

## 3. The forms

Eight forms make up "dependent types" in CCL. Four bind a term, two bind a type, and two bind
nothing but refer to something by quoting it.

| Form | Written | Binds, over | Eliminated by |
| --- | --- | --- | --- |
| Pi function | `(𝑥 : 𝐴) ⇒ 𝐵`, or `(𝑥 : 𝐴) ⤇ 𝐵` for a collection | `𝑥`, over the codomain (not the domain) | application: discharge `𝑥` to the argument |
| Refinement | `{𝐵 \| 𝑝}` | `__elem`, over the predicate | nothing; a substitution rewrites the predicate |
| Dependent tuple | `(𝑎 : 𝐴) × 𝐷(𝑎)` | each component, over the ones after it | projection `𝑝.𝑘` |
| History | `(𝑘 : 𝐷) ⤇ 𝑉` inside `Mut`/`feed` | the position `𝑘`, over the value | mutability elimination / `channelize` |
| Dependent sum | `Σ (σ : 𝐾). 𝐷 ⤇ 𝑉` | a type witness `σ`, over the sum's own type only | `unbox(𝑐)`, `σᵢ(𝑐)`; planning realizes or erases |
| Generalized type | `∀ (𝐷 <: 𝑇). …` | type parameters, over the type | instantiation at each use |
| Witness projection | `σᵢ(𝑐)` | nothing; it quotes the term `𝑐` | erasure of a determined witness |
| Family application | `𝐷₁(𝑘)` | nothing; it applies a family to binders | instantiation |

Two orientation points:

- `List`, `Set`, `Map` and `Collection` annotations are all **sums** (§8). `Array` and
  `FullMap` are not.
- A term quoted inside a type (a predicate, a projection's term, a family's argument) keeps
  its *own* binders as names. They are compared by position (§5).

## 4. The one scoping rule

Everything else hangs off this rule:

> **Every stored type is well-scoped, at every phase.** Each name free in a type slot is bound
> by a term binder around the slot's node, or is one of the program's free names (its sources
> and sinks).

Inside a type, the type's own binders also bind:

- a Pi binder over its codomain
- a dependent-tuple component over the components after it
- `__elem` over a refinement's predicate
- a quoted term's binders over that term
- a sum's witnesses within its own type **and nowhere else**
- a `Poly`'s type parameters within that type **and nowhere else**

**The rule does not change from phase to phase.** Lowering and elimination change which form
a term takes, not what binds where. When a pass moves a term, it has to deal with the names
that term's types use. It cannot assume a later pass will tidy them up.

There is one exception, and it lasts only until mutability elimination. While inference runs,
a read of a mutable variable goes through an **opaque** binder (`__read`), so `x := x ^+ 1`
contributes `{Int | __elem == __read ^+ 1}` and never a type that names the mutable variable.
A type lifted past that `let` keeps the name. Mutability elimination then names the value
each read took and makes every opaque `let` transparent.

Who checks it:

- `check_scope_valid` checks every node type after inference, in every build, and reports
  `ScopeViolation`.
- `well_scoped::assert_well_scoped` runs in debug builds at every boundary `settle` checks.
- `debug_assert_no_free_witness` checks witnesses after inference, lambda elimination and
  planning.

## 5. How a type spells a binder: locally nameless

A stored type uses two spellings, and which one depends on where the binder is:

```
  binder AROUND the type   →  a name      (a free, uniquified Name)
  binder INSIDE the type   →  an index    (Name::PiBound: count binder crossings)
  a refinement's element   →  __elem^𝑛    (𝑛 = refinements crossed; __elem is 𝑛 = 0)
```

An index counts crossings into a binder's scope. There are two kinds of crossing: entering a
function's codomain, and moving to a later component of a dependent tuple. A function's
domain is not in its own binder's scope:

```text
(k : ?K) ⤇ ((i : {?D | __elem ▷ f == #0}) ⤇ ?V)
                                      └─ #0 is k: the domain is not under i
```

The same reference to `k` inside the inner *codomain* would be `#1`.

Refinement elements nest the same way. The filter in `[g for g in groupby(xs, 𝑓) if 𝑝(g)]`
is `__elem ▷ 𝑠 ▷ (λ g → 𝑝(g))`, with

```text
g : {𝐼 | __elem ▷ xs ▷ 𝑓 == __elem^1} ⤇ 𝑇
                            └─ one refinement out: the group's key
```

**Why indices:** two alpha-renamed types are then *structurally* equal. Refinement
deduplication, compaction and specialization keys can compare predicates without recovering
a name pairing that was thrown away. A function's `name` slot is only an *opening address*
and a display spelling. It is not part of identity.

**Interior term binders stay named.** A lambda inside a predicate keeps its named parameter,
and two predicates compare with their interior binders paired by position
(`eq_term_modulo_ty_slots`). Without this, two authored filtered comprehensions with
alpha-equivalent predicates would split their refinements and fail an invariant data-domain
check.

### Closing and opening

Converting names to indices is *closing*. Converting indices back to names or arguments is
*opening*.

| Operation | Direction |
| --- | --- |
| Constructing a function (`Type::pi`, `fun_like`, rebuilds like `emit_cast`) | closes |
| Compaction and keying | close their reads |
| Descending into a function to compare it with a variable | opens at the binder's name |
| Applying a function (`discharge_codomain`) | opens at the argument |
| Reading a stored predicate as a term (predicate compilation, the checker) | opens, then recloses |
| Display | opens what it walked through, but never rewrites the stored type |

The predicate case is subtle. A reader that builds new function types around a predicate's
subterms adds crossings, so an index read in stored form would land on the wrong function.
Such a reader therefore works on the opened form.

## 6. Inference under binders

### Telescopes

Every inference variable carries the **telescope**, the list of term binders it was minted
under. The invariant:

> **A variable resolves to a type naming its telescope's binders and nothing else.**

What this buys: when a substitution reaches a variable that is not resolved yet, the solver
can still tell that the substitution does nothing to it if every binder it touches is outside
the telescope. Every "leave this variable alone" decision rests on that.

No single point sees everything a variable resolves to, so two checks hold the invariant:

- **At record time**, `enforce_bound_scope` reads each bound as its edge leaves it and panics,
  in every build, on any name outside the holder's telescope.
- **At resolution**, debug builds check each resolved type (`assert_resolves_in_scope`).

Both are compiler invariant failures, not user diagnostics.

### `Subst`: moving a type across a binder

A `Subst` carries a type from one scope to another. Its entries:

| Entry | Meaning |
| --- | --- |
| Rename | replace one name with another |
| Discharge | replace a binder with a term. **This is application**: applying a dependent type to an argument |
| Join | take a contribution's type over every value of a binder it crosses |
| Witness rename / discharge | the same for a sum's witnesses |
| Elimination | read a sum through a term (`unbox`) |

A `Subst` is simultaneous: no replacement is substituted into another. Capture is
**asserted** rather than silently avoided by alpha-renaming.

### Bounds carry substitutions

A stored bound has a substitution on each side: `𝑉‹self› <: ty‹ty_subst›`. An ordinary edge
uses identities. An application creates the interesting ones. `InferCtx::apply` mints a fresh
expected binder and gives the result the expected function's codomain under the discharge
`[binder ↦ argument]`. That discharge stays in the graph until coalescing forces it.

Consequences worth knowing:

- `g(0)` and `g(1)` are different facts. The constraint cache is keyed by substitution pairs,
  so they don't collapse just because the variables match.
- `L <: 𝑉[𝑎]` and `𝑉[𝑏] <: 𝑈` are facts about two different instances of `𝑉`. The closure
  draws no edge between them.
- A bound under a discharge counts as `𝑉`'s own content only where the discharge cannot
  change it.

### Suspension

A substitution `σ` reaching an *unresolved* variable `𝛼` denotes `𝛼[σ]`, which cannot be
computed yet. `Subst::apply_type` instead returns a fresh `𝛽` whose lower and upper bound
are both `𝛼` under `σ`: a **suspension**. Compaction then applies `σ` to whatever `𝛼`
turns out to be. `𝛽`'s telescope is `𝛼`'s, minus what `σ` replaces, plus what `σ`'s range
reads. Without suspension, a substitution that reached a type slot inside a predicate would
miss what that slot later resolves to.

## 7. Leaving a binder's scope

A type written under a binder can name the binder. A position outside the binder cannot.
**Each kind of binder has its own exit**, and the compiler never gets this by "dropping
whatever doesn't fit":

| Binder | Exit |
| --- | --- |
| Pi binder | the result becomes a function type that binds it |
| Transparent `let x = e` | discharge `[x ↦ e]` |
| Opaque `let`, `:=` | keep the name (until mutability elimination) |
| Lambda whose body binds opaque variables | the codomain drops refinements at **positive** positions |
| Loop / lambda / pattern binder crossed by a write (`<<`, `<<=`, `:=`) | **join** over its values, or **key** by position |
| A chain's intermediate | read as the chain's input carried to that point |

### The lambda barrier

An opaque binder inside a function body stands for a different value on every call, so a
refinement that names it would tie `f(1)` and `f(2)` to one `r`. The codomain therefore drops
every refinement at a positive position, which gives a supertype that is still sound. A
refinement at a **negative** or **invariant** position cannot be dropped, because dropping it
does not give a supertype. If such a refinement names the opaque binder, inference refuses the
lambda with `OpaqueEscape` and asks for a result annotation.

### Joining, decided by position

A write inside a loop to a variable declared outside contributes to a history whose type is
the **join of every value written**. A refinement that names a joined binder is handled by
where it sits:

| Where the refinement sits | Outcome |
| --- | --- |
| On a sum's candidate | widens to `SubtypesOf` what remains: `box([v for v in xs if v > r])` fed from a loop over `r` contributes `Σ (σ : SubtypesOf([0, 2])). σ ⤇ Int` |
| In a data domain | **no join exists**, since each value has its own keys: `NoJoinOverBinder` |
| Elsewhere, positive | dropped: the join keeps what every value establishes |
| Elsewhere, negative (a compute domain) | `NoJoinOverBinder`: the right answer is a meet of predicates, which compaction does not compute |

Inference types a `def` body once, before any call supplies an argument. So
`def f(y): out << [v for v in xs if v > y]` is refused even when `f` is called only once.

### Keying: a history whose value depends on its position

A history's type is a data function `(𝑘 : 𝐷) ⤇ 𝑉`, and `𝑉` may read `𝑘`. A feed is keyed
when its target is fed from one place, it is outside a transaction, and every binder it
crosses is a `let` or a loop variable. In that case a loop variable `𝑥` over `𝑠` exits as a
join carrying the term `𝑘 ▷ 𝑠` at the key, and a collection's domain **reads that term**
instead of being refused:

```
  for r in rs:
      out << [v for v in xs if v > r]

  out : feed((𝑘 : 𝐷) ⤇ ({𝐼 | xs(__elem) > 𝑘 ▷ rs} ⤇ Int))        (schematic)
                         └─ each row filtered by its own position's r
```

Under nested loops whose inner keys depend on the outer value, the key is a dependent tuple of
the positions (§9).

### Chains name each position

In `𝑒₀ ≫ 𝑒₁ ≫ … ≫ 𝑒ₙ`, each `𝑒ᵢ`'s binder `𝑥ᵢ` binds within `𝑒ᵢ`'s own type **and nowhere
else**. The chain's own type is a function of its input alone, with each position written as
the input carried there:

```text
(𝑥₀ : 𝐷) ⇒ 𝐶[𝑥ᵢ ↦ 𝑥₀ ▷ 𝑒₀ ≫ … ≫ 𝑒ᵢ₋₁]
```

The payoff: **a type that names a position does not depend on how the position is computed.**
Planning can turn a group-by into `converse` and `map`, or a join into its plan, and splice
nested chains, all without restating any type, because no type names another morphism's
binder.

## 8. Dependent sums: a collection whose domain is one of several

§2 left a gap: invariance forbids joining `[0, 1] ⤇ Int` with `[0, 2] ⤇ Int`, and `List(Int)`
must accept a list of any length. A **sum** fills it:

```text
Σ (σ : 𝐾). σ ⤇ 𝑉        a collection whose domain is some member of the kind 𝐾
```

In the representation, a sum is a `Type::Fun` whose `FunKind::Data` carries witness binders.
Each witness has an ID and a `TypeKind`, and `Type::WitnessRef` stores the ID only. The kind
lives on the binder so that occurrences cannot disagree about it.

### Kinds and the collection types

| Kind | Members | Used by |
| --- | --- | --- |
| `Enumerated` | a finite list of candidate domains | `box` and joins of boxed collections |
| `UIntRanges` | unrefined `UIntRange` types (dense, no holes) | `List` |
| `SubtypesOf(𝑇)` | types below `𝑇` | `Map`, `Set` |
| `Type` | every type | `Collection` |

| Annotation | CCL |
| --- | --- |
| `Array(n, T)` | `UIntRange(n) ⤇ T` |
| `List(T)` | `Σ (D : UIntRanges). D ⤇ T` |
| `Set(K)` | `Σ (D : SubtypesOf(K)). D ⤇ unit` |
| `Map(K, V)` | `Σ (D : SubtypesOf(K)). D ⤇ V` |
| `FullMap(K, V)` | `K ⤇ V` |
| `Collection(T)` | `Σ (D : Type). D ⤇ T` |

`UIntRanges` rejects a *refined* range, because a filtered list has holes. This is how a
filtered arm that reaches a `List` parameter gets refused.

### Rule: only a term builds a sum

Subtyping **never** introduces a sum around a plain collection and **never** eliminates one.
`box` introduces it:

```text
box : ∀d v. ((k : d) ⤇ v) ⇒ Σ (σ : [d]). (k : σ) ⤇ v
```

| Expression (distinct domains) | Result |
| --- | --- |
| `xs if c else ys` | `DomainJoinConflict` |
| `box(xs) if c else box(ys)` | `Σ (σ : [𝐷ₓ, 𝐷ᵧ]). σ ⤇ 𝑉`, which keeps both |
| `list(xs) if c else list(ys)` | `List(𝑉)`, with rows reindexed |

A mixed boxed/unboxed conditional fails rather than boxing one arm or dropping the other's
witness. A one-candidate sum stays a sum during inference, and only planning can erase it.
The codomain is joined *once* for the whole sum, so `box([1, 2]) if f else box(["a", "b"])`
still fails, because no untagged union exists.

### The Σ rule

Two sums of the same arity relate **positionally**:

```text
    ρ = [w₀⁰ ↦ w₁⁰, …, w₀ⁿ⁻¹ ↦ w₁ⁿ⁻¹]
    Γ ⊢ K₀ⁱ <: K₁ⁱ                         (each i < n)
    Γ, w₁⁰ … w₁ⁿ⁻¹ ⊢ D₀‹ρ› <: D₁             (invariant data-domain relation)
    Γ, w₁⁰ … w₁ⁿ⁻¹ ⊢ V₀‹ρ› <: V₁
    ───────────────────────────────────────────────────────
    Σ (w₀ : K₀…). D₀ ⤇ V₀  <:  Σ (w₁ : K₁…). D₁ ⤇ V₁
```

Kind containment is a fixed matrix. For example, `UIntRanges <: SubtypesOf(_)` is rejected,
and `SubtypesOf(𝑎) <: SubtypesOf(𝑏)` draws `𝑎 <: 𝑏`. A witness against a concrete type is
ordered by its range: `σ <: 𝑇` iff the range is within `SubtypesOf(𝑇)`, and `𝑇 <: σ` iff `𝑇`
is below every candidate.

### The witness context: a sum binds its witnesses within its own type only

**Equal candidate lists do not make equal witnesses**, because two independent collections can
pick different domains from the same list. Witness identity comes only from a correspondence
the caller supplies: the Σ rule's positional pairing, or `witness_instantiation` for an
argument. A consumer that accepts both plain collections and sums carries a funkind variable.
The incoming collection *pins* it, which is kind instantiation, not subtyping, and the consumer
mints its own binder IDs, into which each edge renames the sum's.

Outside the sum's own type, nothing may refer to `σ`. A type outside it names the witness
**through a term**, the same way a pair is read through its projections:

```text
σᵢ(𝑐)       the i-th witness of the sum the term 𝑐 holds (Type::WitnessProjection)
unbox(𝑐)  : (𝑐 : Σ (σ : 𝐾). 𝐷[σ] ⤇ 𝑉) ⇒ 𝐷[σ ↦ σ₁(𝑐)] ⤇ 𝑉
```

`σᵢ(𝑐)` holds the term `𝑐`, compared by normal form, plus the binder's *position* rather
than its ID, since IDs are renamed into every consumer's scope. A key typed `σ₁(𝑐)` applies to
`unbox(𝑐)` like a key to any collection. `unbox` inverts `box`.

In the solver, `unbox` is a substitution component (`Elim`). It waits until it meets a
function. On a settled sum it discharges the binders to `σᵢ(𝑐)`. On a funkind variable it
waits for the arity. On a type variable it suspends.

### Membership is decided at materialization

`admits` is the one membership judgment. When the candidate is still a variable, the kind is
*recorded* on the variable, and **no bound is drawn**: an edge whose presence depended on the
kind would be a second definition of the kind algebra. Coalescing decides each recorded kind
where the position materializes, with the refinement judged whole. On the concrete fragment,
the decision is proved in Lean (`admitsCheck_iff_admits`) and differentially tested against
the Rust.

### Through planning and at run time

- A collection-valued `Case` is **realized where it stands**: it becomes a union of its arms,
  each restricted by its first-match path condition, `⧺ᵢ (armᵢ | π̂ᵢ)`. A `Realize` node
  wraps the union and *asserts* the original sum type, since ordinary subtyping cannot prove
  that change of representation and a `Cast` would keep the union's tagged domain.
- A **determined** witness (one candidate) is erased: `σᵢ(𝑐)` is rewritten to the candidate.
  A **materialized** witness keeps its `box`, and the value carries its own keys.
- A conditional chosen per row (its condition reads a loop variable) is handled earlier, by
  lambda elimination's fan-out of gated legs.
- At run time a projection has no representation of its own. The extent of `σᵢ(𝑐)` is the
  witness's key bound.

## 9. Dependent tuples: the uncurried half of Pi

```text
(𝑎 : 𝐴) ⇒ (𝐷(𝑎) ⤇ 𝑉)      ≅      ((𝑎 : 𝐴) × 𝐷(𝑎)) ⤇ 𝑉
      curried (Pi)                    uncurried (dependent tuple)
```

A nested collection read as one collection is keyed by pairs whose second component ranges
over a type chosen by the first component's *value*. When `𝐷` does not depend on `𝑎`, this
is the plain product `(𝐴, 𝐷)` and the existing `curry`/`uncurry` pair.

**Compared with a sum:** a sum's witness is a *type* fixed per collection. A dependent tuple's
first component is a *value*, and every value has its own fiber.

### Where they come from

A program cannot write a dependent tuple. Three places create one:

- `uncurry(𝑛)`, which flattens a comprehension over several generators. Its scheme always
  builds a `DepTuple`, and compaction collapses it to a plain tuple where no component reads
  an earlier one. `[x for xs in xss for x in xs]` keeps the dependency.
- `channelize`, for a feed under nested loops whose inner keys depend on the outer value.
- Lambda elimination's nested-lambda rule. `λ 𝑎 → λ 𝑏 : 𝐷(𝑎) → body` becomes
  `curry(λ 𝑝 : (𝑎 : 𝐴) × 𝐷(𝑎) → body)` when the inner binder's type still reads `𝑎`. In
  practice that is a membership refinement, such as a group-by whose key reads a loop's
  binder.

### Rules

- **A telescope.** Each component binds over the ones after it. A reference from component
  `𝑘` to component `𝑗` is index `𝑘 − 1 − 𝑗`, so an index is the same in the curried family as
  in its uncurried domain, and uncurrying copies domains unchanged.
- **One spelling.** `Type::dep_tuple` collapses to `Type::Tuple` when nothing reads an
  earlier component.
- **No implicit flattening.** `(𝐴, (𝐵, 𝐶))` and `(𝐴, 𝐵, 𝐶)` are different types, since a
  key's `.1` differs between them. `flatten_domain` is an explicit operation in the types as
  well as at run time.
- **Projection opens.** `𝑝.𝑘` has component `𝑘`'s type opened at `𝑝.0 … 𝑝.(𝑘−1)`. For
  `𝑝 : (𝑎 : Int) × {Int | __elem ∈ keys(𝑎)}`, the term `𝑝.1` has type
  `{Int | __elem ∈ keys(𝑝.0)}`.
- **Subtyping** is component by component, and as a domain it is invariant like every domain.

### Iterating one

No single key collection is shared by every row, so planning rewrites a site over
`((𝑥 : 𝑋) × 𝐷(𝑥)) ⤇ 𝑉` into a site over a **family of keys**
`𝐹 : (𝑥 : 𝑋) ⇒ (𝐷(𝑥) ⤇ 𝐷(𝑥))`, one collection per row, written `(𝐹, 𝑔) ▷ curry_over`. The
non-dependent case is `𝐹 = const(𝐾)`. At run time the extent is bounded component by
component, and each row's keys run on their own.

## 10. After inference: lambda elimination and generalized types

Lambda elimination is lambda *lifting*. One point-free morphism serves every value of the
parameter it eliminated, yet a type written under that parameter can name it. Four rules
decide what happens.

### The Pi-constant form

If a parameter occurs **only in the body's type**, the lambda becomes

```text
const(body) : (𝑥 : 𝐷) ⇒ body.ty
```

The exception is when `body.ty` is a data function whose domain reads `𝑥`.

### A refinement on a collection's domain is data

This is the second ground rule from §2 paying off. A body that *holds* a collection whose
domain reads the parameter **varies** with the parameter, because the filter decides which
entries exist. Such a lambda goes to the nested-lambda rule, which lifts the filter onto the
pair, and not to the Pi-constant form:

```text
λ r → λ v : {Int | v > r} → …          comprehension filtered by an outer binder
λ i → λ k : {Int | k ∈ keys(i)} → …    group-by whose key reads i
```

A domain can read a binder **of the body's own type** without varying the body: a group's
domain reads the group's key, and that family is exactly the Pi-constant type the group-by
recognizer plans. A collection the body takes *as an argument* does not vary it either:
`sum` is the same `sum` for every value.

### One binder for one value

If two binders denote one value, every type that reads either of them has two spellings, and
structural comparison then disagrees. Product β therefore rewrites `𝑥.0 ↦ 𝑎` and
`𝑥.1 ↦ 𝑎 ▷ 𝑔` in types when it removes a pairing `⟨id, 𝑔⟩ ≫ ℎ`.

### Generalized types and families

After lifting, a morphism's type may name a binder that is no longer in scope:

```text
sum : ({[0, 3] | key(__elem) == 𝑘} ⤇ Int) ⇒ Int          names 𝑘, out of scope
  ⟹  ∀ (𝐷 <: [0, 3]). (𝐷 ⤇ Int) ⇒ Int                     generalized
```

The part of the input that names the binder becomes a **generalized parameter**, bounded by
its base without the offending refinements. The use site instantiates it by matching the type
against what it actually receives. If that part also reads the type's *own* binders, it is a
**family**, one type per value:

```text
uncurry : ∀ (𝐷, 𝐷₁(_)). ((𝑘 : 𝐷) ⤇ (𝐷₁(𝑘) ⤇ Int)) ⇒ ((𝑘 : 𝐷) × 𝐷₁(𝑘) ⤇ Int)
```

Rules worth remembering:

- **A collection is never generalized.** Its domain is its data.
- A refinement on a collection's domain that no input part determines does not generalize.
  The morphism depends on a value its input does not carry, so the pass that built it must
  pass that value in, and generalizing panics.
- No `Poly` or `Param` *the program wrote* survives inference. Generalized ones are the only
  `Poly` a later phase holds.

## 11. Through the pipeline

| Phase | What it does with dependent types |
| --- | --- |
| Lowering | writes collection annotations as sums; `groupby`'s Pi type; each comprehension filter as a refinement a `Cast` acquires |
| Inference | names a lambda's parameter as its Pi binder and discharges it at each application; `box` introduces, `unbox` eliminates; `uncurry(𝑛)` keys by a dependent tuple; keyed feeds; kinds decided at materialization; coalescing closes to indices; a specialization stands under the binders its instance reads |
| Post-inference check | rederives every node's type by the same rules (`Typing` is shared by `InferCtx` and `CheckCtx`); after planning, takes a dependent result as recorded instead of rebuilding a quoted term |
| Mutability elimination | names each read's value, makes opaque `let`s transparent, and erases histories to functions (`channelize` for feeds) |
| Lambda elimination | the Pi-constant form; packs dependent binders into dependent tuples; generalizes types that name out-of-scope binders |
| Planning | realizes conditionals where they stand; erases determined witnesses; iterates dependent tuples through key families |
| Operator conversion | bounds a projected witness by its key bound, a dependent tuple component by component, and runs key families beneath the levels above them |

## 12. Invariants cheat sheet

1. **Well-scoped at every phase.** Every free name in a type slot is bound around its node or
   is a source or sink. The only exception is opaque `let` names, until mutability
   elimination.
2. **Names outside, indices inside.** A binder around a type is a name. A binder inside it is
   an index. A function's or tuple component's name slot is an address and a display
   spelling, never identity.
3. **Telescopes.** An inference variable resolves to a type naming its telescope's binders and
   nothing else. This is checked at record time in every build.
4. **Every binder has an explicit exit:** discharge, keep, barrier, join, key, or chain
   rewrite. Dropping a refinement is allowed only where the result is a supertype. Elsewhere
   the compiler reports an error.
5. **Data domains are invariant.** Two collections over different domains meet as an
   equation.
6. **Only a term builds a sum.** Subtyping never introduces or eliminates one, and equal
   candidate lists are not equal witnesses.
7. **A sum binds its witnesses within its own type only.** Outside the sum, the witness is
   named through a term: `σᵢ(𝑐)`, `unbox(𝑐)`.
8. **Kinds are recorded, not bounded,** and they are decided where a position materializes.
9. **No type names another morphism's binder.** Positions are named by what reaches them, so
   rewriting how a position is computed changes no type.
10. **One binder per value.** Two spellings of one value would split structural comparison.
11. **Predicates compare by normal form,** with interior binders paired by position.
12. **Construction closes, descent opens.** Display opens but never rewrites the stored type.
13. **`Subst` is simultaneous, and capture is asserted,** never silently alpha-renamed.
14. **Collections are never generalized.** No `Poly` the program wrote survives inference.

## 13. Open questions

The design docs list these as open:

- **Arbitrary witness-dependent kinds.** A later kind cannot depend on an enclosing witness.
  The kind premise of the Σ rule precedes the new correspondence.
- **Heterogeneous scalar packages.** A sum is a data function, not `Σ (𝑇 : [Int, String]). 𝑇`.
  Supporting that would need introduction and consumer rules, plus a representation.
- **Membership introduction.** A key produced by a collection's own key morphism does not yet
  carry membership in that collection's image.
- **A row's fiber through a loop.** A row typed by a sum and reached through a loop has its
  own domain as its fiber. That fiber could be the key type refined by membership in the row,
  with a check-mode rule that a key in `dom(𝑐)` indexes `𝑐`.
- **Dependent tuples as witnesses.** A dependent tuple as the witness of a `SubtypesOf` kind
  needs a membership check against the kind's tuple of key types.
- **Several places feeding one target** (planned). Such feeds would be keyed by the place, and
  a pattern binder would exit as the scrutinee's payload. Both need a term that reads a
  variant's payload.

## Vocabulary

| Term | Meaning |
| --- | --- |
| Telescope | The term binders an inference variable may name, in order; also a dependent tuple, whose components bind in order. |
| Discharge | Replacing a binder with a term, i.e. applying a dependent type to an argument. |
| Join | Taking a contribution's type over every value of a binder it crosses. |
| Suspension | A variable standing for an unresolved variable under a substitution. |
| Elimination | Reading a sum through a term: `unbox(𝑐)`, whose binders become `σᵢ(𝑐)`. |
| Witness | A sum's binder, standing for the domain a value has. |
| Type kind | What a witness ranges over: candidates, dense ranges, subtypes of a type, or every type. |
| Funkind | A function's data or compute kind, which carries a sum's witnesses; a funkind variable is one not settled yet. |
| Pi-constant form | `const(body) : (𝑥 : 𝐷) ⇒ body.ty`, a lambda whose parameter only the body's type reads. |
| Generalized parameter | A parameter standing for a part of a lifted morphism's type that named a binder out of scope. |
| Family | A generalized parameter that takes terms: one type per value of the binders it is applied to. |
