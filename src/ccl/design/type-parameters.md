# Type parameters

> **Status: [Sketched].** A proposed implementation of
> [chl-spec.md, "6.8 Polymorphic types"](../../../docs/chl-spec.md#68-polymorphic-types).

A written polymorphic type is a `Type`: `Type::Poly` binds type parameters, their bounds, and a
`requires` clause over a body type. A `def` with type parameters is a binding annotated with one.
Inside the body a type parameter is an opaque `Type::Param`. Each use instantiates the parameters as
fresh inference variables and checks the bounds and requirements at its own types, and
specialization substitutes the use's types for the parameters in the cloned body. No `Poly` or
`Param` survives inference.

An unannotated generalized binding keeps the implicit polymorphism of
[3.1 Let-Polymorphism is Freshening
(Instantiation)](type-inference.md#31-let-polymorphism-is-freshening-instantiation): its scheme is
the bound graph, not a `Type::Poly`. A diagnostic renders an inferred scheme in the `Poly`
notation ([Printing an inferred polymorphic type](#printing-an-inferred-polymorphic-type)).

---

## Representation

`Type::Param(Rc<TypeParam>)` is a type parameter and `Type::Poly(Rc<PolyType>)` a polymorphic
type, both in `ccl/ty.rs`:

- A `TypeParam` has an id, which equality, ordering and hashing use; the spelling the user wrote,
  for display; and, once opened, a level (`opened_at`) and a bound normalized at that level.
- A `PolyType` holds its parameters in declaration order, each a `PolyParam` (a declared
  `TypeParam` and its bound); its `requires` clause, each requirement a `TraitRequirement` (a
  trait, its operand types and its associated types by name); and its body.

The variant names follow the spec's terms, "polymorphic type" and "type parameter". `Var` would be
a third meaning for one word: `TypedExprNode::Var` is a term variable, and `Type::Infer` holds an
inference variable. `PolyScheme` stays the name of the implicit, inferred form.

`Poly` is a type, so an alias can name one, and once modules land a `Module{…}` member's type can
be one. Lowering admits one only as a whole `let` annotation or an alias's right-hand side
([Where a polymorphic type may appear](#where-a-polymorphic-type-may-appear)).

A type parameter is **declared** or **opened**.

- **Declared.** Lowering writes one per parameter a `Poly` binds: a `TypeParam` with a name only.
  The `Poly`'s bounds and body, and the annotations of the definition it annotates, name it. Its
  bound is the `PolyParam::bound` beside it, a type slot of the `Poly` that `uniquify` rewrites as
  it rewrites any other.
- **Opened.** Emission opens the `Poly` for each binding it annotates, minting an opened
  `TypeParam` per declared one with a level and a normalized bound
  ([Checking a binding against a polymorphic type](#checking-a-binding-against-a-polymorphic-type)).
  The leaf carries both because the solver reads them where no scope is in hand, as in a
  specialization's pin. While the `Poly` is open, normalization replaces each declared occurrence
  with its opened parameter.

Each binding opens its `Poly` for itself, so two bindings annotated with one alias have parameters
of their own. Only an opened parameter reaches the solver: `TypeParam::level` panics on a declared
one, as normalization does on a declared parameter whose `Poly` is not open.

A `Param`'s bound can hold inference variables whose bounds hold the `Param`. Arena teardown clears
every variable's bounds, which breaks that cycle as it breaks the cycles among variables.

---

## Lowering

The parser gives `Stmt::FunctionDef` a `type_params` field beside `params`, and a `requires` field.
Type parameters stay out of `params` because the parameter count is the arity: it sizes the argument
tuple and fixes how many lambdas a `Mut`-parameter function's chain has (`uncurry_params`).

`declare_type_params` declares each parameter in order as an alias of a declared `Type::Param`,
after lowering its bound with the parameters before it in scope, and records it in the `Poly`. It
refuses a built-in name and a name declared twice.

A type-position `\T, U <: B -> V` lowers through `lower_type_expr_or_poly`, which declares the
parameters in an alias scope of its own and lowers `V` as the body. Only a `let` annotation
(`lower_let_annotation`) and an alias's right-hand side lower through it, and a bounded `<:`
polymorphic annotation is refused. Every other position, nested ones included, lowers through
`lower_type_expr`, which refuses a `Poly` whether written or reached through an alias.

A `def` with type parameters lowers through `lower_def` to a `let` annotated with a `Poly` over a
`Hole` body: the lambda's own annotations already state the signature, and `emit_let` completes the
hole from the lambda's type. The parameters are aliases over the whole definition, parameter
annotations and `=>` result included, so the alias scope opens around `lower_function_body`
rather than inside the body's block. `LoweringContext::type_params_in_scope` lets
`pre_declare_type_aliases` refuse an alias in the body that would hide a parameter. A parameter that
no value parameter's annotation names is refused after lowering, by walking the binders of the
lambda chain `uncurry_params` builds.

A `requires` clause on a `def` or a `Poly` lowers into the `Poly`'s `requires`, as
[Lowering requirements](#lowering-requirements) describes.

---

## Levels

Emission opens a `Poly` when it checks a right-hand side against it ([Checking a
binding against a polymorphic type](#checking-a-binding-against-a-polymorphic-type)): it mints
each parameter at the level the right-hand side is emitted at, one above the binding, which is where
the right-hand side's own inference variables sit.

`type_level` reports a parameter's level. `ChanDom` reports 0 so that it flows outward through
bounds; a type parameter must not ([chl-spec.md, "Type
parameters"](../../../docs/chl-spec.md#type-parameters)). An edge that carries a parameter to a
variable below its level reaches `constrain_go`'s level-mismatch arms, which check for one
(`escaping_param`) before extruding and fail with `TypeParamEscapes`, naming the parameter.
`extrude` never mints a proxy for a parameter.

`freshen_level` reports the level too, so `freshen_above` does not short-circuit past a type that
mentions a parameter.

---

## Checking a binding against a polymorphic type

`emit_let` with an exact annotation `Poly(𝜋)`:

1. Opens `𝜋` inside `in_let_rhs` (`Typing::open_poly`): mints an opened `Param` for each declared
   one at the right-hand side's level, with its bound normalized at that level, which
   normalization puts in place of the declared one until `Typing::close_poly` closes `𝜋` after
   step 2, on every path out. It returns `𝜋` opened, its requirements normalized over the opened
   parameters, which are in scope as **assumptions** while the right-hand side is emitted
   ([Obligations under assumptions](#obligations-under-assumptions)).
2. Emits the right-hand side and records `inferred <: 𝜋.body` through `bind_annotation`, at the
   right-hand side's level, with the parameters opaque. A `def`'s body is a `Hole`, completed from
   the lambda's type.
3. Binds the name at the completed body and generalizes. The body mentions the parameters above the
   binding's level, so `should_generalize` admits the `let` through its level test, and the
   coalesce walk asks the same predicate.
4. Replaces the binding's annotation with `𝜋` opened, over the completed body. `scoped_let` puts
   its `requires` clause in the binding's `PolyScheme` for each use to instantiate, and the
   coalesce walk assumes it while it checks the definition alone
   ([Specialization](#specialization)). A clone of an enclosing definition re-mints the opened
   parameters along with its body, so the clause is always the clone's own.

A right-hand side that would be monomorphic without the annotation, a call or a collection, is an
error at the annotation ([chl-spec.md, "Polymorphic type
annotations"](../../../docs/chl-spec.md#polymorphic-type-annotations)). Lowering refuses a call
or a collection, whose shape is syntactic. A name bound to a monomorphic binding is refused at
emission, where the binding's scheme is known: `MonomorphicPolyBinding`, or an annotation mismatch
when the reconcile in step 2 fails first.

A `def` and `g: \T -> V requires … = e` take this one path. For `g = f` with `e` a `Var`, step 2
instantiates `f` against `V`, which is the check that `f` is at least as general as `g`'s type.

---

## Subtyping with a type parameter

`constrain_go` relates a type parameter `𝑃` by these rules:

| Constraint | Holds when |
| --- | --- |
| `𝑃 <: 𝑃` | always (the identity short-circuit) |
| `𝑃 <: 𝑈`, `𝑈` not a variable | `𝑃` has a bound `𝐵` and `𝐵 <: 𝑈` |
| `𝑄 <: 𝑃`, `𝑄` another parameter | `𝑄`'s bound chain reaches `𝑃` |
| `𝑋 <: 𝑃`, `𝑋` concrete | never |
| a variable against `𝑃` | the existing variable arms |

The bound rule is placed after the variable arms and before the refinement arm, so
`𝑃 <: {Int | 𝑝}` reaches `𝑃`'s bound. `𝑃 <: {𝑃 | 𝑝}` stays in the refinement arm, which has no SMT
sort for a parameter and fails.

`compact` treats a parameter as an atom (`AtomKey::Param`), so a parameter beside another
contribution at one position would collide as two bases do. `relate_params_by_bounds` orders them
through the bounds, before the position materializes:

- Of two parameters a bound chain relates, the join keeps the higher and the meet the lower: under
  `𝑈 <: 𝑇` the join of `𝑇` and `𝑈` is `𝑇`.
- A meet keeps a parameter whose bound chain reaches a type below the other contributions: the meet
  of `𝑇 <: {at: Int, sku: String}` and `{at: Int}` is `𝑇`.
- Otherwise a bounded parameter is widened to its bound and the position merges without it, since a
  value of `𝑇`'s type is a value of its bound's: the join of `𝑇 <: {at: Int}` and `{at: Int@1}` is
  `{at: Int}`, and of `𝑇 <: Int` and `𝑈 <: Int` is `Int`.

An unbounded parameter has nothing to widen to and still collides, which is the error
[chl-spec.md, "Type parameters"](../../../docs/chl-spec.md#type-parameters) gives two parameters
with no common type. Widening at a meet never hides an error the program has: a position holding a
parameter lies in a definition checked alone, whose types are dropped, and every value reaching a
parameter's position was related to it through its bound when its edge was drawn.

---

## Obligations under assumptions

An obligation's candidate set holds its trait's **instances** and its **assumptions**: the
requirements of the `requires` clauses in scope where it is minted (`TraitObligation::assumptions`).
`emit_let` puts a `Poly`'s requirements in scope over its right-hand side
(`Typing::with_assumptions`), and `require_trait` gives each obligation those about its trait.
Lowering leaves every assumption's operands a base or a type parameter
([Lowering requirements](#lowering-requirements)), so an assumption is matched by equality.

A contribution arriving at a position narrows both kinds of row:

| Contribution | Instances | Assumptions |
| --- | --- | --- |
| a base | keep the rows with that base there | keep the rows stating that base there |
| a type parameter an assumption names there (`narrow_param`) | all dropped | keep the rows naming it there |
| any other type parameter | its bound is offered in its place; with no bound, `MissingRequirement` | as for the bound |
| a product | answered by `narrow_product` | the component obligations it mints start from the same assumptions |

So a requirement covering an operator on a bounded parameter answers it before the bound does. The
obligation fails when both kinds are empty. A failure that leaves only assumptions reports what they
accept: `operand 2 is Int, but the only type accepted there is T`.

Deposit reads both kinds: once every surviving row agrees on an associated type, it is deposited,
and it may be a parameter, so `a + b` under `requires Addable(T, T, Output=T)` gives the sum type
`T`. An assumption that leaves `Output` unnamed leaves the position open in the body.

The sweep of [Requirements are read together, once](type-inference.md#requirements-are-read-together-once)
skips an obligation that still holds assumptions: its operand is a parameter, which the sweep's base
intersection cannot read.

### Lowering requirements

`lower_requirements` resolves each requirement against the trait table: the name
(`Trait::from_surface_name`), the operand count, and each associated type by name
(`Assoc::from_surface_name`). It reads an `Equatable` over products componentwise, so
`Equatable({T, U}, {T, U})` lowers to `Equatable(T, T)` and `Equatable(U, U)`. Every operand must
then be a type parameter or a base type, and the requirement must fit some instance at its bases;
any other is refused at the requirement, since no use could satisfy it. A requirement on bases only
is checked and dropped. `Transaction` is refused until
[chl-spec.md, "8.7 Direction [Decided]: transactions as contextual parameters"](../../../docs/chl-spec.md#87-direction-decided-transactions-as-contextual-parameters)
is implemented. For the check that every parameter is determined, a parameter that is the
associated type of a requirement whose operands are determined counts as determined.

---

## Instantiation

The `Var` arm instantiates every binding through `PolyScheme::instantiate_with_params`, which
freshens the body, the bounds and the `requires` clause through one copy (`Instance`):

1. Each type parameter above the scheme's cutoff maps to a fresh variable `𝛼` at the use's level,
   in the use's telescope, through `FreshenCache::params`, and the body freshens through it.
2. For each parameter with bound `𝐵`, the arm records `𝛼 <: 𝐵[𝛼/𝑃]`, the bound freshened through
   the same cache.
3. For each requirement of the scheme's `requires` clause, the arm calls `require_trait` over the
   substituted operands, then records `𝑜 <: 𝛼ₒ` from the obligation's associated variable `𝑜` to
   the substituted associated type.

A failure in 2 or 3 is blamed on the use, with a secondary label at the bound or the
requirement as written, the error shape
[chl-spec.md, "A use that checks compiles"](../../../docs/chl-spec.md#a-use-that-checks-compiles)
states.

---

## Specialization

A specialization clone is freshened with `FreshenLevel::Preserve`, and the level of a parameter says
whose it is:

| Parameter | Freshened to |
| --- | --- |
| at the cutoff's next level: the specialized binding's own | a fresh variable at that level |
| deeper: a definition's nested in the clone | a new `TypeParam`, at the same level and with its bound freshened |
| at or below the cutoff: an enclosing definition's | itself |

The clone's pin, two-way against the use's instantiation type, ties each fresh variable to the
use's types where the parameter stands in the signature. Where it stands only in a bound, as for a
parameter `x <: T`, the variable takes the types flowing in through the pinned parameter. No
per-use table is kept: cloning re-mints node identities, so a table keyed by a use's `NodeId` would
miss the uses inside a clone.

Each use substitutes its own types, so an error that only the opaque parameters expose, such as
two unrelated parameters meeting at one position, never shows in a clone.
`coalesce_generalized_let` checks every definition alone once its last use is specialized, with
its parameters opaque, and that check is what reports such an error.

An obligation copy holding an assumption about one of the specialized binding's own parameters
is reset to its trait's instances and the assumptions that name no such parameter
(`TraitObligation::reset_for_specialization`), and is redelivered its operands' lower bounds once
the clone is pinned (`redeliver`). Freshening writes bounds directly and so does not deliver; the
redelivery, which reads the bounds transitively, replaces it. That a reset obligation resolves
follows from the use having satisfied every requirement at the same types; one that did not would
be an error the definition alone does not raise, which is reported at the use.

A use inside a generic definition checked alone carries that definition's still-opaque parameters
into the specialization it reaches. The coalesce walk keeps the `requires` clauses of the
definitions it is checking alone in scope (`CoalesceCtx::assumptions`), read off their opened
annotations, and a reset obligation is given those as well (`assume_more`).

`spec_key` keys a parameter as an atom by `id`, for the uses inside a definition checked alone.

---

## Where a polymorphic type may appear

A `Poly` reaches the solver only as a binding's annotation: emission opens it and the `Var` arm
instantiates it. Lowering refuses one inside another type, which the spec leaves **[Open]**, so
`constrain_go` never meets a `Poly`, and `compact`, `extrude` and `spec_key` treat one as
unreachable.

A Module-type member check, once modules land, is the same check as a binding's annotation: the
argument member's contract, written or inferred, is checked against the parameter's member type
as a right-hand side is checked against its `Poly`
([Checking a binding against a polymorphic type](#checking-a-binding-against-a-polymorphic-type)).
Members resolve statically to their binders, so no Module type flows through inference variables,
and no subtyping rule between two `Poly`s is needed.

---

## After inference

A `Poly` or `Param` in the tree that survives inference is a compiler defect.
`collect_type_errors` reports one at every strictness, as it reports `Hole`. A specialized binding
is rebuilt as monomorphic `let`s, so its `Poly` annotation leaves with it. `Display for Type`
renders a `Poly` in the spec's notation and a parameter by its spelling. `hash_type_in` hashes a
parameter by its spelling, as it hashes a channel domain, since an identity is per-compilation; no
hashed tree holds one after inference.

---

## Printing an inferred polymorphic type

`poly_for_display` (`ccl::infer::solver::display`) renders a type as an `InferredPoly`: a
`PolyType` over declared parameters, one per variable above a cutoff, as lowering writes one, with
the joins and meets the notation cannot write recorded beside it. An annotation mismatch against a
`Poly` (`InferError::PolyAnnotationMismatch`) uses it for the right-hand side's type, with the
cutoff at the binding's level, so `pick: \T -> T => T = inc` reports `inc` as
`\A -> A => Int requires Addable(A, Int, Output=Int)`, written in CHL by
`chl_print::chl_inferred_poly`.

- **One term.** The type is compacted together with the operands and associated types of every
  obligation watching a variable it reaches, so a variable is one identity across the body and
  the requirements. An operand stands at a positive position: values flow into it, and the
  operator's own operand variable is reached only through what flows in. Each associated type's
  variable is pinned against simplification's polar-only elimination, since it can occur at one
  polarity of the term and still tie the requirement's `Output` to the body.
- **Polarity-correct.** Compaction does not fall back to a variable's upper bound at a positive
  position, so a demand is never shown as a value.
- **Parameters.** Each variable above the cutoff that survives simplification becomes a parameter,
  named `A`, `B`, … in order of first appearance, skipping a spelling a type parameter in the type
  already has. A position no variable and no type reached is a parameter of its own.
- **Bounds.** The type beside a parameter at a negative position is its bound. A parameter that
  occurs once was eliminated by simplification, so its bound is written inline:
  `def at(a): a.at` prints as `\A -> {at: A} => A`, and `def both(a): (a.at, a)` as
  `\A <: {at: B}, B -> A => {B, A}`.
- **Requirements.** Each obligation becomes a requirement unless every operand is concrete, which
  the definition already answered. Refinements are dropped, since an instance row matches a base
  whatever its refinements. An obligation a product answered is stated by its components.
- **Joins.** A join or meet the notation cannot write is an `InferredPoly::joins` entry, its
  operands the parameters and type that meet there, and a parameter stands in its place, written
  as its operands: `A ∨ {Int where _ == 1}` where a parameter and a concrete type meet at a
  positive position (`def f(c, a): a if c else 1`), `A ∨ B` where two parameters do, and `A ∧ B`
  at a negative one.

An obligation's requirement is read off its own operand positions, so a freshened copy has to hold
every operand. Freshening a copy freshens every operand of the original, not only those the type
being freshened reaches: the variable a literal flows into is reached through no type.
