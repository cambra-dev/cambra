# Type parameters

> **Status: [Sketched].** A proposed implementation of
> [chl-spec.md, "6.8 Polymorphic types"](../../../docs/chl-spec.md#68-polymorphic-types). Of the
> [Implementation stack](#implementation-stack), items 1 to 4 and 6 to 8 are implemented: the
> parser, polymorphic aliases, type parameters with their bounds, requirements, printing, each
> definition checked alone, and secondary labels. Item 5 is dropped.

A written polymorphic type is a `Type`: `Type::Poly` binds type parameters, their bounds, and a
`requires` clause over a body type. A `def` with type parameters is a binding annotated with one.
Inside the body a type parameter is an opaque `Type::Param`. Each use instantiates the parameters as
fresh inference variables and checks the bounds and requirements at its own types, and
specialization substitutes the use's types for the parameters in the cloned body. No `Poly` or
`Param` survives inference.

An unannotated generalized binding keeps the implicit polymorphism of
[3.1 Let-Polymorphism is Freshening
(Instantiation)](type-inference.md#31-let-polymorphism-is-freshening-instantiation): its scheme is
the bound graph, not a `Type::Poly`. The two coexist, as
[Roadmap and Current Prototype Status](type-inference.md#roadmap-and-current-prototype-status)
anticipates for explicit quantification. A diagnostic renders an inferred scheme in the `Poly`
notation ([Printing an inferred polymorphic type](#printing-an-inferred-polymorphic-type)).

---

## Representation

```rust
pub enum Type {
    // ...
    Param(Rc<TypeParam>),
    Poly(Rc<PolyType>),
}

pub struct TypeParam {
    pub id: TypeParamId,      // identity; equality, ordering and hashing use it
    pub spelling: SmolStr,    // the name the user wrote, for display
    pub level: Level,         // the level of the right-hand side the `Poly` annotates
    pub bound: Option<Type>,  // normalized at `level`
}

pub struct PolyType {
    pub params: Vec<PolyParam>,         // each a shared-hole id, a spelling, and a bound
    pub requires: Vec<PolyRequirement>, // each a trait, its operands, its associated types
    pub body: Type,
}
```

The variant names follow the spec's terms, "polymorphic type" and "type parameter". `Var` would be
a third meaning for one word: `TypedExprNode::Var` is a term variable, and `Type::Infer` holds an
inference variable. `PolyScheme` stays the name of the implicit, inferred form.

`Poly` is a type, so it goes wherever a type goes: a binding's annotation, a `Module{…}` member
once modules land, and, when the spec decides them, a record
field or a function's domain. The representation does not limit where it appears; the solver does
([Where a polymorphic type may appear](#where-a-polymorphic-type-may-appear)).

A `Param` leaf carries what the solver reads of the parameter, its level and bound, as an `Infer`
leaf's variable carries its own. The solver needs them where no scope is in hand: a
specialization's pin and a trait deposit run during coalesce and call `constrain_subtype` without
one.

Neither fact exists when lowering writes a type parameter. Levels are an inference notion, and a
bound's refinement names are resolved by `uniquify`, which runs after lowering and rewrites the
bound in place as a type slot of the `Poly` (`walk_children` visits a `Poly`'s bounds and body).
So before inference a type parameter is a `Type::SharedHole`, as `Hole` stands for an inference
variable: lowering writes a fresh shared hole for each parameter and records its id in the `Poly`.
Opening the `Poly` mints the `Param` leaf and seeds the shared-hole memo with it, and normalization
then turns every occurrence into that leaf
([Checking a binding against a polymorphic type](#checking-a-binding-against-a-polymorphic-type)).

A shared hole normalized before its `Poly` is opened would become an ordinary variable, a
flexible `T`. By construction one cannot be: a parameter occurs only inside the right-hand side its
`Poly` opens first. In debug builds inference entry collects every `Poly`'s parameter holes, and
normalizing one that is not yet seeded panics.

A `Param`'s bound can hold inference variables whose bounds hold the `Param`. Arena teardown clears
every variable's bounds, which breaks that cycle as it breaks the cycles among variables.

---

## Lowering

The parser gives `Stmt::FunctionDef` a `type_params` field beside `params`, and a `requires` field.
Type parameters stay out of `params` because the parameter count is the arity: it sizes the argument
tuple and fixes how many lambdas a `Mut`-parameter function's chain has (`uncurry_params`).

`declare_type_params` declares each parameter in order as an alias of a fresh `Type::SharedHole`,
after lowering its bound with the parameters before it in scope, and records the hole's id in the
`Poly`. It refuses a built-in name and a name declared twice.

A type-position `\T, U <: B -> V` lowers to a `Type::Poly` in an alias scope of its own:
`lower_type_expr_or_poly` declares the parameters and lowers `V` as the body. That function admits a
`Poly` at the root, and `lower_type_expr`, which every other position and every nested position
uses, refuses one, so a polymorphic type inside another type is refused whether written or reached
through an alias. `lower_let_annotation` lowers a `let` binder's annotation through
`lower_type_expr_or_poly`, and so does an alias's right-hand side; a bounded `<:` polymorphic
annotation is refused there.

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

1. Opens `𝜋` inside `in_let_rhs` (`Typing::open_poly`): mints each parameter's `Param` at the
   right-hand side's level, with its bound normalized at that level, and seeds the shared-hole memo
   with it under the parameter's hole. It returns `𝜋`'s requirements normalized, which are in
   scope as **assumptions** while the right-hand side is emitted
   ([Obligations under assumptions](#obligations-under-assumptions)) and recorded for the
   binding's uses.
2. Emits the right-hand side and records `inferred <: 𝜋.body` through `bind_annotation`, at the
   right-hand side's level, with the parameters opaque. A `def`'s body is a `Hole`, completed from
   the lambda's type.
3. Binds the name at the completed body and generalizes. The body mentions the parameters above the
   binding's level, so `should_generalize` admits the `let` through its level test, and the
   coalesce walk asks the same predicate.

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

`constrain_go` gains these rules for a parameter `𝑃`:

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

`compact` treats a parameter as an atom (`AtomKey::Param`), so two parameters at one position
collide as two bases do. `collapse_by_param_bounds` resolves the case a bound relates: at a positive
position it keeps the contribution every other is below through a bound chain, at a negative one the
contribution below every other. Under `𝑈 <: 𝑇` the join of `𝑇` and `𝑈` is `𝑇`. "Below" follows a
bound chain to an equal type only, so a bound that is a strict subtype of another contribution,
such as `𝑇 <: {at: Int}` meeting a wider record, still collides.

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
| a product | answered by `narrow_product`, as before | the component obligations it mints start from the same assumptions |

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
`Equatable({T, U}, {T, U})` lowers to `Equatable(T, T)` and `Equatable(U, U)`. Every operand is then
a type parameter in scope or a base type, and a requirement no instance row could match given its
bases, or with any other operand, is refused at the requirement, since no use could satisfy it. A
requirement on bases only is checked and dropped. `Transaction` is refused until
[chl-spec.md, "8.7 Direction [Decided]: transactions as contextual parameters"](../../../docs/chl-spec.md#87-direction-decided-transactions-as-contextual-parameters)
is implemented. A type parameter that is the associated type of a requirement whose operands are
determined is itself determined, for the check that every parameter is.

---

## Instantiation

The `Var` arm instantiates every binding through `PolyScheme::instantiate_with_params`:

1. Each type parameter above the scheme's cutoff maps to a fresh variable `𝛼` at the use's level,
   in the use's telescope, through `FreshenCache::params`, and the body freshens through it.
2. For each parameter with bound `𝐵`, the arm records `𝛼 <: 𝐵[𝛼/𝑃]`, the bound freshened through
   the same cache.
3. For each requirement of the binding's `requires` clause, normalized when the `Poly` was opened
   and kept in `InferCtx::requirements` by the binding's name, the arm calls `require_trait` over the
   substituted operands, freshened through the same cache, then records `𝑜 <: 𝛼ₒ` from the
   obligation's associated variable `𝑜` to the substituted associated type.

A failure in 2 or 3 is blamed on the use, with a secondary label at the bound or the
requirement as written ([Secondary labels](#secondary-labels)), the error shape
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
its parameters opaque
([type-inference.md, "Checking a definition alone"](type-inference.md#checking-a-definition-alone)),
and that check is what reports such an error.

An obligation copy holding an assumption about one of the specialized binding's own parameters
is reset to its trait's instances and the assumptions that name no such parameter
(`TraitObligation::reset_for_specialization`), and is redelivered its operands' lower bounds once
the clone is pinned (`redeliver`). Freshening writes bounds directly and so does not deliver; the
redelivery, which reads the bounds transitively, replaces it. That a reset obligation resolves
follows from the use having satisfied every requirement at the same types, and the check that a
specialization raises nothing the definition alone does not asserts it.

A use inside a generic definition checked alone carries that definition's still-opaque parameters
into the specialization it reaches. The coalesce walk keeps the `requires` clauses of the
definitions it is checking alone in scope (`CoalesceCtx::assumptions`), and a reset obligation is
given those as well (`assume_more`).

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

## Polymorphic aliases

An alias `g = f` of a generalized `f` needs no annotation. Implemented as
[A name of a generalized binding](type-inference.md#a-name-of-a-generalized-binding) describes.

---

## Printing an inferred polymorphic type

`poly_for_display` (`src/ccl/infer/solver/display.rs`) renders a type as a `Poly` over its
variables above a cutoff. An annotation mismatch against a `Poly` uses it for the right-hand side's
type, with the cutoff at the binding's level, so `pick: \T -> T => T = inc` reports `inc` as
`\A -> (A ⇒ Int) requires Addable(A, Int, Output=Int)`.

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
  `def at(a): a.at` prints as `\A -> ({at: A} ⇒ A)`, and `def both(a): (a.at, a)` as
  `\A <: {at: B}, B -> (A ⇒ (B, A))`.
- **Requirements.** Each obligation becomes a requirement unless every operand is concrete, which
  the definition already answered. Refinements are dropped, since an instance row matches a base
  whatever its refinements. An obligation a product answered is stated by its components.
- **Markers.** A join or meet the notation cannot write is a parameter spelled as what it stands
  for: `A ∨ Int` where a parameter and a concrete type meet at a positive position
  (`def f(c, a): a if c else 1`), `A ∨ B` where two parameters do, and `A ∧ B` at a negative one.

A freshened obligation copy watches only the operand variables freshening reached. An operand it
did not reach, such as the variable a literal flows into, is still the original's, and the copy
records it for the requirement it states (`TraitObligation::inherited_operands`). Narrowing never
reads it, so a copy draws no edge to the definition's variables.

---

## Secondary labels

An error is reported at the node whose rule drew the failing edge, and each other position the
edge involves is a secondary label (`LocatedInferError::related`): `x = id((sku=1))` then
`x.at` is reported at `x.at`, with "the value comes from here" at `id((sku=1))`.

- **Origins on bounds.** `Bound::origin` records where a bound's bounding side came from: for a
  lower bound, the expression the value came from; for an upper bound, what demanded it. An
  `Origin` is a node, or the span of a bound or requirement written in a `Poly`
  (`ty::WrittenAt`), which has no node.
- **The walk carries them.** `ConstrainCache` holds the origins of the edge being walked, set by
  its caller (`ConstrainCache::at`): emission sets the node under emission, and a
  specialization's pin sets the use. Recording a bound stores its bounding side's origin, and
  closing an edge over a stored bound walks on with that bound's origin on its side. Freshening
  and extrusion copy origins, so a definition's bounds point into its body at every use. The
  first edge to fail records its two origins (`ConstrainCache::take_failure`).
- **Trait obligations.** An obligation demands from where it was stated
  (`TraitObligation::required_at`): its operator, or the requirement it was instantiated from. A
  failed narrowing records the obligation as the demand and the contribution's origin as the
  value.
- **Written demands.** The `Var` arm checks a parameter's bound and instantiates a requirement
  under `Typing::with_demand_at`, so a failure points at the bound or the requirement as written.
- **Rendering.** `compile_program` resolves a node through the lowering projection and keeps a
  label whose span lies outside the primary span, reading "required here" or "the value comes
  from here".

Not covered:

- A concrete type carries no origin, so a value meeting a demand without passing through an
  inference variable has no value label: `x = (sku=1)` then `x.at`
  (`a_concrete_value_meeting_a_demand_directly_has_no_label`).
- Narrowing an obligation records no origin, so a conflict between two operands of one operator
  labels neither operand's source: `mk(True) + 1`, where `mk` returns a string.
- An error raised at coalesce, such as an incompatible join or a use whose instantiation does not
  resolve, has no edge and so no label.
- The inspector's diagnostic carries one span (`inspector_model::wire::Diagnostic`), so it shows
  no secondary label.

---

## Implementation stack

One change per item, each updating this doc and the spec status it implements:

1. **Parser** (implemented). `requires` lexed as a keyword; `type_params` and `requires` on
   `FunctionDef` and `Lambda`; a requirement's associated types by name; `<:` on a lambda's type
   parameters. Lowering refuses each new form as unsupported. A capitalized `def` parameter stops
   being a value parameter.
2. **Polymorphic aliases** (implemented).
3. **`Type::Poly`, `Type::Param`, bounds** (implemented). Lowering of `def` type parameters and of
   `\T -> V`, levels and escape, subtyping, checking a binding against a `Poly`, instantiation of
   bounds, specialization, a generic definition checked alone, the post-inference check, display.
4. **Requirements** (implemented). Assumption rows, the componentwise `Equatable` reading,
   unsatisfiable requirements, instantiation of requirements, clone reset and redelivery, the
   sweep.
5. **`Poly` against `Poly`** (dropped). Module types need no subtyping rule between two `Poly`s
   ([Where a polymorphic type may appear](#where-a-polymorphic-type-may-appear)).
6. **Printing inferred polymorphic types** (implemented).
7. **A use that checks compiles** (implemented). Each generalized definition checked alone, and
   the debug assertion that a specialization whose pin succeeded raises nothing the definition
   alone does not. A collection annotation's kind demand is answered against a domain variable's
   upper bounds as well as its lower ones, so a use supplying a domain of the wrong kind fails at
   the use.
8. **Secondary labels** (implemented). An origin recorded on every bound and obligation, giving
   an error at a use its secondary label.
