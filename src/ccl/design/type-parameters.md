# Type parameters

> **Status: [Sketched].** A proposed implementation of
> [chl-spec.md, "6.8 Polymorphic types"](../../../docs/chl-spec.md#68-polymorphic-types). Of the
> [Implementation stack](#implementation-stack), items 1 to 3 are implemented: the parser,
> polymorphic aliases, and type parameters with their bounds. The sections on requirements,
> `Poly` against `Poly`, and printing describe work not yet done.

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
    pub params: Vec<PolyParam>, // each a shared-hole id, a spelling, and a bound
    pub body: Type,
}
```

Item 4 adds a `requires` list to `PolyType`, each requirement a trait, its operand types (any
types), its associated types by name, and a span.

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

A `requires` clause lowers in item 4. Until then lowering refuses one on a `def` and on a `Poly`.
Item 4 resolves each requirement's trait name against the trait table
([chl-spec.md, "Trait requirements [Decided]"](../../../docs/chl-spec.md#trait-requirements-decided))
and lowers each argument as an ordinary type expression. `Transaction` stays refused until
[chl-spec.md, "8.7 Direction [Decided]: transactions as contextual parameters"](../../../docs/chl-spec.md#87-direction-decided-transactions-as-contextual-parameters)
is implemented.

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
   with it under the parameter's hole. Item 4 also pushes `𝜋`'s requirements as **assumptions**
   here ([Obligations under assumptions](#obligations-under-assumptions)).
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

A type parameter arriving at an operator's operand is `Offered::Param`. Delivery offers its bound
in its place, so `x + 1` with `x: T <: Int` resolves as `Int + Int`, and an unbounded parameter fails
with `MissingRequirement`, naming the parameter and the trait. `link_watches` replays a parameter
already on a variable when an obligation is linked to it, as it replays a base. That is item 3. The
rest of this section is item 4.

An obligation's candidate set holds **rows**. A row is an instance from the trait's table or an
**assumption**: a requirement of a `Poly` open where the obligation is minted. `InferCtx` keeps the
stack of open `Poly`s, and `require_trait` adds their requirements on the obligation's trait. An
instance row's arguments are bases; an assumption's are any types.

A contribution arriving at a position keeps the rows whose argument there it **matches**: the same
base, the same parameter, or the same type former (tuple, record, function, collection, variant)
with the same arity and labels. Matching compares heads only. When every surviving row agrees on the
argument at a position, that argument is deposited as an upper bound on the operand variable, the
polarity [Requirements are read together, once](type-inference.md#requirements-are-read-together-once)
uses, and ordinary subtyping checks the rest of the structure. A base's row is fully determined by
its head, so this adds nothing for an instance row.

A product still goes through `narrow_product` for `Equatable`, whose reading is componentwise. An
assumption `Equatable({T, U}, {T, U})` is therefore also read componentwise when the `Poly` is
opened: it adds `Equatable(T, T)` and `Equatable(U, U)`, which the component obligations
`narrow_product` mints are answered by.

Deposit of an associated type is unchanged: once every surviving row agrees on it, it is deposited,
and it may be a parameter. `x + y` under `requires Addable(T, T, Output=T)` gives the sum type `T`.

An obligation that a parameter empties reports the missing assumption by name:
`no requirement states Addable(T, Int); add it to the requires clause`. A requirement that no
instance row could match at some position, such as `Orderable(List(T), List(T))`, is an error at
the requirement when the `Poly` is opened, since no use could satisfy it. The sweep intersects
accepted types, bases and parameters alike, and treats a parameter it settles on as it treats a
base.

---

## Instantiation

The `Var` arm instantiates every binding through `PolyScheme::instantiate_with_params`:

1. Each type parameter above the scheme's cutoff maps to a fresh variable `𝛼` at the use's level,
   in the use's telescope, through `FreshenCache::params`, and the body freshens through it.
2. For each parameter with bound `𝐵`, the arm records `𝛼 <: 𝐵[𝛼/𝑃]`, the bound freshened through
   the same cache.
3. Item 4: for each requirement, the arm calls `require_trait` over the substituted arguments, then
   records `𝑜 <: 𝛼ₒ` from the obligation's associated variable `𝑜` to the substituted associated
   type.

A failure in 2 or 3 is blamed on the use. Item 7 adds a secondary label at the bound's or the
requirement's span, the error shape
[chl-spec.md, "A use that checks compiles [Decided]"](../../../docs/chl-spec.md#a-use-that-checks-compiles-decided)
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
`SpecializeFrame::generic` marks a binding annotated with a `Poly`, and `coalesce_generalized_let`
checks such a definition alone with `typecheck_discarded_definition` once its last use is
specialized, after which nothing clones from it, as it already checks a definition nothing calls. A
diagnostic the clones already raised is not repeated.

Item 4: a cloned obligation holding an assumption of the specialized `Poly` is reset to its trait's
table and redelivered its operands' current lower bounds, so the clone resolves as an ordinary
monomorphic body. Freshening writes bounds directly and so does not deliver; the redelivery replaces
it. That the reset obligations resolve follows from the use having satisfied every requirement at
the same types, and item 7 of the [Implementation stack](#implementation-stack) asserts it.

`spec_key` keys a parameter as an atom by `id`, for the uses inside a definition checked alone.

---

## Where a polymorphic type may appear

A `Poly` reaches the solver in two ways. As a binding's annotation, emission opens it and the `Var`
arm instantiates it, so `constrain_go` never sees it. Anywhere else, `constrain_go` meets it inside
another type, and the rules are:

| Constraint | Rule |
| --- | --- |
| `Poly(𝜋₁) <: Poly(𝜋₂)` | open `𝜋₂` with its parameters opaque and its requirements assumed, instantiate `𝜋₁`, and constrain the bodies. This is the Module-type member check |
| `Poly(𝜋) <: 𝑈`, `𝑈` not a `Poly` | instantiate `𝜋` and constrain its body |
| `𝑋 <: Poly(𝜋)`, `𝑋` not a `Poly` | refused: `𝑋` would have to be generalized where it stands |

The spec leaves a polymorphic type nested inside another type **[Open]**. Until it decides, lowering
refuses one, and the first two rows serve Module-type member checks once modules land. Until item
5, `compact`, `extrude` and `spec_key` treat a `Poly` reaching them as unreachable. A refused case is
an error, never an approximation.

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

A diagnostic renders a generalized binding's scheme as a `Poly`:

- each quantified variable becomes a parameter, named `A`, `B`, … in order of first appearance,
  with its upper bound as `<:` when it has a single concrete one;
- each obligation watching a quantified variable becomes a requirement, with an associated variable
  named by the same rule;
- a part the notation cannot write, such as the kind of a function type or a refinement over a name
  not in scope at the diagnostic, is rendered with a marker rather than dropped.

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
4. **Requirements.** Assumption rows, head matching and its deposit, the componentwise `Equatable`
   reading, unsatisfiable requirements, instantiation of requirements, clone reset and redelivery,
   the sweep.
5. **`Poly` against `Poly`.** The subsumption rule, with Module types as its consumer.
6. **Printing inferred polymorphic types.**
7. **A use that checks compiles.** Each generalized definition checked alone; the debug assertion
   that a clone whose pin succeeded raises no error; an origin recorded on every bound, giving
   every use error its secondary label.
