# Type parameters

> **Status: [Sketched].** A proposed implementation of
> [chl-spec.md, "6.8 Polymorphic types"](../../../docs/chl-spec.md#68-polymorphic-types). Of the
> [Implementation stack](#implementation-stack), items 1 and 2, the parser and polymorphic aliases,
> are implemented; nothing past them is.

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
    Poly(Rc<PolyType>),
    Param(Rc<TypeParam>),
}

pub struct PolyType {
    pub params: Vec<Rc<TypeParam>>,
    pub requires: Vec<Requirement>,
    pub body: Type,
}

pub struct TypeParam {
    pub id: TypeParamId,           // identity; equality and hashing use it
    pub spelling: SmolStr,         // the name the user wrote, for display
    pub span: Span,
    pub level: Cell<Option<Level>>,
    pub bound: Option<Type>,
}

pub struct Requirement {
    pub trait_: Trait,
    pub args: Vec<Type>,           // one per operand position, any type
    pub assoc: Vec<(Assoc, Type)>, // `Output=O`
    pub span: Span,
}
```

The variant names follow the spec's terms, "polymorphic type" and "type parameter". `Var` would be
a third meaning for one word: `TypedExprNode::Var` is a term variable, and `Type::Infer` holds an
inference variable. `PolyScheme` stays the name of the implicit, inferred form.

`Poly` is a type, so it goes wherever a type goes: a binding's annotation, a `Module{…}` member
once modules land, and, when the spec decides them, a record
field or a function's domain. The representation does not limit where it appears; the solver does
([Where a polymorphic type may appear](#where-a-polymorphic-type-may-appear)).

A `Param` leaf points at its own declaration, not at its `Poly`. A parameter's bound rides in the
leaf because the solver relates types where no scope is in hand: a specialization's pin and a trait
deposit run during coalesce and call `constrain_subtype` without one. A bound names only the
parameters before it ([chl-spec.md, "Bounds [Decided]"](../../../docs/chl-spec.md#bounds-decided)),
so the `Rc`s through bounds are acyclic, and a `Poly` owning its parameters closes no cycle either.

`level` is set when a `Poly` is opened for checking ([Levels](#levels)). Lowering cannot set it,
because levels are an inference notion.

---

## Lowering

The parser gives `Stmt::FunctionDef` a `type_params` field beside `params`, and a `requires` field.
Type parameters stay out of `params` because the parameter count is the arity: it sizes the argument
tuple and fixes how many lambdas a `Mut`-parameter function's chain has (`uncurry_params`).

A type-position `\T, U <: B -> V requires …` lowers to a `Type::Poly` in an alias scope of its own:

1. Each parameter in order is declared as an alias of a fresh `Type::Param`, after lowering its
   bound with the parameters before it in scope.
2. Each requirement's trait name resolves against the trait table
   ([chl-spec.md, "Trait requirements [Decided]"](../../../docs/chl-spec.md#trait-requirements-decided)),
   and each argument lowers as an ordinary type expression. `Transaction` is refused as unsupported
   until
   [chl-spec.md, "8.7 Direction [Decided]: transactions as contextual parameters"](../../../docs/chl-spec.md#87-direction-decided-transactions-as-contextual-parameters)
   is implemented. An unknown trait name or a wrong operand count is a lowering error.
3. `V` lowers in that scope and becomes the body.

A `def` with type parameters lowers to a `let` whose binding is annotated with the `Poly` its
signature denotes: the type parameters and `requires` clause as above, and the body
`{𝐴₀, …} => 𝑅` from the value parameters' annotations and the `=>` result. The definition's alias
scope covers the parameter annotations and the result as well as the body. Today the body's alias
scope opens inside `lower_stmts_inner`, after which `uncurry_params` lowers the parameter
annotations in the enclosing scope, so the scope moves out to `lower_function_body`. The lambda's
own parameter annotations name the same `Param`s as the `Poly`.

A type parameter that no value parameter's annotation mentions, and that is not a requirement's
associated type, is a lowering error.

---

## Levels

Emission opens a `Poly` when it checks a right-hand side against it ([Checking a
binding against a polymorphic type](#checking-a-binding-against-a-polymorphic-type)): it sets each
parameter's `level` to the level the right-hand side is emitted at, one above the binding, which is
where the right-hand side's own inference variables sit.

`type_level` reports a parameter's level. `ChanDom` reports 0 so that it flows outward through
bounds; a type parameter must not ([chl-spec.md, "Type parameters
[Decided]"](../../../docs/chl-spec.md#type-parameters-decided)). Recording an edge that carries a
parameter outward needs `extrude`, and `extrude` meeting a parameter above its target level fails
with `TypeParamEscapes`, naming the parameter and its definition. It never mints a proxy.

`freshen_level` reports the level too, so `freshen_above` does not short-circuit past a type that
mentions a parameter.

---

## Checking a binding against a polymorphic type

`emit_let` with an exact annotation `Poly(𝜋)`:

1. Opens `𝜋`: sets the parameters' levels and pushes `𝜋`'s requirements as **assumptions**, which
   stay in scope while the right-hand side is emitted
   ([Obligations under assumptions](#obligations-under-assumptions)).
2. Emits the right-hand side and records `inferred <: 𝜋.body` through `bind_annotation`, with the
   parameters opaque.
3. Binds the name at `Poly(𝜋)` and generalizes. `should_generalize` admits a `let` annotated with a
   `Poly`, and the coalesce walk asks the same predicate, so emission and specialization agree on
   which `let`s are polymorphic.

A right-hand side that would be monomorphic without the annotation, a call or a collection, is an
error at the annotation ([chl-spec.md, "Polymorphic type annotations
[Decided]"](../../../docs/chl-spec.md#polymorphic-type-annotations-decided)). Lowering refuses a
call or a collection, whose shape is syntactic. A name bound to a monomorphic binding is refused at
emission, where the binding's scheme is known.

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
sort for a parameter and fails. A type-kind constraint on a variable whose lower bound is `𝑃` is
answered by `𝑃`'s bound. `compact` treats a parameter as an atom, so a position with lower bounds
`𝑃` and `𝑄`, neither bounded by the other, is `IncompatibleBounds`.

---

## Obligations under assumptions

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

The `Var` arm instantiates a binding whose type is `Poly(𝜋)`:

1. Each parameter maps to a fresh variable `𝛼` at the use's level, through a `params` map in
   `FreshenCache`, and `𝜋.body` freshens through it.
2. For each parameter with bound `𝐵`, the arm records `𝛼 <: 𝐵[𝛼/𝑃]`.
3. For each requirement, the arm calls `require_trait` over the substituted arguments, then records
   `𝑜 <: 𝛼ₒ` from the obligation's associated variable `𝑜` to the substituted associated type.
4. The map is recorded in a table keyed by the use's `NodeId`, which the coalesce walk reads.

A failure in 2 or 3 is blamed on the use, with a secondary label at the bound's or the requirement's
span, the error shape
[chl-spec.md, "A use that checks compiles [Decided]"](../../../docs/chl-spec.md#a-use-that-checks-compiles-decided)
states.

---

## Specialization

`specialize_use` reads the use's map and seeds `FreshenCache::params` with it before freshening the
clone, next to `seed_chan_dom_pairings`. Freshening meets a parameter in three ways:

| Parameter | Freshened to |
| --- | --- |
| of the specialized binding's `Poly` | the use's `𝛼` |
| of another `Poly` above the cutoff, as in a nested definition's annotation | a new `TypeParam`, its bound freshened, so the nested `Poly` is α-renamed |
| at or below the cutoff, an enclosing definition's | itself |

A cloned obligation holding an assumption of the specialized `Poly` is reset to its trait's table
and is redelivered its operands' current lower bounds, so the clone resolves as an ordinary
monomorphic body. Freshening writes bounds directly and so does not deliver; the redelivery replaces
it. That the reset obligations resolve follows from the use having satisfied every requirement at
the same types, and item 7 of the [Implementation stack](#implementation-stack) asserts it.

A never-called definition is coalesced in place by `typecheck_discarded_definition`, with its
parameters as atoms. `spec_key` keys a parameter as an atom by `id` for the uses inside it.

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
refuses one, and the first two rows serve Module-type member checks once modules land.
A refused case is an error, never an approximation.

---

## After inference

A `Poly` or `Param` in the tree that survives inference is a compiler defect.
`collect_type_errors` reports one at every strictness, as it reports `Hole`. A specialized binding
is rebuilt as monomorphic `let`s, so its `Poly` annotation leaves with it. `Display for Type`
renders a `Poly` in the spec's notation and a parameter by its spelling. `hash_type_in` hashes a
parameter by `id`, and a `Poly` by its parameters' positions, so α-equivalent `Poly`s hash equal.

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
3. **`Type::Poly`, `Type::Param`, bounds.** Lowering of `def` type parameters and of
   `\T -> V`, levels and escape, subtyping, checking a binding against a `Poly`, instantiation of
   bounds, specialization, the post-inference check, display.
4. **Requirements.** Assumption rows, head matching and its deposit, the componentwise `Equatable`
   reading, unsatisfiable requirements, instantiation of requirements, clone reset and redelivery,
   the sweep.
5. **`Poly` against `Poly`.** The subsumption rule, with Module types as its consumer.
6. **Printing inferred polymorphic types.**
7. **A use that checks compiles.** Each generalized definition checked alone; the debug assertion
   that a clone whose pin succeeded raises no error; an origin recorded on every bound, giving
   every use error its secondary label.
