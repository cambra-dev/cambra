# Nominal types

How the compiler implements
[chl-spec.md, "6.8 Nominal types and methods [Decided]"](../../../docs/chl-spec.md#68-nominal-types-and-methods-decided).

A `type` declaration lowers to a `NominalDecl` (`ccl/nominal.rs`), and an application of it is
`Type::Nominal(decl, args)`. Inference relates two applications of one declaration argument by
argument and relates a nominal type to no other type. The type keeps its name to operator
conversion. A pass that reads a value's shape, rather than relating its type, reads the
representation through `Type::structure`.

---

## Representation

`Type::Nominal` holds the declaration by `Rc` and its type arguments as children. A walk over a
type's children visits the arguments and does not enter the declaration, which is an identity:
equality, ordering and hashing on `NominalDecl` are by its `NominalId`.

A `NominalDecl` holds its name, its type parameters, and its body, set once by `define`:

- One `NominalCtor` per constructor, in declaration order. A constructor has a name and its
  declared parameters, each a documenting name and a type. The type parameters appear in those
  types as declared `Type::Param`s, which `NominalDecl::instantiate` replaces with an
  application's arguments.
- One `Variance` per type parameter.

A constructor's **payload** is the one argument it takes: `Unit` for no parameters, the
parameter's type for one, and the tuple of them for several (`NominalCtor::payload`).

### Variance

`define` reads each parameter's variance off the constructors' parameter types (`occurrences` in
`ccl/nominal.rs`). A position is covariant at the top of a parameter type, flips in a compute
function's domain, and composes through another nominal type's parameter by that parameter's
variance. A data function's domain, a history's children and a listed kind candidate are invariant
positions, and a `SubtypesOf` bound
keeps the variance of the function that carries it. A parameter seen at two variances is
invariant. A parameter seen at none makes `define` fail, and lowering reports it at the
declaration.

---

## Lowering

`lower/nominal.rs` lowers a module's declarations in two steps around its type aliases, because an
alias may name a nominal type and a constructor's parameter type may name an alias:

1. `declare_nominal_types` creates each declaration's head, before `pre_declare_type_aliases`.
2. `define_nominal_types` lowers the constructors, after the aliases. It refuses a declaration
   that reaches itself through its constructors' parameter types before defining any declaration,
   so the `Rc` graph of declarations stays acyclic. It then defines each declaration after every
   declaration it names, which `define` needs to read their variances.

An error in either step leaves the module unlowered, as a module-syntax refusal does. Every use
of a declaration that failed would otherwise report a second error.

A declaration stands only at a module's top level, so the table of declarations
(`LoweringContext::nominal_types`) is never snapshotted. A `type` statement in any other block is
refused where `lower_middle_stmt` meets it. At the top level it binds no value and lowers to
nothing.

A type name resolves after the base types and the aliases in scope. `N` and `N(𝐴…)` lower to
`Type::Nominal`, and the number of arguments must match the declaration's parameters.

### Constructors

A constructor that declares parameters is a function. `bind_constructors` binds each one around
the whole module, under the name `N::c`:

```
let N::c : forall (𝑃…) _ = λ __ctor_arg : payload → N::c(__ctor_arg) in …
```

The lambda's parameter carries the payload as an annotation. A call therefore checks its argument
against the declared parameter type, refinements included, by the rule every annotated parameter
follows. A parameterised declaration's constructor is polymorphic through the `Poly` annotation,
whose parameters are the declaration's own. `N::c` in an expression is a reference to the binding,
and `N::c(𝑎…)` applies it as a call to a `def` is applied (`exprs::apply_named`).

A constructor that declares no parameters is a value. `N::c` lowers to the nominal constructor
over `unit` where it is named, and needs no binding.

The constructor node is `TypedExprNode::VariantCtor` with `nominal: Some(decl)`, which keeps the
declaration through every pass. The tag is the
constructor's name, which is how a value identifies its constructor
([chl-spec.md, "A nominal type is opaque"](../../../docs/chl-spec.md#a-nominal-type-is-opaque)).

### Taking a value apart

A `match` arm names a constructor, `case Shape::rect(w, h):`. `constructor_arms_type` checks the
arms before anything lowers: they name constructors of one declaration, each binds one name or
`_` per declared parameter, and without a `case _:` every constructor has an arm. A `match` that
mixes tag arms and constructor arms is refused. Each arm lowers to a `Pattern` whose `nominal`
names the declaration, binding the constructor's payload. For a constructor of one parameter
that binding is the user's name. For several it is a minted name, and each named parameter is
substituted by its projection of the payload tuple (`bind_parameters`), as a multi-parameter
function's parameters are, so an arm whose body is a feed keeps the bare feed the loop fan-out
reads.

An assignment `Price::new(c) = p` is a one-arm `Case` over `p` whose body is the rest of the
block. It is accepted only for a declaration with one constructor, where the match cannot fail.

The single-constructor form also binds `N::extract`, the function `λ 𝑛 : N(𝑃…) → match 𝑛:
case N::new(𝑟): 𝑟`, around the module beside its constructor (`bind_extract`).

### Associated functions

`def N::f(…)` lowers as a `def` named `N::f`, bound where the statement stands, as a module
function is. An `impl N(𝑃…):` block binds its `def`s there, each taking the block's type parameters
before its own (`lower_associated_def`), and each after the block's functions it names
(`order_by_reference`), so they reach each other in any order. A method's `self` without an annotation is
annotated `N(𝑃…)`, the declaration at the block's parameters. Outside a block a parameterised
type's method annotates its `self`. `N::f` in an expression names the binding, and `N::f(𝑎…)`
applies it.

`declare_associated_functions` records every associated function before anything lowers, so a
method call anywhere in the module names every type declaring its method. It checks each against
its type: the type is declared in the module, the name is free in the type's namespace, which the
constructors and `extract` share, and the function declares a value parameter. An associated
function stands at a module's top level, and one with a `Mut` parameter is refused.

### Method calls

A method call `𝑥.m(𝑎…)` is the call `N::m(𝑥, 𝑎…)` for the `N` that `𝑥`'s type names, which
lowering does not know. The parser keeps the call apart from a call of a field, `(𝑟.f)(𝑎…)`, as
`Expr::MethodCall`. Lowering builds the application with a placeholder for the function:

```
(𝑥, 𝑎…) ▷ method(m; N₁::m, N₂::m, …)
```

The placeholder, `TypedExprNode::Method`, holds the method's name, whether the call passes
arguments after the receiver, and, as its children, a reference to each `N::m` the module declares,
so `uniquify` resolves the candidates as it resolves any reference. ANF treats it as an atom, so it
stays the application's function. No type declaring `m` is a lowering error.

Inference resolves the placeholder where it emits the application (`resolve_method`, called from
`emit_apply`). The argument is emitted first, as for every application, so the receiver is typed by
everything the program states before the call. The receiver is the argument, or the first
component of its tuple type when the call passes arguments. That type names a nominal head,
directly or through the bounds its variable has gathered, or the call is an error asking for an
annotation on the receiver: no later use decides it (`docs/chl-spec.md`, "Associated functions and
methods"). The head's candidate replaces the placeholder, and the application is emitted as any
call of a `def`. A head with no candidate is an error naming the type and the method, and a type
that is not nominal is an error saying it has no methods. No `Method` node survives inference.

---

## Inference

### The constructor rule

`emit_variant_ctor` types a nominal constructor `N::c(𝑒)` as `N(𝛼…)`, one fresh variable per type
parameter, and constrains `𝑒` below the constructor's payload at `𝛼…`. The payload is compared
with its refinements stripped. The node is only ever the body of the constructor's function, whose
parameter annotation already discharged them, and the declaration's own predicates were never
typed.

### The constructor-pattern rule

`emit_case` hands a `Case` whose patterns name a declaration to `emit_nominal_scrutinee`. The
scrutinee is constrained below the declaration at fresh arguments, and each arm's binder takes its
constructor's payload at those arguments. The payload keeps the declaration's refinements, typed
as an annotation's predicates are: every value of the type was built by a constructor, whose
function discharged them. So `Price::new(c) = p` gives `c` the type `{Int where _ >= 0}` for
`type Price = {Int where _ >= 0}`.

### Subtyping

`constrain_go` relates `N(𝑎…) <: N(𝑏…)` by relating each pair of arguments as its parameter's
variance requires. A contravariant pair is related in the flipped direction with the two sides'
morphisms swapped, as a function's domain is, and an invariant pair in both directions. A nominal
type paired with any other type, including another nominal type, falls to the catch-all mismatch.

`extrude` carries each argument across a level boundary at the polarity its variance gives it,
and an invariant argument through the two-way proxies a history's payload uses.

### Compaction and coalescing

`CompactType::nominal` maps each declaration at a position to its arguments, one position per
argument. Two contributions of one declaration merge argument by argument, a contravariant one at
the flipped polarity. Two declarations at one position are two shapes, so coalescing reports the
join of two nominal types as a conflict. `coalesce_compact_go` materializes the entry as
`Type::Nominal`, each argument at the polarity its variance gives it. The specialization key
(`spec_key`) and the simplification and display walks follow the same polarities.

### Traits

A nominal type offers no trait (`traits::offered`), so `==`, ordering and arithmetic on a nominal
value are rejected where the operator is applied.

---

## After inference

A nominal type is concrete, and stays in every type slot to operator conversion. A nominal value is
opaque to the passes after inference: it has no fields and satisfies no trait, so it is never a
key, a domain, or an operator's operand, and those passes move it without reading its shape. The
shape is read where a value is built or taken apart, through `Type::structure`, which answers a
nominal type's **representation** and every other type itself:

- `lambda_elim`, where a constructor becomes `variant_wrap` and a `Case` becomes
  `variant_project`. A nominal scrutinee's projections take the nominal type itself as their
  domain (`arms_variant`), since the arms name constructors of that type.
- Operator conversion, where `extent_of` builds a value's extent and the `VariantCtor` and
  `variant_wrap` arms build a union column.

The representation of `N(𝑎…)` is the closed variant tagged by constructor name, each tag carrying
its payload at `𝑎…`, with the tags in name order (`NominalDecl::representation`). It carries no
refinement of the declaration's. Each construction discharged them during inference, and the
copies the declaration holds are untyped.

A runtime value is held in that representation, as the union value its constructor's tag names.
The reload guard compares extents, so it sees the representation as well.

---

## Not implemented

- A recursive declaration, one whose constructors' parameter types reach the declaration itself.
  Its representation would be an infinite type. Lowering refuses it at the declaration.
- An associated function with a `Mut` parameter. Lowering refuses it at the parameter.
- A refinement in a constructor's parameter type that names a module binding. The constructor
  functions are bound outside the whole module, where no module binding is in scope, so lowering
  refuses a parameter type with a free name.
