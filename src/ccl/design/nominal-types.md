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
type's children visits the arguments and does not enter the declaration, which is an identity.
Equality, ordering and hashing on `NominalDecl` are by the path of the module that declares it and
its name ([chl-spec.md, "Nominal type identity"](../../../docs/chl-spec.md#nominal-type-identity)),
so one source declares the same types in every compilation. A compilation holds at most one
declaration of a path, since lowering refuses a second. Two compilations may each hold one with
different constructors, and these compare equal, so a comparison of one version's types with the
next version's compares the declarations' bodies itself. The program's own declarations sit at the
root module's path, which is empty.

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
variance. A data function's domain, a history's children and a listed kind candidate are
**equality** positions, and a `SubtypesOf` bound keeps the variance of the function that carries
it. A parameter seen at none makes `define` fail, and lowering reports it at the declaration.

An invariant parameter is one of two `Variance`s, which a join treats differently:

- **`Invariant`**: seen at an equality position. Both sides of a relation are one type there, so
  two applications whose arguments differ have no join.
- **`Bipolar`**: seen at both polarities and at no equality position, as `T` in
  `cell(T, T => T)`. Its argument has an **input** side, which the parameter's negative
  occurrences read, and an **output** side, which its positive ones read. An argument that any
  program writes or any constructor builds is both sides at once; a join makes them differ, and
  `Type::Split` holds the two then. `instantiate` replaces a bipolar parameter by the side its
  occurrence reads (`nominal::sides`).

This is the polar treatment of an invariant constructor in subtyping inference with lazy joins: a
join of `Cell(Int@1)` and `Cell(Int@2)` is the application whose output side is their join, `Int`,
and whose input side is their meet, which both arms are subtypes of. Equating the two arms'
arguments instead would need a join computed when the bounds are recorded, which the solver does
not do.

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

The constructor node is `TypedExprNode::NominalCtor`, holding the declaration, the constructor's
name and the payload. It is its own node rather than a `VariantCtor` because it has its own typing
rule: a `VariantCtor` builds a one-tag structural variant that width-subtypes into wider ones, and
a `NominalCtor` builds a value related only to its declaration. Every pass that matches one has an
arm for the other. A runtime value of either is the union row its tag names, so `lambda_elim` and
operator conversion lower both the same way. The constructor's name is the tag, which is how a
value identifies its constructor
([chl-spec.md, "A nominal type is opaque"](../../../docs/chl-spec.md#a-nominal-type-is-opaque)).

---

## Inference

### The constructor rule

`emit_nominal_ctor` types a constructor `N::c(𝑒)` as `N(𝛼…)`, one fresh variable per type
parameter, and constrains `𝑒` below the constructor's payload at `𝛼…`. The payload is compared
with its refinements stripped. The node is only ever the body of the constructor's function, whose
parameter annotation already discharged them, or a constructor without parameters, whose payload
is `unit`; the declaration's own predicates were never typed.

### Subtyping

`constrain_go` relates `N(𝑎…) <: N(𝑏…)` by relating each pair of arguments as its parameter's
variance requires. A contravariant pair is related in the flipped direction with the two sides'
morphisms swapped, as a function's domain is, and an invariant pair in both directions. A bipolar
pair relates its output sides as a covariant pair and its input sides as a contravariant one, so
two arguments that are not split relate both ways. A nominal
type paired with any other type, including another nominal type, falls to the catch-all mismatch.

`extrude` carries each argument across a level boundary at the polarity its variance gives it,
and an invariant argument, or a bipolar one that is not split, through the two-way proxies a
history's payload uses. A split argument extrudes each side at its own polarity.

### Compaction and coalescing

`CompactType::nominal` maps each declaration at a position to its arguments' **sides**: one per
argument, and two for a bipolar one, its input then its output (`NominalDecl::sided_variances`).
Two contributions of one declaration merge side by side, a contravariant side at the flipped
polarity, so a join meets the input sides and joins the output sides. An invariant argument is
compacted as a data domain is, both sides merged however the walk reaches it, and two that differ
are recorded on the inputs of the merge (`CompactType::nominal_conflict`), which coalescing
reports as incompatible bounds. Two declarations at one position are two shapes, so coalescing
reports the join of two nominal types as a conflict. `coalesce_compact_go` materializes the entry
as `Type::Nominal`, each side at its own polarity and a bipolar argument's two sides as one type
where they agree (`nominal::split`). The specialization key (`spec_key`) and the simplification
and display walks follow the same layout and polarities.

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
  `variant_project`.
- Operator conversion, where `extent_of` builds a value's extent and the `NominalCtor` and
  `variant_wrap` arms build a union column.

Planning treats a constructor's payload as a product's component: a collection-valued payload is
an iteration site (`planning::iterate`'s `mark_component_source`). The payload position is handed
the constructor's declared parameter type (`planning::conditionals`'s `child_demand`), so a `box`
entering the described sum `type Bag(T) = List(T)` declares stays, as one entering an annotated
`let`'s does.

The representation of `N(𝑎…)` is the closed variant tagged by constructor name, each tag carrying
its payload at `𝑎…`, with the tags in name order (`NominalDecl::representation`). It carries no
refinement of the declaration's. Each construction discharged them during inference, and the
copies the declaration holds are untyped. A refinement inside an argument `𝑎` stays, since the use
that wrote it typed it.

A runtime value is held in that representation, as the union value its constructor's tag names.
The reload guard compares extents, which leave out the type's name and its declaration's
refinements, so it refuses every variable whose type mentions a nominal type
([program-evolution.md, "Six refusals"](program-evolution.md#six-refusals)).

---

## Declarations lowering refuses

- A recursive declaration, one whose constructors' parameter types reach the declaration itself.
  Its representation would be an infinite type. Lowering refuses it at the declaration.
- A refinement in a constructor's parameter type that names a module binding. The constructor
  functions are bound outside the whole module, where no module binding is in scope, so lowering
  refuses a parameter type with a free name.
