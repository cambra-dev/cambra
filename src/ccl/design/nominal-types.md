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
Equality and hashing on `NominalDecl` are by the path of the module that declares it, its name,
and its implicit arguments
([chl-spec.md, "Nominal type identity"](../../../docs/chl-spec.md#nominal-type-identity)), so one
source declares the same types in every compilation. A compilation holds at most one declaration of
a path, since lowering refuses a second. Two compilations may each hold one with different
constructors, and these compare equal, so a comparison of one version's types with the next
version's compares the declarations' bodies itself. The root module's declarations sit at its path,
which is empty, and another module's at that module's path. A declaration has no order, since its
implicit arguments are types, which have none, so the solver keys its nominal contributions by
declaration in a `DeclMap`, which finds a key by equality and keeps its entries in insertion order.

The implicit parameters are the type parameters and the `const` parameters of the declaring module
that the type reaches, recorded once the module lowers (`NominalDecl::implicit` and
`NominalDecl::implicit_consts`). The module's own code names the declaration with each standing for
itself. The arguments an import or a run passes make an instance whose implicit arguments are
theirs, sharing the declaration's body, so two imports or runs given different arguments hold two
types ([modules.md, "Nominal types across
modules"](../../../docs/modules.md#nominal-types-across-modules)). A type argument is a `Type`
(`NominalDecl::substituted`). A `const` argument is a `ConstTerm`, a term over the `const`
parameters of the module that wrote the `import` or `run`, kept in normal form, so it is a value
once linking has given those parameters theirs (`NominalDecl::substituted_consts`,
`src/ccl/constant.rs`).

A `NominalDecl` holds its name, its type parameters, and its body, set once by `define`:

- One `NominalCtor` per constructor, in declaration order. A constructor has a name and its
  declared parameters, each a documenting name and a type. The type parameters appear in those
  types as declared `Type::Param`s, which `NominalDecl::instantiate` replaces with an
  application's arguments.
- Each parameter's `WrittenOrder`: the order of its type as the declaration writes it, each
  record the declaration writes by its fields as written and a tuple by position. A
  `Type::Record` keeps no order, so this is where a nominal type's order comes from
  ([chl-spec.md, "Equality and order"](../../../docs/chl-spec.md#equality-and-order)).
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
the whole module, under the name `N::c`, or, for a declaration whose refinements read a `const`
parameter, below that parameter's `let` (`below_last_let`), where the name is in scope:

```
let N::c : forall (𝑃…) _ = λ __ctor_arg : payload → N::c(__ctor_arg) in …
```

The lambda's parameter carries the payload as an annotation. A call therefore checks its argument
against the declared parameter type, refinements included, by the rule every annotated parameter
follows.

A refinement in a constructor's parameter type names only `_` and constants ([chl-spec.md, "9.19
Constants"](../../../docs/chl-spec.md#919-constants)). `lower_parameter_type` replaces each constant
binding it names, and each constant of another module, by its term (`predicate_term`), so the
parameter type reads only the module's `const` parameters, and refuses any other name. In a copy of
the module, linking replaces each of those by the term its import or run gives it
(`settle_const_params`, [modules.md, "Linking"](../../../docs/modules.md#linking)), so
`type Capped = {Int where _ <= limit}` under `limit = max_rate * 2` checks `Capped::new(3)` against
`{Int | __elem <= 10}` in a run given `max_rate=5`. A parameterised declaration's constructor is
polymorphic through the `Poly` annotation, whose parameters are the declaration's own. `N::c` in
an expression is a reference to the binding, and `N::c(𝑎…)` applies it as a call to a `def` is
applied (`exprs::apply_named`).

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

### Taking a value apart

A `match` arm names a constructor, `case Shape::rect(w, h):`. `constructor_arms_type` checks the
arms before anything lowers: they name constructors of one declaration, each binds one name or `_`
per declared parameter, and without a `case _:` every constructor has an arm. A `match` that mixes
tag arms and constructor arms is refused.

Each arm lowers to a `Pattern` whose head is `PatternHead::Constructor`, naming the declaration and
the constructor, where a tag arm's head is `PatternHead::Tag`. Both match a runtime row by the same
tag, which is all a pass that only dispatches reads (`Pattern::tag`). The pattern binds the
constructor's payload: under the parameter's own name for a constructor of one parameter, and under
a minted name for several. Each named parameter of several is then substituted by its projection of
the payload tuple (`bind_parameters`), as a multi-parameter function's parameters are, so an arm
whose body is a feed keeps the bare feed the loop fan-out reads.

An assignment `N::c(𝑎…) = 𝑣` is accepted only for a declaration with one constructor, where the
match cannot fail. It lowers to the plain bindings it means (`ConstructorAssignment`), each
lowered as `𝑥 = 𝑒` is at that statement's position. The payload binds to the one-arm `Case`
`match 𝑣 { N::c(𝑝) → 𝑝 }`, under the parameter's own name for a constructor of one parameter and a
minted name `𝑝` otherwise. Each named parameter of several then binds to its projection `𝑝.𝑖`.
The rest of the block is the body of those bindings and not of the `Case`, so a loop body keeps
the statement sequence the mutability-elimination phases read.

The single-constructor form also binds `N::extract`, the function
`λ 𝑛 : N(𝑃…) → match 𝑛 { N::new(𝑟) → 𝑟 }`, around the module beside its constructor
(`bind_extract`).

### Associated functions

`associated_defs` reads the associated functions a statement declares, `def N::f(…)` or each
`def f(…)` of `impl N(𝑃…):`, a `pub def` as its `def`. `lower_associated_def` lowers each as a
`def` named `N::f`, bound where the statement stands, as a module function is. A block's `def`s take
its type parameters before their own. A method's `self` without an annotation is annotated
`N(𝑃…)`, the declaration at the block's parameters. Outside a block a parameterised type's method
annotates its `self`. `N::f` in an expression names the binding, and `N::f(𝑎…)` applies it.

A block's functions reach each other in any order, so the block lowers to one
`TypedExprNode::DefGroup` of them, in source order, whose binders scope over every definition and
over the rest of the module. Which function a method call names is known only once inference has
typed its receiver, so inference decides the order of the `let`s the group means, from the calls
the functions make (`type-inference.md`, "A definition group is emitted in the order its
references need"). A function that reaches itself through those calls is an error naming the
functions.

`declare_associated_functions` records every associated function before anything lowers, so a
method call anywhere in the module names every type declaring its method. It checks each against
its type: the type is declared in the module, the name is free in the type's namespace, which the
constructors and `extract` share (`member`), and the function declares a value parameter. A
repeated name is reported with its first declaration labelled. `self` is the first parameter, and
its annotation is checked (`check_self_annotation`): a block's `self` and a type without
parameters' take none, and outside a block a parameterised type's is the type at the function's own
type parameters, each named once. An associated function stands at a module's top level, and one
with a `Mut` parameter is refused.

`associated_reach` refuses an associated function that reaches the module's state, a source, a value
parameter without `const`, a member of a Module-typed parameter, or a member of a run the module
declares other than its types' functions and constructors, through the module's bindings and
functions: the copies of the module whose arguments the
type does not tell apart share the type, so their copies of the function must be one function. A
type parameter or a `const` parameter it reaches the same way joins the type's identity instead
(`settle_implicit`).

### Method calls

A method call `𝑥.m(𝑎…)` is the call `N::m(𝑥, 𝑎…)` for the `N` that `𝑥`'s type names, which
lowering does not know. The parser keeps the call apart from a call of a field, `(𝑟.f)(𝑎…)`, as
`Expr::MethodCall`. Lowering builds the application with a placeholder for the function:

```
(𝑥, 𝑎…) ▷ method(m; N₁::m, N₂::m, …)
```

The placeholder, `TypedExprNode::Method`, holds the method's name, whether the call passes arguments
after the receiver, and, as its children, the candidates. Lowering adds a reference to each `N::m`
the module declares and to each public `q::N::m` of a public type a qualifier `q` of the module
reaches (`foreign_methods`), which `uniquify` resolves as it resolves any reference. Linking adds a
reference to each run's and shared import's copy of each public method of that name
(`add_method_copies`), which reaches a type whose module the calling module neither imports nor
runs. ANF treats the placeholder as an atom, so it stays the application's function. A method that
no type the module declares or its qualifiers reach declares, and that no module lowered before it
declares in public (`LoweringContext::reached_methods`), is a lowering error.

Inference resolves the placeholder where it emits the application (`resolve_method`, called from
`emit_apply`). The argument is emitted first, as for every application, so the receiver is typed by
everything the program states before the call: the constraints emission has drawn when it reaches
the call. Those come from the receiver's own expression, the definitions of the bindings it names,
parameters' annotations, the declared results of the functions it calls, a comprehension's source,
and an earlier call of a chain, whose function is resolved and emitted first. A function of the same
`impl` block counts as before the call, since the group emits it before the call is resolved. A use
after the call does not, so a lambda's parameter typed only by the lambda's application is
unresolved at a method call in its body. `what_states_a_receivers_type_before_its_call` names each
case. A lambda applied where it stands has its parameter
related to the argument before its body is emitted, as a `let` binds its value, and a
comprehension's generator is one: its element reads each binder's type from the source. The receiver
is the argument, or the first component of its tuple type when the call passes arguments. That type
names a nominal head, directly or through the bounds its variable has gathered, or the call is an
error asking for an annotation on the receiver: no later use decides it (`docs/chl-spec.md`,
"Associated functions and methods"). The first candidate of the head's declaration whose binding
is in scope at the call replaces the placeholder (`Typing::binds`), and the application is emitted
as any call of a `def`. Every copy of a type's method is one function, since an associated function
reaches nothing a run gives its module, so a run's copy and a shared import's are interchangeable.
With none in scope, the first candidate lowering found is chosen, and it is unbound there, as a
module function called above its `def` is. A copy linking added is never chosen out of scope. The
other candidates are dropped without being emitted, so one whose `def` stands later in the module
than the call reports nothing. Each candidate records the
parameters its method declares after `self`, and a call passing another number of arguments is an
error naming the method and both counts. A head with no candidate is an error naming the type and
the method, and a type that is not nominal is an error saying it has no methods. No `Method` node
survives inference. A method no type declares is a lowering error pointing at `(r.f)(…)`, the call
of a field's function, and a position, `t.0(…)`, names no method.

### The compiler-provided `Option`

`Option(T)` is a `NominalDecl` the compiler provides (`nominal::option`) at the path `std::Option`,
with the constructors `none` and `some(T)`, the method `is_none`, and no source. Its constructor
names are the tags the runtime builds when it answers a checked lookup (`V_NONE`, `V_SOME`), so a
lookup's answer is a value of it. `LoweringContext::nominal_type` answers it for the name `Option`
after the module's own declarations, and `Type::option_of` builds an application of it.

A member of `Option` is bound only where the module names it: a reference records it
(`member_reference`), and `bind_constructors` binds the recorded ones, `is_none` as
`λ 𝑜 : Option(𝑇) → match 𝑜 { Option::some(_) → false; Option::none → true }` (`bind_is_none`). A
method call names every type that declares its method, because inference picks the candidate
from the receiver's type, so any `.is_none()` call binds `Option::is_none`, even one whose
receiver is a type declaring its own `is_none`. A module that names no member lowers as it would
without the declaration. Its
identity is its path, so every compilation, and every version of a reloaded program, names the
same type. Its spans are empty, and lowering refuses the programs that would point a diagnostic at
one: a declaration named `Option`, and an associated function of it.

---

## Inference

### The constructor rule

`emit_nominal_ctor` types a constructor `N::c(𝑒)` as `N(𝛼…)`, one fresh variable per type
parameter, and constrains `𝑒` below the constructor's payload at `𝛼…`. The payload is compared
with its refinements stripped. The node is only ever the body of the constructor's function, whose
parameter annotation already discharged them, or a constructor without parameters, whose payload
is `unit`; the declaration's own predicates were never typed.

### The constructor-pattern rule

`emit_case` hands a `Case` whose heads are constructors to `emit_nominal_scrutinee`. The
scrutinee is constrained below the declaration at fresh arguments, and each arm's binder takes its
constructor's payload at those arguments. The payload keeps the declaration's refinements, typed
as an annotation's predicates are: every value of the type was built by a constructor, whose
function discharged them. So `Price::new(c) = p` gives `c` the type `{Int where _ >= 0}` for
`type Price = {Int where _ >= 0}`. A refinement that reads a `const` parameter is left out
(`NominalCtor::destructured`): the declaration's copy of it names the parameter as the module
spells it, which only the constructor's function, bound where the name is in scope, resolves.

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

A nominal type offers its declaration as its head (`traits::offered`), which only a declared
instance accepts ([type-inference.md, "What the tables hold"](type-inference.md#what-the-tables-hold)).
Arithmetic on a nominal value calls its instance's function, and a comparison compares by value
([type-inference.md, "An operator's instance"](type-inference.md#an-operators-instance)); without
an instance, the operator is rejected where it is applied.

An instance of `Equatable` or `Orderable` has no block. Lowering checks that it names one nominal
type twice and that every constructor's argument compares by value under its `requires` clause
(`compares_by_value`), and, for `Orderable`, that the type has one constructor whose argument has
a written order. The instance goes in the program's `InstanceTable` with the others, which every
check after inference reads.

Lowering declares a module's traits after its types and before their associated functions, and
its instances after those (`lower::traits`). An instance's `def`s lower where its `impl` stands,
each completed from the trait's signature at the instance's types: a missing annotation becomes the
trait's type there, and one the `def` writes is compared with it. Each body reads the
requirements the trait's clause names, at the instance's types, and those the block's clause names
(`lower_instance_def`). The block's functions are a `DefGroup`, bound so that each follows the ones
of its instance it calls ([type-inference.md, "Trait functions"](type-inference.md#trait-functions)).

---

## After inference

A nominal type is concrete, and stays in every type slot to operator conversion. A nominal value is
opaque to the passes after inference: it has no fields, and no operator trait accepts it, so it is
never a key, a domain, or an operator's operand, and those passes move it without reading its shape. The
shape is read where a value is built or taken apart, through `Type::structure`, which answers a
nominal type's **representation** and every other type itself:

- `lambda_elim`, where a constructor becomes `variant_wrap` and a `Case` becomes
  `variant_project`. A nominal scrutinee's projections take the nominal type itself as their
  domain (`arms_variant`), since the arms name constructors of that type.
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
- An associated function with a `Mut` parameter. Lowering refuses it at the parameter.
- A refinement in a constructor's parameter type that names a binding other than a constant, or a
  constant whose value is a tuple, a record or a list, which a predicate does not hold yet. Lowering
  refuses it at the parameter type. A `const` parameter's value is known only once an import or a
  run gives it, so linking refuses a run that gives a tuple, a record or a list to one such a
  refinement reads
  ([modules.md, "Linking"](../../../docs/modules.md#linking)).
