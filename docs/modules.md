# Modules

> **Status: [Sketched].** A proposed implementation. The [Implementation
> stack](#implementation-stack) lists the work that remains.
> [Dependencies](#dependencies) lists the features outside modules it assumes, and [Open
> questions](#open-questions) what it leaves undecided.

The language rules for modules are [chl-spec.md, "9. Modules"](chl-spec.md#9-modules):
imports, runs, parameters, visibility, qualified references, Module types, shared imports, and how a
reload treats runs. This document is how the compiler implements them, and uses that section's
vocabulary ([chl-spec.md, "9.1 Vocabulary"](chl-spec.md#91-vocabulary)).

Every module the root reaches is linked into one CCL tree before inference. Inference, planning, and
the runtime see no module boundaries, as [docs/design.md, "What the architecture
buys"](design.md#what-the-architecture-buys) requires. Each module is also checked on its own, so a
library builds without any module that uses it.

Namespacing lives in the structured `Name` ([src/ccl/design/ir.md, "Structured names and
α-uniquification (Barendregt
convention)"](../src/ccl/design/ir.md#structured-names-and-α-uniquification-barendregt-convention)).
A top-level binder carries the run it belongs to. Identity is still the `uid`.

Backwards compatibility is not a constraint. Programs, goldens, and hot-reload state keys all
change.

---

## Members are resolved statically

`n::f` lowers to a reference to the binder of `n`'s member `f`, not to a projection of a record.
Two properties depend on that:

- **Let-polymorphism.** Inference generalizes only `let`-bound function definitions
  ([src/ccl/design/type-inference.md, "Levels, Schemes, and
  Let-Polymorphism"](../src/ccl/design/type-inference.md#levels-schemes-and-let-polymorphism)), so
  `n::id(1)` and `n::id("a")` in one tree require a direct reference to the generalized binder.
- **Type members.** A type alias is erased at lowering and is not a value. `n::T` is resolved
  against the module interface in type position, or against the parameter's Module type when `n`
  is a parameter.

A Module-typed parameter names exactly one shared import or run in each copy of its module. It
lowers to a `let` per entry, `audit::events`, and creating a copy of its module binds each to the
member of the shared import or run passed, at the type the Module type gives it ([A Module type is
not a `Type`](#a-module-type-is-not-a-type)). Specialization and planning see the member, and
checking against the Module type costs one `let`.

## Pipeline

```
root file
  → load     parse the root; follow its imports and runs to files; parse each once, with its own
             FileId
  → graph    build the module graph; refuse cycles; compute link order
  → lower    once per module, in link order, against the interfaces of the modules it imports and
             runs, each import's shared import decided before its importer lowers. Produces a chain,
             with each `run` statement a `Run` node, and an interface
  → link     create each shared import, one per imported module and distinct set of arguments, in
             link order, and the root's run, which creates each run it declares at its `run`
             statement; each run a uniquified copy of its module's chain
  → check    once per module: its check tree, its chain with its parameters abstract, its runs,
             the shared imports it reaches, and its arguments' checks, inferred alone, as
             chl-spec.md's "9.14 Checking a module on its own" requires; once every module is
             checked, an import of a module that is run, or a run of one that is imported, is
             refused
  → infer …  over the linked tree, once every check passes: specialization and refinement
             propagation
```

Each run is a copy of its module's chain, uniquified alone, so every binder of the copy is its own
([A module lowers once](#a-module-lowers-once)). Uniquifying a run uses the property `uniquify`
already has for lowering's pre-cloned subtrees ([`src/ccl/uniquify.rs`](../src/ccl/uniquify.rs),
"Mint before copy"): the runs already created inside it stay settled.

Errors in one file do not stop loading or lowering the others, and every module's errors are
reported together. A lowering error stops the compile before any module is checked.

## Loading

Loading is the `load` and `graph` steps, and runs before compilation. `LoadedProgram::load`
([`src/ccl/load/`](../src/ccl/load/mod.rs)) produces the `SourceMap` of every file the root reaches,
each file's parse, the module graph, and the link order. Every compile entry point takes the
`LoadedProgram`, so compilation reads no file.

- **Edges.** The module graph's edges are the top-level `import` and `run` statements, bare or under
  `pub`. Lowering refuses a nested one, and it names no module.
- **Resolution.** Each module path is resolved once. A path beginning with `std` resolves against
  the std root, which has no modules until the std root item of the
  [Implementation stack](#implementation-stack). Any other path resolves through a `ModuleFiles`:
  `DiskFiles` reads under the root file's directory, and `InMemory` holds text keyed by module path.
- **Disk.** `DiskFiles` matches the root file's name and each component of `a/b/c.cambra` against
  its directory's entries, so a file whose name differs only in case is not the root or the module
  on any file system. A file it already read for another module path, compared by canonical path, is
  refused.
- **The root.** The root's module path is its file name without `.cambra`. A module naming that path
  reaches the root's own file, so the cycle is reported rather than the root read twice. A root
  built by `LoadedProgram::from_text` has no module path, and no statement can name it.
- **Missing modules.** Each statement naming a module with no file is an error at its module path.
  The message says why: no file, a file differing in case, a file another module path already
  reached, or a failed read.
- **Files with no tree.** `parse_module` returns no tree for a file when its grammar fails where
  recovery does not apply, and loading follows none of that file's statements.
- **Cycles.** Each strongly connected component with a cycle is one error. It names the shortest
  cycle through the component's least module path, with a label at each statement in it. The link
  order exists only for an acyclic graph.
- **Compilation.** Loading's errors come first: every file's parse errors, then missing modules and
  cycles.

## Lowering

### A module lowers once

Every module lowers once, in link order, so the modules it imports and runs lower before it
(`ProgramLowering::lower`). Lowering produces:

- **A chain**: the module's top-level statements around `MODULE_BODY`, not uniquified. A binder is
  a raw name. A reference to another module's member is a raw name spelled through its qualifier,
  `m::f`. A `run` statement is a `Run` node over the rest of the module, holding the run name, the
  module it runs, and its statement ([ir.md, "`Run` — a `run` statement before
  linking"](../src/ccl/design/ir.md#run--a-run-statement-before-linking)).
- **An interface** ([The module interface](#the-module-interface)).
- **The sinks the module declares**, which a run of it registers.

Lowering errors are reported once per module, however many runs it has.

Linking creates each run from its module's lowering (`ProgramLowering::create`):

1. **Copy** the chain. `Clone` mints fresh node ids and records each copy for provenance.
2. **Create each run it declares**, at its `Run` node, and put its chain there around the rest of
   the module (`ProgramLowering::expand_runs`).
3. **Uniquify** the copy with the run's home, in a scope that maps each spelling through a
   qualifier to the binder of the run the qualifier reaches: `m::f` to the shared import's member,
   `eu::f` to the member of the run `eu` created in step 2. Each `use` name of an import maps to its
   member's binder.
4. **Register** the sinks the module declares, keyed by the run path.

A created run's names are every spelling its top level resolves: its spine's binders by spelling,
and its scope's entries. A module reaching the run spells each through its qualifier for it, which
is how a type alias's predicate reaches a private member or another module's member
([Imported aliases are closed over their
module](#imported-aliases-are-closed-over-their-module)).

The root lowers last and has one run, with no home. Its run registers its sinks and reads every
program sink at its tail (`finish_program`) before it is uniquified, once the runs it declares are
in place.

### Names carry their home

A reference to another module's member needs no name of its own kind. It lowers to a raw name
spelled through its qualifier, `m::f` or `eu::f`, and creating the run it stands in resolves that
spelling to the binder of the run the qualifier reaches ([A module lowers
once](#a-module-lowers-once)). Through a Module-typed parameter it is the `let` the parameter binds,
`audit::f` ([A Module type is not a `Type`](#a-module-type-is-not-a-type)).

Lowering and linking hold a name spelled through qualifiers as its segments (`QualifiedName`), and
join them with `::` only in the raw name a reference lowers to and in the scope a run is uniquified
in (`raw_scope`).

One change to `Name` (`src/ccl/names.rs`): **`Name::Unique { base, uid, home }`**, where `home` is
the run a member belongs to: `Import(SharedImport)` for a shared import's member, its module path
and its arguments, `Run(run_path)` for a member of a run a `run` statement declares, and absent for
a local. Identity remains the `uid`.
`home` is metadata of the kind `base` already is. It is implemented as `home: Option<Arc<Home>>`.
`uniquify::run_in` mints a run's top-level binders with it, and every other binder, the root's
members included, without one. A pass that re-mints a copy of a binder keeps its home
(`Name::fresh_like`).

Module paths and run paths are shared behind an `Arc`: cloning one copies a pointer, and `Display`
renders it without a lookup table. Neither uses a per-compilation counter. They appear in state keys
and record labels, and a counter would give two compilations of one root different labels, the
defect [`Name::field_key`](../src/ccl/names.rs) documents.

Rendering: symbolic IR output prints a member as `home::base`, `catalog::price`,
`scaled(scale=3)::by`, or `eu::stock`, and a local as `base`. A diagnostic qualifies an imported
module's or a run's members the same way, in that module's own diagnostics too: a diagnostic's text,
types included, is formatted during inference, before the error has a location.

`home` widens `Unique`, and `PiRef` boxes its hint to keep `Name` at the width `Unique` needs.

`Name::Raw` is unchanged. A raw name is written in one module, and resolves within the run of it
being created, through that run's scope when it is spelled through a qualifier.

A record label and a variant tag in `ccl::Type` and in a term are a `Label`, which carries the
module path it belongs to
([chl-spec.md, "9.12 Field labels and tags belong to a module"](chl-spec.md#912-field-labels-and-tags-belong-to-a-module)).
Two labels are one label when both spelling and module agree. The root's labels have no module
path and render bare. Another module's label renders `module::label`, which is also its spelling at
run time. A run's top-level mutable variable is labeled in its run (`Name::field_key`), so two runs
of one module keep separate store fields. Its label renders `eu::stock`, as the member reads, and
its run-time spelling is `@eu::stock`, which no module's label has.

A nominal type's constructor is not a label. The value it builds carries a tag of the root's
namespace spelled as the constructor, so `Option::some` builds the same value in every module, and
a user's `` `some `` builds that module's own tag.

### Imports

- **An imported module has a shared import per distinct set of arguments its imports pass**, created
  from its lowering in link order and linked around the root ([A module lowers
  once](#a-module-lowers-once)).
- **An interface records declarations.** `Interface` (`src/ccl/lower/modules/interface.rs`) records each
  top-level binding's visibility, declaration, and call shape, and each top-level type alias's type
  as its module lowered it. `m::f` lowers to the raw name `m::f`, and `m::T` to the alias's type
  spelled through `m` ([Imported aliases are closed over their
  module](#imported-aliases-are-closed-over-their-module)). A private member is an error with a
  label at its declaration, and a missing one is an error.
- **`use`.** A `use` item reaches its member as `m::f` or `m::T` does. A value's name resolves
  through the scope each run of the module is uniquified in, and a type's is an alias in scope
  throughout the module ([`use` names are environment entries, not
  bindings](#use-names-are-environment-entries-not-bindings)). A member spelled like a `use` name is
  an error, and so is a `use` name spelled like an import name, another `use` name, a builtin, or a
  built-in type. A builtin call resolves by its spelling before scope (`lower_call`), so a `use`
  name spelled like one would never reach its member.
- **What an import may hold.** Lowering refuses no statement of an imported module: a shared
  import performs its module's whole top level, as a run does, loops and induction variables
  included. Whether the module may be imported at all is decided once every module is checked,
  from what its top level requires and causes ([Checking a module on its own](#checking-a-module-on-its-own)).
  Lowering declares a sink without opening anything, so creating a shared import of a module that
  binds one is harmless; its import is refused before the program runs.
- **State.** A shared import's top-level induction variable is labeled in the shared import
  (`Label::in_import`), so each shared import keeps its own history, as each run does. A store keys
  a variable by the label's run-time key, `@@scaled(scale=3)::total`, which a store resumed by
  another version reads back, and a type argument's only identity across compilations is its
  spelling, so the label is the shared import's spelling. Two shared imports of a module that
  declares state whose type arguments are distinct types spelled alike are refused at the second
  `import` (`ProgramLowering::shared_import`).
- **`Mut` parameters.** A call to an imported `def` with a `Mut` parameter, qualified or through
  `use`, takes the curried shape the `def` lowers to.
- **Labels.** An unqualified label belongs to the module that writes it, `this::` spells the same
  label, and `m::` qualifies the label of the module `m` names. A nominal type's constructor is not
  a label, so `Option::some` is the same in every module
  ([Names carry their home](#names-carry-their-home)).
- **Arguments.** Each import's shared import is decided by what it writes, once the modules its
  importer imports have lowered and before the importer does (`ProgramLowering::import_keys`): its
  module and its arguments, `Home::Import`'s `SharedImport`. Each import qualifier records the
  shared import it reaches and the types that gives its module's type parameters. A shared import is
  created for the first statement that reaches it. Two sets are compared as written ([Link-time
  constants](#dependencies)). An argument is a literal, a type, or an import name; anything else is
  an error at the argument ([Dependencies](#dependencies)). An import name's shared import is part
  of the key, `shop(counter=counter)`, and is created first
  (`ProgramLowering::ensure_shared_import`). Each literal is bound at the head of the shared
  import's chain, at its parameter's type, and a parameter with neither an argument nor a default is
  an error at the `import`.
- **Type arguments.** A type argument is lowered against the importer's other imports, so the
  importer's imports are decided in rounds: one waits until the imports whose names its arguments
  write are decided. Its key is the type made canonical, each record's fields and each sum's arms in
  label order (`Type::canonical`), so `holder(T={a: Int, b: String})` and
  `holder(T={b: String, a: Int})` are one key. Keys are interned per compilation (`TypeKeys`) and
  ordered by their spelling, so the order of a module's shared imports does not depend on statement
  order. A type argument is built from built-in types and imported type
  members: one naming a type the importer declares, or with a refinement that reads a value, is an
  error at the argument. This restriction is temporary: link-time constants lift it ([Link-time
  constants](#dependencies)). The module's copy for the import takes each type argument as a run's
  copy does ([Runs](#runs)).

### Runs

- **A run is created from its module's lowering.** A `run` statement lowers to a `Run` node over
  the rest of the declaring module (`LoweringContext::take_run`), and creating the declaring
  module's run creates this one at the run path `n`, or `eu::n` for a run the run `eu` declares, and
  puts its chain there (`ProgramLowering::expand_runs`). Its members' home is `Home::Run`.
- **A run stands at its statement.** A reference to the run name above the statement is refused,
  and each value a run's `use` clause binds is a `let` at the statement of the raw name `n::f`, so
  both are in scope from the statement down ([chl-spec.md, "9.3 Runs"](chl-spec.md#93-runs)). A
  reference to such a value that no binder of the module's chain binds stands above the statement,
  and is refused there (`LoweringContext::uses_above_their_runs`).
- **A run performs its module's whole top level**: its state, loops, sources, and sinks. Lowering
  declares a sink (`LoweringContext::declared_sinks`), and creating a run registers it keyed by the
  run path, `eu::out` (`LoweringContext::register_sinks`). The program's tail reads it through the
  binder the run's chain minted (`LoweringContext::run_sink_names`). A run's mutable variables are
  labeled by run path in history records, so two runs keep two histories.
- **A run's feed is fed through its run name.** `a::events << e` feeds the run's public feed, as
  `events << e` does inside it: a feed's target may be qualified (`feed_target`). Declaring a
  public feed makes its module a run, so no import name reaches a feed.
- **Routes are unique across runs.** Creating a run registers its routes. A route two runs serve is
  an error at the second `run` statement, with a note at the first. A route's address is a
  constant, so a module takes it from a `const` parameter and each run serves the address its
  arguments give. A route whose address reads a parameter names its requests' source by its
  statement in the module's chain, and creating a run renames the run's copy to the source of
  the address the run gives (`sinks_at`, `HttpRoute::at`). A module's check keeps the
  statement's name, which a source that opens nothing answers to.
- **A parameter is a `let` at the head of its module's chain**, of its default, or of an `Abstract`
  when it has none ([ir.md, "`Abstract` — a value known only by its
  type"](../src/ccl/design/ir.md#abstract--a-value-known-only-by-its-type)). The interface records
  each parameter's annotation and whether it has a default.
  A `run` statement binds each argument above its `Run` node under `argument_name`'s
  double-underscore name, `__run::eu::port`, at the parameter's annotated type spelled through the
  run name, so a mismatch is reported at the argument. Creating the run points each parameter with
  an argument at that name, and refuses one with neither an argument nor a default at the `run`
  statement. A parameter annotated with `_` takes the type its module's check infers, so a bad
  argument for one is reported at the argument too ([Checking a module on its
  own](#checking-a-module-on-its-own)). A value parameter without an annotation is refused
  (`refuse_module_syntax`). The root takes every parameter's default, and a parameter without one
  is an error there.
- **A `const` parameter takes a constant.** `declare_run_types` reads each `const` argument of a
  `run` statement as a term over the declaring module's `const` parameters
  (`LoweringContext::run_consts`, `src/ccl/lower/constants.rs`), refusing one that is not a
  constant. The run name's qualifier records the terms, so a type reached through it is the
  instance they give, and the `Run` node holds them. Creating the run substitutes the creating
  run's values into them, and gives each parameter its term, its import's literal, or its default
  over the parameters above it (`ProgramLowering::create`). The term reduces to a value once every
  parameter it reads has one, which is what a type's identity compares, so runs given `5` and
  `2 + 3` reach one type. A module's own check gives its parameters no values, so there a term
  over them compares as written.
- **A top-level `=` binding is a constant when its definition is one.** Before the module's
  statements lower, `settle_constants` reads each binding's definition as a term, caching the term
  or why the definition is not one, and reports nothing. A read that requires a constant reports
  the cached reason at the read (`Refused::of_definition`), and the interface records each public
  binding's result, so an importer's read reports the same reason.
- **A `def` whose body is a constant over its parameters may be called in a constant.**
  `settle_constants` reads each `def` too (`LoweringContext::const_function`): its parameters are
  `ConstParam`s, its local `=` bindings and its value are terms over them, and it states no clause
  and takes no `Mut` parameter. A call in a constant substitutes its arguments' terms into the
  function's (`ConstFunction::applied`), so `plus(4)` and `5` reach one type. A call of a function
  that may not be called reports the cached reason at the call (`Refused::of_function`), and the
  interface records each public `def`'s result, read through `m::f` or a `use` name with the
  importer's `const` arguments substituted.
- **A type parameter is an alias of a declared `Type::Param`** from its statement down, as a `def`'s
  is, and binds no `let` (`LoweringContext::declare_type_parameter`). The interface records its
  bound and its default. A `run` statement's type arguments are lowered ahead of the module's
  statements, with its type aliases, where the statement stands
  (`LoweringContext::declare_run_types`). The run name's qualifier records the types they give, so
  `n::Pair` and a `use` type name of the run take them, and so does each value argument's
  annotation. The `Run` node holds the type arguments. Creating the run substitutes each default
  before the run is uniquified, since a default is the run's own type, and each argument after.
  Linking puts a `let type` of each argument, `__run::n::T`, where the `Run` node stood, so the
  declaring module's uniquification resolves the argument's refinements where they are written, and
  the run's copy shares the resolved predicates. In a run's copy, a use of `T` is checked against
  the argument. The module's own check holds `T` opaque apart from its bound, and the declaring
  module's check compares each argument with that bound ([Checking a module on its
  own](#checking-a-module-on-its-own)).
- **`pub` on a `run` is a parse error**, since a module returns a run by binding it to a public
  member ([A Module type is not a `Type`](#a-module-type-is-not-a-type)).

### The module interface

Lowering records each module's `Interface` (`Interface::of_lowered`): each parameter, and each
top-level member, public and private, so that `m::hidden` can say the member is private and point at it:

| Member | Recorded |
| --- | --- |
| value, `def`, mutable variable, feed | its visibility, its statement, and for a `def` whether it takes a `Mut` parameter |
| type alias | its visibility, its statement, and its type as its module lowered it |
| nominal type | its declaration, visibility and statement, and each associated function's visibility, statement and arity, and whether it is a method (`NominalMember`) |
| member bound to a module, `pub audit = a` | its visibility, its statement, and the module it is bound to, as its module spells it |
| parameter | its annotation, Module type, or bound, and whether it has a default |

The interface holds no contract. A module's check infers its members' contracts (`check_module`),
and `cambra check` prints them with the interface (`Interface::written`).

A `def` with a `Mut(…)` or `Feed(…)` parameter lowers as a curried chain, and its call sites
must match (`LoweringContext::history_param_fns`). The interface carries that shape so a user's call site lowers
correctly: a qualified callee reads it from the member, and a `use` name of such a `def` is
registered in `history_param_fns` when its module begins lowering.

Each module is lowered with fresh block state. Every spelling-keyed map in `LoweringContext`
(`transactional_vars`, `type_aliases`, `history_param_fns`, `shadow_depth`, `nominal_types`,
`associated_functions`, `used_nominal`) covers one module. The
entries a module seeds from interfaces and from its parameters' Module types, `Txn` members in
`transactional_vars` and `Mut`- and `Feed`-parameter functions in `history_param_fns`, are keyed
by qualified spelling. The `MutWrite` shape a `:=` to one lowers to then applies to `eu::stock` and
`audit::stock` exactly as it applies to `stock` inside its own module.

A module whose own errors stop it from lowering has no interface, and a reference or a `use` item
into it adds no error: that module's own errors account for it.

### Imported aliases are closed over their module

An alias's predicate names resolve where the alias is declared, at its `LetType`
([ir.md, "Type aliases resolve where they are
declared"](../src/ccl/design/ir.md#type-aliases-resolve-where-they-are-declared)). The interface
holds each top-level alias as its module lowered it, so its predicates read raw names spelled as
that module spells them. `m::T` lowers to the alias's type with each raw name its predicates read
free spelled through `m`, `limit` as `m::limit` (`reroot`). Creating the importer's run resolves
`m::limit` to the binder in `m`'s run, so no binder of the importer can capture it. A run's names
include the names its own scope resolves, so a predicate reading another module's member,
`stock::cap`, is reached as `m::stock::cap`.

A top-level alias's predicate sees only the module's members and the prelude, so every name it
reads is a binder of its module. Visibility does not apply to those names ([chl-spec.md, "9.13
Private-in-public"](chl-spec.md#913-private-in-public)), and a private one renders qualified, as
`inventory::catalog` ([Names carry their home](#names-carry-their-home)).

### Nominal types across modules

Every module declares its nominal types before its statements lower, as the root does
(`declare_top_level_types`): their heads, then its type aliases, then their constructors and
associated functions. Its constructor functions are bound around its chain (`bind_constructors`),
and an `impl` block's `DefGroup` stands on its spine, so a copy's names include the type's functions
and a `run` below the block is created. A declaration's path is its module's
(`NominalDecl::module`), and the root's is empty.

A name whose last qualifier segment is a type, `Shape::circle` or `shop::Shape::circle`, names a
member of that type (`nominal::resolve_type`). The type is one the module declares, one a `use` name
of the module names (`LoweringContext::used_nominal`), or a public one of the module the qualifier
names (`Qualifier::reach_nominal`), which reports a private one. Another module's member reads the
binding its module's chain binds, spelled through the qualifier, `shop::Shape::circle`, which
creating the copy resolves as it resolves any qualified member. `shop::Shape` and `shop::Box(Int)`
in a type position name the type the same way (`qualified_nominal`). A public nominal type that
takes no type arguments is a type member as an alias is, so it fills a Module type's type member
(`Qualifier::reach_type`, `Interface::missing`). A method call's candidates add
each public method of each public type a qualifier of the module reaches, an import's qualifier
before a run's, since a run's name is in scope only below its statement (`foreign_methods`).
Linking records each copy of each public method that a run or a shared import holds
(`ProgramLowering::method_copies`), with its type as the instance that copy's arguments reach. A
copy recorded inside a run takes the arguments of each run around it too, since a run's type
argument may name a parameter of the module that declares it. Linking adds the copies of a call's
method to its candidates once the program, or a module's check tree, is assembled
(`add_method_copies`). Inference takes a copy only where its binding is in scope, so a
call reaches the method of a value whose type comes from a module the calling module neither
imports nor runs: the value comes from a run or a shared import that encloses the call, whose copy
is in scope there.

A type's identity takes the module's type parameters and `const` parameters it reaches
([chl-spec.md, "Nominal type identity"](chl-spec.md#nominal-type-identity)). Once the module lowers,
`settle_implicit` records them on the declaration (`NominalDecl::implicit`,
`NominalDecl::implicit_consts`): those its constructors' parameter types name, those its associated
functions reach, and those of every type of the module it names, transitively. A function reaches
the parameters the types of its definition name, those of each top-level binding and function it
reads, and each `const` parameter it reads, all of which `associated_reach` follows
(`AssociatedReach`). A module's type parameters are its `param T`s and the abstract type members of
its Module-typed parameters. Equality and hashing compare the implicit arguments with the path and
the name. The module's own code names the declaration with each parameter standing for itself.
`substitute` and `substitute_in` turn it into the instance an import's or a run's type arguments
and `const` terms reach (`NominalDecl::substituted`, `NominalDecl::substituted_consts`), in a type
and in the nodes that hold a declaration outside a type slot: a `NominalCtor`, a constructor pattern
and a method candidate. Both kinds of argument ride one `Arguments` map, so every site that
substitutes an import's or a run's types substitutes its constants. A type reached through a
qualifier is the instance that qualifier's arguments reach (`Qualifier::instance`). The instance
shares the declaration's body, and `instantiate` replaces its implicit parameters with its
arguments in a constructor's payload, so a type of the module that the payload names, `Order`'s
`Amount`, is the instance of the same arguments. A diagnostic writes the arguments on the module,
as an import or a run passes them, `shop(Receipt=stripe::Receipt)::Order` or
`shop(max_rate=5)::Capped` (`NominalDecl::spelled`).

The copies of a type's associated functions are one function only if they reach nothing an import or
a run gives their module but what the type's identity records. `associated_reach` checks that on a
uniquified copy of the module's chain, so a reference reads the binder it resolves to. It follows
each top-level binding and function an associated function reads, and refuses one that reaches a
mutable variable, a feed, a source, a value parameter without `const`, a value member of a
Module-typed parameter, or a member of a run the module declares, naming the path it reaches it
through. Each type parameter and `const` parameter it reaches joins the type's identity.

`cambra check` prints each public type as its module declares it, with each type parameter's
variance and the module's type parameters whose arguments tell its instances apart, and each
public associated function with its contract (`NominalMember::written`). A contract writes the
module's own nominal types by name and another module's qualified by it (`chl_type_in`).

### A Module type is not a `Type`

A Module type is a `ModuleType` (`src/ccl/module_type.rs`), its entries in the order written, and
not a `Type`: no value has one ([chl-spec.md, "9.8 Module types"](chl-spec.md#98-module-types)).
What a type alias names is an `AliasType`, a `Type` or a `ModuleType`, and a `LetType` holds one,
so an alias of a Module type is declared, exported, and closed over its module as any alias is
([Imported aliases are closed over their module](#imported-aliases-are-closed-over-their-module)).
A Module type is written as a parameter's annotation, an alias's right-hand side, or an entry of
another Module type (`lower_alias_type`). Anywhere else it is an error, as is a Module type's alias
named as a value's type.

A name denotes a module when it is an import name, a run name, a parameter annotated with a Module
type, a top-level member bound to a module, `pub audit = a`, or a `use` name of a member bound to one.
Each is a `Qualifier`, and so is a path through public members bound to a module, `shop::audit`.
A qualifier spells a member reached through it as the module it names is spelled: a binding
`k = c` spells `k::f` as `c::f`, and through an interface `h::k::f` is `h::c::f`
(`ModuleBinding::name`). Creating a run then resolves those spellings as any other, and a
binding needs no names of its own.

A Module-typed parameter lowers once, before any argument exists
(`LoweringContext::declare_module_parameter`). Its Module type gives it a view (`ModuleView`) and
a `let` per value entry at the head of its module's chain, `audit::count`, at the entry's type. A
reference through it resolves to that `let`, so the module sees the entry's type, and a member the
Module type does not name is an error at the reference. A binding of the parameter, or of a path
through it, reaches what the parameter does. A module entry reaches its members through its own
Module type, with its values' `let`s spelled under it, `shop::audit::events`.

A `run` statement passing a module to a Module-typed parameter checks, while the declaring module
lowers, that the module has every member the Module type names, public (`uncovered`). Passing a
parameter on checks the next run's Module type against the parameter's view. A parameter annotated
with a Module type must be passed a module, and a module must be passed to one. Creating the run
binds each entry's `let` to the argument's member, imaged at the argument, so a member whose type
does not fit is the argument's error (`ProgramLowering::bind_module_parameter`). An argument whose
module has errors of its own binds nothing and adds no error, as a reference into it adds none. The
argument's members are those of the run or shared import it names, or, for a parameter passed on,
those of that parameter's argument (`module_names`). A default names an import, checked while the
module lowers and taken by a run that passes no argument.

A polymorphic entry's `let` carries its polymorphic type, as a `def` with type parameters does. A
feed entry, `Feed(T)`, is a feed handle with its domain left to inference, and `audit::events << e`
feeds the argument's feed through the `let`. A binding exported in an interface carries its
spelling and its view, so a module reaching `h::k` reaches what `k` does in `h`.

A type member of a Module type is a `TypeEntry`, an alias for the entries after it. An exact one,
`Name = T`, is `T`. An abstract one, `Name <: T` or `Name: K`, is a declared `Type::Param`, and
each Module-typed parameter takes the Module type with a fresh one for each, so two parameters of
one Module type take two arguments (`instantiate`). Inside the module `audit::Event` is what the
entry writes. Linking passes each abstract member as a run's type argument under its spelling,
`__run::s::audit::Event`: the declaring module reads the argument's member where the `run`
statement stands (`LoweringContext::declare_run_types`), an import reads it where its key is
decided, and a default reads it where the parameter is declared. The declaring module's check
compares the argument's member with an exact entry's type or an abstract entry's bound ([Checking a
module on its own](#checking-a-module-on-its-own)). A Module-typed parameter
that a `run` statement passes to another run is declared in the pass that lowers the run's type
arguments, so one declared below the statement is an error at it.

### `use` names are environment entries, not bindings

`import n use f` in module `m` does not lower to a `let`. Each run of `m` is uniquified with `f`
mapped to the binder of `n`'s member `f` in `n`'s shared import, beneath every binder of the tree
(`uniquify::run_in`). An unshadowed use of `f` resolves to that binder, and a local `f` shadows it
by ordinary lexical scope. The scope has no position, so a `use` name is in scope throughout its
module, above its `import` too. A `use` clause on a run binds `f` instead with a `let` of `r::f` at
the `run` statement ([Runs](#runs)).

A `let f = n::f` would lose polymorphism. Its right-hand side is a variable, not a lambda, so
inference does not generalize it (`should_generalize`, [type-inference.md, "3.1 Let-Polymorphism is
Freshening
(Instantiation)"](../src/ccl/design/type-inference.md#31-let-polymorphism-is-freshening-instantiation)).

`import n use T` for a type alias declares `T` in `m`'s `type_aliases` with `n`'s type spelled
through `n`, in scope throughout `m` (`LoweringContext::begin_module`).

### Intrinsics resolve by identity

The std root ([chl-spec.md, "9.16 The std root"](chl-spec.md#916-the-std-root)) is CHL source
embedded in the binary. A std file has a `FileId` and a path like any other, `<std>/http.cambra` for
`std::http`, so an error inside it renders against its source. The `http` status helpers are
ordinary CHL functions there.

A std module may bind an intrinsic, meaning a builtin source, sink constructor, or special form. The
interface records the member as that intrinsic. Lowering recognizes a special form by what the
callee resolves to: `reqs, resps = http::serve(…)` is the `http_serve` tuple form because
`http::serve` resolves to the intrinsic.

An address argument of `http::serve` is a constant, as of `http_serve`. Route uniqueness across
runs is checked as linking creates each run ([Runs](#runs)), since two runs of one module may serve
one address.

### Registries keyed by spelling

Four registries are keyed by a spelling that is unique within one file and not across modules and
runs, and each takes the member's qualified spelling, `home::base`. Sink bindings and
history-record labels take it as each run is created (`LoweringContext::register_sinks`,
`Name::field_key`). State identity and the `@LoadFrom` spelling take it with hot reload
([Implementation stack](#implementation-stack)):

- **Sink bindings** (`LoweringContext::sink_bindings`), and so the linked tree's trailing-record
  field names and `CompiledOutput::name`. Two runs of one module each bind `resps`.
- **History-record labels** (`Name::field_key`). One transaction can write `eu::stock` and
  `us::stock`, and both keys land in one `Transact` history record. A user identifier cannot
  contain `::`, so a qualified label cannot collide with a local's.
- **State identity** (`VarPath`), in [Program evolution](#program-evolution).
- **The `@LoadFrom` loaded spelling**, which becomes a run path plus a spelling.

## Linking

The **link order** is a topological order of the module graph
([chl-spec.md, "9.11 The module graph"](chl-spec.md#911-the-module-graph)) in which each module follows
every module it has an edge to. Ties break by module path, lexicographically. The order is a
function of the graph alone: reordering statements in a file does not change it, and neither does
discovering modules in a different order.

The order does not affect meaning, since members of different modules never share a scope. It is
deterministic because two compilations of one root must produce one tree: program diffing compares
trees structurally ([src/ccl/design/diffing.md](../src/ccl/design/diffing.md)).

Linking puts one shared import per imported module and distinct set of arguments, in link order,
around the root, and each run at its `run` statement in the module that declares it
([Runs](#runs)). Each is created from its module's lowering, which happens once ([A module lowers
once](#a-module-lowers-once)). Each copy of a module after the first in a tree copies the
module's refinement predicates too (`copy_predicates`), since uniquifying rebuilds a predicate
with the ids it had, and two runs holding one predicate's ids would collide. The first keeps the
module's own, which its nominal types' declarations share, so a predicate inference reads off a
declaration is one the tree holds.

Once the tree is assembled, each `const` parameter of each copy is settled to the term its import or
run gives it (`settle_const_params`): a literal, or, in a module's check tree, a term over the
checked module's own `const` parameters. Each reference a predicate makes to the parameter reads
the term, each operation over literals this leaves is folded, and each ternary whose condition this
decides takes its arm. A refinement check compares terms, and a predicate that reached the argument
only through the parameter's `let` would compare an unknown. The `let` of a scalar parameter is
bound at the singleton of its term, `{Int | __elem == 𝑡}`, and holds the literal, or `Abstract` in
a check tree, so a read of the parameter meets a refinement over it. A module's check binds each of
its own `const` parameters through a binder spelled alike, of an `Abstract` value, just above the
parameter's `let` (`read_through_atom`): the parameter's predicates read that binder and its
singleton names it, since a `let`'s annotation lies outside the `let`'s own scope. A run that gives
a tuple, a record or a list to a `const` parameter a predicate reads is an error at
the run, since a predicate holds no such value yet (`compound_const_reads`).

**The per-module check runs parsing, lowering, uniquification, and inference** (`Phase::Lower`,
`Phase::Uniquify`, `Phase::Infer` in `src/ccl/context.rs`), plus the run-site checks of the
module's own `run` and `import` statements ([Checking a module on its
own](#checking-a-module-on-its-own)). Lowering's own refusals are part of it: the
mutation-statement rules, visibility, and a duplicate literal route within the module. So is a
`Txn` read or write that no `with begin():` block encloses, which inference refuses.

**Every later pass runs only on the linked tree**, because it needs the bodies of called functions
inlined or the run tree assembled:

| Pass | What it can refuse |
| --- | --- |
| inlining (`Phase::Inline`), then `check_transact_rejections` | the mutable-variable checks: a nested transaction, a block that writes only induction variables, an induction variable written under a branch in a block, a reference after `await_final` |
| the transaction phase (`Phase::Transact`) and `mut_elim` (`Phase::Letrec`) | recurrence shapes they do not support |
| channelization (`Phase::Channelize`) | a feed whose contributions do not route |
| the as-of-read rewrite, lambda elimination, planning | shapes the planner cannot emit dataflow for |
| route uniqueness | one `(port, method, path)` served by two runs |
| operator conversion (`Phase::Convert`) | a route or source the engine cannot open |

An error from a link-time pass is a real error, not a compiler defect, and names the run whose copy
failed ([Diagnostics](#diagnostics)).

Linking also runs inference over the whole tree once more, once every module's check has passed.
That run specializes and propagates refinements across modules. It can still refuse code inside a
module body where several modules' uses of one coupled member ([chl-spec.md, "9.14 Checking a
module on its own"](chl-spec.md#914-checking-a-module-on-its-own)) meet, as a monomorphic member two
importers settle does, or where a run's argument meets an unbounded type parameter.

## Checking a module on its own

Each module the root reaches is checked once, on its own, before the linked program is inferred
(`ProgramLowering::check`, `check_modules` in `src/ccl/context.rs`). Its check tree is the module
linked as though it were the root, with its own parameters abstract:

- **The module's chain**, copied. A value parameter, and each value entry of a Module-typed
  parameter, is a `let` of `Abstract` at its type, a value known only by its type
  ([ir.md, "`Abstract` — a value known only by its
  type"](../src/ccl/design/ir.md#abstract--a-value-known-only-by-its-type)). A feed entry is a `let`
  of `Defer`. A default with an annotation is checked against it.
- **Its type parameters** are opened for the whole check (`infer::check_module`). `T <: B`, and an
  abstract type member of a Module-typed parameter, is an opened parameter, opaque apart from its
  bound. A bare `T` is one inference variable at the module's level.
- **Its runs and imports** are created as linking creates them, bodies included, registering no
  sink or route. An exactly annotated member is bound at its annotation, so a use sees no body. An
  unannotated or `<:` member is inferred with the module's uses of it.
- **Its run-site checks.** Each type argument, and each type member of a module argument, is
  compared with what its parameter states, as the declaring module writes both (`TypeCheck`): an
  `Abstract` at the argument's type flows into a `let` at the bound, and for an exact entry the
  other way too. A run's checks stand below its `Run` node and an import's at the head of the
  module.
- **Its arguments for inferred parameters.** A module's check notes the type it infers for each of
  its value parameters annotated with `_` (`note_parameter_types` in `src/ccl/context.rs`), and the
  check of a module passing it an argument annotates the argument's `let` with that type
  (`annotate_arguments`, `ModuleCheck::arguments`), so a bad argument is reported at the argument.
  A type the uses leave open, or one that reads a refinement or a type parameter, is not noted, and
  such an argument is checked through the uses, as a coupled member is.

The root has a check of its own only when it has parameters or its runs and imports have checks or
pass arguments for inferred parameters. Otherwise the linked program's inference is its check.

A check also answers what the module's top level requires and causes, less what its scopes
discharge (`ModuleChecked::top_level`; [chl-spec.md, "Shareable modules
[Decided]"](chl-spec.md#shareable-modules-decided)). Once every module is checked,
`import_and_run_errors` in `src/ccl/context.rs` reads it for each module's `import` and `run`
statements (`ModuleCheck::statements`), and for the root's, which lowering keeps on the context
because the root usually has no check of its own (`LoweringContext::root_statements`). A module is
shareable when its top level requires and causes nothing, a sink it binds causing `Emit`, and it
runs no module.
`@LoadFrom` is outside the effects model, so a load bears on none of this. A
statement whose module is shareable and whose arguments an import could pass, each a constant, an
import name, or a type written over imports (`ModuleStatement::importable_arguments`), must be an
`import`; any other must be a `run`. The error at an `import` names what makes the module a run,
with a label at the statement it comes from: the `run`, or the node where the first label its top
level holds entered (`obstacle`). `cambra check` prints that reason as the interface's last
line (`Interface::written`).

An error of a `run` statement or of its arguments, such as a missing argument, depends on the
statement and the interface it runs alone. Creating a run raises it only when the statement is the
checked or linked module's own, and creating a run that another run declares raises none
(`ProgramLowering::nested`), so the error is raised once, by the check of the module holding the
statement.

Errors from every check are merged, each reported once. Two errors are one when they stand at one
span and are equal once each inference variable is numbered by first appearance and each name is
written as its module spells it (`error_key`), since each check holds its own copy of a module, with
its own inference variables and its own names for the module's members. A check's error in another
module's code is that module's own when its own check raised it. Otherwise the checked module's use
raised it, and it carries a secondary label at the module's `import` or `run` statement that brings
that code in (`ModuleCheck::reached_by`). A module whose check fails stops the compile before
linking's inference. A module is checked against its dependencies' bodies, so each check infers them
again; keeping each module's inferred schemes for its users would remove that cost.

`cambra check lib.cambra` checks a file on its own (`check_program`). It lowers the file as a module
rather than as a root (`lower_for_check`), so its parameters need no defaults, and links nothing: it
checks each module the file reaches and then the file. Each route a module declares is a source
that opens nothing, so the check binds no port. It prints the file's interface
(`Interface::written`): each parameter with its type, bound, or Module type, then each public member
in the order declared. A value's contract is its annotation or the type it infers, a generalized
one's written as a diagnostic writes an inferred polymorphic type, joins and all. A `def` with a
`Mut` parameter lowers curried and is written as its callers apply it, one function of the tuple of
its parameters (`Contract::uncurried`). Inference notes a
generalized member's scheme while it is live (`Typing::note_scheme`), and a monomorphic member's
type is the one its uses settled. A type parameter with no kind written is one inference variable
for the whole check, and a contract writes that variable as the parameter (`write_opened`), so
`def wrap(x): id(x)` over `def id(x: T) => T` prints `wrap: T => T`. Lowering expands an alias
where it is written, so a type prints expanded: `base: {Int where _ > 0}` for `base: Count`.

---

## Files and spans

### A span carries its file

```rust
pub struct FileId(u32);
pub struct Span { pub file: FileId, pub start: usize, pub end: usize }
```

`start` and `end` stay byte offsets into their own file. `Span::join` of spans in two files is a
defect, asserted in debug.

The alternative is one offset space across all files, with each file assigned a base offset, which
is how `rustc`'s `SourceMap` works. `Span` would carry no file. It fails on edits: changing
one file moves the base of every file after it, and so every span in them. Spans are compared across
versions by `/diff` output and the inspector. A per-file offset changes only when its own file
changes.

The parser threads the file through chumsky's span context: `chumsky::span::Span::Context` is
`FileId`.

`FileId` is an index into the compilation's `SourceMap`, meaningful within one compilation. Anything
that outlives a compilation names the file by path.

A member exists once per run but is written once in its module, so one span covers every copy. A
diagnostic about a copy names the run as well as the span.

### The source map

`SourceMap` holds, per `FileId`, the file path, the source text, and a newline index built on first
use. Loading adds each file's module path. `CompiledProgram::loaded` keeps the `LoadedProgram` a
program was compiled from, and `CompiledProgram::sources` reads its map. The line and column of a
span are computed from the map when a diagnostic renders.

### Diagnostics

`CompileError::render` and `eprint` take the `SourceMap` in place of `(src_name, src)`. The ariadne
source cache is keyed by `FileId`, so a single report can label several files. Several errors do:

- a private or missing member: primary label at the reference, secondary at the declaration;
- an import of a module that is run: primary label at the `import`, secondary at the statement
  that makes it a run;
- a run of a shareable module whose arguments an import could pass: at the statement;
- a module-graph cycle: one label per statement in the cycle;
- a public name bound twice, and a conflict between an import, run, or parameter name and a member:
  both sites;
- a missing argument: primary at the `run` or `import` statement, secondary at the parameter;
- an argument that does not fit its parameter: at the argument;
- a route conflict between runs: both `run` statements;
- a use that fails a contract: primary at the use, secondary at the library line the requirement
  comes from.

An inference error's span resolves through the lowering projection, as it does today.

A module lowers once, so a lowering error is reported once however many runs the module has, and its
check reports its inference errors once ([Checking a module on its
own](#checking-a-module-on-its-own)). An error a pass after linking raises in a run's copy carries a
secondary label naming the run at its `run` statement, or at each `import` that reaches a shared
import ([chl-spec.md, "9.14 Checking a module on its
own"](chl-spec.md#914-checking-a-module-on-its-own)). The run is the home of the innermost binding
of a run's member whose right-hand side holds the error's node (`home_of`), and an error no such
binding holds is labelled at every run of its module (`RunSites`). Errors raised alike in several
copies are one error, labelled at each run: inference merges a bounds conflict met in several copies
and keeps each copy's node (`LocatedInferError::also`), and linking merges the rest by `error_key`
(`merged_copies`).

---

## Program evolution

[src/ccl/design/program-evolution.md](../src/ccl/design/program-evolution.md) keys state by
`VarPath` and pairs versions by a structural diff of whole trees. The reload rules for runs are
[chl-spec.md, "9.18 Reloading a program of modules"](chl-spec.md#918-reloading-a-program-of-modules).

- **State belongs to runs.** A `VarPath` begins with the run path, then the enclosing binding chain,
  spelling, and index as today. The run-path segment has its own variant, so a run `cart` and a
  binding named `cart` never produce the same address. Display: ``eu::`a`.`n` ``. A shared import
  holds no state, so no address names one.
- **A reload carries every file.** `/diff` and `/reload` take a bundle mapping each module path to
  its source, including the root's. The single-source request form is removed. Reading files from
  disk at reload time is not offered: `/diff` answers about exactly the version it was sent. Until
  the bundle exists, a posted version is its root file alone, and one that names a module is refused
  ([program-evolution.md, "The control port"](../src/ccl/design/program-evolution.md#the-control-port)).
- **The run tree is diffed by run path.** A run marked `@RenamedFrom(eu)` pairs with the
  predecessor's run `eu` instead of its own path.
- **`@Discard` on a run** covers every address below its run path.
- **Held addresses are recorded in the branch table** ([program-evolution.md, "The branch table"](../src/ccl/design/program-evolution.md#the-branch-table)). A tombstone resolves against every
  version in the branch's ancestry ([chl-spec.md, "8.9 `@Discard` [Decided]"](chl-spec.md#89-discard-decided)),
  so each branch's entry keeps the set of `VarPath`s every version in its ancestry held. A reload
  adds the new version's, and a branch created from a parent starts with a copy of the parent's
  set. The record lasts as long as the process. A record that survives a restart waits on durable
  state.
- **A moved member that holds no state** loses only its operator reuse.

---

## Inspector

The payload's `source` becomes `sources`: one entry per file, carrying `file`, module path, file
path, and text. The `file` of every `span` on the wire indexes `sources`
([src/inspector_model/design.md](../src/inspector_model/design.md)). The source pane shows one file
at a time, with a file list. Clicking a node in another pane opens the file its span points into. A
node of a member also names its run.

This moves every golden wire fixture. The re-bless procedure is in
[web/CLAUDE.md](../web/CLAUDE.md). Until then, a program of several modules gets the degraded
payload, with a diagnostic saying the inspector shows one file.

---

## Worked example: two storefronts and an audit log

The example uses **[Decided]** surface that is not implemented (`Feed(…)` declarations, `in`
guards, `!`) and surface this design adds.

`catalog.cambra`, a library:

```python
pub Dollars = Int
pub Item = {{price: Dollars, cost: Dollars} where _.price >= _.cost}

pub def sale_price(item: Item, qty: Int) => Dollars:
    max([(item.price * qty) // 2, item.cost * qty])
```

`audit_api.cambra`, a library holding the interface as a type:

```python
pub Event = {app: String, event: String}
pub AuditLog = Module{events: Feed(Event)}
```

`audit.cambra`, a runnable module whose Module type is a subtype of `AuditLog`:

```python
import std::http
import audit_api use Event

pub events: Feed(Event)

reqs, resps = http::serve("9000", "GET", "/events")
for req in reqs:
    resps[req.http::id] = [e.audit_api::app + ": " + e.audit_api::event for e in events]
```

`storefront.cambra`, a runnable module with parameters:

```python
import std::http
import catalog
import audit_api

const param port: String
param region: String
param audit: audit_api::AuditLog

items: Map(String, catalog::Item) = [
    "tee" -> (catalog::price=25, catalog::cost=11),
    "mug" -> (catalog::price=12, catalog::cost=5),
]
stock: Mut(Map(String, Int), Txn) := ["tee" -> 500, "mug" -> 200]

order_reqs, order_resps = http::serve(port, "POST", "/order")

for req in order_reqs:
    order = req.http::body
    result = with begin():
        if order.sku in items and order.sku in stock:
            s = stock[order.sku]!
            if s >= order.qty:
                stock[order.sku] := s - order.qty
                audit::events << (audit_api::app=region, audit_api::event="order " + order.sku)
                str(catalog::sale_price(items[order.sku]!, order.qty))
            else:
                "out of stock"
        else:
            "unknown item"
    order_resps[req.http::id] = result
```

`deploy.cambra`, the root:

```python
run audit
run storefront(port="8080", region="eu", audit=audit) as eu
run storefront(port="8081", region="us", audit=audit) as us
```

What each rule contributes:

- `catalog` performs no IO, so `storefront` imports it, and both storefront runs reach its one
  shared import.
- `storefront` checks alone: its parameters are typed by their annotations. Each `run` checks its
  arguments: the run `audit` has an `events` member of type `Feed(audit_api::Event)`, so its Module
  type is a subtype of `AuditLog` by width.
- `items` and `stock` belong to each run: `eu::stock` and `us::stock` are two variables.
- `eu` and `us` feed one `audit::events`, because the root hands both the same run.
- Labels from another module are qualified: `catalog::price`, `audit_api::app`, `req.http::body`.
  The request body's `sku` and `qty` are written unqualified, which assumes the **[Open]** rule for
  data from outside the program gives them to the handler's module ([chl-spec.md, "9.12 Field
  labels and tags belong to a module"](chl-spec.md#912-field-labels-and-tags-belong-to-a-module)).
- The routes are `8080 POST /order`, `8081 POST /order`, and `9000 GET /events`, distinct after
  linking binds each run's `port`.
- A reload adding `run storefront(port="8082", region="ap", audit=audit) as ap` starts a third store
  with its initial stock. Removing `us` needs `@Discard run storefront as us`.

---

## Implementation stack

The work that remains, one PR per item, each updating the spec and design docs it touches:

1. **Public mutable members.** `pub` on the `:=` that introduces a `Txn` variable, a `Txn` entry in
   a Module type, a write through a qualifier, and an argument's member with a `Mut` parameter
   reached through a Module-typed parameter.
2. **Labels through a Module-typed parameter**, whose module is the argument's and is not known
   where the module lowers.
3. **Inferred type arguments.** A type parameter a `run` or an `import` leaves out, inferred from
   the types of its other arguments ([chl-spec.md, "9.4 Parameters"](chl-spec.md#94-parameters)).
4. **The interface as written.** `cambra check` printing a type with the alias names its module
   wrote, which needs a named wrapper type that every comparison looks through, and a diagnostic
   eliding the qualifier on its own module's members, which needs a diagnostic's text formatted once
   the error has a location ([Names carry their home](#names-carry-their-home)).
5. **The std root.** `std::http` as a std module, intrinsics recognized by identity, `http_serve`
   removed.
6. **Hot reload.** Bundles on the control port, the run-tree diff, `@RenamedFrom` on runs,
   qualified `@LoadFrom` loads, `@Discard`.
7. **No trailing expressions**, once an output sink exists. The compiler's own test harness keeps
   them through a compile option the CLI does not expose, and reads the value through the `main`
   output.
8. **The inspector's multi-file source pane.**

---

## Dependencies

Features this design assumes that have meaning outside modules: each is wanted in a single-file
program too, and each is a change of its own. What the design needs that only modules use is part of
the [Implementation stack](#implementation-stack).

- **A function that opens a transaction, called from a loop.** Over a list literal it panics in
  `transact_phase` (`splice_stores: x escaped its binder`). Over `stdin()` it commits once whatever
  the iteration count. The capture and `Mut`-parameter forms fail the same way. Needed by any module
  function that owns a transaction and serves a request loop.
- **Mutable writes inside a comprehension.** A function writing a mutable variable, called in a
  comprehension's element, has its writes dropped rather than applied or refused.
- **Trait requirements in generalized types.** A requirement a body places on a generic parameter is
  part of the inferred type, so a use that fails it is rejected at the use.
- **Refinements over mutable state.** A refinement whose predicate reads a mutable variable,
  `{String where _ in stock.keys()}` over `stock: Mut(Map(String, Int), Txn)`, names a key set that
  changes with each commit. The compiler cannot name a mutable map's key set in a type today, in one
  file or several. Needed for a per-run type such as `InStock` ([chl-spec.md, "9.7 Importing
  asserts a shareable module"](chl-spec.md#97-importing-asserts-a-shareable-module)).
- **Constants where an import resolves.** A link-time constant is a `const` parameter or a binding
  whose definition is a constant ([chl-spec.md, "9.19 Constants"](chl-spec.md#919-constants)), and
  linking gives each run's `const` parameters their values ([Runs](#runs)). An import's arguments
  key its shared import before the importer lowers, so an import argument is a literal, an import
  name, or a type built from built-in types and imported type members whose refinements read no
  value. Comparing an omitted argument with one equal to its default needs the default evaluated
  at link time too: until then they reach two shared imports, where chl-spec.md's
  "9.2 Imports" has them reach one ([Imports](#imports)).
- **`Feed(…)` declarations** ([chl-spec.md, "8.4 Feeds are the second form of
  mutability"](chl-spec.md#84-feeds-are-the-second-form-of-mutability)), for a public feed with no
  initializer.
- **A user-facing output sink**, since trailing expressions are removed. The spec defines no sink a
  script can write to ([chl-spec.md, "10. Sinks"](chl-spec.md#10-sinks)).
- **`rec` bindings**, for cycles in the module graph ([chl-spec.md, "13. Reserved for future
  work"](chl-spec.md#13-reserved-for-future-work)).

---

## Open questions

The language's open questions are
[chl-spec.md, "9.20 Open questions"](chl-spec.md#920-open-questions).

- **Sharing members between runs.** Each run is a full copy of its module, so a function that reads
  no state is linked once per run. Sharing such members between runs would save that compile
  time.
- **Link-time checks per module.** The mutable-variable checks, channelization, and planning run
  only on the linked tree ([Linking](#linking)). Running them per module would need a function's
  writes and feeds summarized in its interface, so a caller could be checked against the summary
  rather than the inlined body.
- **Caching.** Every reload compiles everything the root reaches. A module's lowering and check
  depend only on its source and the interfaces it uses, so both can be cached by content hash.
