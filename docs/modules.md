# Modules

> **Status: [Sketched].** A proposed implementation. The first four items of the [Implementation
> stack](#implementation-stack) are implemented, and the sixth, runs and value parameters
> ([Runs](#runs)).
> [Dependencies](#dependencies) lists the features outside modules it assumes, and [Open
> questions](#open-questions) what it leaves undecided.

The language rules for modules are [chl-spec.md, "9. Modules [Decided]"](chl-spec.md#9-modules-decided):
imports, runs, parameters, visibility, qualified references, Module types, shared runs, and how a
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

A Module-typed parameter names exactly one run in each run of its module. It lowers to a `let` per
entry, `audit::events`, and creating a run of its module binds each to the argument run's member at
the type the Module type gives it ([Module types are not value
types](#module-types-are-not-value-types)). Specialization and planning see the member, and
checking against the Module type costs one `let`.

## Linking

The **link order** is a topological order of the module graph
([chl-spec.md, "9.11 The module graph"](chl-spec.md#911-the-module-graph)) in which each module follows
every module it has an edge to. Ties break by module path, lexicographically. The order is a
function of the graph alone: reordering statements in a file does not change it, and neither does
discovering modules in a different order.

The order does not affect meaning, since members of different modules never share a scope. It is
deterministic because two compilations of one root must produce one tree: program diffing compares
trees structurally ([src/ccl/design/diffing.md](../src/ccl/design/diffing.md)).

Linking puts one shared run per imported module and distinct set of arguments, in link order,
around the root, and each run at its `run` statement in the module that declares it
([Runs](#runs)). Each is created from its module's lowering, which happens once ([A module lowers
once](#a-module-lowers-once)).

**The per-module check runs parsing, lowering, uniquification, and inference** (`Phase::Lower`,
`Phase::Uniquify`, `Phase::Infer` in `src/ccl/context.rs`), plus the run-site checks of the
module's own `run` statements: argument types. Lowering's own refusals
are part of it: the mutation-statement rules, the out-of-block `Txn` read gate, visibility, and a
duplicate literal route within the module.

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

An error from a link-time pass is a real error, not a compiler defect, and is reported where
[chl-spec.md, "9.14 Checking a module on its own"](chl-spec.md#914-checking-a-module-on-its-own) says: at its span, naming the run, with a secondary label at the statement that brought the
run into the program.

Linking also runs inference over the whole tree once more. That run specializes and propagates
refinements across modules. It reports nothing located inside a module body, because the
per-module inference already accepted every body. An error there is a compiler defect, asserted in
debug.

That guarantee holds only if an inferred type states every requirement its body imposes. Today one
kind of requirement is enforced only when a concrete type is delivered: a trait requirement on a
generic parameter ([type-inference.md, "Checking a definition
alone"](../src/ccl/design/type-inference.md#checking-a-definition-alone)). Making it
part of the generalized type is a dependency ([Dependencies](#dependencies)).

The compiler's own test harness enables trailing expressions, which
[chl-spec.md, "9.17 No trailing expressions"](chl-spec.md#917-no-trailing-expressions) refuses, through a
compile option the CLI does not expose. The harness reads the value through the `main` output as
today.

---

## Resolution

### Names carry their home

A reference to another module's member needs no name of its own kind. It lowers to a raw name
spelled through its qualifier, `m::f` or `eu::f`, and creating the run it stands in resolves that
spelling to the binder of the run the qualifier reaches ([A module lowers
once](#a-module-lowers-once)). Through a Module-typed parameter it is the `let` the parameter binds,
`audit::f` ([Module types are not value types](#module-types-are-not-value-types)).

One change to `Name` (`src/ccl/names.rs`): **`Name::Unique { base, uid, home }`**, where `home` is
the run a member belongs to: `Shared(SharedRun)` for a shared run's member, its module path and its
arguments, `Run(run_path)` for a member of a run a `run` statement declares, and absent for a
local. Identity remains the `uid`.
`home` is metadata of the kind `base` already is. It is implemented as `home: Option<Arc<Home>>`.
`uniquify::run_in` mints a run's top-level binders with it, and every other binder, the root's
members included, without one. A pass that re-mints a copy of a binder keeps its home
(`Name::fresh_like`).

Module paths and run paths are interned and shared: cloning one copies a pointer, and `Display`
renders it without a lookup table. Neither uses a per-compilation counter. They appear in state keys
and record labels, and a counter would give two compilations of one root different labels, the
defect [`Name::field_key`](../src/ccl/names.rs) documents.

Rendering: symbolic IR output prints a member as `home::base`, `catalog::price`,
`scaled(scale=3)::by`, or `eu::stock`, and a local as `base`. A diagnostic about a location in a
module elides the qualifier on that module's own members. That elision is not implemented: a
diagnostic's text, types included, is formatted during inference, before the error has a location,
so every diagnostic qualifies an imported module's or a run's members, its own diagnostics
included.

`PiRef` boxes its hint to keep `Name` at the width `Unique` needs. `home` widens `Unique`: `Name`
grows from 32 to 40 bytes, `Type` from 64 to 72, and `TypedExpr` from 328 to 368.

`Name::Raw` is unchanged. A raw name is written in one module, and resolves within the run of it
being created, through that run's scope when it is spelled through a qualifier.

A record label and a variant tag in `ccl::Type` and in a term are a `Label`, which carries the module
path it belongs to
([chl-spec.md, "9.12 Field labels and tags belong to a module"](chl-spec.md#912-field-labels-and-tags-belong-to-a-module)).
Two labels are one label when both spelling and module agree. The root's labels have no module
path and render bare. Another module's label renders `module::label`, which is also its spelling at
run time.

`Option`'s tags `some` and `none` belong to the std root, and a user's `` `some `` builds its own
tag. Applied as written, that rule would leave no module able to match an `Option`. Until `Option` is
a nominal variant, `some` and `none` share the root's namespace, so every module's unqualified
`some` and `none` are `Option`'s.

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
   qualifier to the binder of the run the qualifier reaches: `m::f` to the shared run's member,
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

### Pipeline

```
root file
  → load       parse the root; follow its imports and runs to files; parse each once,
               with its own FileId
  → graph      build the module graph; refuse cycles; compute link order
  → lower      once per module, in link order, against the interfaces of the modules it imports
               and runs. Produces a chain, with each `run` statement a `Run` node, and an interface
  → check      once per module: inference over the module alone, as chl-spec.md's "9.14
               Checking a module on its own" requires
  → run sites  each import against the IO its module performs and the state it declares; each
               run's arguments against its module's parameter types
  → link       create each shared run, one per imported module and distinct set of arguments, in
               link order, and the root's run, which creates each run it declares at its `run`
               statement; each run a uniquified copy of its module's chain
  → infer …    over the linked tree: specialization and refinement propagation
```

Each run is a copy of its module's chain, uniquified alone, so every binder of the copy is its own
([A module lowers once](#a-module-lowers-once)). Uniquifying a run uses the property `uniquify`
already has for lowering's pre-cloned subtrees ([`src/ccl/uniquify.rs`](../src/ccl/uniquify.rs),
"Mint before copy"): the runs already created inside it stay settled.

Errors in one file do not stop loading, lowering, or checking the others. Every module's errors are
reported together.

### Loading

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
- **Disk.** `DiskFiles` matches each component of `a/b/c.cambra` against its directory's entries, so
  a file whose name differs only in case is not the module's on any file system. A file it already
  read for another module path, compared by canonical path, is refused.
- **The root.** The root's module path is its file name without `.cambra`. A module naming that path
  reaches the root's own file, so the cycle is reported rather than the root read twice. A root
  built by `LoadedProgram::from_text` has no module path, and no statement can name it.
- **Missing modules.** Each statement naming a module with no file is an error at its module path.
  The message says why: no file, a file differing in case, a file another module path already
  reached, or a failed read.
- **Unlexable files.** A file the lexer rejects has no tree, so loading follows none of its
  statements.
- **Cycles.** Each strongly connected component with a cycle is one error. It names the shortest
  cycle through the component's least module path, with a label at each statement in it. The link
  order exists only for an acyclic graph.
- **Compilation.** Loading's errors come first: every file's parse errors, then missing modules and
  cycles. Only the root is lowered, and lowering refuses every `import` and `run`.

### Imports

Importing values and type aliases is implemented: `import m`, `import a::b as c`, and
`import m(x=1)`, `use` clauses on an `import`, `pub` on value bindings, `def`s and type aliases,
`m::f` as a value, a callee, and a qualifier of labels and tags, and `m::T` as a type.

- **An imported module has a shared run per distinct set of arguments its imports pass**, created
  from its lowering in link order and linked around the root ([A module lowers
  once](#a-module-lowers-once)).
- **An interface records declarations.** `Interface` (`src/ccl/lower/modules.rs`) records each
  top-level binding's visibility, declaration, and call shape, and each top-level type alias's type
  as its module lowered it. `m::f` lowers to the raw name `m::f`, and `m::T` to the alias's type
  spelled through `m` ([Imported aliases are closed over their
  module](#imported-aliases-are-closed-over-their-module)). A private member is an error with a
  label at its declaration, and a missing one is an error.
- **`use`.** A `use` item reaches its member as `m::f` or `m::T` does. A value's name resolves
  through the module's uniquify scope, and a type's is an alias in scope throughout the module
  ([`use` names are environment entries, not
  bindings](#use-names-are-environment-entries-not-bindings)). A member spelled like a `use` name is
  an error, and so is a `use` name spelled like an import name, another `use` name, a builtin, or a
  built-in type. A builtin call resolves by its spelling before scope (`lower_call`), so a `use`
  name spelled like one would never reach its member.
- **Linking** replaces each placeholder with the code below it: every shared run once, in link
  order, around the root, the first in link order outermost.
- **IO and state.** A module that declares a sink or mutable state (`sink_site`, `state_site`), or
  reads a registered source, which lowering records, has no shared run. Each `import` of it is an
  error, labeled at the site (`Unimportable`). Lowering declares a sink without opening anything, so
  lowering such a module is harmless; a run of it registers the sink.
- **What an import may hold.** A `run`, a top-level loop, and an expression statement in an
  imported module are errors, reported once, where the module is first imported
  (`ProgramLowering::importable`).
- **`Mut` parameters.** A call to an imported `def` with a `Mut` parameter, qualified or through
  `use`, takes the curried shape the `def` lowers to.
- **Labels.** An unqualified label belongs to the module that writes it, `this::` spells the same
  label, and `m::` qualifies the label of the module `m` names. `some` and `none` are `Option`'s in
  every module ([Names carry their home](#names-carry-their-home)).
- **Arguments.** Each import's shared run is decided by what it writes, before any module lowers
  (`ProgramLowering::shared_runs`): its module and its arguments, `Home::Shared`'s `SharedRun`. Each
  import qualifier records the shared run it reaches. A shared run is created for the first
  statement that reaches it. Two sets are compared as written, so an omitted argument and one equal
  to its default reach two shared runs, where chl-spec.md's "9.2 Imports" has them reach one.
  Comparing them needs a default evaluated at link time ([Link-time constants](#dependencies)). An
  argument is a literal or an import name; anything else is an error at the argument
  ([Dependencies](#dependencies)). An import name's shared run is part of the key,
  `shop(counter=counter)`, and is created first (`ProgramLowering::ensure_shared_run`). Each literal
  is bound at the head of the shared run's chain, at its parameter's type, and a parameter with
  neither an argument nor a default is an error at the `import`.

A module whose own errors stop it from lowering has no interface, and a reference or a `use` item
into it adds no error.

### Runs

Running modules is implemented: `run m(x=e)` and `run a::b as n`, value parameters, a run's
members reached as `n::f`, `n::T`, and `n::label`, and `use` on a run.

- **A run is created from its module's lowering.** A `run` statement lowers to a `Run` node over
  the rest of the declaring module (`LoweringContext::take_run`), and creating the declaring
  module's run creates this one at the run path `n`, or `eu::n` for a run the run `eu` declares, and
  puts its chain there (`ProgramLowering::expand_runs`). Its members' home is `Home::Run`.
- **A run stands at its statement.** A reference to the run name above the statement is refused,
  and each value a run's `use` clause binds is a `let` at the statement of the raw name `n::f`, so
  both are in scope from the statement down ([chl-spec.md, "9.3 Runs"](chl-spec.md#93-runs)).
- **A run performs its module's whole top level**: its state, loops, sources, and sinks. Lowering
  declares a sink (`LoweringContext::declared_sinks`), and creating a run registers it keyed by the
  run path, `eu::out` (`LoweringContext::register_sinks`). The program's tail reads it through the
  binder the run's chain minted (`LoweringContext::run_sink_names`). A run's mutable variables are
  labeled by run path in history records, so two runs keep two histories.
- **A run's feed is fed through its run name.** `a::events << e` feeds the run's public feed, as
  `events << e` does inside it: a feed's target may be qualified (`feed_target`).
- **Routes are unique across runs.** Creating a run registers its routes. A route two runs serve is
  an error at the second `run` statement, with a note at the first. A route address is a literal,
  so two runs of one module that serves a route always conflict.
- **A parameter is a `let` at the head of its module's chain**, of its default, or of a placeholder
  when it has none. The interface records each parameter's annotation and whether it has a default.
  A `run` statement binds each argument above its `Run` node under `argument_name`'s
  double-underscore name, `__run::eu::port`, at the parameter's annotated type spelled through the
  run name, so a mismatch is reported at the argument. Creating the run points each parameter with
  an argument at that name, and refuses one with neither an argument nor a default at the `run`
  statement. An unannotated parameter's type is inferred from the module's uses, so a bad argument
  for one is reported where the module uses it, until a module is checked alone. The root takes
  every parameter's default, and a parameter without one is an error there.
- **Refused:** a type parameter (item 7), `@RenamedFrom`, and a `run` in an imported module. `pub`
  on a `run` is a parse error, since a module returns a run by binding it to a public member
  ([Module types are not value types](#module-types-are-not-value-types)). `pub` on `:=` is
  refused, so no module reaches another run's mutable variable.

### The module interface

Checking a module records whether the module performs IO or declares mutable state, with the site
that does, and, for each public member:

| Member | Recorded |
| --- | --- |
| value, `def`, type alias, `Txn` mutable variable, feed | its kind, its contract, and for a `def` whether it takes a `Mut` parameter |
| intrinsic | the intrinsic ([Intrinsics resolve by identity](#intrinsics-resolve-by-identity)) |
| parameter | its type, or for a type parameter its bound, and its default if it has one |

It also records each private member's spelling and span, so that `m::hidden` can say the member is
private and point at it.

A `def` with a `Mut` parameter lowers as a curried chain, and its call sites must match
(`LoweringContext::mut_param_fns`). The interface carries that shape so a user's call site lowers
correctly: a qualified callee reads it from the member, and a `use` name of such a `def` is
registered in `mut_param_fns` when its module begins lowering.

Each module is lowered with fresh block state. Every spelling-keyed map in `LoweringContext`
(`transactional_vars`, `type_aliases`, `mut_param_fns`, `shadow_depth`) covers one module. The
entries a module seeds from interfaces and from its parameters' Module types, `Txn` members in
`transactional_vars` and `Mut`-parameter functions in `mut_param_fns`, are keyed by qualified
spelling. The out-of-block read gate and the `MutWrite` shape then apply to `eu::stock` and
`audit::stock` exactly as they apply to `stock` inside its own module.

When a module has errors, its interface holds the members that checked. A reference to a member
missing from a module that has errors is not reported, because that module's own errors account for
it.

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

### Module types are not value types

A Module type is a `ModuleType` (`src/ccl/module_type.rs`), its entries in the order written, and
not a `Type`: no value has one ([chl-spec.md, "9.8 Module types"](chl-spec.md#98-module-types)).
What a type alias names is an `AliasType`, a `Type` or a `ModuleType`, and a `LetType` holds one,
so an alias of a Module type is declared, exported, and closed over its module as any alias is
([Imported aliases are closed over their module](#imported-aliases-are-closed-over-their-module)).
A Module type is written as a parameter's annotation, an alias's right-hand side, or an entry of
another Module type (`lower_alias_type`). Anywhere else it is an error, as is a Module type's alias
named as a value's type.

A name denotes a module when it is an import name, a run name, a parameter annotated with a Module
type, a top-level binding of a module, `pub audit = a`, or a `use` name of a member bound to one.
Each is a `Qualifier`, and so is a path through public members bound to a module, `shop::audit`.
A qualifier spells a member reached through it as the module it names is spelled: a binding
`k = c` spells `k::f` as `c::f`, and through an interface `h::k::f` is `h::c::f`
(`ModuleMember::spelling`). Creating a run then resolves those spellings as any other, and a
binding needs no names of its own.

A Module-typed parameter lowers once, before any argument exists
(`LoweringContext::declare_module_parameters`). Its Module type gives it a view (`ModuleView`) and
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
does not fit is the argument's error (`ProgramLowering::bind_module_parameter`). The argument's
members are those of the run or shared run it names, or, for a parameter passed on, those of that
parameter's argument (`module_names`). A default names an import, checked while the module lowers
and taken by a run that passes no argument.

A polymorphic entry's `let` carries its polymorphic type, as a `def` with type parameters does. A
feed entry, `Feed(T)`, is a feed handle with its domain left to inference, and `audit::events << e`
feeds the argument's feed through the `let`. A binding exported in an interface carries its
spelling and its view, so a module reaching `h::k` reaches what `k` does in `h`.

Not implemented: an entry that is a `Txn` variable or a type member, an argument's member with a
`Mut` parameter, and a label through a Module-typed parameter, whose module is the argument's and
is not known where the module lowers.

### `use` names are environment entries, not bindings

`import n use f` in module `m` does not lower to a `let`. `m`'s tree is uniquified with `f` mapped
to the binder `n`'s chain minted for its member `f` beneath every binder of the tree
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
`std::http`, so an error inside it renders against its source. The `http` status helpers are ordinary CHL functions there.

A std module may bind an intrinsic, meaning a builtin source, sink constructor, or special form. The
interface records the member as that intrinsic. Lowering recognizes a special form by what the
callee resolves to: `reqs, resps = http::serve(…)` is the `http_serve` tuple form because
`http::serve` resolves to the intrinsic.

An address argument of `http::serve` is a string literal, as recognition matches today. A
parameter address waits on link-time constants ([Dependencies](#dependencies)). Route uniqueness
across runs moves past linking, since two runs of one module that serves a literal route serve the
same address.

### Registries keyed by spelling

Four places keyed by a spelling that is unique within one file and not across modules and runs. Each
switches to the member's qualified spelling, `home::base`. The first two are switched
(`LoweringContext::register_sinks`, `Name::field_key`), and the last two switch with reload:

- **Sink bindings** (`LoweringContext::sink_bindings`), and so the linked tree's trailing-record
  field names and `CompiledOutput::name`. Two runs of one module each bind `resps`.
- **History-record labels** (`Name::field_key`). One transaction can write `eu::stock` and
  `us::stock`, and both keys land in one `Transact` history record. A user identifier cannot
  contain `::`, so a qualified label cannot collide with a local's.
- **State identity** (`VarPath`), in [Program evolution](#program-evolution).
- **The `@LoadFrom` loaded spelling**, which becomes a run path plus a spelling.

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
use. Loading adds each file's module path. `CompiledProgram::sources` keeps the map a program was
compiled from. The line and column of a span are computed from the map when a diagnostic renders.

### Diagnostics

`CompileError::render` and `eprint` take the `SourceMap` in place of `(src_name, src)`. The ariadne
source cache is keyed by `FileId`, so a single report can label several files. Several errors do:

- a private or missing member: primary label at the reference, secondary at the declaration;
- an import of a module that performs IO or declares mutable state: primary label at the `import`,
  secondary at the IO site or the state;
- a module-graph cycle: one label per statement in the cycle;
- a public name bound twice, and a conflict between an import, run, or parameter name and a member:
  both sites;
- an argument mismatch: primary at the `run` statement, secondary at the parameter's annotation and,
  for a Module-typed parameter, at the member whose contract does not fit;
- a cycle among runs: one label per `run` statement in it;
- a route conflict between runs: both `run` statements;
- a use that fails a contract: primary at the use, secondary at the library line the requirement
  comes from.

An inference error's span resolves through the lowering projection, as it does today.

A module lowers once, so a lowering error is reported once however many runs the module has. An
inference error in a module that runs more than once, or is imported with more than one set of
arguments, is reported once per run, each report identical, since inference sees each run's copy.
The label naming the run whose copy failed, with a secondary label at its `run` statement or
`import` ([chl-spec.md, "9.14 Checking a module on its
own"](chl-spec.md#914-checking-a-module-on-its-own)), is not implemented.

---

## Program evolution

[src/ccl/design/program-evolution.md](../src/ccl/design/program-evolution.md) keys state by
`VarPath` and pairs versions by a structural diff of whole trees. The reload rules for runs are
[chl-spec.md, "9.18 Reloading a program of modules"](chl-spec.md#918-reloading-a-program-of-modules).

- **State belongs to runs.** A `VarPath` begins with the run path, then the enclosing binding chain,
  spelling, and index as today. The run-path segment has its own variant, so a run `cart` and a
  binding named `cart` never produce the same address. Display: ``eu::`a`.`n` ``. A shared run
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
guards, `!`) and surface this design adds. Its route address `port` is a parameter, which waits on
link-time constants ([Dependencies](#dependencies)); until they exist, the two storefront runs
serve one literal address and conflict.

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

param port: String
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
  shared run.
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

The example is the seed of a multi-file north-star program, `tests/programs/deployment/`.

---

## Implementation stack

One PR per item, each updating the spec and design docs it touches:

1. **Spans carry a `FileId`; `SourceMap`; multi-file diagnostic rendering.** Every compilation is
   still one file. The inspector wire gains `file` and the goldens are re-blessed.
2. **Syntax.** The seven keywords, `import`, `run`, and `param` statements with `use` clauses,
   `@RenamedFrom`, `@Discard`, `pub` on introducing statements, and `::` in qualified names, labels,
   and tags. Lowering refuses each of them with an unsupported error
   (`src/ccl/lower/module_syntax.rs`).
3. **Loading and the module graph.** Path resolution, per-file parsing, module paths in the
   `SourceMap`, cycle refusal, link order.
4. **Imports**, in four parts:
   1. **Values.** Per-module lowering and uniquification, interfaces, shared runs, the IO check on
      imports, visibility, qualified callees, labels and tags that carry their module.
   2. **`use` clauses.**
   3. **Imported type aliases**, closed over their module.
   4. **`Mut`-parameter functions**, and the refusal of importing a module that declares state:
      state belongs to runs ([chl-spec.md, "9.7 Importing asserts no IO and no
      state"](chl-spec.md#97-importing-asserts-no-io-and-no-state)).
5. **Per-module checking.** Inference over one module against the interfaces it uses, contracts in
   the interface, `cambra check`.
6. **Runs and parameters**, in two parts:
   1. **Runs without parameters.** A run per `run` statement at its statement, a run's
      `Unique::home`, run members, state and IO in runs, sink and history keys qualified by run
      path, route uniqueness across runs.
   2. **Value parameters.** `param`, keyword arguments, defaults, run-site checks.
7. **Module types and type parameters**, in three parts:
   1. **Arguments to an import.** One shared run per module and distinct set of constant arguments
      ([chl-spec.md, "9.2 Imports"](chl-spec.md#92-imports)), with a literal as the constant.
   2. **Module types.** `Module{…}`, Module-typed parameters and the qualified references through
      them, an import name or run name as an argument, a member bound to a run, and feeding another
      run's feed.
   3. **Type parameters**, and a type as an argument.
8. **The std root.** `std::http` as a std module, intrinsics recognized by identity, `http_serve`
   removed, route uniqueness across runs.
9. **Hot reload.** Bundles on the control port, the run-tree diff, `@RenamedFrom` on runs,
   qualified `@LoadFrom` loads, `@Discard`.
10. **No trailing expressions.** The harness-only compile option, once an output sink exists.
11. **The inspector's multi-file source pane.**

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
- **`requires Transaction`** ([chl-spec.md, "8.7 Direction [Decided]: transactions as contextual
  parameters"](chl-spec.md#87-direction-decided-transactions-as-contextual-parameters)). A function
  that reads or writes `Txn` state inside its caller's transaction, and so two module functions
  composed in one transaction. The lexical read gate refuses a `Txn` read in a `def` outside a `with
  begin():` of its own until then.
- **Trait requirements in generalized types.** A requirement a body places on a generic parameter is
  part of the inferred type, so a use that fails it is rejected at the use. The guarantee of
  [chl-spec.md, "9.14 Checking a module on its own"](chl-spec.md#914-checking-a-module-on-its-own) rests on
  it.
- **Refinements over mutable state.** A refinement whose predicate reads a mutable variable,
  `{String where _ in stock.keys()}` over `stock: Mut(Map(String, Int), Txn)`, names a key set that
  changes with each commit. The compiler cannot name a mutable map's key set in a type today, in one
  file or several. Needed for a per-run type such as `InStock` ([chl-spec.md, "9.7 Importing
  asserts no IO and no state"](chl-spec.md#97-importing-asserts-no-io-and-no-state)).
- **Link-time constants.** A value fixed once linking binds a run's arguments, such as a route
  address passed as a parameter, and every argument to an import, which keys its shared run. A run
  argument may be any expression, so this needs its own definition of which expressions are
  link-time constants and when they are evaluated ([chl-spec.md, "9.19 Open
  questions"](chl-spec.md#919-open-questions)). Until it exists a route address is a literal
  ([Intrinsics resolve by identity](#intrinsics-resolve-by-identity)), and an import argument is a
  literal, a type, or an import name.
- **`Feed(…)` declarations** ([chl-spec.md, "8.4 Feeds are the second form of
  mutability"](chl-spec.md#84-feeds-are-the-second-form-of-mutability)), for a public feed with no
  initializer.
- **A user-facing output sink**, since trailing expressions are removed. The spec defines no sink a
  script can write to ([chl-spec.md, "10. Sinks"](chl-spec.md#10-sinks)).
- **`rec` bindings**, for cycles in the module graph ([chl-spec.md, "13. Reserved for future
  work"](chl-spec.md#13-reserved-for-future-work)).

---

## Open questions

The language's open questions are [chl-spec.md, "9.19 Open questions"](chl-spec.md#919-open-questions).

- **Sharing members between runs.** Each run is a full copy of its module, so a function that reads
  no state is linked once per run. Sharing such members between runs would save that compile
  time.
- **Link-time checks per module.** The mutable-variable checks, channelization, and planning run
  only on the linked tree ([Linking](#linking)). Running them per module would need a function's
  writes and feeds summarized in its interface, so a caller could be checked against the summary
  rather than the inlined body.
- **Caching.** Every reload compiles everything the root reaches. A module's lowering and check
  depend only on its source and the interfaces it uses, so both can be cached by content hash.
