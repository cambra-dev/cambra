# Lowering — CHL to CCL

`ccl/lower/` converts CHL syntax into the typed expression tree described in [ir.md](ir.md).
Lowering selects CCL node shapes and records written annotations; it does not solve types. New
expression and binding types generally start as `Type::Hole`, while annotations and constructs with
known types supply more specific information. Inference resolves the remaining holes. The
subsequent `uniquify` pass assigns distinct identities to binders; see
[Structured names and α-uniquification](ir.md#structured-names-and-α-uniquification-barendregt-convention).

## Lambda expressions and function definitions

A one-parameter lambda lowers to one `Lambda`, such as `λ x → body`. An ordinary multi-parameter
lambda or `def` also lowers to one `Lambda`. Its parameter is a fresh synthetic tuple name, and
each use of a source parameter becomes a projection of that tuple. For a two-parameter function
whose body is `x + y`, the result is `λ __arg_tuple_0 → __arg_tuple_0.0 + __arg_tuple_0.1`.
A call `f(a, b)` packs its arguments and applies once: `(a, b) ▷ f`. A single-argument call
applies its argument directly. Ordinary call targets must be names.

`LoweringContext::fresh_tuple_arg` gives each tuple parameter a distinct reserved name. The
projection substitution traverses expression and type slots, including refinement predicates, and
respects inner binders. Distinct reserved names prevent an outer tuple reference from being captured
by a nested multi-parameter lambda. Substitution preserves each parameter occurrence's source site.
Direct projection substitution avoids introducing `Let` bindings under the lambda. Such bindings
would be lifted by `lambda_elim` into morphisms that current simplification does not reduce to the
required bare projections.

Parameters with ordinary annotations retain those annotations on the lambda binding. For a tupled
function, the binding carries a tuple of parameter annotations, with `Type::Hole` in unannotated
positions. A `def` output annotation inserts an annotated binding for `__output` inside the lambda
body. Its refinement predicate can therefore refer to function parameters.

A function with a `Mut(…)` or `Feed(…)` parameter uses named, curried lambdas instead. A mutable
write and a feed each keep the parameter name as their target; a tuple projection cannot be a
`MutWrite` or `Feed` target. Calls to these functions use successive applications, so inlining can
substitute the caller's mutable variable or channel at each named binder before lambda elimination.
`Mut(…)` and `Feed(…)` parameter annotations stamp history types with inferred domains; a
transactional `Mut(…, Txn)` parameter fixes its domain to `Txn`. Other parameters retain their
annotations.

The ordinary tuple shape prevents syntactic multi-argument functions from producing a nested
lambda chain that `lambda_elim` would turn into `curry`. Explicitly nested lambdas can still
produce that internal combinator and are not generally compilable through operator conversion.
CHL has no built-in surface `curry` function.
Function and lambda parameters must be nonempty. The parser rejects variadic, keyword-only, and
default parameters.

## Builtin calls

`lower_call` resolves a call's name through `SurfaceBuiltin::from_name`, the table in
[design-chl-parser.md, "Surface builtins"](../../../chl-parser/design-chl-parser.md#surface-builtins),
before it consults scope. A `Function`-kind builtin lowers in its own arm, and a call of the wrong
arity is refused. A call of the `Qualifier`-kind `summon` is refused: the parser reads
`summon(T)::f` itself. Any other name, including a builtin of another kind, lowers as a call to a
registered source when one has that name and as an ordinary application otherwise. A zero-argument
call to such a name that no registered source has is refused, because an ordinary application needs
an argument; `begin()` and `test_sink()` in expression position are refused this way. The `with`
block recognizes `begin`, and `sink_declaration` recognizes `http_serve` and `test_sink`, both
through the same table.

## Generator functions and feed-only loops

Every loop's source `𝑐`, a `for` statement's and a comprehension's `for` clause's alike, lowers to
`𝑐 ▷ Iterable::elements` (`lower_loop_source`): the loop walks the collection the source's
`Iterable` instance returns. Over a structural collection the call is the identity, and coalescing
removes it
([type-inference.md, "A collection is answered off the table"](type-inference.md#a-collection-is-answered-off-the-table)).

A feed-only or yield-only `for` loop without loop-carried mutation lowers to a composition of its
source and an iteration lambda: `source ≫ (λ x → body)`. The composition carries a data-function
annotation. A loop that feeds an existing defer handle needs no result binding. A loop with `yield`
creates a result defer handle and replaces each `yield 𝑒` with a feed to that handle:

```text
def f(xs):
    for x in xs:
        yield x * 2
```

lowers to the shape:

```text
let f = λ xs →
    let __result_0 = defer
    in xs ▷ Iterable::elements ≫ (λ x → feed(__result_0, x * 2)); __result_0
in body
```

The semicolon denotes an `ExprStmt` that sequences the loop before the final defer read. Nested
loops produce nested compositions. Bindings before the loop become enclosing `Let` nodes; bindings
in its body become per-iteration `Let` nodes. A generator expression goes through
`lower_list_comp` instead, which builds a `Comprehension` node holding the element and one
generator per `for` clause, each with the guards that follow it; `ccl/comprehension.rs` turns that
into the lambda and application encoding, whose shape depends on the number of generators and
guards.

An ordinary `=` inside a loop body introduces an immutable local when its name belongs to that
body or is fresh there. Assignment to an enclosing name is rejected with a diagnostic directing
the writer to `:=` for mutable state. Function definitions inside the loop follow the same scope
rule as assignments.

### Mutation-accumulation loops

A loop that writes an outer mutable variable with `:=` or `+=` retains a structured `For` node.
`find_mutation_loop_vars` finds those writes, including writes under conditional branches. The
`For` body is a statement chain ending in `unit`: mutable writes become `MutWrite`, feeds become
`Feed`, ordinary local bindings become `Let`, and bare effect expressions become `ExprStmt`.
Lowering does not construct a recurrence or decide whether each `MutWrite` has a mutable type.

`mut_elim` consumes `For` and `MutWrite`. It builds one guarded `LetRec` history per loop, whose
decision contains a `writes` record keyed by accumulator. It supplies read-your-writes behavior
and hoists each in-loop feed out as a loop over that history feeding each value. `planning::plan_loops` subsequently
turns the recurrence into `Transact`; operator conversion realizes an induction-domain transaction
with `InductionStore`. See
[The model: histories and causal recursion](mutability.md#the-model-histories-and-causal-recursion)
and [mut_elim: eliminating overwrite mutability](mutability.md#mut_elim-eliminating-overwrite-mutability).

A generator with loop-carried mutation uses this `For` path and a synthesized result defer. Each
`yield` feeds that defer. A conditional in a mutation loop becomes a statement-position `Case`
whose branches contain statement chains. The merge of a write branch and its carry is constructed
by `mut_elim`. A nested `for`, at the body's top level or inside such a conditional, lowers as a
loop of its own whose recurrence is nested in the enclosing one
([ir.md](ir.md#transact--the-domain-parameterized-recurrence-carrier)). A `with begin():` block
nested inside such a conditional is unsupported.

## Tuple patterns

`AssignmentBindings::Tuple` lowers `𝑝₀, …, 𝑝ₙ = 𝑣` to shadowing `let`s. Each component's value is
bound to a minted name, and only then does each component pattern bind from the name its value
is under, so `b, a = (a, b)` reads both old values.

A tuple literal under a tuple pattern of the same length binds each element directly, at every
depth of nesting, so the statement builds no tuple it only takes apart. Any other value is bound
once to a minted name, and component `𝑖` reads its projection `.𝑖`. A feed handle projected out of
a bound tuple literal whose every element is a literal, a source or a handle reaches `channelize`
as an alias of its channel through the inline pass's tuple-projection rule (the module docs of
`src/ccl/inline.rs`). A handle in any other tuple does not reach it
([mutability.md, "`Feed` is a CCL type"](mutability.md#feed-is-a-ccl-type);
[chl-spec.md, "A deferred collection inside a data structure [Open]"](../../../docs/chl-spec.md#a-deferred-collection-inside-a-data-structure-open)).

A `for` binder that is a pattern or `_` lowers as the loop over a minted name whose body starts
with the assignment `𝑝 = 𝑒` (`ForPattern` in `lower/loops.rs`), so every loop site lowers a binder
that is one name. The pattern's names leave the body's mutation scope: they shadow a like-named
outer binding, as a plain loop variable does. A comprehension binder that is a pattern binds a
minted name, and each name the pattern binds reads what the assignment `𝑝 = 𝑒` binds it to, in the
binder's guards, the generators after it and the element (`lower_clauses` in
`lower/comprehension.rs`). `_` binds a minted name that nothing reads.

## Feed declarations and operators — `x: Feed(V)` / `<<` / `<<=`

Feed syntax initially produces `Defer`, `Feed`, and `Define` nodes. A feed is given its value by
at least one `<<` or exactly one `<<=`; a feed with neither reports `NoFeedOrDefine`, and mixing
the two is an error. Feed and define expressions have type `Unit`.

| CHL | Lowered role |
|---|---|
| `x: Feed(V)` | Bind a `Defer` handle |
| `x << value` | Add a `Feed(x, value)` contribution |
| `x <<= value` | Add the sole `Define(x, value)` contribution |

`x: Feed(V)` becomes `let x : Feed(V) = Defer in body`, the `Defer` imaging the annotation
(`feed_declaration` in `lower/stmts.rs`). A declaration with any other annotation is refused, since
only a feed is introduced with no value. A feed or define in statement position is sequenced through
`ExprStmt`. A function of several parameters substitutes a projection of its argument tuple for each
parameter, but binds one its body feeds to that projection (`uncurry_params`), since a feed targets
a name. Inlining folds a projection of a tuple literal holding a feed handle to its element, so the
binding becomes an alias of the handle the caller passed. A top-level
`𝑝 = http_serve(port, method, path)` binds `𝑝` to the tuple `(Source(requests), responses)`, where
`responses` names a `Defer` that a `let` around the statement binds. Both names are minted from the
route, and `responses` is the sink's name for compilation, so the program's sink record reads the
channel whatever `𝑝` binds.

`out = test_sink()` binds a response `Defer` to a `TestSink` registered by the test through
`GlobalContext::register_test_sink`. This form exists only under `cfg(test)` or the `test-helpers`
feature. `sink_declaration` in `lower/sinks.rs` recognizes both sink declarations; non-top-level
blocks reject them because the program's sink record reads only top-level bindings.

### The `channelize` step (feed channelization)

`channelize::run` executes on the inferred and inlined tree immediately after `mut_elim`, before
`lambda_elim` and loop planning. `mut_elim` has already hoisted feeds from structured mutation
loops, so channelization handles them like feeds from other expressions. It eliminates `Defer`,
`Feed`, `Define`, and `ExprStmt` before downstream passes run.

For each cluster of consecutive defer bindings, channelization extracts its feeds or define from the
cluster body and builds a channel expression for each handle. Multiple feeds combine with `Copair`
(`++`), each contribution under its feed's site's tag ([sites.md](sites.md#channel-tags)). Feeds
inside iteration retain their iteration context. An extracted feed takes a copy of each binding it
reads in the scope it leaves: a `let`, or a channel group, which is what a feed declared beneath the
extracted one, as in a loop body, has become by then. A recurrence group is not copied. A multi-arm
feeding `Case` inside a loop produces a refined-source channel for each feeding arm. A guarded
feeding `Case` outside iteration can use a one-shot lift; a scrutinee-pattern feeding `Case` there
is rejected. The cluster becomes a mutually scoped `Feed`-kind `LetRec`. Recognition later orders an
acyclic group as `Let` bindings; an unguarded cycle between channels is rejected.

`channelize` also lifts defer-returning bindings and substitutes aliases that carry defer handles.
It drops the `ExprStmt` nodes after their feed contributions have been extracted. The
[mutability design](mutability.md) records the phase order; `channelize.rs` documents its
extraction cases and structural errors.

### Inference before channelization

Inference checks `Defer`, `Feed`, and `Define` on the source-shaped tree. A defer has a transient
`Feed` history type with rigid domain `ChanDom(d)`, and each contribution is constrained to its
handle. The domain name lets consumers type against the handle before the channel is assembled.
Channelization stamps constructed nodes from their typed children, then substitutes each rigid
name with its assembled domain and erases the `Feed` history wrapper. This does not require a
second inference pass. The strict post-channelization type check verifies the result. See
[Feed handles as invariant histories](type-inference.md#feed-handles-as-invariant-histories).

For a structured mutation loop, `emit_for` checks that the source is a function, binds its element
type to the loop target, and checks the body as a statement. The `For` node has type `Unit`.
`mut_elim` constructs the later decision record and its `__to_<defer>` feed fields.

## `if` and `match` in value position

An `if` or `match` block used as an assigned value parses as `ChlExpr::Block`. Lowering sends its
final statement through the same path as a tail-position conditional. The one-line `match` form
does so as well. No separate block-expression node remains. The result is normally a `Case`; a
default-only `match` uses the sequence described below. A value-returning `if` requires an `else`
branch.

## Variants and match

A variant constructor becomes `VariantCtor(tag, payload)`. A bare `` `tag `` and `` `tag() ``
both supply a `unit` payload. The payload can be a tuple or record, using ordinary term syntax.
`Option(T)` names the compiler-provided nominal type, built by `Option::some` and `Option::none`
([nominal-types.md](nominal-types.md#the-compiler-provided-option)); the backtick tags `` `some ``
and `` `none `` are ordinary tags that build a structural variant.

`match 𝑠` becomes a `Case` with a scrutinee and one `Branch` per arm. Tagged branches carry a
`Pattern(tag, binding, empty_payload)` and a literal `true` guard. A named payload binds its name.
Both ``case `tag(_)`` and ``case `tag`` use a fresh inaccessible binder, but only the latter
sets `empty_payload`: it requires the tag's payload to be `Unit`. Duplicate tags are rejected.
`case _:` must occur once at most and must be last.

Inference constrains the scrutinee to be a subtype of the branches' variant. Shared tags carry
their payload types directly into the pattern bindings. Without a default arm, the branches'
variant is closed, so every possible scrutinee tag must have an arm. With a default arm, it is
open to extra scrutinee tags while retaining the payload constraints on shared tags. Branch result
types join to determine the `Case` result.

### Surplus match arms

The scrutinee may have fewer tags than the arms cover. Such arms stay in the tree. Their
`variant_project` produces an empty restriction, so they contribute no value at runtime.
Inference pins an otherwise unobservable payload type to the type of its position, then to a type
accepted by its uses, or to `Unit` if neither applies. Exhaustiveness applies from
scrutinee tags to arm tags; surplus arm tags are valid. The fan-out for a `match` inside a lambda
combines restrictions on the same domain with
`DisjointJoin`, as distinguished from `Copair` in
[ir.md](ir.md#copair-and-disjointjoin--two-collection-combining-operations-not-one).

Pruning against the scrutinee read alone can remove tags still present in the enclosing lambda's
domain: specialization may narrow the read without narrowing that parameter. The resulting body
would handle fewer tags than its declared domain. The arm is therefore retained and its payload
resolved from its uses; see
[An unobservable arm payload is pinned to what its uses require](type-inference.md#an-unobservable-arm-payload-is-pinned-to-what-its-uses-require).

### Scalar match encoding

A scalar `match` in value position compiles to a one-shot driver. Each tagged arm restricts that
driver through `variant_project(tag)`, evaluates its body on the surviving payload, and combines
the arms with `Copair`. `final_or_default` extracts the resulting scalar. The scrutinee enters
each arm through `const(𝑠)`; it is not the input to the `iterate` driver, which accepts no input.
The corresponding scalar guarded `if` uses guard restrictions and first-match complements instead of
tag projections. A single tagged arm needs no union. `variant_project` takes its payload extent
from its own type, which is available even when the scrutinee cannot carry that tag.

This one-shot scalar encoding is called the C-form in `lambda_elim.rs`. Replacing it with
`𝑠 ▷ (λ __scrut → match __scrut { … })` would require feeding the scrutinee into the planned
`iterate`, which accepts no upstream input. A single tagged arm avoids `Copair`, but its stream
is still an iteration site. Without a default, `final_or_default` takes the bare stream and
reports an invariant violation if that stream is empty; it does not invent a result. With a
default, it takes `(stream, default)` and returns the default when no tagged arm contributes.

### The default arm

`case _:` has no pattern and contributes the fallback value to `final_or_default`, outside the
tagged-arm union. It needs no synthesized complement predicate. A default-only `match` lowers to
`ExprStmt(scrutinee, default_body)` so the scrutinee is still checked, while the result does not
depend on its value or require a variant scrutinee. Channelization removes the `ExprStmt`.

The open variant used by inference is necessary to preserve payload flow from scrutinee to arm
binder while allowing extra tags. A common supertype above both the scrutinee and arm variant
would lose that payload constraint. In lambda elimination, the variant consumed by projections
includes the scrutinee's tags as well as the tagged arms when a default is present. A tagged
`match` with a default inside an enclosing lambda remains unsupported by that elimination path.

## Type annotations

`lower_type_expr` converts CHL type syntax into CCL types. A written annotation is retained on
the relevant binding or expression for inference to check. `Type::Hole` remains available for
unannotated positions and the `_` type wildcard.

A refinement `{T where p}` becomes a `Type::Refinement` over the lowered base and a lowered
predicate. In that predicate only, term `_` names the reserved `__elem` binder. The context
restores its ordinary meaning after the predicate; type `_` remains a hole. A nested refinement
is flattened so its predicates restrict the same element. Predicate type checking occurs during
inference. See [Refinement syntax](../../../docs/chl-spec.md#64-refinement-syntax).

`T => U` becomes a nondependent compute function type `𝐴 ⇒ 𝐵`, with both operands lowered
recursively. A data collection uses its collection constructor instead. Function-type syntax in
value position is rejected. Refinements nested in either operand retain their predicates for
inference to check.

## Type-alias statements

A capitalized assignment `Name = T` declares a type alias. `pre_declare_type_aliases` scans each
block forward before its statements lower, converts every right-hand side through
`lower_type_expr`, and records the result with its statement in `LoweringContext::type_aliases`. A
type use substitutes the `Type` of the innermost declaration whose statement ends before the use,
and a use above every declaration of its name is refused. An alias may therefore refer to an
earlier alias in its block, but not to itself or a later alias. Built-in type names cannot be
redefined, and a name cannot be declared twice in one block. A type parameter is declared in the
same table, in scope throughout its definition.

The alias statement emits a `LetType` over the rest of its block (`lower_type_alias_decl`), holding
the same `Type`, or Module type, its uses substitute. Uniquify resolves the type's predicates
at that node, so a predicate reads the bindings the declaration sees, and then removes it
([ir.md, "Type aliases resolve where they are
declared"](ir.md#type-aliases-resolve-where-they-are-declared)).

`with_block_type_aliases` snapshots and restores the alias map around nested blocks. Top-level
recovery declares aliases directly and collects their errors so other statements can still be
checked; nested block lowering stops at the first alias error. The declaration scan precedes any
block-entry pass that lowers an annotation, including `pre_register_txn_decls`. This order lets a
transactional `Mut(Cents, Txn)` declaration resolve `Cents` before transaction registration.

## Names lowering resolves

**Planned.** Lowering returns, beside the tree, a `ResolvedNames` table with one row per name it
resolves in a type or a module path. Those names have no place in a term. Lowering substitutes an
alias by the type it names, turns a nominal type's name into a `Type::Nominal` and a type
parameter into a `Type::Param`, and turns a qualifier into the module it reaches, so no pass after
lowering holds the name. A row is the use's span, the name as written there, and the target the
name resolves to.

| A use of | Resolves to | Lowering finds it through |
|---|---|---|
| a type alias: `Item` in `def f(i: Item)` | the alias's name in `Item = {price: Int}` | `LoweringContext::type_alias`, through the `DeclaredAlias`'s `name_span` |
| a type parameter: `T` in `def first(T, a: T, b: T) => T` | the `T` that heads the parameter list | `type_alias`, which holds a type parameter as a `DeclaredAlias` whose `name_span` is the parameter's |
| a nominal type: `Shape` in `s: Shape`, in `Shape::rect(1, 2)` and in `case Shape::rect(w, h)` | `NominalDecl.span`, the name the declaration binds | `LoweringContext::nominal_type` |
| a module qualifier: `catalog` in `catalog::price`, each segment of a `use` path | the module's file | `ModuleScope.qualifiers`, whose `Qualifier.file` names it |
| a `use` item that names a value: `f` in `use m::f` | the member's binder | `Reached::Value` |
| a `use` item that names a type | the alias or nominal declaration, as for a use of either | `Reached::Type`, `Reached::Nominal` |
| a type a `use` item brought in: `T` in `x: T` after `use m::T` | `T`'s declaration in `m`, the `use` item's own target | `type_alias`, through the `name_span` `Reached::Type` carries, or `nominal_type`, through `used_nominal`'s `NominalDecl.span` |

`DeclaredAlias` gains a `name_span`, the span of the name its declaration binds: the left-hand side
of an alias statement, a type parameter, or, for a `use` type name, the alias's name in the module
that declares it. `Reached::Type` gains that span beside the type, so an import's and a run's `use`
type names both resolve into the declaring module, as their nominal counterparts do. A `use` type
name whose module has errors names no type and has no row.

A target is a `Span` for a declaration lowering locates directly, or the `Uid` of a value member's
binder. A module's target is the empty span at the start of its file. A `Uid` target resolves
through the binder's binding occurrence, as a use of the binder does
([provenance.md](provenance.md#name-occurrences)). A span names its file, so a target in another
module's file resolves there. A name with no declaration in any source has no row: `Int`
and the other built-in types, and the compiler-provided `Option`, whose `NominalDecl.span` is empty.

The table is an output of lowering, not of provenance. No pass after lowering reads or rewrites the
names it records, so a row needs no `NodeId` and no copy rule. It describes the program lowering
saw, which is the program the `pre-inference` pane holds, and like the tree it exists only when
lowering succeeds. A `Type` cannot carry the ids instead: it derives `Clone`, `Eq` and `Hash`, keys
the solver's constraint cache, and is cloned by the solver, substitution, monomorphization and
planning outside any recording ([provenance.md](provenance.md#the-occurrence-field)).

`every_resolved_name_spans_its_spelling`, over the pipeline corpus, checks that the text at each
row's use span is the name the row records, and that a span target's text is that name too, except
for a module's empty span.

## `pass` statements

`contributing_stmts` removes `pass` at each block entry, before the last value-producing
statement is selected. A value block containing only `pass` is rejected. A feed-only `for` body
with no other statement yields `unit`; a structured loop body or transaction block retains its
manufactured `unit` terminal. A transaction with no resulting footprint is rejected by its own
block rule.

One pre-filter classification is an exception: `for_body_terminal_is_bare_effect` examines the
loop body's last statement before `pass` removal. In a final-position loop whose body ends in
`bump(c)` followed by `pass`, that check misses the effect-call path and lowering rejects the
loop. Removing the trailing `pass` selects the supported path. This is a lowering limitation,
not intended `pass` semantics.

## Module syntax

A top-level `import` or `run` with its `use` clause, `pub` on a value binding, a `def`, or a type
alias, and a qualified value, type, label, or tag lower ([docs/modules.md,
"Imports"](../../../docs/modules.md#imports), [docs/modules.md,
"Runs"](../../../docs/modules.md#runs)).
A module lowers once, and linking creates each run of it from that lowering ([docs/modules.md, "A
module lowers once"](../../../docs/modules.md#a-module-lowers-once)). Lowering resolves each
qualified form against the module's import names and run names (`ccl/lower/modules/scope.rs`): a value
to the raw name `m::f`, which creating the module's run resolves to the binder in `m`'s run, a type
to the type its alias names, spelled through `m`, and a label to a `Label` of the module it names.
An import's `use` name for a value lowers as a raw name, which the same scope resolves. A run's is
a `let` at the `run` statement. A `use` name for a type is an alias, in scope throughout the module
for an import and from the statement down for a run. A `run` statement lowers to a
[`Run`](ir.md#run--a-run-statement-before-linking) node over the rest of the module, below a `let`
per argument. A value `param` lowers to a `let` at the head of its module's chain, of its default,
which creating a run or a shared import replaces with its argument ([docs/modules.md,
"Runs"](../../../docs/modules.md#runs)). A shared import's arguments are bound at the head of its
chain, one shared import per module and distinct set of arguments ([docs/modules.md,
"Imports"](../../../docs/modules.md#imports)). A Module-typed `param` lowers to a `let` per entry of
its Module type, which creating a run binds to the argument's members, and a top-level binding of a
module to nothing ([docs/modules.md, "A Module type is not a
`Type`"](../../../docs/modules.md#a-module-type-is-not-a-type)). A sink is declared, and registered
by each run of the module.

The rest of the module syntax parses ([chl-spec.md](../../../docs/chl-spec.md), "9. Modules") and
does not lower yet: `@RenamedFrom`, `@Discard`, `pub` on a mutable variable, and a write to another
module's member. `refuse_module_syntax` (`ccl/lower/module_syntax.rs`) walks the whole module,
every block and every expression, and reports one `LoweringError::Unsupported` per construct, and
the module lowers nothing when it reports. A path with a capitalized qualifier segment,
`Price::discounted`, is refused as a method reference rather than as module syntax
([chl-spec.md](../../../docs/chl-spec.md), "6.8 Nominal types and methods [Decided]"). A module that
uses refused syntax therefore reports only those refusals, and none of the lowering errors its
other statements would raise.
