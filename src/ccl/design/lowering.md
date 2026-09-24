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

A function with a `Mut(…)` parameter uses named, curried lambdas instead. A mutable write must keep
the parameter name as its target; a tuple projection cannot be a `MutWrite` target. Calls to these
functions use successive applications, so inlining can substitute the caller's mutable variable at
each named binder before lambda elimination. `Mut(…)` and `Feed(…)` parameter annotations stamp
history types with inferred domains; a transactional `Mut(…, Txn)` parameter fixes its domain to
`Txn`. Other parameters in the curried chain retain their annotations.

The ordinary tuple shape prevents syntactic multi-argument functions from producing a nested
lambda chain that `lambda_elim` would turn into `curry`. Explicitly nested lambdas and explicit
`curry` remain separate constructs and are not generally compilable through operator conversion.
Function and lambda parameters must be nonempty. The parser rejects variadic, keyword-only, and
default parameters.

## Generator functions and feed-only loops

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
    in xs ≫ (λ x → feed(__result_0, x * 2)); __result_0
in body
```

The semicolon denotes an `ExprStmt` that sequences the loop before the final defer read. Nested
loops produce nested compositions. Bindings before the loop become enclosing `Let` nodes; bindings
in its body become per-iteration `Let` nodes. Generator expressions use `lower_list_comp` instead:
its lambda and application encoding depends on the number of generators and predicates.

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

`mut_elim` consumes `For` and `MutWrite`. It builds a guarded `LetRec` history for each accumulator,
supplies read-your-writes behavior, and hoists in-loop feeds into ordinary feeds of the loop
history. `planning::plan_loops` subsequently turns the recurrence into `Transact`; operator
conversion realizes an induction-domain transaction with `InductionStore`. See
[The model: histories and causal recursion](mutability.md#the-model-histories-and-causal-recursion)
and [mut_elim: eliminating overwrite mutability](mutability.md#mut_elim-eliminating-overwrite-mutability).

A generator with loop-carried mutation uses this `For` path and a synthesized result defer. Each
`yield` feeds that defer. A conditional in a mutation loop becomes a statement-position `Case`
whose branches contain statement chains. The merge of a write branch and its carry is constructed
by `mut_elim`. Nested `for` and `with begin():` blocks inside such a conditional remain unsupported.

## Deferred collection operators — `defer` / `<<` / `<<=`

Deferred collection syntax initially produces `Defer`, `Feed`, and `Define` nodes. A defer binding
accepts any number of feeds or exactly one define; mixing the forms is an error. Feed and define
expressions have type `Unit`.

| CHL | Lowered role |
|---|---|
| `x = defer()` | Bind a `Defer` handle |
| `x << value` | Add a `Feed(x, value)` contribution |
| `x <<= value` | Add the sole `Define(x, value)` contribution |

`x = defer()` becomes `let x = defer in body`. A feed or define in statement position is sequenced
through `ExprStmt`. A top-level `requests, responses = http_serve(port, method, path)` instead
binds a registered request `Source` and a response `Defer`; the response binding is registered as
a sink for compilation.

### The `channelize` step (feed channelization)

`channelize::run` executes on the inferred and inlined tree immediately after `mut_elim`, before
`lambda_elim` and loop planning. `mut_elim` has already hoisted feeds from structured mutation
loops, so channelization handles them like feeds from other expressions. It eliminates `Defer`,
`Feed`, `Define`, and `ExprStmt` before downstream passes run.

For each cluster of consecutive defer bindings, channelization extracts its feeds or define from
the cluster body and builds a channel expression for each handle. Multiple feeds combine with
`Copair` (`++`), whose contributions occupy distinct index sets. Feeds inside iteration retain
their iteration context. A multi-arm feeding `Case` inside a loop produces a refined-source
channel for each feeding arm. A guarded feeding `Case` outside iteration can use a one-shot lift;
a scrutinee-pattern feeding `Case` there is rejected. The cluster becomes a mutually scoped
`Feed`-kind `LetRec`. Recognition later orders an acyclic group as `Let` bindings; an unguarded
cycle between channels is rejected.

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
[Feed handles as an invariant History constructor](type-inference.md#feed-handles-as-an-invariant-history-constructor-typehistory--kind-feed-).

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
`Option(T)` expands to the two-tag variant ``{`some{T} | `none}`` in type position; constructor
terms receive no special handling for those names.

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
Inference pins an otherwise unobservable payload type to a concrete required upper bound, then
to a type accepted by its uses, or to `Unit` if neither applies. Exhaustiveness applies from
scrutinee tags to arm tags; surplus arm tags are valid. The fan-out for a `match` inside a lambda
combines restrictions on the same domain with
`DisjointJoin`, as distinguished from `Copair` in
[ir.md](ir.md#copair-and-disjointjoin--two-collection-combining-operations-not-one).

### Scalar match encoding

A scalar `match` in value position compiles to a one-shot driver. Each tagged arm restricts that
driver through `variant_project(tag)`, evaluates its body on the surviving payload, and joins the
disjoint outputs. `final_or_default` extracts the resulting scalar. The scrutinee enters each arm
through `const(𝑠)`; it is not the input to the `iterate` driver, which accepts no input. The
corresponding scalar guarded `if` uses guard restrictions and first-match complements instead of
tag projections. A single tagged arm needs no union. `variant_project` takes its payload extent
from its own type, which is available even when the scrutinee cannot carry that tag.

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
`lower_type_expr`, and records the result in `LoweringContext::type_aliases`. A later type use
substitutes that `Type`; the alias statement emits no `Let`. An alias may refer to an earlier alias
in its block, but not to itself or a later alias. Built-in type names cannot be redefined, and a
name cannot be declared twice in one block.

`with_block_type_aliases` snapshots and restores the alias map around nested blocks. Top-level
recovery declares aliases directly and collects their errors so other statements can still be
checked; nested block lowering stops at the first alias error. The declaration scan precedes any
block-entry pass that lowers an annotation, including `pre_register_txn_decls`. This order lets a
transactional `Mut(Cents, Txn)` declaration resolve `Cents` before transaction registration.

## `pass` statements

`contributing_stmts` removes `pass` at each block entry, before the last value-producing
statement is selected. A value block containing only `pass` is rejected. A feed-only `for` body
with no other statement yields `unit`; a structured loop body or transaction block retains its
manufactured `unit` terminal. A transaction with no resulting footprint is rejected by its own
block rule. A trailing `pass` therefore leaves the shape of an otherwise contributing block
unchanged.
