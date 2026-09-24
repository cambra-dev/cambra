# CCL IR — the typed AST

CCL is the typed expression tree between CHL source and the dataflow operator graph. Lowering
constructs `TypedExpr` nodes, inference resolves their `Type` slots, and later passes transform the
tree before operator conversion. This document specifies the node vocabulary and the invariants
needed to read or transform it. See the [design index](README.md),
[lowering](lowering.md), [type inference](type-inference.md), and
[optimization](optimization.md) for the surrounding passes.

---

## Key design decisions

### Purity invariant: CCL is a pure value language

Every `TypedExprNode` denotes a value. Type inference, rewriting, and planning may duplicate or
reorder expressions; a node therefore cannot execute I/O or dispatch a sink as a pipeline effect.
`Defer` is a pure placeholder for a deferred output. `LoweringContext` records its sink binding,
and `compile_program` assembles the `SinkConsumer` at the program boundary. Source registrations
follow the same boundary rule. The [CCL invariant](../CLAUDE.md) applies to new node variants.

### Less normalized than ANF

Compound expressions may occur directly inside other expressions. `f(x + y)` can be represented as
`(x + y) ▷ f`; no `Let` is required between the addition and the application. `Let` names a value
when the lowering or a later pass needs a shared binding or a scope. The tree is less normalized
than strict A-normal form, leaving nested expression structure available to later rewrites.

### Structured names and α-uniquification (Barendregt convention)

`Name` distinguishes source spellings, minted binder identities, compiler binders, and references
inside dependent types (`ccl/names.rs`):

| Variant | Identity and use |
|---|---|
| `Raw(String)` | Source spelling before uniquification; lexical scope distinguishes equal spellings. |
| `Unique { base, uid }` | Source binder minted by `uniquify`; `uid` distinguishes binding sites, while `base` retains the source spelling. |
| `Synthetic { kind, uid }` | Compiler binder with a fresh `uid`; `kind` identifies its origin (`Pair`, `Mono`, `FloatedDefer`, or `SolverArg`). |
| `Reserved(ReservedName)` | Special name; the shared refinement-element binder is `__elem`. |
| `PiBound(PiRef)` | Bound reference in a function type's codomain; its de Bruijn index determines equality, while its spelling hint is display metadata. It is never a term binder. |

Lowering can produce two `Let` binders spelled `x` for successive source assignments. The
`uniquify` pass mints an identity for each source binding site and resolves bound uses according
to lexical scope. A reference to the second binder then differs from a reference to the first,
even though both display as `x`. `Unique` and `Synthetic` draw identifiers from the same fresh-id
space; a synthetic name records compiler origin rather than claiming a source declaration.

Structural comparison of copied, already-minted terms preserves binder identity. Independently
lowered α-equivalent terms can have different `uid`s and need not compare equal. Lowering therefore
uniquifies a comprehension source before copying it into a loop-join predicate. The whole-program
pass does not mint again at that copied binding site; several copied sites may carry one `uid`.
The checked invariant is that every binding site is minted, with copies retaining identity.

`Name::base()` is for display. Scope and identity checks use the variant and its fields, such as
`is_elem()` for the reserved refinement binder. Dependent function types close references to a
`PiBound` index; its hint can differ between references that compare equal. See
[type inference](type-inference.md) for the locally nameless refinement representation.

### Binding structure lives in one place

`ccl/scope.rs` defines term binding with `for_each_scoped_item`. It yields direct children with
their enclosing binders and yields the name occurrences made by the node itself. Free-variable
analysis and `Subst::rewrite_expr` use that walk. The scope rules are:

| Node | Binder scope |
|---|---|
| `Lambda` | `param` binds in `body`. |
| `Let`, `MutDecl` | `binding` binds in `body`; `bound_expr` or `init` is outside its scope. |
| `LetRec` | Every group binder binds in every definition and in `body`. |
| `For` | `target` binds in `body`; `iter` is outside its scope. |
| `Case` | A branch pattern's payload binder binds in that branch's `guard` and `body` only. |
| `Feed`, `Define`, `MutWrite` | `name` is a use of an enclosing binder. |
| `Transact` | Keys and writer footprints are history-record labels, not variable uses; the node binds nothing. |

`Binders` borrows binder slots without allocating a list and implements the `shadows` check for
each child. `Transact` labels are emitted as `KeyRef`, distinct from the `VarRef` occurrences that
free-variable analysis counts. A node's type slots and their refinement predicates require the
caller's type walk; the term-scope walk does not traverse them.

The immutable walk lists children in `TypedExpr::walk_children` order. It groups each binder's
children consecutively, so `for_each_scoped_item_mut` can announce a scope once and pair it with
the mutable child walk. Tests in `scope.rs` check child order, name occurrences, and agreement with
`TypedExpr::walk_binders`. The scope and binder enumerations are exhaustive over node variants;
adding a binding form requires declaring its scope and its binder slot. `uniquify` walks its own
mutable environment because it mints names before descending, but checks its result against
`walk_binders`.

`Subst` is simultaneous: a replacement is not substituted into another replacement during the
same application. `Subst::rewrite_expr` restricts mappings under binders that shadow their keys
and asserts that a replacement cannot be captured by a crossed binder. Its in-place discharge
keeps the replaced occurrence's root `NodeId` and freshens replacement interiors. Transport mode
(`Subst::apply_expr_inner`) constructs a new tree and records new node identities. Both modes
visit refinement predicates in type slots as well as expression children. A substitution may be
vacuous in the expression children yet still affect a predicate or a witness reference in a type.

### Source locations on substituted parameter projections

An ordinary multi-parameter `def f(p, q)` lowers to one lambda over a tuple parameter.
`uncurry_params` substitutes a projection for every use of `p` or `q`:

```
λ __arg_tuple_0 → __arg_tuple_0.0 + __arg_tuple_0.1
```

The original parameter has no `TypedBinding` in that shape. The outer `Apply` of the substituted
projection keeps the parameter occurrence's `NodeId` and source span. Its `Proj` child carries the
parameter declaration span from the substitution template. A definition lookup can therefore
distinguish the use site from the declaration. The test
`a_substituted_parameter_carries_occurrence_and_declaration_spans` checks both spans.

Replacing each parameter with an inner `let p = __arg_tuple_0.0` would put `p`'s binder inside the
lambda body. A refinement inferred for the lambda's codomain can refer to a parameter expression,
but the inner `Let` binder is out of scope in the lambda's own type. Substituting the tuple
projection keeps that refinement in the tuple binder's scope. This limitation is specific to the
ordinary tupled form: a multi-parameter function with a `Mut` parameter remains a chain of named
lambdas, because a mutable write needs a named target (`lower/functions.rs`).

### Application shape

`Apply` has one function child and one argument child; its symbolic form places the argument first:
`𝑎 ▷ 𝑓` means `𝑓(𝑎)`. A one-argument CHL call uses one `Apply`. An ordinary multi-argument call
`f(a, b)` packs `(a, b)` into one argument, matching the tupled parameter lambda. A call to a
function with a `Mut` parameter instead uses chained applications matching its named lambdas.

At the IR level, a curried application forms a chain: `𝑏 ▷ (𝑎 ▷ 𝑓)` has an outer application
whose function is the inner application. CHL call lowering currently requires a named target, so
the source spelling `f(a)(b)` is rejected. Curried functions that survive inlining may require a
`curry` combinator that operator conversion does not currently compile. The ordinary tupled
lowering avoids that form; see [lowering](lowering.md).

### Lambda/Apply encoding of collection iteration

Collection iteration uses ordinary function nodes in two lowering shapes. A single-generator
comprehension such as `[f(x) for x in xs]` builds an outer lambda over an iteration position:
`λ __iter_record → __iter_record ▷ xs ▷ (λ x → f(x))`. The first application reads the
source at that position; the second maps its element through the body. Multiple generators nest
those application and lambda pairs, with a product of source domains for the outer parameter. A
statement loop without the comprehension's index plumbing uses
`xs ≫ (λ x → body)` (`Expr::for_loop`, `lower/loops.rs`). Both forms use existing function
nodes; neither introduces a dedicated collection-iteration node. `lambda_elim` removes the
lambdas and produces point-free combinators; operator conversion builds the dataflow operators. See
[lambda elimination](optimization.md#lambda-elimination-ccllambda_elimrs) and the
[operational lowering model](/docs/operational-semantics/lowering.md).

### `MutDecl` — the mutable variable introduction

`x := init` introduces a mutable variable with `MutDecl { binding, init, body }`. The binder is
live only in `body`; the seed `init` is evaluated outside its scope. `MutWrite` names an existing
mutable variable and optionally carries a key for a keyed write. The mutability phases eliminate
these nodes into a causal `LetRec` or, for sequential positions, shadowing `Let`s.

`MutDecl` is the node that introduces a mutable variable in an expression body. A `Let` over a
mutable initializer binds the value read from it; `b = a` does not create a mutable alias. A
`Lambda` parameter may also bind a mutable history for pass-by-reference calls. This distinction
is structural and remains available after source annotations are cleared by inference. See
[mutability](mutability.md) for read and write rules.

### `Cast` — explicit refinement acquisition

`Cast { value, target }` attaches a refinement to a function's domain. Lowering constructs it for
comprehension filters, loop guards, and `groupby`. The emitted target has the shape
`{𝐷 | 𝑝} ⤇ 𝑉`, often with holes for 𝐷 and 𝑉.
The resolved type is written to the wrapping
expression's `ty`. Keeping `target` in the node lets type and predicate walks find it without
treating a call annotation as a hidden operand.

`emit_cast` decomposes the value as a function and rebuilds it with the target's domain
refinements and function kind. The result restricts where the function is used; it does not
establish that an arbitrary scalar satisfies a new predicate. An `Int` to `{𝑥: Int | 𝑝(𝑥)}`
conversion is a value-level narrowing and is outside this rule. The current implementation
honors function-domain refinements, not a general conversion to every supertype. Nested domain
refinements compose in the rebuilt domain. Planning uses the refinement for `Restrict`, while
operator conversion discards the `Cast` wrapper after the restriction is planned. See
[dependent refinements](type-inference.md#45-dependent-refinements-via-pi-types) and
[optimization](optimization.md).

`Realize(value)` has a different owner and obligation. Planning introduces it after inference
when it realizes a conditional collection's dependent-sum type as a gated collection over a
positional variant domain. The asserted type is the `Realize` node's own `ty`; the node has no
target field. The gated collection and the sum are not related by the ordinary `Cast` rule.
Operator conversion compiles `value` and drops the `Realize` wrapper. See
[conditional planning](optimization.md) for the realization step.

### `Case` only — no `IfThenElse`

`Case { scrutinee, branches }` represents `if`/`elif`/`else`, conditional expressions, and
variant matches. Each ordered `Branch` has an optional tag `pattern`, a Boolean `guard`, and a
`body`; the first matching pattern with a true guard wins. `if` and `elif` lower with no
scrutinee or patterns. An else arm has a true guard. A variant match supplies the scrutinee and
per-tag payload binders; a branch without a pattern is its default arm. A pattern-only branch
carries a literal true guard. See [variants and match](lowering.md#variants-and-match).

Inference constrains a pattern's payload binder from the matching scrutinee tag. With no default
arm, the match must cover the scrutinee's tags; a default arm permits other tags. Every guard must
have type `Bool`. Each body flows into one result type variable, so the result is the arms' join.
Different scalar types currently produce an incompatibility error. Data-collection arms at
different domains can coalesce to a dependent sum, while shared refinements can survive the join
(`infer::emit::emit_case`, `infer::solver::coalesce`).

### Other expression forms

The remaining nodes supply values or mark source structure for a later phase:

| Nodes | Contract |
|---|---|
| `Lit`, `Var`, `Builtin` | Literal, named reference, and compiler primitive reference. `Builtin` avoids magic variable spellings for combinators. |
| `BinOp`, `UnaryOp` | Typed scalar operations with expression operands. |
| `Tuple`, `Record`, `List` | Positional product, named product, and source list construction. Elements may be expressions. |
| `VariantCtor` | Tag and payload construction, dual to a `Case` pattern. |
| `Proj` | First-class tuple or record projection; applying it to a value gives field access. |
| `Compose` | Point-free function composition in application order, introduced by lambda elimination. |
| `ExprStmt` | Statement expression followed by its continuation. |
| `For`, `MutWrite`, `Begin` | Pre-phase loop, mutable write, and transaction-block structure; mutability phases consume them. |
| `Feed`, `Define`, `Defer` | Deferred-output write, definition, and placeholder; `channelize` resolves them. |
| `Error` | Recovery placeholder accompanied by lowering errors; compilation stops before inference. |

`Source` is specified under [source injection](#source-injection). `Realize`, `Transact`,
`LetRec`, and `Aggregate` have their own sections because their typing or phase ownership needs
more than a node description.

### `Copair` and `DisjointJoin` — two collection-combining operations, not one

`Copair` and `DisjointJoin` differ in result domain and definedness. Their types describe
different operations:

| Node | Input collections | Result domain | Definedness |
|---|---|---|---|
| `Copair` (`⊎`) | `𝐴 ⤇ 𝑉`, `𝐵 ⤇ 𝑉` | Positional sum `𝐴 + 𝐵` | Tags keep all positions distinct. |
| `DisjointJoin` (`⊔`) | Partial maps on one 𝐷 | The same 𝐷 | Operand positions must be disjoint. |

`Copair` is the collection operation behind `a ++ b`. `emit_copair` assigns each operand an
anonymous `FieldKey::Index` tag in a `Type::Variant` domain and joins their codomains. Thus
`xs ++ xs` retains both copies of every row. `TypedExpr::copair` flattens nested value-form
copairings at construction; a let-bound operand can still contain its own tagged domain. The
point-free `Builtin::Copair` form may arise when lambda elimination lifts an inside-lambda
value-form copairing.

`DisjointJoin` joins partial collections over one domain without adding tags. `lambda_elim`
introduces it for `Case` fan-outs whose first-match arms partition the fed input. Inference
requires a shared domain; the type does not itself prove positional disjointness. Operator
conversion uses the flat merge that relies on that property. A copairing of the same arms would
instead create a positional variant domain, which would not have the domain expected by a
consumer of the original input. The node distinction records the operation at construction
rather than inferring it from whether conversion received a fed input.

Without a fed input, operator conversion builds a tagged union for `Copair` and a flat union for
`DisjointJoin`. With a fed input, it supports the disjoint join and rejects `Copair`: tagged
demultiplexing and re-tagging of a fed copairing is not implemented. A union-domained generator
beside another generator can reach this rejection
(`a_union_generator_beside_a_second_generator` in
`tests/compilation_pipeline/scalars_collections.rs`).

### `Transact` — the domain-parameterized recurrence carrier

`Transact { keys, writers, domain }` is the recurrence carrier for mutable accumulation loops and
transactions. It denotes a record whose fields are key histories, each of type `𝐷 ⤇ 𝑉` over the
shared sequencing domain 𝐷. A read of key `k` projects `__hist.k`. Each `TransactKey` carries its
initial value, evaluated once outside the writer bodies. Each `WriterSite` carries an iteration
source, a point-free decision body, and read and write key lists. Its decision is either
`` `commit(writes) `` or `` `abort(unit) ``. The store's feedback and scheduling belong to
the compiled operator, while the node denotes the resulting history record.

`planning::plan_loops` constructs `Transact` from a recognized causal `LetRec` after lambda
elimination. An induction group has one writer with the accumulator footprint; a transaction
group can have multiple writers with separate read and write sets. Operator conversion selects
the position-driven induction store for a concrete iteration domain and the concurrent commit
store for `Type::Txn`. The node carries the domain so conversion can choose the engine without
reconstructing it from the writer expressions. See
[mutation loops](lowering.md#mutation-accumulation-loops)
and [loop planning](mutability.md#loop-planning-plan_loops-letrec-patterns--the-transact-carrier).

### `LetRec` — causal mutually recursive definition groups

`LetRec { bindings, body }` scopes every binder over every group definition and over `body`.
`mut_elim` and `transact_phase` turn mutable state into such groups. A history definition reads
strictly earlier positions through `get_prev_seq` or `get_prev_txn`; trailing reads use
`final_or_default`. Feed outputs can be carried through the group's decision record before
channelization gathers them. The symbolic form is
`letrec 𝑏₁ = 𝑒₁; …; 𝑏ₙ = 𝑒ₙ in body`.

`check_letrec_causal` rejects a cycle in the group's reference graph made entirely of
non-causal references. A guarded reference must occur in a previous-value accessor's history
slot; a reference in the accessor's position or default argument remains non-causal. The check
looks at value dependencies, including binder shadowing, rather than type-slot predicates.
`plan_loops` recognizes causal induction and transaction groups and produces `Transact`; it also
flattens acyclic channel groups into ordinary `Let`s. A raw `LetRec` reaching operator conversion
is unsupported. See [the history model](mutability.md#the-model-histories-and-causal-recursion)
and `ccl/letrec.rs`.

### `TypedExpr` — type slot on every node

Every expression is a `TypedExpr` with a `TypedExprNode`, a `ty` slot, an optional
`user_annotation`, and a `NodeId`. `TypedExpr::new` stamps a `Type::Hole`; inference replaces it
with a registered inference variable or a resolved type. `TypedBinding` carries a name, a `ty`
slot, and an optional source annotation. Inference checks annotations and clears both expression
and binder `user_annotation` slots before downstream passes. No persistent `declared` field exists;
the binder's resolved `ty` is the type at which references are bound. See
[the binder slot](type-inference.md#the-binder-slot-and-why-annotations-do-not-outlive-inference).

`NodeId` tracks provenance, not expression equality: `TypedExpr` comparison ignores it.
`Clone` freshens node identities, while `clone_preserving_ids` and `preserve` are explicit paths
for carrying an existing identity through a rebuild. A substitution's in-place replacement keeps
the occurrence root and freshens copied interiors. Passes that rebuild nodes must decide which
identities survive so the lowering projection can still attribute diagnostics; see
[provenance](provenance.md).

### Type vocabulary

`Type` contains both durable value types and temporary inference or phase markers. The main
durable forms are:

| Form | Meaning |
|---|---|
| `Base`, `UIntRange` | Scalar types and dense finite index domains. |
| `Fun` | A function `𝐴 ⇒ 𝐵` or data collection `𝐴 ⤇ 𝐵`; an optional named binder scopes over the codomain. |
| `Tuple`, `Record` | Positional and named products. |
| `Variant` | Tagged sum; source tags use `FieldKey::Name`, while anonymous positional sums use `FieldKey::Index`. `Openness` distinguishes a complete tag set from an open requirement. |
| `Refinement` | A base type restricted by a nonempty set of predicates; construction flattens nested refinements. |
| `DataSource`, `Txn` | An external source's nominal domain and the transaction sequencing domain. |
| `WitnessRef` | Reference to a dependent-sum witness; eliminated when the sum is consumed or realized. |

A data function can carry witness binders in its `FunKind`: for example,
`Σ (𝐷 : [𝐷₀, 𝐷₁]). 𝐷 ⤇ 𝑉` ranges over two possible collection domains. The witness reference
is durable through inference and planning; it is not an inference placeholder. Its binder range
is a `TypeKind`, separate from the `Type::Variant` used for tagged values. The positional
`Variant` used by `Copair` is thus a data domain, while the Σ records a choice of domain for one
collection. See [type inference](type-inference.md) for witness subtyping and consumption.

### Transient types and inference slots

| Form | Created for | Resolution |
|---|---|---|
| `Hole` | Unrelated unknown slots created by lowering and constructors. | Inference replaces each slot; a survivor is an error. |
| `SharedHole(id)` | Lowering positions that must share one inferred type. | Annotation normalization maps equal ids to one inference variable. |
| `BoundedHole(𝑇)` | An annotation slot constrained below 𝑇. | Annotation normalization creates an inference variable with an upper bound. |
| `Infer(var)` | Solver variable with level and bounds. | Coalescing resolves it where required; strict typecheck rejects a survivor. |
| `History` | Mutable or deferred-output handle over a domain. | Mutability phases or `channelize` erase it to a function type. |
| `ChanDom(name, level)` | Nominal domain of a defer channel. | `channelize` substitutes its assembled domain. |

`Hole` has no identity, while `SharedHole` links positions before inference. Neither is a value
type. `BoundedHole` is also an annotation obligation, not a union of all subtypes of its bound.
`Infer` may remain temporarily where a value has not been exercised; strict typecheck requires a
fully resolved tree before operator conversion. Lowering does not mint solver variables.

`History { domain, value, history_kind }` denotes a `domain ⤇ value` handle. `Overwrite` is a
mutable variable, rendered `Mut(value, domain)`: ordinary reads yield its value, and its phase
builds carry-forward histories. `Append` is a feed channel, rendered `feed(domain ⤇ value)`:
reads yield the whole collection, with no off-path carry. Both children are invariant in the
type relation. Lowering can construct histories for declarations and parameters, and inference
propagates them. `Type::feed`, `Type::mutable`, and `Type::history` own construction;
`Type::history` is the single constructor that fills the fields. Its argument order is
`(domain, value, kind)`, even though `Mut` displays the value first.

`History` has no function binder slot. A feed's value therefore cannot currently depend on its
own position, despite the arrow-shaped read view. `ChanDom` is minted when inference types a
defer binding; its introduction level lets specialization freshen a channel introduced inside a
generalized definition while retaining a captured outer channel. See
[`Mut` as a type](mutability.md#mut-is-a-ccl-type) and
[`Feed` as a type](mutability.md#feed-is-a-ccl-type).

---

## Aggregation

### `Aggregate` — first-class aggregation node

`Aggregate { input, kind }` identifies a fold independently of a function name. CHL `sum(xs)` and
`max(xs)` lower to this node. `OperatorSchemes::aggregate` supplies the whole input-to-output
type; `emit_aggregate` applies that scheme to the inferred input. A collection input has data
function type `𝐷 ⤇ 𝑉`. `Sum` requires `Int` elements and yields `Int`. `Max` yields the element
type and also requires `Comparable`. `Drain` consumes any element type and yields `Unit`; `Sole`
yields the element type and requires at most one input element at runtime. Operator conversion
dispatches by `AggregateKind`, without inspecting a call-site variable name.

`AggregateKind` also defines the output extent, seed, fold, and partiality. `Sum`, `Max`, and
`Drain` use total folds with an in-band identity. `Sole` has an `Option(𝐴)`-like accumulator:
empty is represented by an empty column, one element by a length-one column, and adding another
element faults. `is_partial` states that distinction, and `initial_accumulator` checks that the
seed representation agrees. The duplicate-key check for map construction uses this `Sole` law
(`ccl/aggregate.rs`).

---

## Source injection

`Source(name)` is a value reference to an externally registered data source. Lowering recognizes
registered zero-argument source calls and records the source name in the node. Inference gives it
a data function type with a nominal `DataSource(name)` domain and the registered element type.
Operator conversion resolves that domain to the registered source extent and reader.

`GlobalContext` coordinates the lowering, inference, and conversion registries. The lowering
registry makes names available while constructing the tree; `compile_program` registers sources
with inference and conversion after lowering has discovered them. The conversion registry
shares a materialized source extent across references to the same registered source. Sink
bindings remain outside the expression tree as described by the purity invariant.
