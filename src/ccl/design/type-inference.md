# Cambra's Inference Algorithm

Cambra infers CCL types with directional subtype constraints. This document specifies constraint
emission, bound propagation, type materialization, and the handling of polymorphism and refinements.
The [glossary](#7-glossary) defines the terms used in the implementation.

---

## 1. Algorithm Overview

The solver follows Lionel Parreaux's *Simple Essence of Algebraic Subtyping* (ICFP 2020): it
records subtype constraints as bounds on inference variables, then materializes types according to
polarity. Cambra's implementation supports structural records and variants, refinements, and
use-site specialization.
The paper's principal-type result does not establish that every accepted Cambra expression has a
representable principal `ccl::Type`.[^1] Incompatible untagged alternatives are rejected here.

Constraint emission traverses the CCL AST, writes a `ccl::Type` on each node, and relates produced
types to expected types. The notation `constrain(lhs, rhs)` means `lhs <: rhs`; the code calls
`constrain_subtype`. The solver works on `ccl::Type` itself. An unknown is `Type::Infer` with
shared, mutable bounds, not a separate internal type language (`infer/emit.rs`,
`infer/solver/constrain.rs`).

### Bounds and constraint propagation

The inference solver represents an unknown type with `Type::Infer(Rc<InferVar>)`. The shared
`InferVar` lets every occurrence refer to the same unknown. It has an identity (`uid`), a level,
and mutable lower and upper bounds, along with other inference state (`src/ccl/infer_var.rs`). In
the explanation below, `constrain(lhs, rhs)` is shorthand for the directional subtype requirement
`lhs <: rhs`; the implementation entry point is `constrain_subtype`, whose recursive engine is
`constrain_go` (`src/ccl/infer/solver/constrain.rs`).

A bound records one side of a subtype fact. A lower bound `L` on an unknown `α` means `L <: α`; an
upper bound `U` means `α <: U`. For example, when a type is required to fit an expected type, the
solver checks the subtype relation between the produced type and that expectation. If the expected
type is an inference variable, the produced type can become one of its lower bounds. If the
produced type is a variable and the expectation is concrete, the expectation can become one of its
upper bounds.

For ordinary compatible-level cases, adding a bound also checks the bounds already recorded on
that variable, so the new relation is propagated transitively. With a variable on the left, the
solver adds the right-hand type as an upper bound and recursively checks each existing lower bound
against it. Those lower bounds must also be subtypes of the new upper bound. With a variable on
the right, the solver adds the left-hand type as a lower bound and recursively checks it against
each existing upper bound. The new lower bound must satisfy every upper-bound requirement already
on the variable. This describes the principal bound-propagation work; dependent substitutions,
refinements, and other solver behavior are outside this schematic account.

When both sides are variables at the same level, the left-variable arm takes precedence. For
`v <: w`, it records `w` as an upper bound of `v`, then checks `v`'s existing lower bounds against
`w`. It does not immediately add the reciprocal type-bound edge to `w`. Later traversal of the
bounds graph during type compaction (`compact_type`) recovers transitive bounds. This same-level
case is not a rule for every variable pair: different levels may select another branch or require
extrusion and retry (`constrain_go` in `src/ccl/infer/solver/constrain.rs`).

Constraint-order independence is an intended property: applying the same constraint set in
different orders should either coalesce to equivalent variable types or reject in every order. The
particular constraint that reports failure may depend on order. The explicit bound updates and
later graph traversal are part of how the solver handles this property, but the algorithm
description alone does not establish it for all inputs.

Function-kind variables are separate from ordinary type inference variables. When two
function-kind variables meet, `constrain_fun_kind` records their relation on both variables.
Resolution follows the lower and upper kind relations, avoids revisiting nodes, and joins the
information encountered (`constrain_fun_kind` in `src/ccl/infer/solver/constrain.rs`;
`FunKindVar::resolved` in `src/ccl/ty.rs`). Deferring this join matters: copying only the pins known
when a relation is created can miss pins that arrive later or through another related variable.

The current kind information forms a lattice with `Unpinned` as bottom and `Conflict` as top.
`Compute` and `Data` are incomparable; `Data` is below `Plain` and each `Sum(n)`. `Plain` conflicts
with every `Sum(n)`, and sums with unequal arities conflict. Join is commutative, associative, and
idempotent. Resolution also incorporates information from constructed collection widths
(`built_over`), so following explicit kind relations is not its only input (`KindPin::join` and
`FunKindVar::resolved` in `src/ccl/ty.rs`).

#### Constraint-order checks

The order-independence fuzz test compares a baseline with eight shuffled orders for each of 2,000
generated constraint sets by default; `CAMBRA_FUZZ_N` configures the set count. This is evidence
from coverage, not a proof for all inputs (`solving_is_independent_of_constraint_arrival_order` in
`tests/constraint_order_fuzz.rs`). A separate test,
`a_shared_kind_var_resolves_the_same_way_in_every_order`, checks all 24 permutations of one
four-constraint case, demonstrating delayed kind propagation for that case rather than proving
the general property.

### Positions and Polarity

A **position** is a type's location within another type. A function domain and codomain are
positions, as is each record or tuple field. Its **polarity** is determined by the path from the
outermost type, which starts positive:

- A function codomain preserves polarity; its domain reverses it.
- Record and tuple fields preserve polarity.

In `(𝐴 ⇒ 𝐵) ⇒ 𝐶`, the path to `𝐴` crosses two domains.
Its polarity is positive. Polarity follows the whole path through nested functions.

Bounds have a union or intersection interpretation, but `ccl::Type` has no general untagged union
or intersection constructor. Compaction merges compatible shapes at each position:

- At a positive occurrence, compaction reads the variable's lower bounds. Compatible record bounds
  retain their common fields; variant bounds retain the tags either value may carry.
- At a negative occurrence, it reads upper bounds. Compatible record requirements combine their
  fields; variant requirements retain only tags acceptable to both consumers.

These are the polarity-selected contributions, not the complete materialization rule. At an entered
negative position, compaction also reads lower bounds, even when upper bounds already supply a
shape. The resulting type accounts for both supplied values and consumer requirements. See
[Coalescing](#coalescing-from-bounds-to-types) for the distinction from shape recovery.

The solver stores bounds instead of constructing union or intersection nodes. `compact_type` merges
their structural contributions, and `coalesce_compact` reports an `IncompatibleBounds` error if a
position contains incompatible concrete shapes such as `Int` and `String` (see
[Coalescing](#coalescing-from-bounds-to-types)).

### Levels, Schemes, and Let-Polymorphism

Levels distinguish variables local to a generalized function from variables captured from its
surrounding scope. A `PolyScheme` freshens the former at each use and preserves the latter.

Larger level numbers denote deeper inference scopes. Emission enters one level deeper for every
`let` right-hand side and every `MutDecl` initializer, then restores the surrounding level before
checking the body. The decision to generalize a `let` follows emission of its right-hand side;
it does not control that level increment (`in_let_rhs` in `infer/context.rs`, `infer/emit.rs`).

- Every inference variable records the level at which it was minted. A `PolyScheme` stores the
  binding's cutoff level. Instantiation freshens variables above that cutoff and preserves
  variables at or below it (`infer/solver/scheme.rs`).[^2]
- Bound recording cannot place a deeper variable directly on a shallower variable's bounds.
  **Extrusion** makes a proxy at the shallower level and relates it to the original with a
  polarity-appropriate bound (`infer/solver/constrain.rs`).

For a schematic `let id = λ x → x`, if `x` has type `α` above the binding cutoff, separate uses
receive independent copies such as `β ⇒ β` and `γ ⇒ γ`. See
[Let-Polymorphism is Freshening (Instantiation)](#31-let-polymorphism-is-freshening-instantiation)
for the binding and specialization rules.

### Coalescing: From Bounds to Types

**Coalescing** resolves the bound graph into `ccl::Type` using
`compact_type` → `simplify_type` → `coalesce_compact`. These functions are defined in
`infer/solver/`; `infer/solve.rs` sequences them. For each variable, compaction first traverses
bounds on the side selected by polarity:

- Positive occurrences read lower bounds.
- Negative occurrences read upper bounds.

The opposite side has two roles. Shape recovery can supply a shape when the polarity-selected
bounds leave the entered position undetermined. Separately, a negative position merges lower-bound
information with its upper-bound requirements whether or not shape recovery is needed. Within an
invariant position, that merge also applies when the walk reaches the variable through a bound
chain. `compact_type_polarity_only` disables both opposite-side reads. See
[The collapse happens at the position](#the-collapse-happens-at-the-position) and
[Invariant positions](#an-invariant-position-reads-both-sides-however-the-walk-reached-it).

An unresolved position can remain `Type::Infer`; a structural collision is an error.
Generalized definitions are materialized through their use-site specialization clones, which lets
the output tree carry monomorphic types. See
[Pass 2: Coalesce and Write-back](#pass-2-coalesce-and-write-back).

### Example: Bounding and Typing

The Python-like functions below are schematic constraint examples, not runnable CCL source. They
show where bounds arise and which results Cambra can materialize.

#### Incompatible lower bounds

```python
def get_status(is_ready):
    if is_ready:
        return 200     # Type: Int
    else:
        return "Wait"  # Type: String
```

The condition requires `is_ready: Bool`. If both branches feed one result variable `α`, the branch
constraints give it lower bounds `Int` and `String`. The schematic algebraic result is
`Bool ⇒ (Int ⊔ String)`. Cambra's `ccl::Type` has no such untagged union. Materializing the
positive result position reports `IncompatibleBounds` (`infer/solver/coalesce.rs`). A tagged
`Variant` can carry alternatives with a discriminator (see
[Information Flow and Type Mapping](#4-information-flow-and-type-mapping)).

#### Compatible upper bounds

```python
def extract_info(user):
    name = capitalize(user.name)  # capitalize() requires a String
    age = math_add(user.age, 1)   # math_add() requires an Int
    return name
```

Suppose `capitalize` requires `String` and `math_add` requires `Int`. The field uses impose record
requirements on the parameter variable `β`: schematically,
`β.upper = [{name: String}, {age: Int}]`. The parameter is negative in the function type, so
compaction combines these compatible upper bounds into a record with both fields. The schematic
result is `{name: String, age: Int} ⇒ String`. Name-keyed fields materialize as `Type::Record`
(`infer/solver/coalesce.rs`).

#### A generalized identity function

```python
def identity(x):
    return x
```

The body gives `x` and the result the same variable `α`, yielding `α ⇒ α` before a call
constrains it. If bound as a qualifying `let`, this type becomes a `PolyScheme`. Each use receives
a fresh instance. Coalescing creates a specialization for each distinct use-site instantiation and
shares one when the specialization key matches (`infer/context.rs`, `infer/solve.rs`). An unused
definition is still checked for errors before its specialization-free binding is removed (see
[Typechecking a never-called definition](#typechecking-a-never-called-definition)). A use whose type
remains unresolved can survive inference as `Type::Infer` and fail the strict post-inference check.
`ccl::Type` has no `Type::ForAll`; implicit generalization is represented by `PolyScheme`, not by a
first-class quantified type (`infer/solver/scheme.rs`).

### Roadmap and Current Prototype Status

A `let` whose RHS is a `Lambda` generalizes when its type contains variables above the binding
level and its function kind is not `Data` (`should_generalize` in `infer/context.rs`). Each use
instantiates the scheme. During coalescing, `specialize_use` freshens a copy of the definition,
pins it against the use's live type, and coalesces the copy. A `SpecKey` identifies uses that can
share one specialization; the resolved type alone is not the key (see
[Keying a specialization](#keying-a-specialization)). A collection-valued binding is not
generalized (see
[Generalizing a collection is filter pushdown](#generalizing-a-collection-is-filter-pushdown)).

Exact `𝑥 : 𝑇` and bounded `𝑥 <: 𝑇` annotations apply to `let` and function parameters.
A bounded annotation becomes a fresh inference variable with an upper bound. The
`normalize_annotation` step erases the pre-inference `Type::BoundedHole` marker (see
[Annotation kinds: exact and bounded](#annotation-kinds-exact-and-bounded)).

Structural variants represent tagged alternatives, including named and positional sums. The
solver handles their subtype relations and pattern-match requirements (see
[Information Flow and Type Mapping](#4-information-flow-and-type-mapping)). Refinements also remain
on the lattice: structural predicate equality matches them, and `smt_sub` can discharge a remaining
entailment requirement within its supported fragment (see
[Semantic entailment as a fallback](#semantic-entailment-as-a-fallback)). A function type may carry
an optional Pi binder, allowing a result refinement to refer to its argument. Dependent
application discharges that binder; group-by lookup uses this mechanism (see
[Dependent refinements via Pi types](#45-dependent-refinements-via-pi-types)).

Trait obligations for operators are implemented. Operator signatures state requirements such as
`Addable` and `Comparable`. The inference solver narrows base-type candidate instances before
materialization; `Equatable` additionally handles tuple and record equality componentwise (see
[A product is answered off the table](#a-product-is-answered-off-the-table)). This is separate from
a general nominal-type system (`infer/schemes.rs`, `infer/solver/traits.rs`).

`ccl::Type` has no first-class explicit `∀` type. The SMT fallback handles linear integer
arithmetic over supported `Int`/`Bool` predicate forms. Both inference and `inline` use `smt_sub`;
inlining uses it to check a refined parameter's precondition before beta-reduction. A predicate
it cannot encode falls back to the structural mismatch, and point-free predicates after
`lambda_elim` do not reach that fallback
(`infer/solver/smt.rs`, `infer/solver/constrain.rs`). These are limits of the implemented paths,
not additional inference passes.
Post-planning checks use structural predicate equality; supporting semantic entailment there
requires an SMT encoding for the point-free forms.

---

## 2. The Inference Pipeline

Inference emits constraints, materializes types while specializing generalized definitions, and
strips redundant refinements from predicate interiors. These are the three passes described below.
Binder-slot resolution and specialization run inside the second pass, not as later repair passes.

The entry points are `infer` in `infer/api.rs` and `run` in `infer/mod.rs`. Their order is:

1. Normalize registered source types and emit constraints onto the expression tree.
2. Resolve the operand requirements accumulated during emission. This sweep runs before
   materialization, while generalized definitions and their variables remain available for blame.
3. Run `coalesce_pass`, including binder-slot resolution and specialization.
4. Run `strip_predicate_interiors`.
5. In debug builds, check term-variable scope validity and the absence of free witnesses.
6. On success, clear expression and binder annotations. On failure, retain annotations for
   diagnostics.

Emission returns at its first error. Coalescing can accumulate multiple errors and returns before
predicate stripping if it finds any. The requirement sweep also has debug checks around it:
`verify_narrowing_is_complete` audits eager narrowing, and `seal_emission` marks the end of
definition-obligation narrowing. See [Requirements are read together, once](#requirements-are-read-together-once).

### Pass 1: Constraint Emission

`emit_node` in `infer/emit.rs` traverses the expression tree, emits constraints through
`InferCtx`, and stores the emitted type in each node's `expr.ty`. Annotation normalization
replaces holes with inference variables and retains refinement wrappers. The normalized solver
type is distinct from the original `user_annotation`, which remains available until successful
inference consumes it.

A stored `Type::Infer` refers to a shared `Rc<InferVar>`. Constraints added later are therefore
visible through types already stored on other nodes. The AST slots refer to the live bound graph;
they are not snapshots of its bounds.

The structural rules are generic over `Typing`. For example, `emit_lambda` binds the parameter
while checking its body, and `emit_apply` checks the argument and function before calling the
context's application rule. The context determines whether an obligation adds constraints or
checks a recorded result. See [The post-inference check](#the-post-inference-check-shared-rules).

For ordinary compute functions, subtyping reverses the domain relation and preserves the codomain
relation. Record subtyping requires the producer to supply every demanded field. Inference-variable
arms record a bound and propagate it against the opposite bound list. These are distinct from data
domain invariance and history invariance; a generic contravariant-function rule does not describe
every function kind. See [Bounds and constraint propagation](#bounds-and-constraint-propagation)
and [Data domains are invariant](#data-domains-are-invariant).

#### Apply is one-way

The ordinary application rule emits a function-shape constraint and an argument constraint:

```text
fn_ty <: (x: domain) ⇒ codomain
arg_ty <: domain
```

This is schematic compute-function notation. `InferCtx::apply` also carries function-kind
information and discharges the dependent result binder to the argument term. Mutable
pass-by-reference arguments and checked lookup have additional rules in `emit_apply`; the two
edges above are not a complete specification of those cases.

The rule does not emit a reverse `domain <: arg_ty` edge to determine a projection's width.
A projection such as `.0` imposes a requirement on one field, not a closed arity. Its emitted
tuple requirement is a dense prefix with fresh fillers before the selected field
(`proj_requirement`), because `Type::Tuple` has no sparse, minimum-arity form.

Projection width is supplied during coalescing, not by reversing the application constraint.
See [Closing the single-sided blind spots](#closing-the-single-sided-blind-spots-no-separate-pass)
for direct projections and [Binder-slot resolution](#binder-slot-resolution) for lambda parameters.

### Pass 2: Coalesce and Write-back

`coalesce_node` in `infer/solve.rs` resolves children and then the enclosing expression.
The walk also fills binder slots, visits predicates embedded in types, and replaces generalized
bindings with their demanded specializations. Application order follows the
[read-stability contract](#coalesce-ordering-and-read-stability).

`resolve_var_type` runs three solver functions:

```text
compact_type → simplify_type → coalesce_compact
```

These functions live under `infer/solver/`; `infer/solve.rs` sequences them. A result need not
be fully determined: unresolved positions can remain fresh `Type::Infer` placeholders.
Materialization is not itself a guarantee that strict downstream type checking will accept the tree.

#### Compaction

`compact_type` follows inference-variable bounds and combines the contributions at each type
position into a `CompactType`. A `CompactGraph` contains the root contribution and a map for
recursive-variable definitions. Contributions include variable identities, atoms, product and
variant shapes, function and history shapes, refinements, and kind information.

Polarity selects the primary bound list: lower bounds at a positive occurrence, upper bounds at
a negative one. Function domains reverse polarity; codomains preserve it. Compatible record
contributions retain common fields in a positive merge and combine required fields in a negative
merge. This describes the shape merge, not an explicit union or intersection type in `ccl::Type`.

The walk also reads opposite-side bounds under two separate rules: position-local shape recovery
and negative-position merging. A negative position can merge lower bounds even when its upper
bounds already provide a shape. See [The collapse happens at the position](#the-collapse-happens-at-the-position).

Generalized definitions follow the [specialization lifecycle](#specialization-scope-and-lifecycle),
including the separate [diagnostic walk for unused definitions](#typechecking-a-never-called-definition).

#### Simplification

`simplify_type` analyzes variable co-occurrence in the compact graph and rewrites variable
identities. It applies three rules:

1. Eliminate a non-recursive variable that occurs at only one polarity.
2. Merge variables that co-occur symmetrically. Recursive and non-recursive variables are not merged
   with one another.
3. Eliminate a variable absorbed by the same concrete atom at both polarities.

These operations remove or replace variable contributions, not whole type positions. Concrete
structure remains after a variable is removed; a position with no remaining structure can
materialize as `Infer`. The rules run on ordinary monomorphic types and the instantiated types
of generalized definitions.

The analysis reads the variable sets produced by compaction. A negative-position merge includes
identities from both bound directions, so its co-occurrence set is not just the set of variables
visible in the final rendered type. Refinements belong to positions, not variable identities;
`simplify_reconstruct` retains them while changing the variable sets.

#### Materialization outcomes

`coalesce_compact` converts structural contributions into `ccl::Type`. It does not expose the
original bound-graph variable identities as output type variables.

| Contributions at a position | Result |
| --- | --- |
| No concrete shape | A fresh `Type::Infer` placeholder |
| One compatible shape | The corresponding concrete type, with materialized children |
| Distinct incompatible shapes, such as `Int` and `String` | `IncompatibleBounds` |
| A tagged variant shape | `Type::Variant`, retaining its tags rather than treating them as an untagged collision |

Product materialization in `materialize_record` additionally distinguishes field keys:

- Dense index keys produce `Type::Tuple`.
- Name keys produce `Type::Record`; open versus closed named width is not represented at this layer.
- Sparse index keys leave a fresh `Infer`. Their children are still visited before the shape is
  discarded, so nested materialization errors are not skipped.
- Mixed index and name keys produce `UnresolvedPartial`.

The solver does not invent an untagged sum to resolve incompatible concrete shapes.

### Closing the single-sided blind spots (no separate pass)

Projection-domain specialization and binder-slot resolution are operations within
`coalesce_node`. They are not reverse constraints inserted during emission or a post-inference
saturation pass.

A projection requirement can omit fields that exist in its input. Resolving that requirement alone
does not recover those fields. After the children resolve, `specialize_projection_domain` rebuilds
a direct `Proj` function type from the resolved input and its existing codomain:

- In `Apply`, the input is the resolved argument.
- In `Compose`, the input is the preceding morphism's codomain. The walk also rebuilds the
  composition's type from its endpoint morphisms.
- In cast targets and other type slots, `coalesce_type_predicates` reaches these same rules.

The helper applies only to `Proj` nodes. A function hidden behind a `Var` does not acquire a
projection domain through it; generalized bindings use
[specialization](#31-let-polymorphism-is-freshening-instantiation). A lambda's domain instead carries
argument lower bounds and body-demand upper bounds. Negative-position compaction reads both;
[binder-slot resolution](#binder-slot-resolution) then refreshes its parameter from that domain.

Using resolved inputs here avoids tying width recovery to a particular emit-time inference
variable. Freshening a generalized definition creates new variables, whereas the specialized
projection still has the resolved input at its own use site.

A bare domain variable is not the same problem as a structured projection requirement. Compaction
can recover a bare variable from its bounds. A projection's untouched fields may have no relevant
bounds at all, so its complete input shape must come from the expression using it.

#### The collapse happens at the position

`compact_go` can use opposite-side bounds to determine a position whose primary bounds do not
determine a shape. `fallback_allowed` permits this only when collapse is enabled and the walk
entered the variable as a structural position, rather than following another variable's bound
chain. Each structural child starts a new position.

This recovery chooses a materialized type; it is not an additional subtype judgment. From
`L <: c` and `a <: c`, no relation between `L` and `a` follows. Reading `c`'s opposite
side while traversing `a`'s bounds would otherwise attribute another use's information to `a`.

Shape determination treats variants differently at the two polarities:

- At a positive position, a variant contribution records the producer's tags. It counts as a
  concrete shape, so fallback does not replace it with an upper-bound demand.
- At a negative position, upper-bound variant tags describe the arms a body handles. That does
  not determine the tags of the incoming value, so the opposite-side read can still supply them.
- Atom, record, function, and history contributions count as shapes without this variant-specific
  distinction. Variable identities, refinements, and kind information do not by themselves supply
  the concrete shape tested by this condition.

A negative entered position also merges the opposite side when its primary bounds already
determine a shape. `compact_go` first traverses and combines opposite-side bounds at their own
polarity. It then either uses the recovered shape for an undetermined position or merges the
recovered contribution with the primary one at the position's polarity.

For example, a grouping key can have singleton `Int@1` below it and `Int` above it. Reading the
demand alone loses the singleton. The negative-position merge retains the contribution needed for
the invariant data domain. Tests include `a_negative_position_meets_both_sides` in
`infer/solver/compact.rs` and `a_groupby_over_a_singleton_element_literal` in
`tests/compilation_pipeline/joins_aggregates_groupby.rs`.

This resolves one position. Relating two spellings of an invariant domain is a separate constraint;
see [A shared hole naming a domain states an equation](#a-shared-hole-naming-a-domain-states-an-equation).

For an open variant demand nested under a structural child, the negative merge intersects tags and
combines openness through `CompactVariant::meet_openness`. A closed producer can therefore close
the demand's marker while unnamed producer tags are removed from this materialized view. This is
the documented approximation, not an exact representation of open-variant intersection.
`a_settled_negative_position_closes_an_open_child_demand` checks the reading.
`test_default_arm_under_a_record_field` checks the default-arm execution, which is compiled from
the `Case` rather than inferred from that narrowed view.

`compact_type_polarity_only` disables both opposite-side rules. It answers which information
arrived along the selected bound direction, without resolving an uninhabited position from its
demands. [Unobservable-arm payload pinning](#an-unobservable-arm-payload-is-pinned-to-what-its-uses-require)
needs that distinction: an unreachable arm can acquire upper-bound requirements without receiving
a value.

##### An invariant position reads both sides however the walk reached it

Inside an invariant position, negative merging also applies to variables reached through bound
chains. Shape recovery remains position-local. The merge condition in `compact_go` is:

```rust
let merge = !pol && (allow_fallback || (st.collapse && pos.invariant));
```

Without the invariant exception, the same domain can resolve differently depending on whether the
walk entered it structurally or followed a bound to it. Invariance then rejects two readings of
what should be one domain.

A mutable map seeded with one entry exercises this case. Its key has a singleton type, and the
`box` scheme shares a variable between its domain and its sole sum candidate. Following the
resulting chain must retain the same key-domain information as entering the position directly.
The regression cases include `a_one_entry_seed_reads_as_a_map` and the related keyed-write tests.

The exception does not enable negative merging along every bound chain. An unrestricted read
would revisit nested types more often and would also reach compute-function parameter domains.
The higher-order dependent-application case can present data domains whose predicates differ
only in the spelling of a discharged binder. Structural refinement comparison does not identify
those spellings. See `higher_order_dependent_application_discharges_the_binder` in
`tests/type_check.rs`.

##### Compaction traversal cost

`CompactState::in_process` prevents recursive re-entry while a variable is being visited; it is
not a cache of completed results. The entry is removed when that visit returns. Reaching a
position again can therefore repeat compaction, and each structural child can enable a new
opposite-side read.

A result memo keyed only by variable identity and polarity would omit relevant inputs:
`subst_acc` composes the substitutions on the path, and `st.scope` records the refinement
scope. Reusing a result across different substitutions or scopes would conflate distinct readings.
No such compaction result memo is implemented here. Memoization or interning would require its
own correctness and performance checks; the traversal cost alone does not establish a safe key.

#### Binder-slot resolution

Binder types are not expression-node types. Resolving every `expr.ty` does not resolve a
lambda parameter, let binding, match payload, or loop target automatically.

`coalesce_node` handles those slots explicitly:

- `refresh_lambda_param_slot` derives a lambda's `param.ty` from its coalesced domain.
  This preserves refinements read in the domain's negative position. The helper uses
  `Type::domain`, including sum-typed functions.
- `resolve_binder_slot` resolves a let or mutable binding, match payload, or loop target in
  place, then coalesces the predicates carried by the resulting type.
- The visitor also handles `LetRec` slots, but the ordinary pipeline creates recurrence
  carriers after inference. Their presence in the visitor is not a claim that normal inference
  receives planned `LetRec` or `Transact` nodes.

A slot is not filled by copying the RHS type. An unannotated ordinary let can agree with its RHS,
but a dereferenced copy binds a value while its RHS is a history handle, and a mutable declaration
binds a handle while its initializer is a value. `resolve_binder_slot` preserves the emitted
binding rule.

Resolving structure alone is insufficient. Predicates carried by a binder type have their own
expression type slots, so `coalesce_type_predicates` must visit them too. A skipped slot retains
its pre-coalesce predicate allocation and unresolved interior types. A value binding exposes this
directly because no later specialization rebuilds its definition. Grouping values and matches
over conditionally constructed collections exercise that path.

Monomorphic variable uses share their binder's inference variables; they do not need a lexical
lookup merely to read those bounds. Generalized uses do require the specialization scope, and
lambda-parameter domain refresh is a separate operation. Slot resolution uses the type stored on
the binder; specialization still needs its lexical scope.

### Pass 3: Stripping Predicate Interiors

`strip_predicate_interiors` in `infer/strip.rs` removes refinements from expression and binder
types inside a refinement predicate. It runs after successful coalescing and before the debug
scope check.

A predicate is an expression tree whose nodes carry types. Arithmetic within it can acquire a
refinement that repeats part of the enclosing predicate. For example, an interior `1 ^+ 3`
can carry its own sum refinement while the outer predicate states `__elem == 1 ^+ 3 ^+ 2`.
A discharge that updates the outer predicate can leave an interior copy naming a binder that has
gone out of scope. The stripping pass removes that redundant copy rather than relying on both
representations remaining synchronized.

The pass has two exceptions:

- Refinements on a data function's data domain retain their predicate interiors. Planning compiles
  those predicates into iteration or restriction, and operator conversion reads the interior
  types. `compiled_refinements` collects the exempt refinements before rewriting.
- A `Cast` target remains intact. It is an operand that specifies the cast, not just metadata
  describing the result; comprehension filters are read from it.

Exemptions are matched by `Refinement`'s structural equality, not a type-slot location or
predicate address. One filter can occur in a source, map, cast, and consumer contract. Exempting it
at one occurrence and rebuilding it at another would retain two equal terms at different
allocations. The sharing tests cover that failure shape.

Stripping does not establish that all later substitutions descend correctly into predicate type
slots. It removes redundant interiors at this point in the pipeline. The remaining scope and
sharing checks have separate responsibilities.

### The post-inference check (shared rules)

The compiler runs inference before its transformation passes and checks recorded types again at
later boundaries, including inlining, lambda elimination, and planning. The checks do not run a
second inference pass.

The structural expression rules in `infer/emit.rs` are generic over the `Typing` trait.
Two contexts implement their operations:

| Context | Child types and obligations |
| --- | --- |
| `InferCtx` | Recursively emits children, creates inference variables, instantiates schemes, and records subtype constraints |
| `CheckCtx` | Reads already-recorded child types, checks the required relations, and reconciles a reconstructed result with the node's recorded type |

Sharing those rules keeps application decomposition, composition adjacency, and product
construction consistent between inference and checking. It does not mean every context hook has
the same implementation. In particular, inference can suspend dependent discharge over live
variables, whereas checking works with recorded types.

The post-inference checks retain refinements in both relation checks and reconciliation.
They do not justify a transformation by erasing its predicates first. A pass that introduces a
refined type must leave the node reconstructable under the checking rules; see
[Refinements on the lattice](#refinements-on-the-lattice).

Post-planning checks use structural predicate equality. Semantic entailment at that stage requires
an SMT encoding for point-free expressions.

---

## 3. Specialization and Predicate Ownership

Generalization creates fresh bound-graph instances at uses. Coalescing specializes definitions
using those live instances, and predicate-rebuild memos preserve sharing where the rewrite context
permits it. These operations have separate scopes and lifetimes.

### 3.1 Let-Polymorphism is Freshening (Instantiation)

`should_generalize` in `infer/context.rs` selects a syntactic lambda whose function kind is
not `Data` and whose type contains a variable above the enclosing level. A non-function value
or a function with no quantifiable variable remains monomorphic. There is no use-count exception
or separate eligibility rule for collection-producing UDFs.

Every let RHS is emitted one level deeper, whether or not it is generalized. A `PolyScheme`
records the cutoff level. Instantiation freshens variables above that cutoff and preserves
captured variables at or below it. Each generalized `Var` use receives its own instantiation
during emission.

Later compiler passes consume monomorphic expressions. `coalesce_node` therefore specializes a
generalized binding when it reaches a use, rather than leaving a universal type for later passes.

#### Specialization scope and lifecycle

`CoalesceCtx::scope` contains a `SpecializeFrame` for each in-scope generalized let and shadow
markers for other binders. `lookup_generalized` searches inward to outward, stopping at a shadow
of the same name. A frame retains the original definition until its body's walk is complete.

`specialize_use` performs these operations:

1. Mark the frame `demanded` before any operation that can fail.
2. Resolve the use's instantiation for structural checks and channel-domain pairing.
3. Compute its `SpecKey` from the still-live type before this use's pin.
4. On a memo hit, rename the use to the existing specialization and copy its resolved type.
   A surviving use also marks a previously unreferenced specialization as referenced.
5. On a miss, clone the definition and freshen its type slots with levels preserved.
   `seed_chan_dom_pairings` aligns rigid channel-domain names with the use before freshening;
   a two-way subtype pin cannot equate two different rigid names.
6. Pin the clone and live use type in both directions, using a fresh `ConstrainCache`.
   Pin errors are reported at the use site.
7. Coalesce the clone in the definition site's scope, then restore the use site's scope.
8. Rename the use to `Name::mono`, stamp the clone's resolved type, and register the clone under
   the pre-pin key.

Freshening reaches node types, binder slots, refinement-predicate slots, and substitution payloads
on copied bound edges. It must not leave the clone's quantified interior variables attached to the
original definition's inference state.

The re-entrant clone walk suspends entries at and above the definition's frame. A binder introduced
between definition and use cannot capture the clone's references. The frame itself is suspended
because CCL lets are non-recursive; a same-named outer binding remains visible to the definition.
Nested generalized bindings push their own frames during the clone's walk.

`Name::mono` carries the source binding and a fresh uid. When the enclosing body finishes,
`coalesce_generalized_let` rebuilds it as a chain of referenced specializations. Each layer
discharges its binder from the body's result type when that name is free in the result's
refinements. See [`let` binders and scope exit](#let-binders-and-scope-exit).

The original definition is not coalesced in place while its uses need clones. Its quantified
variables carry the bounds copied into each specialization; overwriting them would remove that
input. A never-demanded definition takes the
[diagnostic-only path](#typechecking-a-never-called-definition).

A memo hit is not pinned again. A miss pins a variable-bearing clone, whereas a hit contains
already materialized types. Constraining that concrete result against another live use is a
stronger operation and can reject a use whose own clone would have coalesced compatibly.
A separate non-recording subsumption check is not implemented for this purpose.

#### Coalesce ordering and read stability

Specialization runs during coalescing so that parents consume specialized child types on their
first visit. Dependent application can discharge against the clone's resolved predicates without
a second post-coalesce reconstruction. The use's `expr.ty` must still expose its live bound graph
for keying and pinning; materializing that slot first would overwrite it. A generalized definition
calling another generalized definition follows the same recursive walk; the outer clone is pinned
before its body reaches the inner use.

The live graph is not frozen after emission. Pins can add bounds during specialization.
`Apply` coalesces its function before its argument so that the function's specialization can
deposit demands before the argument is read.

The ordering invariant requires specialization not to invalidate types already read by the walk.
Debug builds log `ReadRecord` snapshots that retain the live variables and their resolved
results. At the end of a successful coalesce pass, `assert_reads_stable` resolves them against
the final graph.

The comparison is bounded:

- It checks structural shape, bases, ranges, and other materialized structure.
- Stamped reads also compare refinement-wrapper depth, not the number of predicates in each set.
- Underdetermined positions are wildcards; fresh `Infer` identities cannot be compared across
  resolutions.
- It does not compare predicate contents as a proof of semantic equality. Scope validity and the
  post-inference reconciliation checks cover different obligations.
- `ReadPurpose::Instantiation` excludes refinement-wrapper depth. That preliminary resolution serves
  channel-domain pairing and error reporting, not the use's final stamped type or its
  specialization key. The base structure is still checked.

The check is debug-only. The compilation strategy relies on the ordering invariant in all builds.

#### Typechecking a never-called definition

A generalized definition with no demand is checked before being dropped.
`typecheck_discarded_definition` coalesces it in its definition-site scope and retains diagnostics,
not its resolved expression.

Emission already visits the body. It can reject a conflict with a concrete type immediately.
Other errors require reading several bounds together: `λ a → (a.0, a.foo)` demands both a tuple
and a named record from one parameter. Resolving the unused definition detects that conflict even
without a call site.

An unused definition can retain unresolved positions because no use supplies their types.
That residue is tolerated during inference and disappears with the discarded subtree; it is not
evidence that a surviving unresolved function can pass strict compilation checks.

Calls from discarded code are checked too. They can specialize an outer generalized binding to
test the callee's demands against the arguments. Those specializations remain registered for memo
reuse, but they are not spliced into a surviving outer let unless a surviving use references them.

Three frame fields distinguish these decisions:

| Field | Meaning |
| --- | --- |
| `demanded` | A use reached `specialize_use`, even if resolving it later failed |
| `Specialization::referenced` | The specialization must be retained when its let is rebuilt |
| `inside_discarded` | The frame was created inside a subtree that will itself be discarded |

An empty specialization list does not establish deadness: a failed use can mark a demand without
creating a clone. Rechecking its definition as dead code would duplicate diagnostics.
Discarded uses do register clones; registration and splice liveness are separate.

`inside_discarded` is a property recorded when the frame is created, not a saved scope depth.
The re-entrant specialization walk truncates the scope stack, so a depth comparison would
misclassify frames pushed inside a discarded clone.

The dead-definition walk runs in release builds too. Nested dead definitions are checked once per
specialization of their enclosing live definition because their types can depend on that
specialization. Repeated diagnostics are deduplicated. Memo registration avoids cloning an outer
callee independently for every dead use, but it does not remove the general specialization-growth
problem.

A failed use that returns before renaming can still refer to a binding dropped during the let
rebuild. No pass reads that tree: `run_frontend` in `ccl/context.rs` resolves each inference
error's blame node to a source span and then discards the tree. The fix is to replace the failed
use with `TypedExprNode::Error`, keeping its `NodeId`, and to widen that node's contract from
pending lowering errors to pending lowering or inference errors. The contract records how the node
is used today. Its guarantee is that no pass running on an error-free tree meets the node, and a
failed inference run keeps that guarantee.

Trait requirements need an additional check. Eager obligation narrowing depends on concrete
types arriving, so resolving an unused definition alone does not establish satisfiability of all
its operand requirements. The pre-coalesce
[requirement sweep](#requirements-are-read-together-once) reads them together.

A conditional over a collection parameter illustrates the distinction between a requirement and a
concrete conflict. In a body shaped like `if p: [x for x in xs if q] else: xs`, both domain
spellings can refer to the same variable and record the filter as a requirement on the parameter.
A concrete call can expose incompatible domain alternatives and be rejected. Over a literal or
source collection, the domains are already concrete in the definition, so the same conflict need
not wait for a call. See [The domain join needs `box`](#the-domain-join-needs-box).

Regression coverage is in `tests/type_check.rs` and `infer/solve.rs`, including
`a_dead_definitions_calls_splice_no_specialization`,
`a_suppressed_specialization_does_not_get_its_definition_re_walked`, and
`one_defect_does_not_multiply_by_the_enclosing_specialization_count`.

#### Keying a specialization

`SpecKey` in `infer/solver/spec_key.rs` determines whether two uses share a specialization.
It is computed from the live instantiation type before that use's pin. A memo entry stores the
key of the use that created it, not a key recomputed from the finished clone.

Both sides of a comparison are computed by one procedure at one point in the pin's lifecycle.
A clone's coalesced type is the pin's output, and a candidate's key is the pin's input. For a
definition whose clone type gains a refinement across the pin, a key read from the clone never
equals a candidate's key, so a memo keyed that way is write-only and identical call sites each
mint a clone (`identical_instantiations_share_one_specialization` in `infer/solve.rs`).

A materialized `Type` is not the key. Compaction selects and merges contributions to produce one
type; specialization must distinguish the bound directions that affect the clone. A domain is a
negative position, so its materialized type reads upper bounds, the definition body's demands. It
drops positions the body never reads, and it omits an argument's refinement, which arrives as a
lower bound through the `arg <: domain` edge. A clone's interior reads its parameter at a positive
position and sees those refinements. In particular, the key's directed reads are not ordinary
negative-position compaction with its opposite-side merge.

`spec_key` takes two reads of the root and keeps them separate:

| Root read | Function domain | Function codomain |
| --- | --- | --- |
| Positive | Upper-bound requirements | Lower-bound contributions |
| Negative | Lower-bound contributions from arguments | Upper-bound requirements from consumers |

Each read follows the bound list selected by its current polarity. It does not follow both lists at
every variable. The two reads flip in lockstep, so at the root's immediate positions every bound
list is consulted by one of them. Deeper paths diverge: a variable reached only through a lower
bound is visited only by the read that arrived there, at that read's polarity, and its other bound
list is read by neither. The clone's own resolution reads that position from the same side, so a
bound the key does not see is one the clone does not see either. The guarantee is agreement with
the pin, not coverage of the whole bound graph.

Combining the two views into one would lose the direction in which information arrived.
Traversing both bound lists at every variable can instead reach shared graph components belonging
to unrelated uses.

Within a directed read, `KeyView::union` accumulates contributions without polarity-dependent
narrowing. A key that narrows can only under-split, and under-splitting is a miscompile, while
over-splitting costs one redundant clone. Keying on a materialized type narrows this way:
`λ a, b → a + b` at `(1, 2)` and `(1, 5)` both keyed on `((1, Int) ⇒ Int)`, and the shared
clone typed `.1` as `2`. Undetermined positions use a canonical empty view, not a fresh
placeholder identity. Conflicting contributions can coexist in a key; ordinary resolution, not the
key, reports type conflicts. Refinement comparisons are type-blind and compare sets rather than
insertion order.

The key also preserves distinctions needed by code generation, including function kind, history
kind, and witness/kind shape. It does not use fresh inference-variable identities as a substitute
for those distinctions.

`key_go` has a cycle guard and a completed-result memo. The memo includes variable identity,
polarity, and enclosing binders, and is used only with an identity accumulated substitution.
A result whose walk cut a cycle is not cached. This memo belongs to one `spec_key` calculation;
it is distinct from the specialization list stored on a frame and from compaction's cycle guard.

##### Key timing and precision limits

A candidate and an existing entry need not have been keyed against the same graph state.
Each is measured before its own pin, but earlier specializations can already have added bounds.

For nested calls such as `f(f(3))`, function-before-argument coalescing specializes the outer
function use first. Its pin can place a consumer demand on the inner result, and the inner use's
negative read follows that demand. Whether the key changes depends on the structure contributed by
the demand. The key is therefore not a fingerprint of a graph frozen at the end of emission.

Differently recorded demands can cause redundant specializations. Equality testing distinguishes
a key without that demand from one containing it; the cost described here is over-splitting,
not a rule permitting a demanded use to reuse a less-constrained entry.

The frame scans its specialization list linearly. Building `S` distinct specializations can require
quadratically many structural key comparisons. Inlining runs after this work and does not bound
its cost. Per-instantiation rigid channel-domain names can also distinguish definitions containing
a defer, even when their argument base types agree.

The key can also distinguish inputs a function never reads. For example, uses of
`λ a, b → a` at `(1, 2)` and `(1, 5)` can produce identical code under different keys.
Deduplicating completed clones is not implemented. It would require comparison modulo freshly
minted names and placeholders, handling the effects of a discarded clone's pin, and retaining only
referenced specialization bindings.

Refinement distinctions cannot be discarded solely to reduce the clone count. Planning compiles
iteration-domain refinements into filters in `application_order`, so different predicates can
produce different code. Literal singleton types can therefore cause per-value specialization when
the corresponding contributions reach the key. Exact annotations and the resulting bound graph
affect that behavior; “one clone per argument tuple” is not an unconditional count.

This is separate from runtime sharing. After inference, `inline` expands non-`Data` function
bindings, including collection-producing UDFs, while preserving `Data` bindings. See
[Collection sharing](optimization.md#collection-sharing) and
[Exact annotations bound monomorphization](#exact-annotations-bound-monomorphization).

The [coalesce ordering contract](#coalesce-ordering-and-read-stability) explains why specialization
must precede the parent's materialization in this implementation.

#### Refinement representation during specialization

A `Refinement` contains an immutable `Rc<TypedExpr>` predicate. Its equality is type-blind
structural term equality (`eq_term_modulo_ty_slots`); the predicate's embedded type slots are
inference metadata, not part of that comparison.

The predicate is bare: the reserved `REFINEMENT_BINDER` name, `__elem`, denotes the value of
the refined base type. A refinement binds that name, and a nested refinement shadows it.
Free-variable, substitution, and lambda-elimination traversals must respect that binding.

A predicate function `p : D ⤇ Bool` is a term used by iteration and restriction. A refinement
stores the bare predicate `__elem ▷ p`, not that function as its type-level predicate.
`bare_predicate_of_fn` constructs the bare form; planning's `fn_of_bare_predicate` recovers the
function when building a term such as `Restrict`.

A generalized function can be used only inside a predicate, for example in a comprehension filter.
`coalesce_type_predicates` visits those expression trees with the specialization scope active,
so their uses follow the same `specialize_use` path. Inlining also traverses predicates.

Freshening copies predicate type slots and substitution payloads with the rest of the clone.
Coalescing rebuilds a predicate rather than mutating a term shared with the original definition.
Equal predicate terms can still carry different inference metadata because equality ignores those
slots. That does not remove the obligation to visit and resolve each relevant occurrence.

When allocation identity is needed, `PredicateId` uses the predicate's address. Structural
equality and allocation identity serve different purposes: equal terms are not necessarily one
allocation, and a rewritten term is not identified merely by its predecessor's structural type.

#### Cast targets and inferred views

A `Cast` has two distinct type-bearing roles. Its target contains the refinements supplied by
the cast itself; the expression's inferred type also includes refinements inherited from the value.

`canonical_cast_ty` and `canonicalize_cast_types` preserve that distinction when types are
rebuilt. The target retains the cast's own refinements on the rebuilt bases, while `expr.ty`
contains the value and target refinements together.

Copying the entire inferred type into the target would make an operand depend on the route by which
the value's type was derived. It can satisfy a union-based result check while changing the cast's
own predicate identity. Coalescing therefore resolves the cast's value and establishes the shared
bases before coalescing its target predicates.

#### Sharing is an invariant, not an optimization detail

Predicate-rebuilding passes preserve sharing among occurrences of the same original allocation
when they run under the same rewrite conditions. Lowering establishes shared filter predicates
with `Refinement::sharing`. A pass-scoped memo maps an original allocation and its context to one
rebuilt allocation; a vacuous rewrite retains the original.

This is not a global interning rule for every structurally equal predicate. Different contexts can
require different results, and [generic instantiation](#one-known-exception-scoped-and-unfixed-generic-instantiation)
currently creates separate allocations even for occurrences that shared an origin.

Sharing affects later compilation cost. Planning memoizes predicate compilation by allocation and
base type. Splitting one predicate into several equivalent allocations can make it compile each
copy.

The [memo context rules](#predicate-memo-contexts) specify when a rebuild may be reused.
`tests/predicate_sharing.rs` checks for equal predicates at distinct allocations after inference.
Its programs use distinct authored filters, so an equal group identifies a split rather than two
independently authored equal predicates. `distinct_predicate_rcs` supports allocation-count checks;
neither check proves global interning or measures downstream compilation cost.

#### One known exception, scoped and unfixed: generic instantiation

`freshen_refinement_predicate` in `infer/solver/scheme.rs` clones the predicate, freshens its
type slots, and installs an unconditional new `Rc`. It does not use a `PredMemo`.
Occurrences that shared an allocation before instantiation can therefore emerge as separate
allocations, including inside one specialization clone.

The downstream cost of this exception is not established here. The
[sharing corpus](#sharing-is-an-invariant-not-an-optimization-detail) uses comprehensions, not
predicate-bearing UDF instantiation, and does not cover this exception.

Possible remedies include memoizing freshening under an adequate context or retaining the origin
for a vacuous freshen. Neither is implemented. A fix must also preserve node identity: sharing one
rebuilt term across slots is valid, but two distinct live terms must not carry equal `NodeId` sets.
`distinct_predicate_terms_never_share_a_node_id` in `src/ccl/panes.rs` guards that distinction.

#### Type-slot coverage

A predicate walk must visit every carried type slot, not just `expr.ty`. The set includes
expression annotations, cast targets, binder types, and binder annotations.
`Expr::walk_type_slots` and `walk_type_slots_mut` define the shared traversal surface.

Free-variable queries must see these slots too. A pass that skips a subtree after `is_free`
returns false cannot rewrite a predicate hidden from that query. `Cast.target` is one such
location; a comprehension's filter can live there rather than in an ordinary child expression.

Annotations have a shorter lifetime than inferred types. Lowering writes them and inference
consumes them, but pre-inference and in-inference traversals still need to visit them.
`clear_annotations` removes them only after successful inference, including annotations inside
predicate trees. See [The binder slot, and why annotations do not outlive inference](#the-binder-slot-and-why-annotations-do-not-outlive-inference).

`walk_type_slots_covers_every_carried_type_slot` tests traversal coverage with a distinct marker
in each directly carried type. An erasure pass and its postcondition must not both omit the same
slot; using one incomplete traversal for both would hide the omission.

#### Predicate memo contexts

`PredMemo<C>` reuses a result only when both the original predicate address and context `C`
match. The context must include every condition under which the same predicate can rebuild
differently. A context that distinguishes unnecessary cases can lose sharing; one that omits a
relevant distinction can reuse the wrong result.

| Pass | Context | Required property |
| --- | --- | --- |
| `simplify` | `()` | The rewrite depends on the term |
| `uniquify` | `()` | Shared occurrences preserve the same binding interpretation; copied subtrees are uniquified before copying |
| `coalesce` | `()` | Shared occurrences are resolved under the walk's common graph and scope assumptions |
| `inline` | `()` | The substitution is fixed for the sweep; shadowed subtrees are skipped |
| `subst` | `Subst` | Different substitutions must not share a result merely because the origin matches |
| Planning | `Type` | Predicate compilation depends on the refinement's base type |

Address-keyed memos retain their original allocations for their entire lifetime. Without that
keepalive, replacing the last reference could free an address and allow an unrelated predicate
allocated later in the same pass to collide with the old entry. `PredMemo` owns that keepalive
alongside each rebuilt result.

A unit context is a caller obligation, not a property guaranteed by the memo. For example,
inlining's binder handling must skip shadowed subtrees rather than descend under a different
effective substitution while retaining the same key.

Constraint emission uses `TermMemo` instead. A cast can introduce a distinct domain variable for
the reserved predicate binder at each occurrence, so the emitter must run for every occurrence.
`rebuild_always` performs each emission and then shares the resulting term allocation with the
other occurrences. It shares allocations without skipping the constraints each occurrence adds.

#### Predicate rebuild completion

`PredMemo::rebuild` and `TermMemo::rebuild_always` take their transforms as closures.
On ordinary return from the callback, the memo completes installation and recording. The caller
does not hold a token that it must later finish; an early return inside the closure still returns
to the memo's completion step.

The memo is a clonable `Rc<RefCell<_>>` handle. It releases the store borrow before invoking the
transform, so a transform can re-enter the context that owns the memo. Coalescing type predicates
and emitting cast predicates require this reentrancy.

A callback's reported `changed` flag is not the only change signal. A nested memo operation can
redirect a predicate during the callback. `rebuild` therefore also compares the store's revision
counter before deciding whether to retain the rebuilt copy or reuse the origin.
`walk_refined_predicates_mut` reports change to callers that run a fixpoint.

### 3.2 The `InferArena`: who owns inference variables

Inference-variable bounds can form strong-reference cycles. Recording a same-level
`α <: β` adds `β` to `α`'s upper bounds, not an immediate reciprocal bound on `β`;
other constraints or recursive bounds can still complete a cycle. Removing variables from the
expression tree does not break the references between their bound cells.

`InferArena` in `infer/api.rs` owns the teardown of each inference run. Its thread-local
capture records a strong handle to every variable minted while the arena is active.
The type itself carries the variable handle, so the arena enumerates these handles for cleanup
rather than serving as a lookup table.

On drop, the arena takes the captured variables and clears both their bound lists and trait-watch
lists. Watches can form another cycle: a variable watches an obligation whose output type refers
back to a variable. Clearing only bounds would leave those references intact.

No borrow of a captured variable's bounds or watches may remain live across teardown, which mutably
borrows both cells. Successful materialization creates fresh unresolved placeholders rather than
reusing bound-bearing solver variables, so clearing the graph does not remove constraints needed by
the successful result. Weak edges would require a separate owner and fallible upgrades; the arena
retains strong references during solving and performs one linear cleanup.

`infer` constructs the arena before running inference, so both success and error returns execute
the same cleanup. Variables retained in an error-path expression no longer have a live solver graph
after that teardown.

The arena is thread-local and non-reentrant: at most one is active on a thread, with a debug
assertion on nested entry. The guard is neither `Send` nor `Sync`, so it cannot be moved to
another thread for teardown.

---

## 4. Information Flow and Type Mapping

Cambra carries features beyond plain algebraic subtyping (explicit refinements, tagged sums); this section describes how each is represented in the solver and materialized back out.

#### The unified tagged sum

Cambra has **one** sum representation, the **tagged variant** — `Type::Variant(Vec<(FieldKey, Type)>, Openness)`. Since the solver works on `ccl::Type` directly, there is no second variant form to convert to: inference, coalescing, and the public AST all use this one type. (Internally, `compact_type` keys its transient `CompactType` bag by `FieldKey`, but that is an implementation detail of compaction, not a separate type.)

Tags are [`FieldKey`]s — the same key type as records/tuples — so a sum can be **named** (`FieldKey::Name`, a source-level `` `tag(…) ``) or **anonymous/positional** (`FieldKey::Index`, the dual of a tuple). A positional union `A | B` is simply `Variant([(Index 0, A), (Index 1, B)])`, and the surface `++`/`Copair` produces exactly that (see §2's `emit_copair`). One constructor, one coalesce path, one width-subtyping rule (the dual of records: a subtype has *fewer* tags).

That one rule does **two** jobs, and the [`Openness`] marker is what separates them. Recursing into a tag both sides carry is what pushes the payload into the supertype's slot — how a `match` arm's binder learns its type from the scrutinee. Rejecting a subtype tag the supertype lacks is the exhaustiveness check. A **closed** arm set does both; an **open** one keeps the payload recursion and drops the rejection, which is what a `match` with a `case _:` needs and what no closed judgment can express (on the tag axis the scrutinee is the supertype, on the payload axis its payload is the subtype, and one edge cannot point both ways).

Openness is a property of a *demand*, never of a value: every producer of a sum is closed, and `Open` appears only on the right of a subtyping edge. Compaction and coalescing **carry** it (`CompactVariant` pairs the tag map with its openness) rather than flattening it, because a type *error* naming that demand is resolved through the same round-trip — closing the arm set there would report that the scrutinee failed to be an exact sum, when what it failed was to be a subtype of a partial one, and only the rendered `| …` tells those apart. Nothing else reads it: the runtime `Extent` has no counterpart, and no node's coalesced type comes out open. That last is an invariant, not a theorem, so `types_agree_modulo_unread` compares openness and an escape shows up there as a disagreement.

Two arm sets meeting at one position meet their openness — `Open` survives only if both sides are open, since a closed side is the one contributing a requirement on the tag set. The tag *map* still merges by the ordinary intersect/union rule; that is an approximation when exactly one side is open, and no program reaches it (a scrutinee takes one `Case` demand per `match`).

Two senses of "union" remain distinct:

* ***union of lower bounds*** — the lattice operation at coalesce time (§1, §2); an internal solver operation, not an AST node.
* a **positional `Variant`** — the all-`Index` tagged sum that materializes a `++` collection-union or a user `A | B` annotation.

Inference does not *infer* a multi-atom sum from a primitive collision (it raises `IncompatibleBounds`); positional variants enter only via `++` or a user annotation.

#### Tagged-variant expressions

* **`VariantCtor { tag, payload }`** constructs a singleton `Variant({tag: payload})`; width-subtyping flows it into any consumer expecting a superset of tags.
* **`Case`** is the single dispatch node for both logical (`if`/guard) and structural (variant-tag) matching — see §2's `emit_case`. A structural `Case` carries a scrutinee and branches with `Pattern`s; width-subtyping enforces tag coverage and binds each payload at its per-tag narrowed type.

(Both are reachable from source: `` `tag(payload) `` lowers to `VariantCtor`, and `match` / `case` to a pattern-`Case` — `match` needs no IR node of its own.)

#### A literal is refined by its own value

A literal is typed by *which* literal it is: `5 : {Int | __elem == 5}`, its base refined by the singleton predicate. Not a `Literal(base, value)` constructor — an ordinary refinement, so every rule above applies unchanged and none has to learn a new case.

The reason is that a literal knows more about itself than its base does, and that knowledge is what a proof obligation needs: `a[0]` can only discharge against `Array(3, 𝑇)`'s index range if `0`'s type says it *is* `0`. Typing `5` as plain `Int` throws that away at the one place it is free to keep. The predicate is built **typed** — only *node* annotations get their embedded predicates re-inferred, and this one rides a type the rule makes rather than one a user wrote.

What this changed is instructive, because refinements were rare enough before that several rules assumed their absence. Each was already wrong for a user-written refinement; literals are merely the first thing that makes them reachable.

* **An operator does not *inherit* its operands' refinements**, and does not have to be *made* not to. A refinement is a fact about a value, so an operator that computes a new value cannot carry one over: `𝑥 + 𝑥` where `𝑥` is `2` produces `4`. Arithmetic, comparison and negation state their requirement as a [trait](#traits), over a variable per operand and per associated type — all unrelated — which leaves no path for an operand's refinement to reach the result by sharing (`an_operator_result_carries_no_operand_refinement`). The remaining monomorphic operators (`and`, `++`, `not`) keep an ordinary scheme and pass their operands verbatim — nothing is shared with the result, so a refined operand simply flows into a concrete domain. Aggregates likewise keep theirs, since their operand is a *collection* whose refinements describe its domain and the rule must see them.

  Inheriting is not the same as **computing**, and only the first is ruled out. `{Int | __elem == 2} + {Int | __elem == 3}` genuinely *is* `{Int | __elem == 5}`, and a trait instance is where such a rule would live, since it determines the output type rather than forcing it to be a position the operands already occupy. Today every instance computes a base and stops — a property of the table, not of the mechanism. Two things would have to change to lift it: an instance would need the operands' *types* rather than their bases, and the deposit would have to move to a point where those types are final. Eager deposit is sound for a base because a base never weakens, while a refinement set only shrinks as further lower bounds arrive — so a refinement computed from a partial view is too strong. A rule computing from resolved operands then meets recurrences (`x := x + 1` resolves its operand through its own output), where it must already be sound at the cut; and anything beyond constant folding and interval arithmetic needs predicate *implication*, which the lattice deliberately does not have (refinements match structurally — see this file's module-level note in `src/ccl/infer/solver/mod.rs`).
* **A mutable variable takes no refinement** from its initializer or from any single write. A mutable variable is not one value but the sequence its writes produce, so its value type is the join over all of them; taking one contribution's refinement would assert it never changes, which is what declaring it mutable denies. The rule holds at every place a mutable variable's value type is *built*, not just at the `:=`/`+=` rule: the `Transact` carrier's keys (where the seed is the value type's only lower bound, so an unstripped seed would resolve the mutable variable — and every read of it — to the seed's singleton), the recognition that builds that carrier, and the phase that reads the value type back off the seed binding.
* **Every merge point joins** — a list's elements, a `Case`'s arms, a mutable variable's seed and writes, a channel's contributions. This is the one rule the singleton made load-bearing, and the one place it is easy to get wrong, because a merge that simply *adopts one input's type* looks right until the inputs carry different refinements. The law: a refinement is a fact about **a value**, and a merge point is not one value — it is whichever input the runtime supplies — so a refinement survives the merge only if *every* input establishes it. Two arms depositing different singletons intersect to none (`1 if 𝑐 else 2` is an `Int`); two arms depositing the same restriction keep it (identical filtered comprehensions stay filtered, `5 if 𝑐 else 5` is still `Int@5`). Where the merge is a fresh variable every input flows into, the solver's join *is* the rule and nothing has to strip; where a pass builds the merged type by hand (`channelize`'s channel union, the `Transact` carrier's key seeds) it must intersect the refinements explicitly.

  **Stripping is not the join.** It over-approximates in the safe direction (a refinement every input establishes is thrown away) and it is not variance-stable: for a *collection* input, whose extent rides the contravariant `Fun` domain, relating a refined input to a stripped sibling demands `𝐷 <: {𝐷 | 𝑝}` and rejects two arms that are literally the same expression. `𝐷 <: {𝐷 | 𝑝}` is never a real obligation in this language — acquiring a refinement is an explicit `cast` — so seeing one means an erasure manufactured it. Inputs whose extents genuinely differ meet on the domain (both refinements accumulate — the extent both admit), since that is where a function type's join puts them.
* **A `Mut` input derefs into the join**, exactly as a mutable read derefs into a tuple element, so a `Case` over two mutable variables types as their *value*. The second-class discipline's rule 1 therefore has no `Mut` on the selection to reject; what it protects — a selected mutable variable reaching a position that writes through it — is its argument clause, which reads the argument *node*. See [No aliasing: `Mut` values are second-class (downward-only)](mutability.md#no-aliasing-mut-values-are-second-class-downward-only).
* **`__elem` is bound by the refinement it rides**, so it is never free *in a type* — the free-variable walk must not report it so.
* **Beta reduction discharges a refined parameter** when the argument's type entails it: substituting the argument is what establishes the precondition.

Singletons are *not* erased after inference. They are ordinary refinements and ride through to the runtime like any other, which also keeps them available to a future constant fold. They print as their base pinned to the literal (`Int@5`, not `{Int | __elem == 5}`).

#### Refinements on the lattice

A **refined type** `{T | p}` carries a *set* of [`Refinement`]s, and the lattice treats each as a black box: it accumulates them and matches them by identity, reasoning about what they imply only through the fallback below (the predicate's logical content is real and used by the runtime, otherwise opaque *here*). It is a fourth structural dimension on `CompactType`, width-subtyped exactly like records: **`{b₁ | S₁} <: {b₂ | S₂}` iff `b₁ <: b₂` and `S₂ ⊆ S₁ ∪ refinements(b₁)`** — more refinements ⇒ subtype. So `{T | p, q} <: {T | p}` and `{T | p} <: T`, but `{T | q} ⊀ {T | p}`. Refinements match by **type-blind structural equality of their predicate terms** (`Refinement`'s `PartialEq` / `eq_term_modulo_ty_slots`) and not by predicate implication, which is what [Semantic entailment as a fallback](#semantic-entailment-as-a-fallback) supplies for the cases structural matching leaves. Structural matching makes refinement identity agnostic to *where* a predicate was constructed (join planning re-mints `{D | p}` at every marker it emits — `make_iterate` / `make_restrict` / `refine_with` — and must match the structurally-identical contract recorded elsewhere on the tree) and to in-place type resolution (copies of one predicate along a monomorphization descent line differ only in their inferred-type slots); a pointer-equal predicate `Rc` short-circuits as the fast path, since a refinement that merely flows around shares its `Rc`. The refinement set merges with the *same polarity rule as `rec`* (positive ⇒ intersect, negative ⇒ union) and is carried verbatim through simplification (refinements are positional, never folded into a variable's identity, so co-occurrence merging can't move or drop them).

##### Semantic entailment as a fallback

A deficit `S₂ \ S₁` over a concrete `b₁` asks `smt_sub`
([`crate::ccl::infer::solver::smt`]) whether `S₁` entails `S₂` before the rule reports a
mismatch. `{Int | __elem == 1 ^+ 3 ^+ 2} <: {Int | __elem == 1 ^+ 5}` holds by that route and
not by structural matching.

The query is `∀ __elem. ⋀Γ ∧ ⋀S₁ ⇒ ⋀S₂`, decided by asking Z3 for unsatisfiability of
`⋀Γ ∧ ⋀S₁ ∧ ¬⋀S₂`. `__elem` is declared once at `b₁`'s sort and shared by both sides, or, where
`b₁` is a product, read through its fields
([A product is reached through its fields](#a-product-is-reached-through-its-fields)). Both
sides are transported into the ambient frame (`Subst::force_refinement`) first, because the
query compares terms and the two sides' predicates are written in different binder contexts.

`Γ` is [The scope a query runs in](#the-scope-a-query-runs-in): every other free name is
declared at a sort as well, so it is universally quantified too, and what is assumed about it
comes from the scope the caller supplies.

The encoding covers linear integer arithmetic over scalars: literals, variables, field
reads, `+`/`-`, `*` with a literal factor, the comparisons, and the boolean
connectives. `smt_sub` returns `false` for one reason: the solver produced a model of
`⋀S₁ ∧ ¬⋀S₂`, a value satisfying `S₁` and violating `S₂`. Every other outcome is an
`SmtError` naming what happened, because a query that was not asked or not answered has no
result of its own to report.

The deficit rule decides an unreadable predicate anyway, as a mismatch: that is the answer
structural matching had already reached, so falling back to it is incomplete and never unsound.
The remaining errors — a solver that will not start, one that breaks mid-query, an `unknown` —
reach `map_constrain_err`, which aborts on each. `TODO(smt-undecided)` there records the policy
those want instead.

##### A product is reached through its fields

An SMT constant stands for a scalar, and the unit one is minted for is an **access path**: a root
name and the projections read through it (`Path`, in `src/ccl/infer/solver/smt.rs`). A record or a
tuple has no sort, so a product-typed name denotes no constant; `x.b` denotes one, and keying that
constant by the path is what makes two occurrences of `x.b` one constant.

`x = (a = 10, b = 2 ^+ 1); def foo(t: Int) => {Int where _ == t + 3}: t ^+ x.b` is the case that
needs it: the body is inferred `{Int | __elem == t ^+ x.b}`, and the entailment follows from
`x.b == 3`.

A path's type is the type its root is bound at, read once per key, and that type wins over the slot
on the term that read it — the scope records what the value is, while a projection's slot
mid-emission is an inference variable. The subject is rooted at `b₁` the same way: a scalar base
declares one constant, a product base declares none and each path read out of it is declared where
it is read. A base that is neither leaves every predicate about it unencodable.

Assumptions come from every prefix of a path rather than from its leaf alone, because a refinement
on a product states its predicate about the product: that `x.b` is `3` can be written on `x` as
`{{b: Int} | __elem.b == 3}` or on its field as `{b: Int@3}`, and the two are one assumption.
`__elem` addresses the subject of the predicate it appears in, so a read inside `x`'s own refinement
reroots onto `x` — `__elem.b` there and `x.b` outside are one leaf.

##### The scope a query runs in

`smt_sub` takes a `ScopeEnv` — a lookup from a free name to the type it is bound at. A path rooted
at a name the scope binds is declared at the sort its type gives it, and the refinements the types
along it carry join the antecedent, restated about the path. A path the scope settles nothing about
is declared at the sort of the node reading it and nothing is assumed about it.

`x = 2; def foo(t: Int) => {Int where _ == t + 2}: t ^+ x` is the case that needs it: the body
is inferred `{Int | __elem == t ^+ x}`, and `t ^+ x == t + 2` follows only from `x == 2`, which
is the refinement on the type `x` is bound at.

Assumptions chain, because a binder is looked up when a predicate mentions it and the lookup
runs on its own refinements too: `x = 2; y = x ^+ 1` reaches `y == 3` by declaring `y`, meeting
`x` inside `y`'s predicate, and declaring `x` with its own. The binder is declared before its
refinements are translated, so binders that reference each other terminate.

A lookup and not an enumeration. Declaring every binder in scope would let one nothing mentions
change the answer — a contradictory binder proves the entailment outright — and it costs a
declaration per binder on a query that names two. A product's fields are not enumerated either,
for the same reason.

Three environments implement the lookup, and a fourth suppresses the query:

- **Emission** passes its lexical scope (`InferCtx`'s `ScopeStack`) plus the opaque binders it has
  recorded, through `constrain_subtype_in`. A binder's slot
  mid-emission is an inference variable, so the scheme body is resolved before it can be read
  as a fact — `value_type`, the compact → simplify → coalesce pipeline with the
  opposite-polarity fallback suppressed. The positive reading is what makes the assumption
  sound: the slot also carries what the binder's *uses* demanded of it, and assuming a demand
  would let an entailment prove itself from what it was asked to establish. `x = 2` needs no
  resolution (the literal's singleton is on the node), `x = 2 ^+ 1` does — the sum's singleton
  is on the variable's bounds, and unresolved the binder has no sort at all. A generalized
  binder's quantified variables stay uninstantiated; a polytype has no sort, so it is dropped
  rather than assumed wrong.
- **The post-inference check** builds its own Γ from the tree it walks (`CheckCtx`'s `scopes`
  and `opaque_binders`) and passes it through `constrain_subtype_in` and
  `constrain_subtype_under_in`. A binder is bound at the type its own rule hands
  `Typing::scoped`, resolved — a fact about every value reaching it, because the binding site is
  held to it by the edge that rule draws. Nothing here resolves a name: a `Var` node's recorded
  type is trusted, and a name Γ does not bind leaves the query an assumption short rather than
  reporting an error.
- **`NoScope`** is the empty environment: `inline`'s discharge check, which runs over a tree
  whose binders it does not hold, and any probe over types built outside a program.
  An empty scope only weakens what the fallback can prove, so it can reject what emission
  admitted and never the reverse.
- **`SkipSmtScope`** decides a deficit structurally, raising no query at all, and
  `constrain_subtype` supplies it — so a caller reaches the fallback by naming a scope. That
  split is caller policy riding the scope trait rather than a fourth environment; the
  `ScopeEnv::is_skip_smt` doc names the shape it wants instead.

Dropping is the discipline throughout: a path with no sort, a predicate body outside the
fragment, a name two binders disagree about. An assumption left out weakens the antecedent and
cannot make an invalid entailment provable.

##### The set is the representation, not just the reading

`Type::Refinement` carries a `RefinementSet` — unordered, deduplicated, with set-semantic `Eq`/`Hash` — and `Type::refined` is the sole constructor, establishing two invariants: the set is non-empty, and the base is never itself a refinement. Nested layers flatten, so `{{𝑇 | 𝑝} | 𝑞}` is *unrepresentable* and "which layer is outermost" cannot be asked.

That question previously had an answer, and the answer was constraint **arrival order**: two refined upper bounds meeting at one variable produced `{{𝑇 | 𝑞} | 𝑝}` or `{{𝑇 | 𝑝} | 𝑞}` depending on which arrived first. Subtyping never cared — the deficit machinery above already compares layers as a set — but `Type`'s derived equality did, and structural equality is load-bearing wherever a type is an **identity**: the trivial-equality short-circuit in `constrain_go`, cache keys, `SpecKey`, and the recorded-vs-recomputed walls. One `Vec` was serving three incompatible readings — a set to subtyping, a stack to planning, an identity to the walls.

Flattening is sound because every refinement at a position restricts the same underlying element: a refinement narrows *which* values inhabit a type, it does not change them, so an outer refinement's `__elem` ranges over exactly the values an inner one does. Canonically *sorting* the `Vec` was tried and rejected: it pins the ambiguity rather than deleting it, and it denies planning the freedom to apply refinements in whatever order it likes.

##### Materializing a refinement set is a pipeline, and a pipeline is ordered

The set is unordered as a *fact about a value*. Materializing it is not: planning emits one `restrict` per refinement, and stage 𝑘 reads elements already narrowed by stages 1..𝑘-1, so its element type is the base narrowed by the refinements applied before it — not the bare base. Planning therefore **chooses** an order.

Which order is free is not entirely planning's to say. Two refinements are usually
independent, and then any order yields a well-typed pipeline for the same final domain and a
cost model could pick the cheapest filter first. Some are not: the outer filter of `[y for y in
[x for x in xs if 𝑝] if 𝑞]` reads the `𝑝`-filtered collection, so `𝑞`'s predicate carries
`{𝐷 | 𝑝}` in its own types and cannot be applied to elements `𝑝` has not yet removed. That
ordering is the program's nesting, and flattening `{{𝐷 | 𝑝} | 𝑞}` into one set leaves it
recorded nowhere but inside `𝑞`'s predicate. `ccl::application_order` reads it back from
there, and orders everything else as the set holds it.

Choosing *differently in two places* is what is never free, since the types along the pipeline
and the predicates compiled for it must agree. That is why the order is recovered rather than
derived: a derived order is only as stable as what it derives from, and the three sites needing
one — the `restrict` chain, the predicates compiled for it, and the check that re-derives both
— run at different points. Ordering by the refinements' rendered predicates was tried and
failed exactly there, because compiling a predicate rewrites the very term the key reads, so
predicates compiled under the order read before compilation landed in a pipeline typed by the
order read after.

The chosen order is a **permutation** of the physical one, and that is the trap: a site
rewriting refinements *in place* walks them physically, and zipping the application order's
types onto that walk pairs refinements with the wrong element type — silently, since the two
sequences have equal length. `application_elem_types` does the permutation explicitly and is
what such a site uses.

Nothing above planning may read the order back. `RefinementSet`'s equality is
order-insensitive, so what planning fixes never reaches an identity — order-blind types, an
order recovered once at planning.

`CAMBRA_REFINEMENT_ORDER=reverse` (debug builds only) flips the set's physical order globally,
and CI runs the suite both ways — an unrun knob rots exactly as an uncompiled feature does. Two
classes of order-dependence survive a compile-clean rewrite of this kind: a consumer that
*iterates* the set and lets the order reach something observable, and a dedup that keeps the
first-inserted of two `eq`-equal members whose type-blind-equal predicate terms carry different
embedded type slots. Recovering a nested filter's order from its predicate is what keeps the
compiled term identical under the flip rather than merely well-typed. The variable is read at
runtime, so the reversed pass reuses the binaries the ordinary one built.

**A refinement never changes a type's shape.** It is a claim about the value at a position, not part of the structure carrying it, so `{(𝐷 ⇒ 𝑉) | 𝑝}` *is* a function and `{Mut(𝑉, 𝐷) | 𝑝}` *is* a mutable variable. Every rule that dispatches on or destructures a shape therefore looks *through* the outer layers first — `Type::peel_refinements`, and the handle accessors `Type::mut_value_type` / `as_feed` / `is_handle` built on it, which are what the typing rules and the second-class `Mut` discipline both ask "is this a mutable variable?" with. It is the same claim-versus-structure distinction a trait obligation draws when it reads a base off an operand ([Refinements are transparent](#refinements-are-transparent)): what narrowing consumes is the structure, and the refinement rides along untouched.

A refinement is **required**, so `constrain_subtype` is strict for *concrete* bases: an unrefined concrete value does **not** flow into a refined position (`T ⊀ {T | p}`), and `{T | q} ⊀ {T | p}`. The one subtlety is the `S₂ ⊆ S₁ ∪ refinements(b₁)` clause: when the subtype side's base `b₁` is an **inference variable**, it can still acquire the deficit `S₂ \ S₁`, so the solver flows `b₁ <: {b₂ | S₂ \ S₁}` onto the variable rather than rejecting (the refinement analog of how the record/function arms thread structure through a variable base; it fails later iff the variable resolves to a concrete base lacking those refinements). This is what lets a value that is *already* refined flow into a position whose variable base demands a further refinement — `{D | p} ⇒ V <: {?a | q} ⇒ V` records `?a <: {D | p}`, so the position carries both `p` and `q`. Acquiring a refinement on a *concrete* value is still an *explicit* operation, not subsumption: the `Cast` node, written `cast({D | r} ⇒ V, value)`, is typed by `emit_cast` rebuilding the value's function type with the target's domain refinements, with no `value <: target` edge (see [`Cast` — explicit refinement acquisition](ir.md#cast--explicit-refinement-acquisition)); nested casts compose because the rebuild stacks onto the refinements the value already carries. The interpreter compiles a refinement on a **collection domain** to a runtime `Restrict`/`Filter` at the iteration boundary (the `Iterate`/`Restrict` arms of `operator_conversion`, where `extent_of` strips the domain refinement into a `Restrict`). The predicate `Expr` of each refinement is inferred/coalesced like any other sub-tree (annotation-borne predicates via `emit_annotation_predicates` / `coalesce_type_predicates`).

**Refinements in the post-inference check.** The post-inference structural check (`infer::check`,
reimplemented on the same structural rules as emission via the `Typing` trait — see §2, *The
post-inference check*) is **strict and refinement-aware throughout** — it does not strip refinements
before its width-subtyping checks. It runs the solver's subtyping relation in two places, both fully
refinement-aware, and both in the Γ the walk builds from the tree ([The scope a query runs
in](#the-scope-a-query-runs-in)), so a refinement deficit reaches the semantic fallback there as it
does during emission. `x: Mut({Int where _ >= 0}) := 0` with a write `x := x ^+ 1` is the case that
needs it: the seed types `Int@0`, the write types `{Int | __elem == __read ^+ 1}`, and neither
matches the declaration structurally — `0 >= 0` admits the seed, and `__read ^+ 1 >= 0` follows from
the type the read's opaque binder is bound at. The two places:

* **Adjacency rules** (a `Compose` link's `prev_cod <: next_dom`, an `Apply`'s argument-vs-domain) check *refinement flow*: feeding an unrefined producer into a refinement consumer is rejected (`T ⊀ {T | p}`), exactly as the solver is. There is **no cast escape** — a producer must already carry the refinement its consumer demands. A `… ≫ (id ≫ cast({D | r} ⇒ V))` chain composes because join planning surfaces the iterated / join-satisfying domain on the *producing* morphism's codomain, so the upstream genuinely supplies `{D | r}` (see the reconstructability bullets below). The producer's refinement and the cast's contract are typically re-minted as distinct predicate terms, so the adjacency relies on the structural-predicate match above.
* **The reconcile** (a node's rule-reconstructed type vs the type inference recorded on it) is the plain strict `rule <: recorded` subtype check, refinements included (the recorded type may be a width-wider supertype — e.g. an annotation). A rule that rebuilds a node's type from its children rebuilds its refinements too, so a recorded refinement the reconstruction lacks is a real disagreement about the node — and in practice it is one specific bug: a **merge point that took one input's refinement** instead of the join of all of them (see the merge law above). Comparing modulo refinements here — stripping both sides, or a refinement-blind relation — is the *only* thing that hides that class, and this is the check best placed to catch it. Keeping it strict is what forced each merge point to join.

For the reconcile to hold, the passes that *introduce* refined types post-inference (lambda-elim, join-planning) must leave each node's recorded type **reconstructable** — consistent with what the bottom-up rules rebuild from its children. These sites were emitting internally-inconsistent or under-refined nodes and are now fixed at the source rather than papered over by relaxing the check:

* **Iterated / join-satisfying extents on producers** (`planning`'s `set_extent` / `refine_extent`). An iteration source produces the refined domain it iterates, so it is symmetric `{D | p} ⤇ {D | p}` (`make_iterate`); a hash join folds its equi-conditions into the key structure with no residual `Restrict`, so the extent it yields would otherwise reach the body's `cast` *bare*. `refine_extent` refines **both sides** for that reason: a data function's domain *is* its data, so refining only the codomain would leave the domain claiming rows the join never produces — readable as a supertype under the contravariant reading of a function, but wrong for a collection, and it puts every enclosing type at odds with the site. Threaded down the combinator's whole function spine so the leaf builtin the Check pass rebuilds from agrees. Reconstructable because a combinator node carries its own function type and `emit_apply` returns *that* codomain verbatim. `make_restrict` builds its refinement directly rather than through `refine_with`, whose trivially-true degeneracy is right for `make_iterate` (an unrefined site should not print `{D | true}`) but wrong here: the caller emits one `restrict` per layer the *site* declared, so dropping a vacuous one leaves the source producing a bare extent while the site — and the body's `{D | true}` cast — still demand the refined one.

* **Dependent groupby refinement** (`lambda_elim`'s cast-wrapped-lambda arm). `groupby` lowers to `λ k → cast({I | key(i) == k} ⇒ A, λ i → c(i))`. Because the key binder `k` is now a genuine **Pi binder** (the refinement closes over it but the *value* does not mention it), lambda-elim emits the Pi-const form `const(cast(c)) : (k) ⇒ ({I | i ▷ c ▷ key == k} ⇒ A)` — the `k`-dependence rides the refinement and is materialized as a `Restrict` at the iteration boundary (the dependent-application model, §4.5). Planning's pointful recogniser (`recognize_groupby_sites` / `convert_groupby_pointful`) matches that Pi-const source directly — identifying the key binder structurally as the free variable on one side of the predicate's equality — and emits the bucketize chain `converse(c ≫ key) ≫ map(c)` **at the source's own type** — `(k: K) ⤇ ({I | key(i) == k} ⤇ V)`, group refinement and Pi binder intact. A group holds the members sharing one key, and a data function's domain *is* its data, so typing a group as the bare `I` would claim every element belongs to every group; the binder has to ride the function type as a Pi or the predicate's `k` dangles.
* **`permute_domain` over a refined morphism** (`join_plan::convert_loop_join`). The combinator is polymorphic in the morphism it rearranges; its declared input type is the morphism's *actual* type (which may carry the join-condition refinement), not a bare `actual ⇒ actual`. Otherwise `apply_function` re-stamps the partially-applied combinator's recorded type to `fun(expr.ty, …)` (carrying the refinement) while its inner `PermuteDomain` builtin keeps the bare declaration — an inconsistent node the reconstruction can't rebuild, because the refinement rides the morphism's *invariant* domain⇒codomain position (where subtyping would demand `T <: {T|p}` *and* `{T|p} <: T` at once).

#### Feed handles as an invariant `History` constructor (`Type::History { kind: Feed }`)

A feed handle is `Type::History { value: 𝑇, domain: 𝐷, history_kind: HistoryKind::Append }` (displayed `feed(𝐷 ⤇ 𝑉)`) — a collection `𝐷 ⤇ 𝑇` carried as two children plus a two-valued `history_kind` marker. It **shares the `Type::History` variant with a mutable variable** (`history_kind: Overwrite`, displayed `Mut(𝑉, 𝐷)`); the two were unified from the former `Type::Feed(ρ)` / `Type::Mut{…}` pair (see [`Mut` is a CCL type](mutability.md#mut-is-a-ccl-type)). `let 𝑑 = Defer in body` gives `𝑑` an `Append`-kind history whose channel `𝐷 ⤇ 𝑇` is the *post-channelize result type* of the binding (a `𝐷 ⤇ 𝑇` channel for fed defers, the defined value's type for `<<=`-defined defers). Like `Hole` and `Infer` the `Append` kind is **transient**, scoped to inference: `channelize` (which runs after inference) eliminates every defer construct along with its feed histories, and no pass downstream of it may observe one. (This is the feed-handle type of [`Feed` is a CCL type](mutability.md#feed-is-a-ccl-type) — what a defer-mediating UDF parameter carries.)

Below, **`Feed(ρ)`** abbreviates a `kind: Feed` history whose reconstructed channel is `ρ = 𝐷 ⤇ 𝑇`; the `value`/`domain` children are the two halves of `ρ`. An `Overwrite` history reaches the relation as a handle — a read has already dereffed at the rule that emitted it — so the four invariance rules below are specifically the `Feed`-kind behavior.

The typing rules are `emit_defer`, `emit_feed`, and `emit_define` in `infer/emit.rs`.
`emit_defer` initially creates a history with fresh domain and value variables. For
`let d = Defer`, `emit_let` immediately replaces the domain with rigid `ChanDom(d)`.
A feed contributes `δ ⤇ value_ty` to the handle's channel; its fresh domain variable is
constrained to that rigid name, not left as an unconstrained `Infer`. A define contributes
its entire value type. Both statements have type `Unit`.

A structurally opaque target, such as a lambda parameter, receives a feed-handle upper bound.
The call-site argument meets that bound, and history invariance propagates contributions back
to the caller's channel. A bare `Defer` RHS is not generalized, so feeds and reads share its
history. A defer inside a generalized function freshens with the function's instantiation.
`channelize` later substitutes the assembled channel domain for each `ChanDom`.

`History` is the lattice's only **invariant** constructor. Feeding is a contravariant capability (a feed contributes an element *into* the channel) while reading is covariant, so a feed handle flowing through a function parameter must propagate feed contributions *backwards* to the caller's channel — a one-way `arg <: param` edge would strand the callee's contribution on the parameter variable. Four constraint rules (`constrain_go`), where `Feed(a)`/`Feed(b)` are same-`kind` (`Feed`) histories:

1. **`Feed(a) <: Feed(b)`** ⇒ both `a <: b` and `b <: a` (invariance — payloads are equated). The payload edges run under **identity morphisms**: a payload is the channel's plain value type, not content inside a Pi binder's scope, so apply-site discharges do not transport into it — and must not, or the two-way edge makes two distinct non-invertible discharges meet at one payload variable (the closure-bridge corner) for ordinary chained defer functions. The cost: a binder-dependent refinement inside a fed value's type is not discharged across the handle (out of scope alongside the filter-feed-through-UDF gaps).
2. **`Feed(a) <: 𝑇`** for non-feed `𝑇` ⇒ `a <: 𝑇` — transparent read (`sum(d)`, `d + 1`, `x <<= y` chains discharge through the handle). The post-inference structural check mirrors this: `CheckCtx::apply` takes the handle's read view (`Type::read_view`) once and hands that one function to both consumers an application reaches, the shape edge (`as_function`) and the argument edge (`constrain_argument`).
3. **`Fun(…) <: Feed(a)`** ⇒ `Fun(…) <: a` — a *channel-shaped* lhs is the read view of the feed handle (coalescing a use position that both held and read the handle surfaces the bare channel; monomorphization's two-way pin then meets that view against the definition's `Feed`).
4. **`𝑇 <: Feed(a)`** for any other non-feed `𝑇` ⇒ `ConstrainError::NotAFeed` — the write capability cannot be conjured from a plain value (`g(5)` where `g` feeds its parameter).

The shared variant keeps the overwrite/feed operator discipline **on the type**: rule 1's invariance arm matches only *same-`kind`* `History`/`History` pairs, so an `Overwrite` history demanded as a feed (or a feed as an overwrite history) is not equated — the `Overwrite` history arrives as the handle it is and meets rule 4, whose left-hand side is any non-feed shape, as `NotAFeed`. So `<<` into a `:=` mutable variable, or `+=` on a `defer` channel, is a type error with no separate structural check (see [`Mut` is a CCL type](mutability.md#mut-is-a-ccl-type)).

Invariance has no MLsub-blessed polar story, so the two polarity-sensitive mechanisms treat it specially:

* **Extrusion** (`extrude_invariant`): a history's `value`/`domain` variables crossing a level boundary each get a *single* fresh proxy linked to the original by **both** a lower and an upper bound (an equality link through the standard lower×upper closure), instead of the polar one-way link. The proxy registers under both `ExtrudeCache` polarity keys.
* **Compaction/coalesce**: the two children occupy a dedicated `CompactType::history_slot` (carrying the `kind`), recursing at the **same polarity** — by compaction time the constraint-level invariance has already propagated both directions, so this is materialization only, not a second polarity analysis. `simplify_type` walks the slot at the same polarity; refinement/co-occurrence behavior is unchanged.
* **Transparent read at joins** (`dissolve_read_feeds`): rule 2 covers a feed handle meeting a concrete consumer *directly*, but a read can also meet other contributions through a shared join variable (`x + 1` flows `Feed(Int)` and `Int` into the binop's `∀α.(α,α)→α`). At coalesce, a position carrying a `Feed`-kind `history_slot` **alongside** non-feed contributions dissolves the handle into its channel before the contribution count; a feed handle alone (or two handles merged) keeps its constructor. Feeding-then-scalar-reading still errors correctly: the dissolved channel is `Fun(?, T)`, which genuinely collides with a scalar.

Freshening (`freshen_above`) is polarity-free and recurses through the payload like any position, so a generalized DI function (`λ𝑛 → let 𝑥 = Defer in …`) instantiates a fresh feed handle per use site — the "fresh defer per call" semantics.

### The binder slot, and why annotations do not outlive inference

A binder's `ty` records **the type the binder is bound at** — the type its references have. For an unannotated binder that is its initializer's type, but the two are not the same thing, and every binder position resolves the slot the same way: emit writes the type it bound the variable at, coalesce resolves it in place. `let` was once the exception, reconstructing its slot afterwards as a copy of the coalesced RHS type, and that is what made annotations look load-bearing after inference.

Two annotated forms are where the initializer's type and the bound-at type diverge, in opposite directions:

* A **deref-copy** `y : 𝑉 = 𝑥` off a mutable variable `𝑥` binds `y` at the value type `𝑉`, while its initializer is a *history*. Recording the initializer's type made `y` an alias of `𝑥` in the type system — so the second-class `Mut` discipline, which keys on types, then misfired on a variable the user declared immutable: `z = y` was rejected as an unannotated `Mut` alias, and `y += 1` was *accepted* as a write.
* A **mutable variable introduction** `𝑥 : Mut(𝑉) := init` binds `𝑥` at the history `Mut(𝑉, 𝐷)`, while its initializer is a plain value. Recording the initializer's type left the mutable variable's own slot reading `𝑉`, so the transaction-mutable variable scan could not classify it from the slot.

Both readers compensated by consulting `user_annotation`, which held the user's declaration and so happened to answer correctly. That is the proxy the slot's honesty removes, and removing it matters because **an annotation is a pre-inference input**: it is a raw type from lowering, never normalized and never coalesced. A pass that pattern-matches one is reading a shape from before inference ran. So `infer` **clears every annotation on success**, and both post-inference walls pin the emptiness (`debug_assert_annotations_cleared`) — an invariant worth checking rather than asserting, since a stale annotation is only *read* by whichever pass thinks to look, and a leak surfaces as a wrong answer somewhere else entirely.

**Both the clearing and the check follow type slots, not just children.** An annotation does not only ride the expression tree: `groupby` stamps the relation tying its key parameter to its key function onto a node inside the cast target's *refinement predicate*, and a predicate hangs off a type slot, which no `walk_children` reaches. A walk over children alone therefore clears every annotation it can see and then certifies the tree clean while a live one sits in a type — the leak and the check blind in exactly the same place, which is why the check could not report it. Both walks compose `walk_type_slots` with `walk_refined_predicates`, so they cover the same ground inference does when it *reads* an annotation.

Nothing has to outlive the annotation. The one fact a later pass used to need from it — *is this binder a mutable variable?* — is answered structurally instead: only `MutDecl` (a `:=` introduction) and a pass-by-reference `Lambda` param bind one, and a `Let` cannot, because `emit_let` reads through an initializer that is a mutable variable. That retired the `Mut` discipline's rule 3 along with the bit that stood in for the declaration (see `src/ccl/design/mutability.md`, "No aliasing: `Mut` values are second-class (downward-only)").

### Annotation kinds: exact and bounded

An annotation at a binder answers one of two different questions, and CHL spells them differently because the answers diverge.

`𝑥 : 𝑇` is **exact**: the binder's type *is* `𝑇`. The initializer (or, at a parameter, the argument) must satisfy `rhs <: 𝑇`, and everything downstream of the binder sees `𝑇` — the value's own type is not observable through it.

`𝑥 <: 𝑇` is **bounded**: the binder's type is *inferred*, with `𝑇` as an upper bound. The value's own type flows through; `𝑇` only constrains what may reach the binder.

The two coincide only where the value's type already *is* the annotation, leaving nothing to discard. They differ wherever the value's type is a **strict** subtype of it — and the annotation's own shape does not decide that, because a Cambra type carries more than a base:

* **Width.** `x : {a: Int} = (a=1, b=2)` binds `x` at `{a: Int}`, so `x.b` is an error. `x <: {a: Int} = (a=1, b=2)` binds `x` at the record's own type, which still has both fields, so `x.b` is `Int@2`.
* **Refinements.** A literal is typed by its own value ([A literal is refined by its own value](#a-literal-is-refined-by-its-own-value)), so `x : Int = 5` binds `x` at `Int` — the annotation is precisely what discards the singleton — while `x <: Int = 5` leaves it at `Int@5`. Only the second still discharges `arr[x]`'s index-range obligation.
* **Delivery.** Trait narrowing consumes bases that *arrive* at an operand ([Delivery: the watch follows the edge](#delivery-the-watch-follows-the-edge)), and only the exact form puts one there — it binds at `Int`, while the bounded form binds at a variable that `Int` sits above. Both `def f(x: Int): x + "s"` and `def f(x <: Int): x + "s"` are ill-typed and both are rejected with no call site, but not by the same machinery: the exact form delivers `Int`, which narrows the obligation until `"s"` empties it, while the bounded form delivers nothing and is caught instead by [Requirements are read together, once](#requirements-are-read-together-once), reading the requirement against the bound already recorded on the value.

  This last one is a difference in *reach*, not in meaning, and it is the only bullet here that is. Do not read it as the split saying that `x <: Int` promises less; what it promises is stated above, and this row is about which mechanism happens to notice.

The refinement case is worth reading twice: the annotation is a bare `Int` and the forms still differ, because `Int@5` is a strict subtype of `Int`. A "simple" annotation is no guarantee that the two agree — only a value that knows nothing beyond the annotation is.

Both kinds apply at both binder positions, `let` and function parameter, with one rule each. The distinction and the two spellings are both settled; the spec states them and gives the reasoning for the tokens ([chl-spec.md](../../../docs/chl-spec.md), "Two annotation forms: exact and bounded"). Nothing below depends on which tokens they are: the mode is a two-valued property of a binder that lowering reads off the surface and turns into `BoundedHole`-or-not, so the surface and the representation are independent.

| | `𝑥 : 𝑇` (exact) | `𝑥 <: 𝑇` (bounded) |
|---|---|---|
| `let` | bind at `𝑇`; require `rhs <: 𝑇` | bind at the inferred RHS type; require it `<: 𝑇` |
| parameter | bind at `𝑇`; every call site requires `arg <: 𝑇` | bind at a fresh variable; require it `<: 𝑇` |

The bounded column is the *only* behaviour that existed before the split, at both positions: a binder annotation contributed one upper bound and nothing else, because `bind_annotation` is one-way (`inferred <: ann` — an annotation has to admit the value, not equal it). A parameter's type was therefore the **meet** of its annotation and whatever its body demanded, which is worth stating plainly because it is neither of the two readings one expects: in `def f(v <: {a: Int}): v.b`, the annotation admits the argument and the projection widens the demand, so `𝑣` ends up at `{a: Int, b: 𝑇}` and callers must supply both fields. That is still what the bounded form means; the split gave it its own spelling and gave `:` the exact reading.

Neither rule needs a mode test at its binder. A parameter binds at `normalize(annotation)`: exact normalizes to `𝑇` itself, bounded to a variable bounded by `𝑇`, and the old two-step (bind at a fresh variable, *then* reconcile against the annotation) is what made an exact annotation behave as neither reading — it contributed one upper bound among several instead of being the type. A `let` binds at the same normalization of its (completed) annotation, and two special cases fall out as consequences rather than tests: a **deref-copy** (`y: Int = x` off a mutable variable) binds at the annotation because that is what exact *means*, and a bare `_` completes to the initializer's type, which for a mutable-variable initializer is the *value* it reads — so `y: _ = x` binds exactly where `y = x` does, and writing through `y` is rejected the same way.

#### BoundedHole is a marker in a type slot, not a type

The bounded form is represented by a `Type::BoundedHole(𝑇)`, which `normalize_annotation` erases into a fresh variable carrying `𝑇` as an upper bound. It is the same kind of object as `Type::Hole` one rung up: `Hole` is the unbounded case, and the two compose in exactly the positions where a compound annotation is partly specified.

Neither is a type, and that is the first thing to know about `BoundedHole`. `Hole`, `Infer`, and `BoundedHole` all inhabit the `Type` enum because *annotation and binder positions are typed positions*, not because they denote anything: `BoundedHole(𝑇)` is not "the type of values below `𝑇`" — no such type exists, since a bound picks out no set of values on its own. It records an obligation for inference to discharge, and inference discharges it by minting a variable and giving it `𝑇` as an upper bound; the bound then lives where bounds belong, on a variable in the constraint graph.

The consequence is that no *typing* rule may take a `BoundedHole`. There is nothing to subtype against, nothing to narrow, nothing to compact — the solver asserts this rather than inventing a rule (`constrain::extrude`, `compact`). Only the structural walks that rewrite every slot uniformly — substitution, free-variable collection, refinement stripping — pass through one, and they do so because they are indifferent to what a slot means.

Putting the bound *in the type* rather than beside it is forced by the **multi-parameter encoding**, not chosen for symmetry. A `def` with more than one parameter uncurries to a single tuple parameter whose annotation is one `Type::Tuple`, with `Hole` at each unannotated position (`lower::functions::uncurry_params`). So `def f(x: 𝐴, y <: 𝐵, z)` has to express three distinct annotation modes *inside one type*, and `Tuple([𝐴, BoundedHole(𝐵), Hole])` does it with no new plumbing. Carrying the mode alongside the type instead would need a mode *tree* mirroring the type's shape, which is this variant in a worse spelling.

#### BoundedHole cannot outlive inference

`BoundedHole` is inference's to erase: Pass 1 replaces it with an `Infer` variable, and nothing downstream can observe one — not by convention but because **the slot it would live in does not survive inference at all**. See [The binder slot, and why annotations do not outlive inference](#the-binder-slot-and-why-annotations-do-not-outlive-inference); the bounded form needs no lifecycle rule of its own.

That the slot does not survive is what makes the guarantee structural, and following `Hole`'s precedent instead would *not* have sufficed. `Hole`'s discipline is erasure plus a check on `ty` slots (`UnresolvedHole`) — which leaves annotation slots covered by neither, so an un-erased marker can sit in one to the end of inference whenever a compound annotation is partly unspecified. That is survivable for `Hole`, which means "unspecified" and is read as such; it is not survivable for `BoundedHole`, which carries a *bound* that something must discharge. A marker whose whole content is a constraint cannot be left somewhere nothing looks.

The remaining backstop is therefore narrow: a binder `ty` is the only slot a `BoundedHole` could reach, and `collect_type_errors` reports `UnresolvedBoundedHole` there. Nothing is expected to trip it — a `BoundedHole` reaching the solver un-normalized fails earlier, since there is no rule for constraining against one.

#### A Hole inside an exact annotation is still inferred

An exact annotation may be partly unspecified — `x: List(_) = [1, 2, 3]`, or the `Feed(_)` bindings the corpus uses. A `Hole` there means "infer this position", so the binder's type is the annotation **with each `Hole` filled from the corresponding position of the inferred RHS type** (`emit::complete_annotation`). That makes `x: _ = e` exactly equivalent to `x = e`, and `x: List(_) = [1, 2, 3]` bind at `List(Int)`. Records complete by *name*, so a field the annotation does not mention is dropped rather than completed — which is exactly the width an exact annotation discards. A **parameter** has no initializer to complete from, so a `Hole` there is simply a fresh variable resolved from the call sites.

The filling is a structural function on the two types, deliberately not a constraint: binding at a normalized annotation and relying on the one-way `rhs <: ann` edge to drive the annotation's fresh variables does *not* work — those variables are minted at the outer level, after the RHS's level has been popped, and escape inference unresolved. Shape disagreements need no handling here, because a `rhs` that cannot flow into `ann` at all is already an `AnnotationMismatch`.

#### A `Mut(…)` annotation is exact

`Type::History` is **invariant in both payloads**: `constrain` relates two histories of
the same kind in both directions, because a mutable variable is read *and* written
through the same binder. A `:=` binder's type is a `Mut(𝑉, 𝐷)`, and those two facts
together rule out both of the spellings a mutable introduction does not accept. Lowering
rejects them (`lower::stmts::check_mut_decl_annotation`) rather than reinterpreting them:

* `𝑥 <: Mut(𝑉) := 𝑒` — under invariance the only type below `Mut(𝑉, 𝐷)` is `Mut(𝑉, 𝐷)`,
  so the bound admits exactly the annotation and `<:` claims nothing `:` does not.
* `𝑥 : 𝑉 := 𝑒` — a plain value type names the wrong thing. The binder is at `Mut(𝑉, 𝐷)`,
  so reading a bare `𝑉` there would make `:` mean something at a `:=` binder that it
  means at no other.

The invariance argument does not depend on the binder being a `:=`, so it rejects a
bounded pass-by-reference parameter too (`lower::functions::mut_param_history_type`):
a `Mut(…)` annotation is exact wherever it is written.

The consequence for the representation is that a `BoundedHole` never wraps a history,
which `normalize_annotation` asserts. That is worth stating, because the alternative is
representable and tempting: **distributing** the bound into the value position, as
`Mut(BoundedHole(𝑉), 𝐷)`. A mutable variable binder's slot must stay structurally a
`History` — `mut_value_type`, the deref coercion in `constrain`, `mut_elim`, and
`transact_phase` all dispatch on that shape, and a variable standing for the whole handle
would skip a write's `value <: 𝑉` edge — so the value position is the only slot a bound
*could* occupy. But that is a fact about the pipeline, not about what `<: Mut(𝑉)`
denotes; distributing silently re-points the bound at a type other than the one written.
Rejecting leaves "a mutable whose value type is inferred under a ceiling" with no
spelling, which is the honest position: under invariance it is not a bound on the
binder's type at all, and no surface syntax puts a bound in a nested position (see
[chl-spec.md](../../../docs/chl-spec.md), "Two annotation forms: exact and bounded").

#### Exact annotations bound monomorphization

An exact parameter annotation is the program's only lever over specialization count, and this is the sharpest practical consequence of the split.

Specialization is keyed on instantiation identity ([Keying a specialization](#keying-a-specialization)), whose negative read follows a domain's *lower* bounds — the argument that flowed in. With a bounded (or absent) parameter annotation the domain is a variable, so each call site's argument type reaches the key, and the definition splits **per distinct argument type, including per literal value**: `let f = λ 𝑣 → 𝑣 + 1 in let a = f(1) in let b = f(2) in a` yields two clones of one body, distinguished only by the singletons `1` and `2`.

An exact annotation binds the parameter at a concrete, level-0 type. `freshen_above` short-circuits it, every instantiation shares one domain, no argument refinement can reach the domain position, and the uses collapse to a single specialization.

Two caveats keep that from being a blanket guarantee. First, the win is confined to the domain, and the key's *codomain* read follows the consumer's demand — deliberately, since the clone is coalesced under this use's pin and a key blind to the consumer would under-split. So an exact annotation collapses the uses only as far as their consumers agree. Second, the bounded form is genuinely per-call-site checked rather than checked once: `freshen_above` copies a variable's bounds, so the `<: 𝑇` obligation is instantiated with each use and enforced at every argument position.

### Flowing In: normalizing annotations

There is no conversion *into* a solver type — the solver consumes `ccl::Type` as-is. The only adjustment Pass 1 makes is `normalize_annotation`, which readies a user annotation / expected type for constraint solving:

* **Holes (`Type::Hole`):** become fresh `Type::Infer` variables at the current level.
* **Bounds (`Type::BoundedHole(𝑇)`):** become fresh `Type::Infer` variables at the current level, carrying `𝑇` as an upper bound — `Hole` with a ceiling (see [Annotation kinds: exact and bounded](#annotation-kinds-exact-and-bounded)).
* **Shared holes (`Type::SharedHole(id)`):** the first occurrence of an id mints a fresh variable
  and every later one reuses it, so two annotation positions carrying one id resolve to one
  variable.
* **Refinements:** are **kept** (recursing to normalize the inner) — they ride the lattice natively (above). A `Refinement(Hole, r)` source annotation thus becomes `Refinement(?fresh, r)`.
* **Everything else** — including existing `Type::Infer` vars, `Tuple`/`Record` products, and `Type::Variant` sums — is kept verbatim and handled by the solver's structural constraint rules. Tuples and records are width-subtyped positionally/by name; variants are admissible at both polarities (the dual of records), so they need no fresh-var indirection.

#### A shared hole naming a domain states an equation

`bind_annotation` is one-way, and the domain position is contravariant, so a shared id lands below
every domain annotated with it rather than equal to any of them. That is a common lower bound: it
orders each domain under the variable and says nothing between the domains. Lowering writes the id
to claim that two positions are one domain — an unfiltered single-generator comprehension and the
source it iterates. A [data domain](#data-domains-are-invariant) is invariant, so the claim is an
equation, and `bind_annotation` draws its other half.

The equation is drawn only where the id names the domain. A domain variable reached any other way
may receive several domains by design — a conditional collection's arms, a domain-generic consumer's
parameter — and `constrain_go`'s invariant-domain arm declines to equate those for that reason.

It is never drawn against a bound witness. A sum's domain is its binder's reference, and entering a
sum is a term ([Only a term builds a sum](#only-a-term-builds-a-sum)), so equating that reference
with a free variable escapes the binder instead of relating two positions.

The merge at a negative position takes no matching exclusion, because it states nothing. A
reference meeting a concrete type is settled where the edge is drawn: `constrain_go` distributes
the demand over the witness's candidates, one invariant edge each, and reports a mismatch where
the kind names no candidate. Compaction reads back only what those edges admitted, and a
reference and a concrete atom arriving at one position are two shapes, which `coalesce_compact`
reports as `IncompatibleBounds`.

### Flowing Out: coalescing

Once constraints are resolved (Pass 2), `coalesce_compact` resolves each node's `Type::Infer` variables in place:

* **Products:** dense `Index` keys become `Type::Tuple`; `Name` keys become `Type::Record`; a sparse `Index` product (an open/under-determined position) coalesces to a fresh `Type::Infer` rather than a concrete product. **No keys at all has no type** — a positive merge intersects field sets, so the empty map is what two products sharing no field merge to, and there is no zero-field product for it to be: `Type::Tuple([])` and `Type::Record([])` are invalid, and unit is a *base* type a product reaches only through an operation that says so (see [docs/chl-spec.md](../../../docs/chl-spec.md#66-the-empty-product-is-unit)). The position is rejected as `CoalesceError::IncompatibleBounds` — bounds with no common shape, which is the same rejection two colliding atoms get, read one level down. The `product` constructor still maps the empty case to `Unit`, because a *constructed* empty product is an operation that says so; the empty case has no keys to tell positional from named keying, so without that collapse each construction site would pick a spelling arbitrarily and two spellings for one type fail to reconcile at the consistency wall, which compares a node's recorded type against one rebuilt from its children.
* **Variants:** materialize into `Type::Variant(Vec<(FieldKey, Type)>)` with tags in `BTreeMap` order. A variant payload sits at a record-field-like position, so it inherits that position's polarity and coalesces by the same rule as a record field value. An all-`Index` variant pretty-prints as a bare `A | B | C`. Arm *order* is a presentation detail and nothing depends on it: arms are keyed by tag everywhere downstream — in a `Type::Variant`, in a runtime union column, and in `variant_project`/`variant_wrap` — so a variant a pass constructs by hand (the writer decision variant ``{`commit{𝑃} | `abort}``) and the same variant materialized by the solver in sorted order are interchangeable.
* **Refinements:** the refinement set carried at a position is re-attached to the materialized inner type through `Type::refined`, which is one `Type::Refinement` node holding the whole set — there are no layers to order. An empty set (and the `None` a non-value contribution carries) yields the bare type.
* **Incompatible bounds:** if a variable accumulates multiple distinct concrete primitives (e.g. `Int` and `String`) with no tag to discriminate them, the solver emits an `IncompatibleBounds` error. A *tagged* sum is unaffected — ``{`i{Int} | `s{String}}`` is a single `Variant`, not a primitive collision.
* **Recursive types:** the algorithm has no occurs check. With one-way Apply edges a self-application like `λx. x x` produces no cyclic bound graph — it types cleanly (MLsub would give `(α ∧ (α ⇒ β)) ⇒ β`; Cambra drops the unconstrained `α` leg and infers `(?a ⇒ ?b) ⇒ ?c`, an unapplied-lambda type carrying `Infer`s), while *misusing* one (`(λy. y y)(1)`) still fails with `ExpectedFunction`. Should a residual cyclic bound graph ever form, `coalesce_compact` rejects it with a `RecursiveType` error — a defensive check; no current emission path produces one.

---

## 4.5 Dependent refinements via Pi types

Some refinement predicates **close over an outer binder**. The motivating case is group-by: partitioning `xs` by `key_fn` produces, per key `𝑘`, the partition `{𝑖: 𝐼 | 𝑖 ▷ xs ▷ key_fn == 𝑘} ⇒ 𝑉` — the predicate references `𝑘`, bound *outside* the refinement. Expressing, propagating, and discharging such predicates inside the solver is what the Pi-type machinery adds. (This folds in the durable material from the original point-in-time design proposal for dependent refinements via Pi types.)

**Pi types.** `Type::Fun` carries an optional binder: `Fun { name: Option<Name>, domain, codomain }`. `name: Some(𝑥)` is the dependent type `(𝑥: domain) ⇒ codomain`, with `𝑥` bound in `codomain`; `name: None` is the ordinary function type. `emit_lambda` always names the binder from the lambda parameter, so a predicate that closes over the parameter stays bound. The binder is **cosmetic for ordinary functions** — `coalesce_compact_go` keeps it only when the codomain's refinement predicates actually reference it (queried via `subst::type_free_vars`) and strips it otherwise, so monomorphic output is unchanged and equality/printing don't churn.

**Substitutions and contexts (`ccl::subst`).** A `Subst` is a context morphism that maps *term* binders (`Var` names) to replacement `TypedExpr`s. It never relabels a type variable — that is freshening's job. Two flavours: a **rename** `[𝑘 ↦ 𝑥]` (invertible) and a **discharge** `[𝑥 ↦ arg]` (one-way). The traversal is uniform over terms and types: `apply_expr` rewrites each node's type slots via `apply_type` in the same pass, so a substituted binder occurring inside a type-borne refinement predicate is discharged where it sits (no value-only contract, no dangling residual for §6.2 to catch in release builds). It is a true no-op when no substituted binder occurs free in the term — value or type slots — so a vacuous discharge from a non-dependent application changes nothing and shares the predicate `Rc`. Capture is impossible under the Barendregt convention (binder uids are minted once at lowering; copies preserve them) and the engine *asserts* it instead of α-renaming. Predicates are immutable, so a substitution always *rebuilds* a changed predicate (a fresh `Rc`); the engine drives two modes that differ only in what else they touch: **transport** (`apply_expr`/`apply_type`, builds new terms — the constraint-edge flavour) and **in-place rewrite** (`rewrite_expr`, mutates the term tree the caller owns; a predicate the substitution actually touches is rebuilt, one it merely walks past keeps its `Rc` — the pass-level flavour that `lambda_elim::substitute`, `channelize::channelize_substitute`, inlining's beta step, and lowering's uncurrying all wrap). Both modes thread the same `PredMemo`, so occurrences that shared one term are re-pointed at the same result. A **context** (`well_formed` / `type_free_vars`) is the dual *checking* device: a type is well-formed iff its predicates' free term-vars are in scope.

**Edges carry substitutions, stored two-sided in their native direction.** Each entry of a variable's bound lists is a `Bound { self_subst, ty, ty_subst }`: an upper entry on `𝑉` reads `𝑉‹self_subst› <: ty‹ty_subst›`, a lower entry `ty‹ty_subst› <: 𝑉‹self_subst›` (both identity for ordinary bounds). `constrain_subtype` delegates to `constrain_go(lhs, rhs, sl, sr, cache)` — each side under its own morphism. The **Fun/Fun arm derives the binder correspondence** `[𝑘 ↦ 𝑥]` onto the lhs side of the codomain edge, and the contravariant domain edge **swaps the two sides** rather than inverting anything. The var arms record edges verbatim — *nothing is inverted at record time*. A **discharge has no inverse**, so edges are recorded in their native direction rather than pre-inverted and re-inverted during closure (which would degrade a discharge to the identity, silently destroying it whenever a consumer edge is recorded before the producer's concrete codomain arrives — the opaque/higher-order application order, O3). Under identity morphisms every arm reduces exactly to the substitution-free solver, so all monomorphic inference is byte-identical.

**Closure chains by bridging holder views, composing forward only.** When a new edge meets a variable's existing opposite edges, the two entries hold `𝑉` under possibly different morphisms (`lo`, `hi`); `bridge_holder_gap` reconciles them by moving whichever side is movable (substitution application is monotone w.r.t. subtyping): equal morphisms need no bridge; an invertible side bridges by `hi ∘ lo⁻¹` (renames only — lossless); two non-invertible composites that share their discharge part and differ only in correspondence renames are factored (`Subst::split_renames`) and bridged on the rename part. Two *distinct* discharges meeting at one variable is the domain-join corner (O1/O4), guarded by `invert_rename`'s panic — the loud tripwire, never a silent drop. The **constraint cache is σ-aware**: it keys each `(lhs, rhs)` pair on the *set of side-morphism pairs* seen, so `g(0)` and `g(1)` flowing into one position record two distinct edges instead of the second being conflated away; termination holds because cyclic (var⇄var) edges carry renames over the episode's finite binder set, whose composites saturate, while discharges ride acyclic content edges.

**Coalesce forces suspended substitutions.** `compact_go` threads a substitution accumulator: descending a bound edge composes the edge's *rendering morphism* (`edge_render_subst`: `ty_subst`, transported across `self_subst` by rename-inversion, or by the identity for a discharge — exact because the content lives in the post-discharge context and cannot mention the discharged binder, debug-asserted) and the composite is applied — *forced* — at each refinement-predicate leaf. A bound reached transitively through `𝑣 → 𝑤 → …` thus arrives with every edge's morphism composed (the deferred transitive closure recovered by the walk). Identity accumulator ⇒ no-op.

**Dependent application.** `Typing::apply` types `f(arg)`. Emit constrains `fn_ty <: (𝑥: 𝑑) ⇒ result` against an expected Pi (the one-way Apply shape edge of §2) and returns `result` under a suspended discharge `[𝑥 ↦ arg]` on a fresh variable's lower edge, fired on the partition predicate at coalesce. So `groupby(xs, key)(𝑘₀)` types as `{𝑖 | 𝑖 ▷ xs ▷ key == 𝑘₀} ⇒ 𝑉`. The **post-inference check** (`CheckCtx::apply`) re-runs the discharge on the resolved codomain so its reconstruction matches; `force_refinement` rewrites the predicate to the same term in both places, so the two refinements compare equal under structural refinement equality (§4).

The expected binder is **always globally fresh** (proposal §5.2 verbatim; the §3.6 freshness discipline). The two-sided edge storage is what makes this sound at every polarity and in every constraint order: the correspondence `[𝑘 ↦ 𝑥]` and the discharge `[𝑥 ↦ arg]` compose forward along the closure regardless of whether `fn_ty` was concrete at the apply site or resolved only later (the opaque/higher-order case — a dependent function received as a *parameter* — now discharges correctly, unblocking O3 at the graph level). A contravariant position is reached by side-*swapping*, not inversion, so the discharge arrives at a `map`/aggregate's parameter domain intact. The remaining deferral is the domain-join corner — two *distinct* discharges meeting at one coalescing position (O1/O4) — guarded loudly by the closure bridge's tripwire.

**Discharged-argument slot resolution.** A predicate's interior is typed **by construction**, and the invariant that makes that hold is that *substitution never discards a type*. A `Discharge` carries a typed argument term and clones it; a `Rename` materializes as a fresh `Var` node and takes the type of the occurrence it replaces, because α-renaming cannot change a term's type — the type belongs to the position, not to the name. Nothing re-derives a predicate's types afterwards, and nothing may: a predicate's interior is outside the walk that resolves node types (its terms ride a *type*), so a slot left untyped here would survive to the post-inference wall as an unresolved variable with no way to recover it except lexical scope — which is a *name* lookup standing in for a type that was thrown away. (`freshen_above` separately copy-and-freshens a specialization clone's predicate type slots.)

**`let`-closing (codomain extraction).** A `let 𝑥 = 𝑣 in body` node's type is the body's type, which may close over `𝑥`. Emission records the lift as a suspended discharge on the `let` node's own variable (see [`let` binders and scope exit](#let-binders-and-scope-exit)), and `coalesce_node` discharges `[𝑥 ↦ 𝑣]` into the resolved type (derived from the body's already-closed type, so chained `let`s close to fixpoint) — the design's `let`-closing refinement-move site. The discharge quotes `𝑣`, so a pass that rewrites `𝑣` re-runs it: `lambda_elim`'s two `Let` arms rebuild the node's type from the eliminated body and definition, and the post-pass check reconstructs it from the tree it is handed, which holds the eliminated `𝑣` alone. Only a dependent binding is rebuilt, so elimination changes a node's type exactly where the term it quotes changed. Together with the contravariant discharge above, every coalesced node's type is **well-formed in its lexical scope**, checked at the end of inference by `check_scope_valid` (§6.2) in debug builds: a free predicate variable must be bound by an enclosing Pi binder or AST binder, or be a source. A violation is a compiler bug (a substitution-descent miss leaving a dangling predicate binder), reported as an internal `InferError::ScopeViolation`. This is a debug-build regression net: because substitution rewrites type-borne occurrences in the same pass as the term, a dangling predicate binder is structurally unrepresentable; the per-substitution `debug_assert`s in `ccl::subst` remain as fast-path guards.

**Lambda elimination.** A `λ 𝑥 → e` whose binder is free only in `e`'s *type* (a refinement closes over it) — not its value — eliminates to the **Pi-const** form `const(e) : (𝑥) ⇒ e.ty` (`is_free_in_value` distinguishes the two). It also fires after the currying/pairing rule rewrites a captured partition predicate onto a pair domain: the residual `λ __pair → <point-free value>` has its binder free only in that refinement.

**Deferred (flagged in code).**
* **O2 (polymorphic case)** — `freshen_above` copy-and-freshens a refined value's predicate type slots through the shared cache (its `Refinement` arm), so a specialization's predicate is a proper freshen instance rather than a shared `Rc`. Immutable predicate terms are acyclic, so no refinement-cycle guard is needed.
* **O4** — two *different* discharges of one refinement (`g(0)` vs `g(1)`) are distinguished once forced — `force_refinement` rewrites the predicate term and refinement equality is structural (§4) — and the constraint cache is σ-aware, so the two discharges record distinct edges rather than conflating. The residual domain-join corner is two *distinct non-invertible* morphisms meeting at one variable (O1/O4), guarded loudly by `bridge_holder_gap`'s panic tripwire rather than silently dropped.

The pipeline passes downstream of inference treat function types structurally and compare modulo the Pi binder (`Type::without_pi_names`). **Refinement-predicate compilation is deferred out of lambda-elim** (proposal §6.3): predicates ride through inference and lambda-elim in their bare pointful form (a bare boolean over the implicit `REFINEMENT_BINDER`), and **planning** compiles them. Order matters: the group-by / hash-join recognizers run *first*, on the bare form — compiling first would destroy the pointful shapes they match (see the pointful-join-recognizers plan) — and `planning::compile_refinement_predicates` then runs the lambda-elim → simplify sub-pipeline on each remaining predicate (keyed by predicate `Rc` identity) before the generic `iterate`/`restrict` lowering consumes it. This is what lets a refined collection — including a group-by over a *filtered* source (`[sum(x) for x in groupby([y+10 for y in xs if y<6], key)]`) — compile to a runtime `Restrict`/`Filter` rather than reaching op-conversion as an un-compiled predicate. Single-key dependent lookups (`sum(groupby(xs, key)(k))`) and the nested filtered-source group-by both run end-to-end with correct values.

### Scoped inference variables: a stored bound closes against a telescope

A refinement predicate may reference an enclosing binder, and the bound carrying that refinement
travels away from the binder during inference. Group-by's lowering does that: it puts the dependent
refinement in a cast target while the function binding `__gb_k` is minted separately, so the
refinement lands on a variable whose position has no enclosing function. Nothing checked it there —
`check_scope_valid` runs on coalesced node types once inference ends, never on bounds — and the
sites that decide identity compare stored types structurally, which is α-sensitive.

Two mechanisms answer that. Each inference variable carries the scope it was created in, and a bound
recorded on it that references anything else is a record-time internal error. References a bound's
own functions introduce are stored as de Bruijn indices assigned when the function is constructed,
so two α-variant closed types are structurally identical at every site that decides identity:
refinement-set dedup, `CompactType::merge`, the constraint cache, and `SpecKey`.

#### The invariant

Every inference variable records the **telescope** of binders in lexical scope at its creation: Pi
binders and `let` binders, interleaved in scope order. Emission already holds this context at every
`fresh()` — `InferCtx::scopes` tracks in-scope bindings for `Var` typing — and discards it.

A bound recorded on a variable **closes against the holder's telescope**: every free term variable
of the bound's type is in the telescope or in the edge's substitution domain. The check runs when
the bound is recorded, and it is a lookup, since uniquify gives every binding site one uid. A
violation names the variable and the reference and fails. Every build enforces it: a release
compile rejects what a debug compile rejects.

An opaque binder is in every telescope of the walk, whatever the lexical position. It carries no
definiens, so a type lifted past it keeps the name and the name outlives its scope ([`let` binders
and scope exit](#let-binders-and-scope-exit)). The telescope therefore holds an opaque set shared by
every variable the walk mints, and entering the binder adds to it, reaching the variables minted
before it as well. That is what admits a write to a mutable variable declared outside the binder:
`x := 0` mints the value variable under an empty telescope, and `x := x ^+ 1` contributes
`{Int | __elem == __read ^+ 1}` over the read binder minted inside
(`src/ccl/design/mutability.md`, "A read is named while inference runs"). The end-of-inference check
states the same rule tree-wide, seeding its root scope with every opaque binder the tree holds
(`check_scope_valid`).

TODO: Opaque binders are exempt from the invariant check at record time, and so escapes of opaque binders currently surface later.

A binder carrying a definiens stays out of that set, its reference being discharged rather than
carried. A `for` target carries neither, so a contribution naming one still fails the check.

Enforcement covers every derivation: the live solve, meaning emission and its specialization pins,
and the pass-boundary re-derivations that check what a pass produced. A re-derivation walks a tree
where a pass has erased term binders, and the refinements it meets still name them. The dependent
function's type binds them there, and the chain walk enters its Pi binder (see [Where the
conversions run](#where-the-conversions-run)). The tree holds every binder its refinements
reference; a reference to one it does not hold is a bound that left its binder's scope.

`ConstrainCache::for_derivation` names the two cases, and the `Fun`/`Fun` codomain edge reads the
same value (see [Where the conversions run](#where-the-conversions-run)).

A program source needs no standing in the telescope, because the check never sees a reference to
one. A source is referenced by a `TypedExprNode::Source` node rather than by a variable: lowering
emits that node for every source reference, `emit_node`'s `Source` arm types it from the source
registry, and the `Var` arm resolves against the scope stack alone and rejects any name not in it. A
source name therefore never reaches `subst::type_free_vars`, so every gap the check finds is a
reference some pass failed to rewrite.

#### A binder reference is stored in one of two forms

The form says whether the type itself binds the reference. The scheme is the standard locally
nameless one: a free reference is a name, a bound one an index.

- **A reference to a telescope entry is a name.** A uniquified name identifies its telescope entry
  exactly, so the record-time check is a lookup, and the same name denotes the same binder at every
  holder that may legally hold the bound. A bound crossing a variable-to-variable edge therefore
  keeps its references as they stand, and the reader re-runs the closure check against its own
  telescope. The discharge machinery keeps addressing binders by name, unchanged.
- **A reference to one of the type's own functions is a de Bruijn index, assigned at abstraction.**
  Constructing a function over a body closes the body: a free reference to the function's binder
  becomes an index counting outward. The type constructors own the conversion, so a function they
  build cannot carry a free name for its own binder, and a closed function is α-canonical. That is
  what the merge, the caches, and `SpecKey` compare on.

The split follows from where identity runs. An identity site sees a refinement without its enclosing
functions — `merge_refinements` compares refinement sets sitting beside `CompactFun`'s `name` slot,
one function below it — so a reference must say which of the two kinds it is, on its own. A name is
ambiguous between them; an index is the second kind and names the function by counting. The
telescope supplies context for the first kind and cannot for the second, whose binders are not in
it.

Structural equality then needs no context: names are globally unique, indices are anchored to
functions that travel with the type, and neither needs re-basing anywhere. The constraint cache's
`(Type, Type)` key is unaffected.

`Type::Fun`'s `name` slot therefore carries no identity: a refinement's binding is its index, so the
slot never participates in an identity comparison. It is the opening address that descent and
application open the function at, so coalesce keeps it exactly on the functions whose codomains
reference it (`subst::codomain_depends_on`) and strips it elsewhere.

#### Interior term binders stay named, and compare by position

A refinement's predicate may contain a term lambda — `λ x → x // 2` in the group-by case — and its
parameter stays a name. That binder sits inside the refinement rather than outside it, so the
compared terms carry it and the correspondence is local: `eq_term_modulo_ty_slots` threads a
pairing and compares a reference to it by its binder's position, and `hash_term_modulo_ty_slots`
hashes it by position so
the `Eq`/`Hash` contract survives. The name stays the stored form, so the predicate is still a term
planning can compile.

Closing treats such a parameter as a shadow: inside the lambda, a reference spelled like the
enclosing function's binder is the lambda's and keeps its name. Uniquification already keeps the two
spellings apart in a compiled program, so the shadow makes closing correct without depending on that
convention, as the `Fun`/`Fun` opening gate does not depend on it either.

Positions and indices are both needed. Every refinement a program produces routes its element
through a function, so it carries an interior lambda, and a filter written twice mints that binder
twice (`λ x#3 → x#3 > 1` against `λ x#6 → x#6 > 1`). Comparing it by name splits a refinement set
that should dedup, and a `Data` domain admits no join across the split: with indices alone,
`if c: [x for x in xs if x > 1] else: [x for x in xs if x > 1]` is rejected
(`tests/type_check.rs`, `test_case_with_filtered_comprehension_arms_passes_consistency_wall`).

#### `let` binders and scope exit

A `let` telescope entry carries its definiens. A refinement may reference it while in scope, which a
user-written refinement type needs (`{Int | __elem > n}` with `n` let-bound). Lifting a type past
the binding discharges the reference to the definiens. No re-addressing is needed: a uniquified name
is its telescope entry's address, so the name-keyed discharge already speaks in entries. A Pi entry
has no definiens, and lifting past one abstracts instead of discharging.

An opaque entry (`x ^= e`) has no definiens either, and lifting past one does neither: the name
stays in the lifted type, and what it means there is the type the binder was bound at, recorded when
the binder is entered (`InferCtx::opaque_binders`) and read by every later refinement query. Entry
rather than exit, because a bound naming the binder is recorded inside its scope.

Emission records the lift, and cannot perform it: the body's type is an inference variable there,
whose refinements sit in its bounds rather than in the type. `InferCtx::close_let_type` mints the
`let` node's type outside the binder and records the body's type on its lower edge under `[𝑥 ↦ 𝑣]`,
a suspended discharge read as an application. Every bound naming `𝑥` then crosses an edge that
discharges the name, and β fires at coalesce. Returning the body's variable verbatim instead lets a
refinement over `𝑥` reach the enclosing lambda's codomain, which is minted outside the binder and
so trips the record-time closure check at the first call site that reads the codomain.

#### A lambda's codomain drops the body's opaque binders

An opaque binder the body introduced stands for one value per call, so a refinement naming it says
nothing about the function's result: it would relate the results of `f(1)` and `f(2)` through one
`r`. `Typing::close_body_type` drops such a refinement and reports the base type, a supertype, so
every result the function produces still inhabits the codomain. A binder still in lexical scope
where the lambda's rule runs was introduced outside the body and denotes one value for the whole
function, so it stays; what is dropped are the binders whose scope closed inside the body.

Emission drops on a second variable rather than on the body's own, so the body node keeps the type
its own rule gave it. `body_ty <: codomain` is an ordinary edge, so what reaches the body's type
still reaches the codomain, call-site bounds included, and the edge's closure deposits the body's
concrete lower bounds on the codomain variable directly, following variable-to-variable edges on the
way. The refinements to drop therefore sit on that variable's own lower bounds, and no later arrival
can name one: a refinement naming an opaque binder is recorded where the binder is in scope, which
is inside the body the rule has just finished emitting.

That variable is minted under the lambda's parameter binder, where the codomain stands: the Pi binds
the parameter in the codomain, so a body refinement naming the parameter closes against the
variable's telescope. Minting it after the parameter's scope closes leaves the parameter out of that
telescope, and the same refinement is then an open bound on it.

A demand on the codomain is met by what flows out of the body rather than narrowing a variable
inside it. `def f(x) => 𝑇` with an unannotated `x` whose body introduces an opaque binder bounds `x`
from its call sites alone; a conflict with `𝑇` surfaces when those bounds reach the codomain.

#### Discharge is application

A `Bound { self_subst, ty, ty_subst }` whose substitution discharges a binder is a closed function
applied at an argument — `(λ𝑥. ty) arg`, written as a type with a free variable plus a map that
promises to remove it. The substitution's domain binders therefore count as the type's own in the
record-time check, and β fires at coalesce against the telescope.

Two mechanisms transported the name form rather than the index, and they retire with it: the
`Fun`/`Fun` `extended_rename` and `Subst::licensed_correspondence_view`. Disabling the licensed view
trips `bridge_holder_gap`'s tripwire on extrusion across levels under a generalized `let` and on
per-occurrence group-by keys through a polymorphic definition, so the index does not subsume them.

#### Where the conversions run

A type is **closed** — references to its own functions stored as indices — from construction on, and
a bound recorded mid-solve is **open**, with references to telescope entries stored as names. An
index counts the functions crossed from their codomain side between the reference and its binder,
named and unnamed alike, so it survives `Type::without_pi_names`. Closing and opening are one walk
each over the mixed type/term structure (`subst`'s `PiWalk`), reached through `close_pi_binder` and
`open_pi_binder` at construction, descent and application, and through `RefinementScope` in the
compact and key walks. Those are the four kinds of site.

**Construction closes.** The type constructors — `Type::pi`, `Type::pi_kinded`,
`Type::pi_eliminated`, `Type::fun_like` — abstract the codomain they are given, and so does every
rebuild that assembles a dependent function around a codomain it computed from node types
(`emit_cast`, `emit_compose`). A codomain that is a bare variable has nothing to close; emission's
`pi(x, D, ?c)` is that case, and the refinements that later accumulate on `?c` reference `x` by name
against their telescopes. A rebuild that carries a `FunKind` takes `Type::pi_kinded` rather than a
`Fun` literal: the group-by partition function (`planning::groupby`'s `emit_groupby`) and the
eliminated group-by lambda's Pi (`lambda_elim`) are dependent collections, and reaching for the
literal to set `kind` leaves a free binder name in a stored type.

Two sites assemble a `Fun { name: Some(_), .. }` and close nothing, one on each side of the
construction boundary. `emit_lambda`'s codomain is the live in-solve type, which stays name-spelled:
its refinements accumulate behind an inference variable, and the compact and key walks are what
close them, so closing the reachable ones here would put an index-spelled refinement and a
name-spelled one at a single position — what closing in those walks exists to prevent.
`coalesce_compact_go`'s refinements arrive already closed, and the `CompactType` it assembles from
mirrors `Fun`s one-to-one, so a closed index counts to the function being built; closing is the
identity there, and the `Fun` literal says so.

**Closing reaches only references spelled as the binder it closes over**, so a codomain carried
from one function into another is aligned before it is closed. Two functions related at a position
have one binder under two names, and `Subst::aligned` is that alignment. Both sites that carry a
codomain across take it: `constrain_go` draws the codomain edge under it, and `complete_annotation`
fills an exact annotation's codomain from its initializer's. A fill that skipped it would leave the
initializer's name free in a stored type, which no construction-time close can repair, because the
name it closes over is the annotation's.

**A refinement closes against the enclosing functions of the walk carrying it.** `compact_go` and
the `SpecKey` walk both do so in the same two arms that force the edge substitutions into it
(`force_refinement`), and `coalesce_type_predicates` does so again on what it rebuilds. That third
site is a re-entry: a predicate's sub-expression type slots hold inference variables `compact_go`
steps over, and resolving them afterwards reads name-spelled references out of the live graph and
puts them back into a type the walk already closed. Nothing earlier can: `CompactType::merge` dedups refinements while bounds
fold, before any function is assembled, so a closed cast and a live emitted function meeting at one
variable would otherwise put an index-spelled refinement and a name-spelled one at a single
position. `subst::RefinementScope` is the state both walks thread — the enclosing-binder stack and
the closing memo in one type, so the two cannot disagree about what a refinement closes against.

**Descent opens.** Walking under a binder converts that binder's indices back to a name. The `Fun`/
`Fun` codomain edge opens each side at its own binder name and carries the correspondence as a
discharge at a variable (`[k ↦ x]`, read as an application), so a bound recorded on an inner
variable references the binder by name and closes against that variable's telescope.
Which derivation is running decides whether that edge opens at all. The live solve opens only toward
a side carrying inference variables, since a dangling index can only land on a bound and only a live
side records one. A re-derivation opens unconditionally, because it reconciles two passes'
spellings of one type.

`normalize_annotation` extends the emission telescope with each Pi binder it descends past, so the
variables it mints inside a dependent annotation carry the binder in scope; this closes the group-by
case, whose refinements land on variables whose telescopes never saw `__gb_k`.
`subst::open_codomain` is the same conversion at a rebuild, where a pass holds a morphism and the
codomain it just read off it. Three passes call it:

- `emit_compose`, before the adjacency `prev_cod <: next_dom`, because the next morphism's domain
  names the binder the chain composes under;
- `lambda_elim`'s application rule, for the `apply` transformer's domain, which sits under the pair
  morphism's binder;
- the group-by recognizer, on the function it matches, because it identifies the key binder as the
  free `Var` on one side of the predicate's equality.

Opening at a name puts a free reference into the type being compared, so the walk descends into the
binder's scope as well. A chain is typed morphism by morphism inside the dependent functions before
it (`emit_compose`'s `compose_chain`), so the variables those steps mint close against the binder
their refinements name: a dependent function and the transformers consuming it are siblings in the
term and nested in scope.

**Application opens at the argument.** Applying a closed function — the dependent-application
discharge, β at coalesce — replaces the binder's indices with the argument term. Opening at a name
and opening at an argument are one operation with a different replacement. The post-inference
check's `apply` rule is this site's second caller: it re-derives an application's type from the
closed function the tree records, so it opens the codomain at the argument before comparing against
the stored, already-discharged type.

Each identity site therefore compares like with like: whether a type is closed follows from which
side of the construction boundary it sits on, not from when it arrives.

#### Display opens what it descended through

An index is a stored form, not a read form. `Display for Type` threads the functions it descends
through and prints a reference to one of them as that function's binder name, so a dependent type
reads with the spellings it had before indices existed:

    ((__gb_k: Int) ⤇ ({[0, 2] | __elem ▷ [1, 2, 3] ▷ (λ x : Int → x) == __gb_k} ⤇ Int))

A display that does not hold the function reads the spelling off the reference instead. A
`Name::PiBound` carries a `PiRef`: the index, plus the binder's spelling where the closing happened.
Identity reads the index alone, so the spelling decides nothing and two equal references may print
differently.

A diagnostic is the display that does not hold the function. It blames a fragment rather than a
whole type — `coalesce_compact_go`'s domain-join conflict reports the domains of the function it is
half-way through assembling, and the function binding their references is further out in the walk,
so there is nothing to descend through. Without the spelling on the reference, that domain reads
`{[0, 2] | __elem ▷ [1, 2, 3] ▷ (λ x : Int → x) == #0}`.

The stored form never converts back. Construction closes at every phase — planning builds functions
through `Type::pi_kinded` — so a one-shot conversion after inference would be undone by the next
rebuild.

#### Freshening and `SpecKey`

The keyed-map type a group-by lowers is the exercising case. A generalized definition holding one,
stored at level `L` with its refinements closed (`#n` is an index):

    (k: ?K) |=> ((i: {?D | __elem |> f == #0}) |=> ?V)

`#0` is the reference to `k`. The predicate sits in the inner function's domain, where only the
outer binder is in scope, because a binder scopes over its codomain and not its domain; the same
reference from the inner codomain would be `#1`.

Freshening copies indices verbatim, and that is the whole interaction. `freshen_above` copies a
`Fun`'s `name` slot structurally, and `freshen_refinement_predicate` rewrites only a predicate's
type slots (through `freshen_expr_type_slots`), leaving term structure including `#0` untouched. An
index is anchored to a function inside the same type being copied, so the copy cannot dangle. Free
names in a predicate — the definition's captured environment, level ≤ `L` — copy verbatim and stay
correct, because every use of the definition sits lexically inside those binders' scope and all
clones share the one captured binder.

`SpecKey` compares the closed spelling across uses. Two uses whose lowered annotations are
α-variant, such as two textually identical group-bys each minting its own binder uids, spell
identically once closed, so their keys agree and the memo shares the specialization. A refinement
referencing a binder outside the walked type keeps its uniquified name in the key, so two uses under
distinct enclosing binders key apart. One function discharged at two arguments keys apart on the
σ-forced predicates, since `key_go` forces each edge's substitution into a refinement before it
lands in the key.

The pin re-bases by opening, not by rewriting indices. `specialize_use` pins a clone to the use's
resolved type: the resolved side is closed, and the clone's emitted functions are live (`pi(x, D,
?c)` with refinements behind variables). The pin's `Fun`/`Fun` edges open the closed side at the
clone's binder names as bounds cross, after which every bound landing on a clone variable is
name-spelled against that variable's telescope. No index is re-based: an index converts to a name at
a binder crossing or to a term at an application, and otherwise travels untouched.

## 4.6 Data vs compute functions

A function either represents a collection or is a capability that can be called.
`Type::Fun` stores which as a `FunKind`, either `Data` or `Compute`.

Lowering chooses the kind from the CHL construct. List literals, comprehensions,
`groupby`, `++`, and registered sources are `Data`; a `lambda` and a `def` are
`Compute`, a generator `def` included — it is a capability whose *result* is a
collection. Where lowering does not yet know the domain and codomain, it states the
kind as a `data_fun` annotation and inference reads that as the stamp. A function
parameter is the one thing lowering cannot decide, having no construct to read: it
gets a kind variable, which the argument pins.

Compute functions follow the usual contravariance on the domain. Data functions are
invariant, because the domain is the exact set of elements the collection holds, so
changing it changes the data. Neither kind converts to the other; they are unrelated
by subtyping.

Downstream phases including inlining and planning dispatch on the distinction, so
every pass carries a function's kind rather than rebuilding one. `Type::fun_like` is
the rebuild that does: it copies the exemplar's kind, so rewriting only a domain or a
codomain cannot turn a collection into a capability.

A `FunKind` answers two questions — whether the domain is data, and, for a sum, which index
the function binds — and only the first travels between types. A cast is where that shows: it
re-views its value at its target, so its node type takes the target's data-vs-capability
answer (`ccl_utils::canonical_cast_ty`) while keeping its own binders. The slot does not
travel, because the index is named at each type's own domain position, so a second type
states it in binders of its own and copying the slot leaves a function binding a name its own
domain does not say.

A kind is never re-derived from a domain's shape, and never from what a consumer will do with
the function. `wrap_with_iterate` asserts that an iteration site is already a collection
rather than making one; a site that reaches it as a capability is a pass that lost the kind,
which is the defect worth reporting.

### A refinement predicate is a data function

A refinement's predicate over a collection yields one `Bool` per element, so its function
form is a collection: `Σ (σ : 𝐾). σ ⤇ Bool` where the domain is a witness. Planning compiles
it under the binders its domain is written under
(`planning::predicates::fn_of_bare_predicate`), and the runtime agrees — `Restrict` evaluates
the predicate over the extent.

Typing it as a capability has nowhere to put the binder. `FunKind::Compute` carries no slot,
so a predicate over a conditional source names a witness its own type does not bind, and
every comparison it reaches needs that binder supplied from outside. Saying it here is what
lets the post-inference check reconcile a node in the empty witness context.

### Generalizing a collection is filter pushdown

`should_generalize` requires a **capability**: a `Lambda` whose kind is not `Data`. The node test
alone does not get there, because `groupby` lowers to a `Lambda` and its type where that predicate
runs is still `(__gb_k: ?𝑘) ⤇ ((__gb_i: {?𝑖 | __elem ▷ xs ▷ key == __gb_k}) ⤇ ?𝑣)` — variables
deeper than the binding level, so the level test admits it. Only the kind catches the one
collection written as a function.

Note *what* that domain refinement is: the dependent group-key predicate of
[Dependent refinements via Pi types](#45-dependent-refinements-via-pi-types). Lookups at different
keys pin `__gb_k` differently, and a `SpecKey`'s negative read follows exactly that
`arg <: domain` edge — so specializing a grouping per use means **one copy of the source filtered
to each reader's key**, which is filter pushdown. That wins when the predicates are selective and
loses when readers are many and overlapping: `sum(g(1)) + sum(g(2)) + sum(g(3))` rebuilds the whole
partition three times where one `Memo` serves all three. The choice is selectivity against reader
count, and inference cannot make it — it runs before planning knows an extent, so the blanket
refusal is the bounded-worst-case side until there is a cost model to consult. The same decision
waits on the term side, where the inlining pass preserves
[collection sharing](optimization.md#collection-sharing).

### Data domains are invariant

The `Fun`/`Fun` domain edge is contravariant, which is right for a *compute*
function: the domain is a parameter, nothing in the language can ask a capability
which inputs it accepts, and shrinking the accepted set only under-promises. A
**data** function's domain is invariant instead;
[The domain join needs `box`](#the-domain-join-needs-box) is the join half of the same
model.

**One lattice.** Subtyping and joining are the same order, so they cannot disagree.
Suppose the contravariant edge applied to data functions, making a wider collection
a subtype of a narrower one — `[0,10] ⤇ 𝑉 <: [0,5] ⤇ 𝑉`, which is `[0,5] <: [0,10]`
at the domain. Then the least upper bound of the arms of `[1,2] if c else [1,2,3]`
is `[0,1] ⤇ Int`, and `sum` of it returns `3` even when the else-arm ran, with
nothing in the type recording that a row was dropped. Under invariance the two
collections are instead incomparable, so they have no least upper bound at all and the
conditional is rejected. Boxing each arm supplies one — the Σ over both domains, which
loses nothing — and that is why the two halves fit together rather than trading off.

**Why the stand-in is not free.** The contravariant reading is tempting because it
looks like record width subtyping, which *is* sound: `{a: Int, b: Int} <: {a: Int}`
because a consumer of `{a: Int}` can only apply a key it declared, so the extra
field is unobservable. A data function has consumers that **reflect** its domain
rather than index into it, and they make the difference observable twice over.

- The declared domain **is the loop bound the program runs**. Op-conversion's
  `Builtin::Iterate` arm builds its iteration source as
  `IterateExtent::new(extent_of(𝐷))` from the *static* domain of the iterate
  marker's predicate. So handing an 11-row collection to a slot declared
  `[0,5] ⤇ 𝑉` does not forget rows the way the record forgets `b`; it emits a
  program that reads six of them and reports the result as the collection's.
- The domain is **reproduced in consumer results**. A comprehension has the shape
  `𝐷 ⤇ 𝐴 ⇒ 𝐷 ⤇ 𝐵`, so `𝐷` occurs covariantly — in an output — as well as
  contravariantly at application, and a variable occurring in both positions is
  invariant. That is the ordinary variance calculus, not a Cambra-specific rule, and
  it is the whole content of the `Data`/`Compute` split: a compute domain occurs
  contravariantly only, because nothing enumerates it.

There is a coherent language in which the wider collection *should* stand in: one
where a declared domain is a **view**, and narrowing it means "give me this much of
it". Cambra is not that language — and the reason is *not* that a data domain is
currently unwritable. It will not stay unwritable:
[`Array(𝑛, 𝑇)`](../../../docs/chl-spec.md#63-direction-collection-types-decided),
a data function over `Fin(𝑛)`, is a planned surface type. The reason is that both
things the view reading would buy are better bought elsewhere, and the surface
syntax is what makes them cheap:

- **"Works for any length" is quantification, not subsumption.** The function that
  accepts every extent is `∀𝑛. Array(𝑛, 𝑇) ⇒ …`, an ordinary scheme the solver
  already freshens per use. Contravariant widening is a poor stand-in for
  polymorphism: it relates one pair of extents at one site, and charges the row-set
  guarantee everywhere for it.
- **A deliberate prefix is a term, not a coercion.** A program that wants the first
  five rows takes them, and the truncation is then visible where it happens, at an
  extent chosen by the use site. A subsumption edge hides the same truncation in a
  declaration, and only ever at the width that declaration happens to name.

So the rule is stable under a surface data domain. What the syntax changes is that
the explicit forms invariance requires become *writable*, which argues for the rule
rather than against it.

**How it is enforced: an equation between types, accumulation at variables.** When
both kinds are concretely `Data` and both domains are concrete, the `Fun`/`Fun` arm
constrains the domains in both directions rather than contravariantly. A domain edge
with a variable on either side records its bound in the edge's native direction and
asserts no equation — n arm domains reaching one consumer's domain variable satisfy
the invariant without being equal to each other — and the reverse obligation is
discharged at materialization, where every contribution to the variable meets in the
compact domain lattice and two distinct domains are a conflict. Both spellings are
order-independent: whether a side is a variable is a property of the edge, not of
when it fires, accumulation commutes, and the lattice decides with every bound in
hand.

Both directions is also all it takes. `[`Type::UIntRange`]` relating only by equality
already rejects both base directions, and refinement **drop** (`{𝐷 | 𝑝} ⤇ 𝑉 <:
𝐷 ⤇ 𝑉`) is already rejected one step less obviously, since behind a contravariant
domain it demands `𝐷 <: {𝐷 | 𝑝}`. What the reverse edge adds is the case that
inversion left admitted — refinement **acquisition**, `𝐷 ⤇ 𝑉 <: {𝐷 | 𝑝} ⤇ 𝑉`, an
unfiltered collection standing where a filtered domain is declared. A failure in
either direction is reported as `ConstrainError::DataDomainMismatch`, naming the two
domains; `a_data_domain_relates_only_to_itself` pins all four directions plus the
reflexive case, and the compute counterpart that still relates contravariantly. The
exception is a domain comparison that raised a query and got no answer back: an
`SmtError` decided nothing, so it is reported as itself rather than relabelled into a
conflict.

**Emitting both directions does not preempt a join.** Two domains meeting at one
variable is a join like any other, and it has the same answer as anywhere else: none,
unless the program wrote a `box`. A domain position is not privileged — it does not get
an implicit sum that a `Case` result would not get. So `[0,1]` and `[0,2]` meeting at a
domain variable is a `CoalesceError::DomainJoinConflict`, and the same program can be diagnosed from the edge
or from coalesce depending on whether a consumer forces the question early (see
[The domain join needs `box`](#the-domain-join-needs-box)).

The rule fires wherever the edge is drawn, the kind edge with it, including the
post-inference re-check in `check.rs`.

## 4.7 Dependent sums

A dependent sum `Σ (𝑤 : 𝐾). 𝐵[𝑤]` is a pair: a **witness** `𝑤` — a type, drawn from a
[type kind](#type-kinds) `𝐾` — and a value of `𝐵[𝑤]` at that witness. The sum is how
a program keeps alternatives the lattice would otherwise have to collapse or reject: a
conditional over two collections holds one collection *or* the other, which one is a
runtime fact, and the type that loses neither domain pairs that fact with the data
([The domain join needs `box`](#the-domain-join-needs-box)).

Currently, we only support a limited form of dependent sums where they are represented as **data function carrying its binders**: `FunKind::Data`'s slot holds the
witnesses ([`Witness`] each — a binder id plus its kind), the Σ mirror of the Pi binder on
`Fun::name`. Every binder scopes over the **domain**, whose occurrences of it are
`Type::WitnessRef` leaves naming the binder; the codomain is the witness-independent
residue, one element type shared across the candidates. `Σ (𝐷 : 𝐾). 𝐷 ⤇ 𝑉` reads "a
collection over some domain in `𝐾`, with element type `𝑉`" — a conditional collection has
this shape, and so do `List` and `Collection`. A plain collection is the same function with an
empty slot, and the two are distinct types with no common upper bound in either direction.

The slot is a **telescope**: binder 𝑖's kind is written under binders 0‥𝑖−1, and a
multi-binder function is what two conditional generators build, its domain the tuple naming
one witness per position. [`Type::sum_binding`] rejects a body whose domain does not
mention the binder — a sum recording a choice nothing can observe.

[collections.md](collections.md) is the collection design built on the sum.

### Type kinds

A witness is a **binder over types**, and the types it ranges over are classified by a
[`TypeKind`]. The kind is a property of those types and never of the binder, and it is what
keeps Σ subtyping to a single rule with no case per kind. Four are wired:
`Enumerated[𝑇₀, …]` (finitely many candidates, named — what `box` and the
conditional-collection join build), `UIntRanges` (every index range, which is what a `List`
is), `SubtypesOf(𝑇)` (every domain below a type — a `Map`'s key bound), and `Type` (the
universe of small types and the domain of `Collection`).

Type kinds form a lattice, and this lattice is used during compaction to solve dependent sum
types.

#### An unresolved candidate becomes a kinding edge

A membership test needs a shape, and a computed collection's domain is still a variable when the
entry term is emitted. So `𝛼 :: 𝐾` is drawn as an **edge** on that variable — `InferBounds::kinds` —
and answered wherever a type reaches it (`solver::constrain::answer_type_kinds`), which is the
first moment it has an answer. A lower bound that is itself a variable inherits the edge instead of
answering it, so the question travels every path a type could arrive by.

The dual case is a shape meeting a witness whose candidate has not resolved. The candidate
is an ordinary variable among the candidates, so the demand lands on it as a bound like any other
and is answered when it resolves — there is nothing to defer and nowhere separate to defer
it to.

The constraint is not a bound, and so has no polarity of its own: `α :: 𝐾` asserts what `α`
must resolve to, which is one fact wherever `α` occurs. Two of them merge by conjunction
rather than by join at one polarity and meet at the other, and extrusion carries them
through both. A kinding constraint does reach a negative position — an annotation is a
demand, so `r: List(Int) = box(…)` records `UIntRanges` on the domain variable at negative
polarity (`test_kinding_constraint_survives_instantiation`) — and that says nothing about
kinds occurring contravariantly, because what sits there is the constraint, not the kind.

### The witness context

A witness is a **name**. What it ranges over is written where it is bound, and every
judgment carries the assignment of names to kinds it is made under — `Γ ⊢ 𝐴 <: 𝐵`, with `Γ`
extended at each Σ the walk descends through. A reference's kind is `Γ(σ)`, and is not
written on the reference.

A Σ's slot **is** the extension it introduces. `Σ (σ₀ : 𝐾₀) … (σₙ₋₁ : 𝐾ₙ₋₁). (𝐷 ⤇ 𝑉)` binds
𝑛 names with their kinds, and binder 𝑖's kind is written under binders 0‥𝑖−1 — a nested
source's candidates may name an outer witness — so a slot is a telescope, and `Γ` is the
concatenation of the slots the walk has entered.

**One place writes a kind, so nothing can hold a second answer.** A representation that
gives a reference its own copy makes two views of one binder expressible, and they diverge
as soon as the copies are taken at different moments: one before a candidate resolves and
one after, which reads as a binder differing from itself.

Two rules follow rather than being stated separately:

- **α-equivalence is name equality under one context.** Two references denote one index when
  they are the same name and `Γ` is the same.
- **An escape is an unclassifiable name.** A reference `Γ` does not classify has no kind to
  report, which is what [The post-inference check](#the-post-inference-check-shared-rules)
  already rejects — so the escape check states this invariant rather than adding one.

**A substitution crosses two contexts, so it renames.** A term filling a Σ-typed position
was written under its own binder, since a binder is minted where a scope needs one, and its
references are classified by its context rather than by the occurrence's. Discharging it
renames its binders to the occurrence's — the direction that leaves every type above the
position alone. A `Compose` is where omitting the rename shows: it recomputes its function's
ends from its elements, so the domain becomes the replacement's witness while the binder
stays its own, and the reference is then classified by neither context
(`at_own_witnesses` in `src/ccl/subst.rs`).

The term sort answers the same question a different way, and the difference says why the
context is needed here. `Telescope` records which term binders a stored bound may close
over and nothing more ([The invariant](#the-invariant)), because a term binder's type is
written on the binding in the tree. A witness has no binding node — the Σ is a type — so its
kind has nowhere else to live.

### Only a term builds a sum

`<:` has no rule that puts a value into a sum. Every sum is **first formed** by a term, and
there is one term per kind a witness can be classified by.

Read it as a statement about *entering*, not about the syntactic origin of every
`Type::Sigma` value: joining two sums forms a third, and must, since a conditional over two
boxed collections has to have a type. That join builds nothing new — its candidates are the
joined sums' — so nothing reaches a sum except through a term that says so. A demand never
forms one.

**`box` — the enumerated sum.** `box` takes a data function and boxes its **domain**:

```
box : ∀𝑑 𝑣. ((𝑘: 𝑑) ⤇ 𝑣) ⇒ Σ (σ : [𝑑]). (𝑘: σ) ⤇ 𝑣
```

An ordinary polymorphic builtin, with the element binder named on both functions so a
dependent collection's Pi binder lands on the witness domain. Two properties follow from
the rules rather than being stipulated:

- **The candidate position is invariant**, so `𝑑` is pinned to the argument's domain
  exactly and `box` never widens first. Retaining the alternatives instead of joining past
  them is the whole service.
- **A singleton does not collapse.** A one-candidate sum and its content are distinct
  types with no edge in either direction, so `box` is never free: a boxed collection is
  consumable, and it is not its argument.

Anything that is not a data function is rejected at the call as the ordinary application
mismatch it is — a scalar has no domain to box.

**`box` is not a no-op.** A sum is a pair, so introducing one pairs the value with its
witness, unlike a [`Cast`](ir.md#cast--explicit-refinement-acquisition), which re-views a
value and compiles away.

### Subtyping for sums

One rule generates the relation, and two absences shape it:

- **The Σ rule** — `Σ <: Σ`, the only rule between two sums ([below](#the-σ-rule)).
- **No introduction** — no rule concludes `𝑈 <: Σ …` for a non-sum `𝑈`. A sum is formed by
  a term ([Only a term builds a sum](#only-a-term-builds-a-sum)).
- **No elimination** — no rule concludes `Σ … <: 𝑈` by forgetting the witness. A sum and a
  plain data function are distinct kinds, and the kind equation rejects the mixed pair
  from either side, which is what makes mixing a boxed and an unboxed arm a conflict
  rather than a silent dissolve, and two unboxed collections a domain conflict rather
  than a silent sum.

There is no consumption arm either — no rule, in any spelling, reads a sum at a plain
function. A consumer that accepts a plain collection and a sum alike is polymorphic over the
kind, and the collection flowing in instantiates it ([Consuming a sum: pinning the
consumer's kind](#consuming-a-sum-pinning-the-consumers-kind)).

#### The Σ rule

A sum whose kind denotes more domains is a supertype: a narrower sum is a subtype of a wider
one, as a variant with fewer arms is a subtype of one with more. `Collection(𝑇)`, whose kind
denotes every domain, is the widest.

The rule relates two sums of arity `𝑛`, pairing binders **positionally** in slot order — the
order materialization contracts to.

```
    𝜌 = [𝑤₀⁰ ↦ 𝑤₁⁰, …, 𝑤₀ⁿ⁻¹ ↦ 𝑤₁ⁿ⁻¹]
    Γ ⊢ 𝐾₀ⁱ <: 𝐾₁ⁱ   (each 𝑖 < 𝑛)
    Γ, 𝑤₁⁰‥𝑤₁ⁿ⁻¹ ⊢ 𝐷₀‹𝜌› <: 𝐷₁         Γ, 𝑤₁⁰‥𝑤₁ⁿ⁻¹ ⊢ 𝑉₀‹𝜌› <: 𝑉₁
    ───────────────────────────────────────────────────────────────────────
    Σ (𝑤₀⁰ : 𝐾₀⁰, …, 𝑤₀ⁿ⁻¹ : 𝐾₀ⁿ⁻¹). 𝐷₀ ⤇ 𝑉₀
        <:  Σ (𝑤₁⁰ : 𝐾₁⁰, …, 𝑤₁ⁿ⁻¹ : 𝐾₁ⁿ⁻¹). 𝐷₁ ⤇ 𝑉₁
```

`𝜌` is the **binder correspondence**, an α-conversion carrying no content: the Fun/Fun arm
extends the sub side's substitution with one rename per paired binder, so the sub side's
witness references are compared under the names the sup side uses. It is built from binder
*identities* rather than from stated kinds, because a consumer's kind is a variable that states
no range until compaction while its identities exist as soon as its arity does. A side stating
no binder ids gets no rename, and the domain edge then compares an arm's witness against a raw
domain rather than two corresponding binders.

Three premises:

- **The kind premise** is kind containment, `𝐾₀ⁱ <: 𝐾₁ⁱ` per binder position
  (`constrain_type_kinds`, [Type kind containment](#type-kind-containment)). It carries no `𝜌`: the
  correspondence does not exist yet where this premise is drawn, so the two kinds are compared
  as written.
- **The domain premise** is the ordinary data-domain edge, invariant rather than contravariant
  ([Data domains are invariant](#data-domains-are-invariant)).
- **The codomain premise** is one covariant edge for the whole sum, which the function rule
  draws, and it carries the Pi binder's own rename extended onto `𝜌` for a named function.

`𝜌` reaches the codomain because it rides `sl`, the arm's substitution, which every sub-edge
inherits — there is no routing decision per premise. On the shape the passes build it changes
nothing there, the codomain being one element type shared across the candidates, and **nothing
enforces that**: `Type::sum_binding` asserts that the *body* mentions the binder, not that the
domain is the only half that does, and a bound reference in a codomain is not a free one, so
the escape check passes it too. Carrying the rename is what keeps the edge correct without
resting on the unchecked half of that invariant.

Both the domain and the codomain sit **inside** the binders, so `Γ` gains them for the descent
and loses them on the way out ([The witness context](#the-witness-context)).

A single-binder sum is the case where `𝐷₀` is just `𝑤₀⁰`, so the domain premise reduces to the
rename and the kind premise carries everything. A two-generator comprehension is where it does
not: its domain is a product of witness references, one per generator, and the domain edge is
what relates them positionally.

**Both sides must state a kind.** A written sum states one; a fun kind variable states none.
Compaction derives one for it: `var_binder_kind` joins the variable's lower bounds, or meets its
uppers where no lower reached it. Which list it reduces decides the operation, because everything
below the kind combines by join at either polarity and everything above it by meet. That answer
moves as the solve proceeds, so a verdict against it would depend on when the edge was drawn, and
`constrain_fun_kind` records against a variable for the same reason. A demand stated *above* a
variable reaches the value through the ordinary transitive closure, where both sides are written
by the time they meet: a bounded parameter `c <: List(Int)` specializes to the collection passed
in, and its bound is checked as the written pair the closure produces.

**Every premise is drawn at every derivation.** A check reconciles two spellings of a settled
tree and records nothing, and none of the three needs to record: containment between two
settled kinds is a comparison, the arms that would record take a variable, and a settled tree
has none. Drawing the kind premise on the live solve alone left a check accepting a collection
where a keyed one was demanded — the domain edge is discharged by `𝜌`, so the premise was the
only thing that looked at the kinds ([One rule for the solve and the
check](#one-rule-for-the-solve-and-the-check)).

##### What checks each premise

Tests are what stands behind `𝜌`, the domain premise and the codomain premise. The kind
premise has an independent implementation behind it as well.

No sum reaches a differential oracle. The model's `CompactTy` gives a function a kind, a
domain and a codomain and no binders (`formal/CclFormal/Merge.lean`), so the wire drops a
`CompactType` whose slot carries binders, and drops a witness atom for the same reason
(`tests/differential_oracle.rs`). What does cross is the kind lattice the kind premise reads:
`TypeKind::refuses` runs against the model's `refuses`
(`differential_refuses_vs_lean_model`), `CompactTypeKind::merge_kinds` against
`mergeTypeKind` (`differential_type_kind_merge_vs_lean_model`), and
`formal/CclFormal/TypeKindIsALattice.lean` proves the lattice laws the model's containment
relation obeys.

A missing `𝜌` is silent, so the Fun/Fun arm asserts the pairing instead: each side states one
binder identity per position of its own arity, and two sums pair every binder. Nothing
downstream would report its absence — the domain premise runs whether or not the rename was
drawn, and compares an arm's witness against whatever stands at the other side's position.

##### Type kind containment

**A type kind is a type of types**, and `𝐾₀ <: 𝐾₁` holds when every type `𝐾₀` classifies `𝐾₁`
classifies too. No variance, and no case per pair. What differs between the four is only how
each *states* which types it classifies, and that is what decides whether a membership
question is answered outright or drawn as an edge.

Nothing here is domain-specific. A Σ's witness is the one type-kind-carrying position in the
grammar and a Σ's witness is a data function's domain, so every type a type kind classifies
*today* happens to be a domain — a fact about that position, not part of the notion.

| sub \ sup | `Enumerated(sups)` | `UIntRanges` | `SubtypesOf(𝑏)` | `Type` |
|---|---|---|---|---|
| `Enumerated(subs)` | each candidate is in `sups` | each candidate is a range | edge `𝑑 <: 𝑏` per candidate | ✓ |
| `UIntRanges` | ✗ | ✓ | ✗ | ✓ |
| `SubtypesOf(𝑎)` | ✗ | ✗ | edge `𝑎 <: 𝑏` | ✓ |
| `Type` | ✗ | ✗ | ✗ | ✓ |

- `Enumerated` names its members, so membership in one is type equality. At the position that
  carries a type kind the classified type is a data domain, and a data domain is invariant
  ([Data domains are invariant](#data-domains-are-invariant)) — so a refined range is a
  different candidate from the range it refines, in either direction. One law, not a second one
  about pairing.
- `UIntRanges` and `Type` state a property of their members and name none, so membership is
  structural — [`TypeKind::refuses`], asked on the candidate whole, since a refined type is not
  the type it refines.
- `SubtypesOf` names its members by a type, so membership is an ordinary subtyping edge. It
  is the only one with a parameter, and a parameter is the one place information flows *in*:
  this is where `Map(_, 𝑉)` takes its key from the domains that reach it. Deciding it
  structurally instead answers "an undecided bound admits anything", and the key is then
  determined by nothing. So a bound is never routed through the structural test, and that test
  refuses nothing for a bound: a caller with no graph to draw into has no answer, and an exact
  match would be certain in neither direction — admitting an unfixed key's every domain and
  refusing every strict subtype a fixed one accepts.
- A candidate that is still a **variable** has no shape to read a property off, so it
  takes a [kinding edge](#an-unresolved-candidate-becomes-a-kinding-edge) and is answered
  wherever a type reaches it. Rejecting it instead would reject a generalized definition
  whose source only its uses can supply.

### The domain join needs `box`

A join of two data functions is not the contravariant meet of their domains. The domain of
a collection is its data, so meeting `[0,1] ⤇ Int` with `[0,2] ⤇ Int` down to `[0,1] ⤇ Int`
discards the third row, with nothing in the type recording that it happened.

So two collections over distinct domains have **no** join. `[1, 2] if c else [1, 2, 3]` is
a domain conflict naming both domains, because no rule puts a data function below a sum,
so there is no upper bound to find ([Only a term builds a
sum](#only-a-term-builds-a-sum)).

**`box` is what supplies one.** Each arm becomes a one-candidate sum, and the join of two
sums is the sum over both domains — `Σ (σ : [𝐷ₓ, 𝐷ᵧ]). σ ⤇ 𝑉`, whose witness is the
runtime branch discriminant. That Σ is the least upper bound *of the boxed arms*: it is a
different element of the lattice from either, and it loses neither domain.

Tracking the kind is what makes any of this statable. Without it both are plain functions,
the compute lattice's meet applies, and the join narrows silently — correct for a
capability, row-destroying for a collection
([4.6 Data vs compute functions](#46-data-vs-compute-functions)).

A sum is never formed to make a join succeed, so two unboxed collections over distinct
domains have no upper bound and their join is a `CoalesceError::DomainJoinConflict`. What the program can ask
for instead:

| written | type | what it keeps |
|---|---|---|
| `xs if c else ys` | `CoalesceError::DomainJoinConflict` | — no upper bound exists |
| `box(xs) if c else box(ys)` | `Σ (σ : [𝐷ₓ, 𝐷ᵧ]). σ ⤇ 𝑉` | both domains, and the discriminant |
| `list(xs) if c else list(ys)` | `List(𝑉)` | the rows, not which range — so lookup is partial |

Two of the three lose something, and which loss to take is a decision about the program,
which is why the type system declines to pick.

#### Where the candidates come from

A sum is formed by a term, so what needs locating is not where the Σ is formed but where its
**candidate list** is: the lattice join, which is coalesce, and not the `Case`.

The decisive case is a conditional whose arms are both parameters:

```
def f(a, b, c):
    b if a else c
f(True, box([1, 2]), box([1, 2, 3]))
```

At the definition there is nothing to enumerate — both arms are inference variables and
neither `box` is in scope — yet the use site yields
`Σ (σ : [[0, 1], [0, 2]]). (σ ⤇ Int)`, while `f(True, 1, 2)` yields `Int` from the same
definition. No syntactic rule at the `Case` can produce that.

Every law about the candidate list is then a join property the lattice already has:

| law | join property |
|---|---|
| candidates are the arms' | union |
| nested conditionals flatten | associativity |
| identical arms dedup | idempotence |
| the codomain is shared | the codomain join, which may **fail** |
| unboxed collection arms have no upper bound | a domain conflict, not a silent narrowing |
| scalar arms produce no Σ | the same join, intersecting refinements |

`emit_case` constrains every arm into a fresh result variable rather than requiring
equality, so the arms meet at their join: homogeneous arms join to their common type, and
data-collection arms with distinct domains form the sum.

#### The codomain join

**A Σ is lossless on the domain and lossy on the codomain.** The shared body's element type
is the ordinary covariant join `𝑉₀ ⊔ 𝑉₁` of the arms' codomains, forgetting which domain
pairs with which element type. Where that join is a structured coarsening it does not
error — record codomains intersect to their common fields, refinements drop to the shared
base. Where it is a scalar union it is unrepresentable, so
`[1, 2, 3] if flag else ["a", "b"]` fails at coalesce with the same `IncompatibleBounds`
rejection as `1 + true`.

The asymmetry tracks whether the loss is observable. Dropping an index drops a row and
leaves no trace, so domains join into the candidate set and never meet. A coarsened
codomain sits in the type and a consumer needing `Int` fails at its own constraint site, so
the shared-codomain Σ is a sound widening into which each arm injects. Preserving the
correlation by default would make every conditional collection a variant that every
consumer downstream destructures.

The recoverable form is a tagged variant carrying each arm's own codomain, which a program
introduces explicitly and `match`es, so the case-split cost is paid by the code that
benefits. Cambra does not narrow on an opaque `Bool`, so flow-sensitive typing is not the
alternative.

### Consuming a sum: pinning the consumer's kind

A sum is consumed at an ordinary application; there is no elimination term, no
elimination edge, and nothing opens a pair. A consumer that accepts a plain collection
and a sum alike — the demand an application deposits, an aggregate's scheme parameter, a
comprehension's source function — carries a **kind variable** (`FunKind::Var`), and the
collection flowing in **pins** it ([`KindPin`]). The pin settles the kind equation, never
a subsumption: nothing is read at a kind it does not have, which is the consuming half of
the two absences in [Subtyping for sums](#subtyping-for-sums). A consumer function lowering
knows to be a collection is minted pinned `Data` ([`FunKind::fresh_data`]), so a
capability flowing into it is the conflict; two kind variables meeting are one kind, so
`constrain_fun_kind` records the edge on both and what either holds reaches the other at the
read. A kind required to be two points is rejected at the edge that completed it, however
many variables lie between the two ends: [`FunKindVar::resolved`] folds the whole component,
and `Conflict` absorbs, so the first edge to observe one is the edge that made it. Lowering shares one kind
variable between a comprehension's source annotation and its result function, the way
`SharedHole` shares their domain, so the result is a collection exactly as the source is
([Data domains are invariant](#data-domains-are-invariant): the domain is reproduced in
consumer results).

**A witness reference names its binder**, everywhere and in one form
(`Witness`: the id, and the kind it ranges over). Unlike the Pi binder it has no
second, positional spelling ([A binder reference is stored in one of two
forms](#a-binder-reference-is-stored-in-one-of-two-forms)), because nothing here needs
α-variant sums to be *structurally* identical: a check relates two witnesses by their
**candidate list** rather than by name ([One rule for the solve and the
check](#one-rule-for-the-solve-and-the-check)). A
reference is a **leaf, not a `Type::Infer`**, so nothing can unify it away — that is what
stops a demand narrowing a conditional collection to one arm.

#### A consumer's binders are a scope, not a name

A function is a scope, and a sum reaching one is written in a different scope: its body
names its own binder, which is bound at the sum and denotes nothing at the consumer. So a
sum relating to a kind variable records its kind below the variable's own binders, picked
where the variable's arity becomes known ([`FunKindVar::binder_ids`]), and the edge carries the
**change of scope** between them — the witness half of [`Subst`], extended where the
`Fun`/`Fun` rule already extends it with a Pi binder correspondence. Every bound the edges
then record carries it, so a reference arriving at a variable is already spelled in that
variable's scope.

The binders are the target of that rename and not a name the consumer states. Two
functions a value reaches are separate upper bounds of one variable and never meet each
other, so each mints its own — and reading the index's name off the kind would name it one
way there and another at the domain position, where the references have merged. A
reference resolving to the second escapes the first, which is what the scope check reports
on a parameter consumed as a sum. [`FunKind::sum_binders`] therefore answers for the
written spelling alone.

#### The index is named at the domain position

Several references reach one domain position: a consumption's arms, each renamed onto the
same binders, and several functions consuming one collection, each with binders of its own.
The position is where they have merged, so it is where the index is named. A kind variable
mints a binder so its edges have a rename target ([`FunKindVar::binder_ids`]), and a route that
crossed no such edge arrives spelling the index in the scope it left; `named_by_domain`
gives the binder the name its domain answers with, position for position, so the function
does not bind a name its own domain no longer says.

A refinement on that domain carries a predicate, and a predicate is a term with type slots
of its own, resolved by their own route through the graph — so they arrive spelling the
index in the scope that route crossed. What ties them back is that the predicate is a term
over one element of the base: it reads the element, at a path of projections where the base
is a product, and the base at that path and the read are one type up to the spelling of its
indices. `type_element_reads_from_base` types each read from the base at its own path, so every
slot in the predicate names the index its domain named. Reading only the binder's own
occurrence leaves a projection's slot naming an index nothing binds, which is free.

What the position ranges over is the **union** of what reached it — the `Σ ⊔ Σ` law this
position is a join at. Keeping one binder's kind outright would answer with one arm where
several arrived, the narrowing [Data domains are invariant](#data-domains-are-invariant)
rules out. The name is a name; the union is the content.

For a collection `xs : Σ (𝐷 : 𝐾). 𝐷 ⤇ 𝑉`, a lookup `xs[𝑖]` emits the one constraint every
application emits — `type(xs) <: (type(𝑖) ⇒ ?𝑟)`
([Apply is one-way](#apply-is-one-way)) — with the kind variable on the demand's function.
The pin settles the kind edge; the element type flows covariantly into the consumer's
codomain, once — a sum's codomain is shared across its candidates, whatever number of
binders the slot carries. The index's own type lands on the consumer's domain variable as
an ordinary bound beside the witness reference, and whether the domain admits it is decided
at materialization, where every bound is in hand ([Materialization](#materialization)).

**The witness is not bound at the consumer.** The consumer's result is an unresolved
variable at that point, so the reference sits on the domain variable until
materialization rebuilds the function that binds it, and none may survive coalesce outside a
slot — that is the escape check, run as scope in `check_scope_valid` alongside the
identical property for Pi's term binders. Checking it per materialized type cannot work:
coalesce runs bottom-up, so at the point a type is built nothing knows what binds it from
outside.

`debug_assert_no_free_witness` asks the same question at each phase boundary — after
inference, after lambda elimination, and after planning, which is the other phase that
rebuilds types from node types. It descends into the predicate a refinement carries, whose
own type slots neither check reaches through the term, and it names the unbound reference:
a witness renders as a bare `σ` unless `CCL_SHOW_BINDERS` is set, so a report about which
name is unbound is otherwise a report about nothing.

#### One rule for the solve and the check

After inference an edge is a **check**, not a second solve: it reconciles two spellings of a
settled tree and records nothing. It asks the same question the solve asks, because a check
that asks a weaker or different one is not checking.

**Two references are one index when they are one name**, and what puts both sides in one
spelling is the correspondence the comparison's caller established. Two Σs meeting bring
their own — `𝜌`, the positional rename of [The Σ rule](#the-σ-rule). A value meeting a shape
written over binders is instantiating them, so reading the instantiation off the two types is
the correspondence there: `constrain_argument` relates an application's argument to the domain
it lands in, and `witness_instantiation` matches that domain against the argument to learn
what its binders became.

Deciding it from what the two references *range over* cannot be right in either direction. Equal kinds do not make two indices one — two collections over
the same candidates are two collections, which is the whole content of the invariance the
domain position has. Nor is containment available: a data domain is invariant, so the domain
edge runs both ways and containment there collapses to equality anyway. The relation is
identity, and the correspondence is what makes identity reachable.

#### A binder is minted where a scope needs one

A witness is minted at `box`'s scheme, once per instantiation; at freshening, which
α-converts a scheme's binder ids per use so two instantiations stay apart; and at a kind
variable, for the scope its edges rename into. Everywhere else a binder is inherited:
deriving a sum — mapping its types, changing its kind — carries the binder it had. What the
id preserves is the thread planning follows from a realization site to its `Case`; identity
between two derivations rests on the candidate list instead, so two mints of one index cost
nothing.
### How a sum flows through the solver

**Emission.** `box`'s scheme is instantiated per use site, each instantiation α-converting
the binder id over a fresh candidate variable, so a sum at emission is typically
`Σ (σ : [?𝑑]). σ ⤇ ?𝑣` — a binder whose candidate has no shape yet. Consumer functions are
emitted with fresh kind variables and no binders; a sum relating to one mints them there,
as the scope its edges rename into ([A consumer's binders are a scope, not a
name](#a-consumers-binders-are-a-scope-not-a-name)).

**Compaction.** A sum lands in the **`fun` slot**, the single carrier every function-shaped
type reaches, with its binders on [`CompactFun::binders`] and the body held **whole**, its
occurrences opened to the named form — compaction takes types apart, and a position inside the carrier is what a bound
already is: detached. `Type::WitnessRef` compacts to an atom, so an occurrence merges by
the law atoms already have: it matches its own binder and nothing else, and meeting a
concrete type is the collision `Int` meeting `String` is. Holding the whole body rather
than the witness-independent residue is what lets a demand land *on* the witness
position — a consumer's `?d ⤇ 𝑉` meeting `σ ⤇ 𝑉` is the merge that resolves `?d` to `σ`,
and a residue has nowhere to put it.

Merging two sums merges kinds and bodies slot against slot over a **fresh** binder both
contributions α-convert onto ([`CompactFun::merge`], whose `merge_binders` reconciles the
positions). Neither side's binder wins: a merge
is a comparison across two scopes, and minting the one they are brought into is the same
act the domain position performs when several references meet there ([The index is named at
the domain position](#the-index-is-named-at-the-domain-position)). A pairing the merge has
no answer for rides the merged sum and is reported at materialization, rather than resolved
by keeping the left contribution — a slot merge returns a value and has no graph to fail
into.

**The merge laws are the lattice bounds** ([`CompactType::merge_bounds`]), so each is
derived from the subtyping rules rather than declared. Neither cross-constructor merge
has an answer — no edge relates a sum to a plain data function in either direction
([Subtyping for sums](#subtyping-for-sums)) — so both cross rows keep both contributions
and coalesce reports them incompatible.

| | law | consequence |
|---|---|---|
| `Σ ⊔ Σ` | union the kinds, join the bodies | `box(xs) if c else box(ys)` keeps both |
| `Σ ⊔ 𝑈` | no answer: both contributions kept, reported incompatible | `box(xs) if c else xs` is rejected |
| `Σ ⊓ Σ` | meet the kinds | a value satisfying both demands |
| `Σ ⊓ 𝑈` | no answer, as at the join | a sum never satisfies a plain concrete demand |

A consumer's demand is not the `𝑈` of that table: its function carries a kind variable, so by
the time it meets a sum it is pinned `Data` over the same binders and merges `Σ ⊓ Σ`. What lands in a
cross row is a genuine kind mixture — a boxed arm against an unboxed one, a boxed value
against a concrete plain annotation — and each is a program error.

A position's **names** are not its content: a variable and a kinding constraint name the
position they sit in rather than contributing a type to it, so a kind whose candidates are
all names resolves to whichever side has content, and a name cannot pick a candidate
out. Reading a name as content produces no error where the mistake is — it produces a
witness sitting in an atom set beside a concrete domain, read later as two alternatives.

#### Materialization

**A data function takes the binders standing in its domain.** The function's slot is read
straight off its domain — the binders each position resolves to, in field order — because
that position is where a consumption's references have merged and been named ([The index is
named at the domain position](#the-index-is-named-at-the-domain-position)). A consumer's
restriction rides the witness occurrence rather than the candidates; references bound by an
enclosing sum are occurrences and stay put.

The kind a position answers with is the **union** of what its references range over, and the
lowest-numbered of them carries it. A binder is a name, so which one is arbitrary as long as
it is stable across the repeated materialization a fixed point performs; the union is not
arbitrary, and keeping one reference's kind outright would answer a consumption with one of
its arms.

A sum with nothing to merge against passes through: the slot keeps its binder id, so a type
that merely passed through comes back equal to itself. A data-⊔-compute collision is a loud
coalesce error.

**Invariance is decided here for the edges that could not decide it.** A domain edge with
a variable on either side records its bound and asserts nothing
([Data domains are invariant](#data-domains-are-invariant)); at materialization every
contribution to the variable meets in the compact domain lattice, where two distinct
concrete domains are a domain conflict and a refined domain pairs with no bare one. A
concrete index's bound beside a witness reference is the same decision: the binders are in
hand, so the demand is checked against what the witness ranges over. The verdict is the
per-edge equation's, reached with every bound in hand.

**Candidate order is first-contribution order, and that is a contract**: it fixes a
deterministic materialization and the discriminant order the value-`Case` fan-out indexes
by. Nothing in subtyping depends on it, because a candidate set is a set and the kind
premise quantifies over its members.

Nested conditionals **flatten**. A Σ re-entering compaction lands in the same slot with its
candidates enumerated, so `(box(xs) if p else box(ys)) if q else box(zs)` forms one flat
three-candidate sum. A candidate is therefore a data function's domain, never itself a Σ,
and `Witness::formed` asserts it. Nesting the boxes instead reaches nothing: `box` takes a
plain collection, so `box` of a sum is the plain-versus-sum kind conflict
([Only a term builds a sum](#only-a-term-builds-a-sum)).

#### Which `Case` a site realizes, and what a leg instantiates

A realization site names a witness; the `Case` that witness stands for is somewhere below
it. Planning pairs the two by **kind**. The site's witness and the value's `Case` are two
derivations of one consumption, so their binder ids differ by construction ([A binder is minted where a
scope needs one](#a-binder-is-minted-where-a-scope-needs-one)) and the candidate list is
the content they share.

Two conditionals over identical candidate lists have structurally identical types, so kind
does not separate them. **Position does**: a site's binders nest in generator order, the
`Case`s stand in the same order below it, and the 𝑖-th same-kind witness therefore pairs
with the 𝑖-th same-kind `Case`. A realized `Case` stops matching the test, so the walk consumes
them in order rather than re-counting (`two_conditional_sources_compile`).

A leg is one chosen arm, and it instantiates every witness it leaves **free** — not only the
binder the site names. A filter's predicate holds its own read of the source, under a binder
of its own, and the predicate spells that witness wherever it projects the element, not only
where it reads the source. Replacing the copy with the arm erases the sum that bound it, so
those occurrences are free; every other sum still standing in the leg carries its own binder,
so a free reference can only belong to the consumption being realized
(`a_filtered_conditional_generator_beside_another`).

**A witness over one candidate quantifies nothing**, and planning instantiates every sum in
that state — not only the binder whose `box` it erased. The candidate is the domain, so a
type still saying `Σ` presents a witness where a consuming site needs an extent, and
`planning::iterate` can build no iteration source for it. Erasing the introduction is not
enough to reach them: a consumer of a sum is a sum over its own binder, so each consumer
downstream still quantifies a witness over the one candidate the introduction had.
Determinedness is a fact about a kind rather than about the term that introduced it, which
is what the pass asks. Realized binders are the exception — one stands over a `Variant` of
its legs' domains and the assertion below is made over it — and so are the sums inside
refinement predicates, which a leg replaces wholesale rather than rewrites.

#### Planning asserts the type it replaces

Planning's realization of a conditional collection is the one place a term's type changes
after the type system is done, and the sum has to survive that in every enclosing mention.
Rewriting those mentions is the obvious approach and the wrong one: they run through
composes, products and projections, a projection names its component twice, and the chain
does not terminate because the last stale mention is not a sum at all.

So realization asserts instead. [`TypedExprNode::Realize`] re-views the gated union at the
type the `Case` had, and nothing above it changes.

It is **not** a [`TypedExprNode::Cast`], because a cast's type is derived from its value's:
`emit_cast` rebuilds the value's function type with the target's domain refinements, so the
result keeps the value's domain shape. Realization asserts a type with a different domain
shape. The sum picks one branch, the tagged union has rows from every leg, and only the gates
reconcile them, which no typing rule can check. A `Cast` over the gated union would type it at
its own `Variant` domain, not at the sum, and making `Cast` accept an asserted type would turn
every other cast from a derived type into a trusted one. What the
node carries, what it does not cover, and why it needs no target field are on
[`TypedExprNode::Realize`] itself.

### Deliberately incomplete here

Everything below is a gap between the model above and what is built. Each item states what
is actually wrong rather than a consequence of one root cause; late materialization of the
Σ is correct, not the shared cause it looks like ([Where the candidate list comes
from](#where-the-candidates-come-from)).

> **An entry names a cause only with a reached-code demonstration** — an instrumented run
> showing the site executing on the failing program, and the outcome changing when the site
> is altered. Three traps make a probe report a site as unreached when it is not: `cargo
> test` captures stderr, so a probe needs `--nocapture`; a probe program that fails at
> *lowering* never reaches inference, so it says nothing about the solver; and a passing
> program is a reference point only if it exercises the same path — lowering distributes a
> comprehension over an inline conditional, so no Σ is consumed there at all.

- **`KindMerge::Conflict` reaches coalesce with two or more domains only in
  hand-constructed compact graphs** (`coalesce_domain_join_conflict_errs`). That
  outcome needs a `Data ⊔ Compute` collision *and* arms at differing domains; no
  source program in the suite produces both at once. Its single-domain outcome is
  reachable from source, and `joining_a_capability_with_a_collection_is_a_kind_conflict`
  is the route: a capability and a collection arrive as two *lower* bounds on one
  variable, and closure relates a lower to an upper rather than a lower to a lower,
  so neither is ever the left of an edge whose right is the other and
  `ConstrainError::KindMismatch` cannot see it.

- **A [`FunKindVar`] is quantified by construction rather than by level.** Freshening copies
  one unconditionally ([`freshen_kind_var`]), where a type variable at or below the
  generalization limit is shared instead, so a kind variable free in the surrounding scope is
  duplicated per instantiation and the two copies are related only by whatever edge the pin
  happens to draw between them. `TypeKind` has no variable at all — what a witness ranges over
  is stated where it is bound, and containment reads it ([Kind
  containment](#type-kind-containment)) — so this is the one kind axis still outside the
  graph.
  Giving [`FunKindVar`] a level is what would retire this entry.

- **There is no runtime witness yet, so a sum over a kind naming no candidate cannot be
  consumed.**
  A sum is a pair, and consuming one projects its witness and dispatches; nothing today
  can read a witness off a value. That is a gap to close, not a property of the design —
  the runtime witness is the load-bearing planned item
  (`src/ccl/design/collections.md`, "Compiling a conditional collection"). Over **named
  candidates** this does not bite — the gate fan-out compiles the conditional and the
  realized union's extent is the selected domain — which is exactly why the gap has stayed
  invisible: the conditional-collection path is the one case that does not need the general
  mechanism. It bites where the kind names none: iterating a `Collection(𝑇)` parameter has to
  find the actual
  runtime domain, and [`extent_of`] maps a *type* to an `Extent`. The shape to follow is
  `Type::DataSource` → `Extent::DataSourceDomain`, which resolves an opaque domain to a
  runtime handle; the witness wants the same treatment. This is the general machinery
  a [first-class `Collection` value](collections.md#compiling-a-conditional-collection)
  needs, and the
  conditional-collection fan-out is its special case rather than a step toward it.

  Consuming a **heterogeneous** sum (`Σ (𝑇 : [Int, String]). 𝑇`) additionally needs the
  consumer valid at every candidate, which for a genuine dispatch is a trait bound. The
  runtime is *not* the obstacle there — `UnionOperator` already produces a
  `Scalar(Union(…))` codomain when its inputs disagree — so what is missing is the
  typing, not the representation. This subsumes the older heterogeneous-scalar-union
  entry, which recorded the opposite diagnosis.

- **A Σ over unresolved candidates cannot be related at all.** The pairing search needs
  ground candidates — a disjunction cannot be recorded as a constraint the way membership in
  `UIntRanges` can — so an unresolved candidate pairs only with its own variable.
  That, and not a variance question, is what keeps formation late: forming a Σ before
  coalesce would produce exactly the Σs the rule cannot relate.

  Forming a Σ at constraint time makes that constraint *live*, and what it turned out to
  require is that a sum's **candidates are an invariant position**. A candidate is a domain,
  and a domain's content arrives as an **upper** bound — a comprehension's iteration key must
  lie in its source's domain — so a candidate variable typically has no lower bounds at all.
  `extrude`'s polar proxy inherits one side only, and extruding candidates at `!pol` handed a
  sum in a negative position a *positive* proxy, which inherits lower bounds: nothing. The
  candidate then materialized unresolved, `Σ (𝐷 : [?93, [0, 2]]). 𝐷 ⤇ Int`, which is what the
  ground-domain assertion catches. Since the kind premise matches candidates *by value*,
  neither direction is the unused one, so candidates now cross a level boundary through the
  two-way proxies `extrude_invariant` builds — the same treatment, for the same reason, as a
  `History` payload.

  That is the whole of it: no groundness precondition is imposed on the join, and an arm whose
  domain is *inferred rather than written* — any comprehension arm, filtered or not — joins
  like a literal one. Refinements were never the discriminator; they only correlate, because a
  filtered comprehension's domain is a refinement over the same kind of variable.

  Two earlier explanations of this are wrong and are recorded here only so they are not
  reached for again. That candidates must be ground *in principle* — they need not; the copy
  was faithful, the proxy was not. And that the hazard is a candidate "recording a bound at
  the wrong polarity" during compaction — compaction walks candidates at `!pol`, which for the
  common positive sum is negative and therefore correct for a domain.

  An arm that is a **UDF call** is *not* closed by the join, and does not need to be. The join
  declines a bare variable — reading a variable's denotation would mean joining its own lower
  bounds transitively, and skipping it would risk dropping a candidate it later resolves to.
  It works because the **solver** propagates it: the arm's collection reaches the join variable
  transitively as an ordinary lower bound, which is what bound closure is for. Taking the
  transitive read inside the join instead requires variable resolution, then re-pairing the
  witness into a sum, then doing that through a variable — three pieces of compaction
  re-implemented at constraint time — and regresses the parameter route. Long-range and nested
  information is the solver's job.

  A use of a **lambda parameter** carries the
  parameter's own variable, and a binder's type is fixed by the contravariant domain of the
  function it binds — the reason `refresh_lambda_param_slot` derives `param.ty` from the coalesced
  domain rather than resolving the slot. Reading that variable *bare*, as the use's own node
  type, loses the same context, and for a data-function domain the loss is not mere
  imprecision: the candidate domains of a conditional collection are alternatives only when
  read **as a domain**, and collide as an untagged sum when read bare. That collision at
  `__iter_record` was the whole of the original failure.

  Two constraints shape the fix, and both are load-bearing. The standalone read must still
  *happen*, because a parent's structural recovery of a contravariant domain
  (`specialize_projection_domain`) reads it — a record-typed parameter's uses are how a
  projection's domain is recovered at all. And the parameter slot
  must only fill uses the read *left* unresolved, because a use whose read succeeded is at
  least as precise as the slot and often more so: a monomorphized parameter's use carries the
  call's literal singleton where the slot, being the coalesced domain, has widened it. So the
  rule is narrow by construction — the slot answers exactly where the bare read has no answer.
  Pinned by `a_udf_call_arm_joins_through_the_bound_graph` and
  `a_lambda_param_use_falls_back_to_the_param_slot`.

  The candidate list is **not** a redundant second alternatives mechanism layered on the
  position's atom set. A flat atom set
  cannot express *which* candidate a refinement belongs to, and that association is semantic:
  `[q for q in [1,2,3] if 𝑝] if 𝑐 else [1,2]` must be `Σ (𝐷 : [{[0,2] | 𝑝}, [0,1]]). 𝐷 ⤇ 𝑉`,
  not `Σ (𝐷 : [{[0,2] | 𝑝}, {[0,1] | 𝑝}]). 𝐷 ⤇ 𝑉` — the filter restricts the arm that was
  taken, not both.
  Distributing a position's refinement over its atoms produces exactly that wrong type, which
  is why `denoted_domains` refuses a position carrying refinements. Per-candidate association
  is what `CompactTypeKind::Enumerated` carries.

  Two sites make that survivable today: `compact_go` and `extrude` walk candidates at
  `!pol`, and the ground-candidate `debug_assert!` in `coalesce_compact_go` forbids a free
  variable in a candidate — which is how a one-sided bounds graph gets an invariant
  position for free. They come due with **formation**, not with the search: once a Σ is
  formed at the join its candidates are whatever the arms inferred, and the discharge has
  to move to where they are ground.

- **Two kinds combine in two places, and the two do not overlap.** [`TypeKind::join`] unions
  the candidates of a conditional's arms as they reach a consumer's kind variable, where they
  are still unresolved variables and have not met as types; `CompactTypeKind::merge` combines
  what met at a compacted position. Containment, the third relation, is
  `constrain_type_kinds`. Neither combiner answers a pair of *different* kinds: no kind spells
  the union of candidates with a property, and answering the universe there would type the
  position `Collection(𝑉)` — the one shape with no static extent — so the pair stops rather
  than widening. `Map` and `Set` lowering is what makes it reachable and what has to decide
  it. Detail in [Type kinds](#type-kinds).

- **The fan-out's discriminant order has never met a multi-candidate sum.** The
  value-`Case` fan-out indexes legs by discriminant order, and it is built only where
  every arm shares one domain — a single candidate, nothing for an order to disagree
  about. Candidate order is *not* an input to subtyping (the rule quantifies over a set),
  so the two do not meet today; they would the moment the fan-out is reconciled against a
  sum with two or more candidates. A Σ formed at the join fixes the order by construction.

- **Witness-dependent kinds are unbuilt.** No kind carries a reference to an *enclosing*
  witness — the `Σ (𝑤₁: 𝐾₁). Σ (𝑤₂: 𝐾₂[𝑤₁]). 𝐵` shape. Nothing forecloses it: it is kind
  subtyping under a substitution, an extension of the kind level rather than of the Σ
  rules. Listed because it is the honest edge of "general dependent sums", not because
  anything needs it.

---

## Traits

The constraint lattice can state that two positions are **equal** or **related by subtyping**. That is everything an operator needs when its result *is* one of its operands — `max(xs)` returns an element, `x.f` returns the field — because "is one of" is a shared lattice position. It is not enough for an operator whose result is **computed from** its operands, and `+` is the smallest example: the sum of two values is neither of them.

### Vocabulary

* A **trait** is a named requirement a list of types may satisfy — `Addable`, `Orderable`, `Comparable`. **A trait is not a type**: no `Type` variant, no lattice point, no subtyping edge, and the type grammar and `constrain_go`'s rules are untouched. Types *satisfy* traits.
* An **instance** is one row of a trait's table: the types it accepts, and the types it associates with them. Written `Addable(Int, Int ⇝ Int)` — accepted types, then `⇝`, then the associated ones.
* An **associated type** is a type a trait *names* — `Output`, the type an arithmetic operator's result takes. A trait is a requirement rather than a function, so it associates any number, **including none**. A type is associated only when it *depends* on the types satisfying the trait: a comparison's `Bool` is the same for every pair `Equatable` accepts, so it belongs to the operator's signature and `Equatable` associates nothing — recording it as an association would claim the trait determines something it does not.
* An **obligation** is what one *use* of a trait records: the demand that some instance fit the type positions at that use — one **operand position** per argument the trait takes, and one **associated position** per type it names. It is a single claim with two halves, and neither alone is the obligation: *the operand positions are types some instance accepts*, **and** *each associated position is what that same instance associates*. Every position is an ordinary inference variable, unrelated to the others.

A signature carries an obligation beside its type — `𝑓 : 𝐴 ⇒ 𝐵 requires MyTrait(𝐴 ⇝ 𝐵)` — and inference must find an instance satisfying it. Nothing about that is operator-specific: obligations ride variables into schemes ([Requirements are generalized](#requirements-are-generalized)), so a function inherits the requirements of the operators in its body, and `λ 𝑎 𝑏 → 𝑎 + 𝑏` is `∀ 𝐴 𝐵 𝑂. 𝐴 ⇒ 𝐵 ⇒ 𝑂 requires Addable(𝐴, 𝐵 ⇝ 𝑂)`. What is missing is only the *surface* — no CHL syntax writes `requires` yet, so every obligation is minted by an operator. (`requires` is the keyword the spec reserves for it, in [transactions as contextual parameters](../../../docs/chl-spec.md#87-direction-decided-transactions-as-contextual-parameters).)

An operator's own signature is `𝐴₁ ⇒ … ⇒ 𝐴ₙ ⇒ 𝑅` plus its obligation, for the trait's arity `𝑛`, where `𝑅` is either one of the associated positions or a type the operator fixes. The three shapes the current operators take:

| operator | signature | obligation |
|---|---|---|
| `+` | `∀ 𝐴 𝐵 𝑂. 𝐴 ⇒ 𝐵 ⇒ 𝑂` | `Addable(𝐴, 𝐵 ⇝ 𝑂)` |
| `==` | `∀ 𝐴 𝐵. 𝐴 ⇒ 𝐵 ⇒ Bool` | `Equatable(𝐴, 𝐵)` |
| unary `-` | `∀ 𝐴 𝑂. 𝐴 ⇒ 𝑂` | `Negatable(𝐴 ⇝ 𝑂)` |

Mechanism: `src/ccl/infer/solver/traits.rs`.

An associated position like `𝑂` is an ordinary inference variable, not a marker standing for a computation. So information flows *backwards* through an operator's result, and misusing that result is an ordinary diagnostic: `(1 + 2) and True` fails as a bound conflict. A marker could not do this — the solver cannot compare an unreduced computation against anything — and a function could then not be typechecked without seeing its call sites.

### A trait is a relation, and today it relates only types

A trait over `𝑁` operand positions, `𝐴` associated types and `𝐹` associated
**functions** is an `(𝑁 + 𝐴 + 𝐹)`-ary relation in which the `𝑁` operand types
functionally determine the `𝐴` types and the `𝐹` functions; `⇝` separates the
determining side from the determined one. An instance is one hyper-edge, and
resolution is the search for a hyper-edge consistent with what inference has determined
about the operand positions.

Cambra implements `𝑁 ∈ {1, 2}`, `𝐴 ∈ {0, 1}` (`Output`, or nothing) and **`𝐹 = 0`**,
with the relation built into the compiler rather than declared in CHL.

`𝐹 = 0` is a gap rather than a decision. A trait's rows *do* denote distinct
functions — `Addable(String, String ⇝ String)` is concatenation and
`Addable(Int, Int ⇝ Int)` is integer addition — and a trait that cannot associate a
function cannot say which. The function is therefore recovered twice outside the trait:
`simplify.rs` rewrites the `String` case to `Concat` (see
[BinOp type rules](#binop-type-rules)), and the interpreter picks the machine operation
from the operand column's runtime representation (`apply_binop_column`, in
`src/interpreter/binop.rs`). The type system narrows to a row of types and then declines
to name the code.

Associating functions, and a CHL surface for declaring the relation, are the two
extensions this shape exists to take: the instances are already *data*
(`Trait::instances`), so both are table extensions rather than new mechanisms.

#### What the tables hold

Every instance in every table accepts **base types only**, and every one is
homogeneous — `Addable(Int, Int ⇝ Int)`, never `Addable(Int, String ⇝ …)`. Both
facts are the tables' content, not properties of resolution: nothing in narrowing or
deposit assumes either. So a trait rejecting a variant is what these rows happen to be,
and not a judgement that such types are incomparable.

### A product is answered off the table

`Equatable` holds of a tuple or record when the two operands are the **same** product and
each component is equatable. No row states it — a row accepts a base — so `narrow_product`
answers it structurally instead: the product is recorded on the obligation, stated as an
**upper** bound on every operand position beside the contributing one, and required of each
component through an obligation of its own over a fresh variable the component flows into.

Three consequences follow from that shape rather than from a choice:

- **A component still unknown resolves later.** It reaches its own obligation by the
  ordinary delivery path, so a record key whose field type has not arrived is deferred
  rather than read early and missed.
- **The propagation is the base case's write-back, one level up.** It is an upper bound for
  the reason [What an obligation determines](#what-an-obligation-determines) gives, and
  every component's refinements are peeled for the reason
  [Refinements are transparent](#refinements-are-transparent) gives — a product carrying
  `Int@1` would hold the operand beside it to one literal.
- **Once answered, the table has nothing left to say.** The candidate set is untouched, so
  the requirement sweep skips the obligation and a base arriving afterwards contradicts the
  product rather than narrowing it.

Equality is the only trait with this reading (`Trait::is_structural`). Ordering a product
needs an order on its components and a record's fields carry none; arithmetic has no product
reading at all.

### Refinements are transparent

`{𝑇 | 𝑝}` satisfies a trait exactly when `𝑇` does. This holds by construction: satisfaction is judged on each bound contribution as it arrives, and refinements are peeled at that moment, when the base exists. Peeling at emission instead would have nothing to work on, an operand usually being still a variable there.

Transparency follows from incremental resolution and is permanent. A candidate set only ever shrinks ([Resolution is incremental](#resolution-is-incremental)), and a refinement is one of the things a bound can deliver late; if `{𝑇 | 𝑝}` could satisfy a requirement `𝑇` does not, a refinement arriving after the base would have to re-admit a dropped candidate, and order would start to matter.

Growing `𝐹` above zero would not change this. Choosing between two functions by `𝑝` is dispatch on a fact about a *value*, which a table keyed on types cannot express — and which no refinement survives in any case: `𝑥 + 𝑥` where `𝑥` is `2` produces `4`.

### Resolution is incremental

An obligation is a monotone fact, resolved as the graph fills in rather than by a sweep at the end of solving — the shape [`FunKindVar`](#46-data-vs-compute-functions) already uses for kinds. Each operand position carries a **candidate set** of instances that only ever shrinks; each associated type is deposited on its position as an ordinary lower bound once every surviving candidate agrees on it. Order therefore does not matter.

A contribution arriving at a position is one of four things, and each has its own outcome:

| contribution | example | outcome |
|---|---|---|
| a **base** | `Int` | narrows the candidate set |
| **not determined yet** | a variable, a hole, a `Feed` handle whose payload arrives separately | nothing to say |
| a **product** | a tuple, a record | answered componentwise by a structural trait, rejected by every other ([A product is answered off the table](#a-product-is-answered-off-the-table)) |
| **determined, and neither** | a variant, a function | rejected — no instance accepts it ([What the tables hold](#what-the-tables-hold)) |

The last is a rejection and not silence, because "no base here" is true of both it and the second. A collection that merely failed to narrow would leave `[1, 2] == [3, 4]` well-typed: a comparison has no associated position to strand, so nothing downstream would object either.

A position that stays in the second row for the whole program — nothing ever determines it — is not a rejection either. Its obligation simply never narrows, and the variable is reported as unresolved rather than as a missing instance.

### What an obligation determines

A deposit records what every surviving instance agrees on. It reaches both kinds of position, at opposite polarities:

| position | bound | because |
|---|---|---|
| associated | **lower** | the obligation is its only source — nothing else constrains it from below |
| operand | **upper** | the table states what *may* reach the operand, not what does |

A lower bound on an operand would invent a value the program never supplied, and would let an under-connected lowering pass by supplying the type its missing edge should have carried. An upper bound cannot: it gives coalesce nothing to resolve *to*.

How much is determined follows from the table. `λ 𝑥 → 𝑥 + 1` is `Int ⇒ Int`, because `Int` at the second position leaves only `Addable(Int, Int ⇝ Int)` and one surviving row fixes every position of it. `λ 𝑎 𝑏 → 𝑎 + 𝑏` determines nothing, and both parameters stay open. Adding `Addable(Float, Int ⇝ Float)` would reopen the first case, two rows disagreeing — which is why a deposit waits for agreement rather than firing on a unique candidate.

### Requirements are read together, once

Narrowing consumes one contribution at a time, so an obligation learns only what is *delivered* to it. Requirements that are individually satisfiable and jointly not therefore pass: in `λ 𝑎 → (𝑎 + 1, 𝑎 + "s")` each obligation narrows through its **other** operand, to `{Int}` and `{String}`; neither set is empty, and nothing compares them.

A pass between emission and coalesce closes this. For each value it intersects what every requirement on that value accepts, with three outcomes:

* **Empty** — nothing satisfies them all, so no argument could. `UnsatisfiableOperand`, listing each requirement together with what the trait's other operand accepts, that being what narrowed it.
* **One base** — the requirements determine the value. It is deposited as an upper bound, and the obligations there are narrowed by it directly, since an upper bound does not reach them on its own.
* **Several** — the value stays open.

Before depositing, the pass reads the bounds the value already carries. A base that disagrees is `RequirementContradictsBound`, naming both it and the required type. Left to the write, the same contradiction reaches coalesce as two `IncompatibleBounds` naming no trait: a *bounded* annotation and a monomorphic operator's operand are ordinary bounds, so no intersection of requirements sees them. An *exact* annotation does not reach here at all — it delivers a base, so the obligation narrows and fails on its own ([Annotation kinds: exact and bounded](#annotation-kinds-exact-and-bounded)).

Both rejections say no argument could work, and they differ in what collides. An empty intersection is the requirements contradicting each other. A bound conflict is the requirements agreeing, on something the program has already ruled out.

Placement is forced at both ends. **After emission**, because that is when a definition's requirements are all recorded. **Before coalesce**, because a generalized definition's subtree is never coalesced in place, so a walk of the tree would see only use-site clones — and a clone that goes unsatisfiable already fails by delivery. The pass repeats **to a fixpoint**: determining one value can leave a neighbouring obligation with a single row, determining another.

**One write lands after the sweep, and it only selects.** An unreachable `match` arm's payload is a position no value reaches, so its type comes from a demand recorded on it or from its own reads, and only coalesce can tell that nothing else did. `pin_unobservable_arm_payload` chooses there: the concrete type an upper bound requires the payload to flow into, else a base every requirement the arm's reads state accepts, else `Unit`. Each is a selection from a set this pass read rather than a restriction past it, which `assert_post_emission_narrowing_selects` checks. The pin records its choice in both directions, because an upper bound does not participate in a merge: the `Case`'s join would read the position as contributing nothing and settle on a type narrower than the arm's own slot, which the post-inference check rejects.

A delivery also tightens what the obligation's other positions accept: `Addable` narrowed to `Int` at position 0 accepts only `Int` at position 1. Nothing re-reads a variable standing at such a position against the requirements this pass already intersected for it. What the pin can deliver bounds the exposure. A base the sweep deposited was narrowed into the obligations by the sweep itself, at fixpoint, so the tightening is not new. `payload_trait_default` delivers `Int`, which every trait table contains, so every sibling intersection still accepts it. A base read off a consumer's bound is neither of those, and an obligation that cannot accept it empties and fails the pin's own assertion rather than narrowing quietly. Whether a stale sibling verdict is reachable at all is unresolved — no program in the corpus reaches one, and the bound is a property of the trait tables rather than of this code.

This is the gap [Typechecking a never-called definition](#typechecking-a-never-called-definition) names. The two are complementary. That walk resolves a dead definition's recorded bounds, which catches `λ 𝑎 → (𝑎.0, 𝑎.foo)`; this pass needs no delivery, and does not depend on whether anything calls the definition.

#### The unit is a place, not a variable

Every position of a requirement is an ordinary inference variable, but a requirement is *about* a value, and one value is generally several variables. A **place** is that value. It is named by a root variable plus the path of field selections reaching it — each element of the path a **step** — and the empty path names the root's own value. `places_under` returns, per place, the variables standing at it together with the requirements they carry; it is one *place*'s requirements that are read together.

Places are found by following **upper** bounds: `𝑣 <: 𝑈` means `𝑣`'s value reaches `𝑈`, so a requirement on `𝑈` is one on `𝑣`. A variable bound stays at the same place, `𝑣` and `𝑈` being two variables for one value; a structural one descends, so in `𝑣 <: (𝑈₀, 𝑈₁)` the requirements on `𝑈₀` belong one field deeper and not to `𝑣`. Each `𝑈ᵢ` is itself a variable, which is why the path is load-bearing rather than decorative: it is what separates the value `𝑈₀` stands for from `𝑣`'s, and what lets variables reached by different routes be recognized as one value.

A variable alone is the wrong unit because the parameter a programmer writes is not one variable. `λ 𝑎 𝑏 → …` uncurries to a lambda over a tuple and rewrites each occurrence of `𝑎` to a projection of that tuple, so each occurrence has its own inference variable and none of them carries both of `𝑎`'s requirements. Written curried, `𝑎` is a binder its occurrences share, and one variable carries both. Only the spelling differs.

Which positions are steps is decided per type former, by an exhaustive match. The rules are one comment per former at `places_under`, in `src/ccl/infer/solver/traits.rs`.

A function's **codomain** is a step; its **domain** is not. Descent groups requirements that constrain the same value, and is not how they are reached — every variable is a root, so all requirements are reached regardless. Across `𝑣 <: (𝐷 ⇒ 𝐶)` and `𝑣 <: (𝐷′ ⇒ 𝐶′)`, the codomains `𝐶` and `𝐶′` consume one value, `𝑣`'s result, and so group. `𝐷` and `𝐷′` are two arguments feeding one parameter — two values — and intersecting their requirements would ask a question the program does not pose. `dom(𝑣)` is a root in its own right, so nothing is missed.

Reading the graph once, at the end, is what [`link_watches`](#delivery-the-watch-follows-the-edge) cannot do: it runs when an edge is **recorded**, so an edge predating an obligation never carries it, and it follows **variable** edges only, stopping at the structural hop a multi-parameter lambda introduces. Two consequences: currying is unobservable, `λ 𝑎 𝑏 → (𝑎 + 1, 𝑎 < 𝑏)` and its curried form taking one type; and `λ 𝑎 𝑏 → (𝑎 + 𝑏, 𝑎 + 1, 𝑏 + "s")` is rejected, where no single requirement is wrong and no variable carries two.

Two problems look like they want an obligation of their own, and are not:

* **A mutable variable's value type** is the *join* over its seed and every write, and the join is already the lattice's: every contribution is a *lower* bound of the mutable variable's value variable, and a positive-position read intersects refinement sets, so a refinement survives exactly when every contribution establishes it. Nothing needs to weaken a contribution to get that — the three rules that emit a contribution edge (`MutWrite`, a mutable binding's initializer, and a `Transact` key's seed) each flow theirs in verbatim. The first two are what define a `:=` mutable variable's `V`; the third is the same rule shape one variable over, on the planning-time carrier, whose key has its own value variable and is checked long after `V` is concrete. A mutable variable with a single contribution therefore *keeps* its refinement (`x := 1` is a `Mut(1)`), which is correct: it really does hold that value at every position.

  A write reaching a mutable variable **through a `Mut` parameter** is one of those writes, and it arrives by the ordinary invariance rule rather than by a mechanism of its own. `emit_apply` decides pass-by-reference from the parameter read off the head of the application spine, and passes the argument's handle through intact; the `(History, History)` arm then relates the two value types in both directions, which is what makes the callee's writes and the caller's declaration one constraint. Reading the parameter's `Mut` syntactically is sound at that one site, since a pass-by-reference parameter is bound at its `Mut(V, D)` by the only code that mints one. While a deref *coercion* sat in the relation this could not work — the handle met a fresh variable and was read through before invariance could see it — so the contribution had to be supplied separately.

  The parameter is read off the **head of the application spine**, not off the function being applied. An n-ary surface call lowers to a curried `Apply` spine, and `apply` types every application as a fresh variable, so the immediately-applied type is a bare `Infer` for every argument after the first — reading it there would contribute for `fw(x, out)` and silently skip `fw(out, x)`. The spine's length is the argument's position, and its parameter is the domain reached by peeling that many codomains off the head (`parameter_type`). For the same reason there is no composite to walk into: rule 2 of the mutability discipline rejects a `Mut` at every position but a domain's root, so a mutable variable is the parameter or it is nowhere.

  A syntactic strip cannot stand in for any of this: `strip_refinements` returns a `Type::Infer` untouched, so it covers a *literal* seed and nothing else — `x := r.a` would type the mutable variable as `{Int | __elem == 0}`. A second strip, on `MutWrite`'s *target*, buys diagnostic ordering by weakening a check that should hold; the constraint is instead skipped outright when the target is not a mutable variable, and `check_mut_write_targets` owns that diagnosis.
* **A projection's domain** resolving to its open-product *demand* rather than to the value flowing in. Replacing the codomain with a field-selection rule does not fix this, because the demand is load-bearing *inference*: `λ 𝑟 → 𝑟.x` infers `{x: ?} ⇒ ?` from that demand alone, and restoring it as a bound puts the narrow record back on the domain. The problem is that a negative position resolves to its demand, which is the same thing the opposite-polarity fallback exists for — see [Closing the single-sided blind spots](#closing-the-single-sided-blind-spots-no-separate-pass).

A **mutable variable** keeps its extent because nothing strips it. A seed contributes verbatim, so `c := [v for v in xs if 𝑝]` types as the filtered collection it is. That shape then fails downstream: it does not terminate in join planning's `insert_iterate_markers`, while everything before it completes (inference, the post-letrec `typecheck`, group-by recognition, `simplify`). A loop body's write computed from the collection's own value, such as `c := [v + 𝑖 for v in c]`, does not finish compiling either. A constant whole-collection write (`c := [3, 4]`) and a keyed write (`m[𝑘] := 𝑣`) compile (`tests/differential_interp.rs`). The non-terminating cases are planning bugs to fix alongside mutable-collection support, not restrictions to encode in the type system.

### Delivery: the watch follows the edge

An obligation is attached to each operand variable as a *watch* (`InferVar::watches`). The invariant is **delivery**: a concrete type reaching an operand variable must reach the obligation watching it.

The bound closure does not deliver on its own. Where two variables sit at different polymorphism levels — as a `let` RHS produces, being emitted one level deeper — their edge is recorded by the arm whose closure runs against the *other* side's bounds, so a type already on the lower variable is never re-offered. The graph stays correct but is only *transitively* readable, which coalesce does and emission does not.

A variable's lower bounds are written in exactly four places, and delivery is wired into each:

* `constrain_go`'s concrete arm — delivers the contribution directly.
* `constrain_go`'s var-var arm — propagates the watch *downward*, toward the variables feeding the watched one, and delivers what they already know.
* `extrude`'s proxy seeding, and `freshen_above`'s clone — both seed bounds by direct writes rather than through `constrain_go`.

That the list is closed is an argument about today's code, not something the compiler enforces, and a missed delivery is quiet: the obligation never narrows, so a type is left undetermined and surfaces phases later on an interior node. `verify_narrowing_is_complete` checks the argument instead of trusting it — after emission, every watched operand is resolved against the completed graph, and a resolved base must already have narrowed its obligation. `a_concrete_operand_reaches_its_obligation` covers the four writers, a case per mechanism.

### Requirements are generalized

Obligations ride variables through `freshen_above`, so a generalized function carries its operators' requirements into its scheme. Each use instantiates and resolves its **own** copy — sharing one would let a `String` use empty an `Int` use's candidate set.

---

## 5. CCL-specific inference rules

§1–§4 describe the engine generically; the general two-pass structure (emit → coalesce) is §2. This section covers the per-node wiring specific to CCL's AST — the structural rule each `TypedExprNode` variant emits. `ccl::infer` runs on a `TypedExpr` whose nodes all carry `Type::Hole`, calls the emit rules below per node, and coalesces the resulting constraint graph back onto each `expr.ty` (§2). A residual `Type::Infer(id)` after inference means the coalesce pass left a variable genuinely unconstrained (e.g. the parameter of an unapplied identity lambda).

### `groupby`

`groupby` is not a dedicated node. It lowers to a cast-wrapped key lambda — `λ k → cast({I | i ▷ c ▷ key == k} ⇒ A, λ i → c(i))` — so its typing falls out of the ordinary `Lambda`/`Cast` rules plus the dependent-refinement machinery of [§4.5](#45-dependent-refinements-via-pi-types); planning's `convert_groupby_pointful` then recognizes the resulting Pi-const source.

### BinOp type rules

| Op kind | Operand constraint | Result type |
|---|---|---|
| `Arithmetic` | a trait obligation over two *unrelated* variables — `Addable`, `Subtractable`, `Multipliable`, `Divisible`, `Exponentiable` | the trait's `Output` |
| `Compare` | a trait obligation — `Equatable` (`==`, `!=`) or `Orderable` (`<`, `<=`, `>`, `>=`), which associate nothing | `Bool`, fixed by the operator |
| `Concat` | both operands constrained to `String` | `String` |
| `BoolLogic` | both operands constrained to `Bool` | `Bool` |

The bottom two rows are ordinary schemes, because their operand types are fixed. The top two are not, and could not be: see [Traits](#traits).

**Note**: String + String → `Concat` rewriting is performed at **compile time** (in `simplify.rs`), not at inference time. Inference accepts `(String, String) ⇝ String` as an `Addable` instance and returns `String`.

### UnaryOp type rules

| Op kind | Operand constraint | Result type |
|---|---|---|
| `Neg` | a **unary** trait obligation — `Negatable` | the trait's `Output` |
| `Not` | operand constrained to `Bool` | `Bool` |

### `Case` inference

For each `Branch { guard, body }`: the guard flows one-way into `Type::Base(BaseType::Bool)` (a refined boolean is still a boolean); every body flows one-way into one shared variable. The overall `Case` type is that variable — the arms' **join**. Two arms of incompatible base types therefore collide as `IncompatibleBounds` at coalesce, where a heterogeneous list literal or `Copair` reports it, rather than as an eager mismatch here. A 0-branch `Case` is a malformed AST (lowering never produces one) and returns `InferError::EmptyCase`.

#### An unobservable arm payload is pinned to what its uses require

An arm naming a tag the scrutinee cannot carry receives no lower bound: no value reaches that payload, and nothing else determines it unless a use of it says something. Such an arm is ordinary code rather than an error (a `match` written for the whole `Option` over a scrutinee inference has pinned to one tag), so inference chooses a type for it rather than reaching the post-inference wall with an unresolved variable. Unobservability is read off the **lower** side alone — a bound *above* the position is a use's requirement, which is what the choice below reads, not evidence that a value arrived.

The rule is **pin to a type the payload's requirements accept**, and a requirement reaches the payload in one of two recorded forms:

- A **subtyping upper bound**, `payload <: 𝑈`, from the binder occurring in a position. When `𝑈` resolves concretely it is the strongest requirement available, and pinning past it contradicts the flow. The commonest shape is the body that *is* the binder (`` `b(w) → w ``), where `𝑈` is the arms' result join: choosing `Unit` there does not merely lose information, it enters that join and collides with the reachable arm's type.
- A **trait obligation**, from an operator read (`w + 1` records `Addable`). The obligations choose from the types their surviving instances still accept.

With neither, nothing observes the payload at all and `Unit` — the type that carries no information — is the choice. The two forms do not compete for one payload: an operand's upper bound is the operator's own requirement variable rather than a concrete type.

Each upper bound is resolved **as its own position**, by a walk entered at that variable rather than as a hop along the payload's bound chain — the distinction [the collapse happens at the position](#the-collapse-happens-at-the-position) draws. Reading it through the payload would collapse its quantifier as a side effect and hand the result to every other variable on the chain; deciding it in the pin is one deliberate choice, at the one variable whose quantifier is being eliminated.

The choice is recorded on the *variable*, not in the binder slot, so every occurrence of it agrees — the slot, the scrutinee's expected variant, and hence an enclosing lambda's parameter type. That is also why the pin precedes the scrutinee's own walk and not merely the branches': the scrutinee's type is the variant these payload variables sit inside, so a pin placed after it leaves that reading stale. Unreachable arms are **kept**, not pruned: an arm for a tag the scrutinee cannot carry projects an empty restriction and contributes nothing, while pruning would narrow the arm set relative to the enclosing lambda's declared domain. `pin_unobservable_arm_payload` in `src/ccl/infer/solve.rs` holds the mechanism, including the ordering constraints that place it inside the coalesce walk.

A refined pin is what makes the compaction identity below load-bearing: an empty
refinement set is absorbing under the positive intersection, so `Int@1` arriving
from the pin would be erased by the scrutinee's own per-tag variable if that
variable's contribution read as an empty set. It does not.
`CompactType::refinements` is an `Option`, the same sentinel every *shape*
component carries: `None` is "no refinement contribution here" and merges as the
identity, and only a *value* carries a set — an empty one included, because a
value that guarantees nothing is a fact about it. A bare variable and a hole are
not values.

### Record literals and field access

A CHL record value is a parenthesised list of `name=value` fields:

```python
r = (x=1, y="hello")   # Record([("x", 1), ("y", "hello")])
r.x                        # Apply(r, Proj(ProjKey::Field("x"))) → 1
t = (1, "hello")       # Tuple([1, "hello"])
t.0                        # Apply(t, Proj(ProjKey::Index(0))) → 1
```

**Lowering:** the surface has one postfix form for both keyings — the parser holds the key
verbatim in `Attribute { attr }`, and lowering resolves which `ProjKey` it is. The two are
disjoint because an identifier cannot begin with a digit, so *leading digit* is the whole
discriminator; nothing is inferred from context. `[…]` is collection lookup only, and
lowers to the application it *is* (`c[k]` → `Apply(lower(k), lower(c))`), so a product —
having no domain — is never reachable through it.

- `(name=v, ...)` → `TypedExprNode::Record([(name, v), ...])`.
- `expr.field` → `Apply(lower(expr), Proj(ProjKey::Field("field")))`.
- `expr.n` → `Apply(lower(expr), Proj(ProjKey::Index(n)))`.

**Type inference:** `Record([(k, e), ...])` infers to `Type::Record([(k, T), ...])` where each `T` is the inferred type of the corresponding value expression — identical in structure to `Tuple` inference.

**Lambda elimination:** `Record(fields)` inside a lambda body is treated identically to `Tuple`: each field expression is recursively eliminated, producing `Apply(Record([…elim fields…]), Zip)`. The inner `Record` node carries type `Record([(k, Fun(D,T)), …])` — a record of morphisms — and the outer `Zip` application fuses them via a shared `FanOut`, producing a morphism to a record. This ensures `typecheck` invariants hold: a `Record` node always has a `Record` type.

**Operator conversion:** At the `Apply(Record([…]), Zip)` node, the `Zip` handler dispatches on the argument shape. For a `Record` argument it uses `zip_arms_named_at`, which selects `Zip::new_at` (function-tiling inputs) or `MakeRecord::new_named` (scalar inputs) and preserves the declared field names in the output `Tile::Record`. `Proj(ProjKey::Field(name))` compiles to a `MapResult` using `FunctionDef::RecordField(name)`, extracting the named field from the upstream record tile — identical in mechanism to `Proj(ProjKey::Index(n))` for tuples.

### `Proj` inference — open product domains

A bare `Proj(key)` node — i.e. the projection morphism, not an application of it — is inferred as a function type whose domain is an ordinary structural product constraining only the projected field. There is no dedicated "partial" `Type` variant; width-subtyping does the work:

| Key | Inferred domain requirement |
|---|---|
| `Proj(Index(n))` | `Tuple([?_0, …, ?_{n-1}, ?a]) ⇒ ?a` — an `n+1`-tuple padded with fresh vars |
| `Proj(Field("x"))` | `Record([("x", ?a)]) ⇒ ?a` — a single-field record |

The index domain is a `Type::Tuple` padded with fresh variables up to index `n`; the field domain is a single-field `Type::Record` (see `emit_proj`). Width-subtyping lets either unify with any concrete product carrying at least that field, constraining `?a` to the element type there.

**What the padding costs the diagnostics.** `Type::Tuple` is dense, so "has position `𝑛`" is only expressible as "is `𝑛+1` wide" — a positional projection cannot state a *sparse* requirement the way the named one does. Two consequences the error path has to absorb, since both would otherwise report a shape the program never had:

- A projection past the end fails as a **width** violation, and the first absent position is the value's own width rather than the one the user asked for. So the subtyping edge reports the *widest* position the requirement demands (`constrain_go`'s tuple arm), which for a projection is the only position genuinely demanded — `t.99` on a 3-tuple is missing `.99`, not `.3`. `InferError::MissingField` then states the requested position against the found width, rather than the padded 100-tuple.
- Projecting with the *wrong keying* (`r.0`, `t.name`) is a `Record`-vs-`Tuple` constructor mismatch whose "required" side is the partial requirement (`(?31)`, `{name: ?31}`). A record/tuple mismatch is always a keying confusion, so the message carries that as a hint instead of leaving the partial shape to be read as a type.

A projection's domain appears only at a negative position, so the one-way constraints leave it under-determined; its full structure (the value actually flowing in) is recovered structurally during the coalesce walk by monomorphizing the morphism to its input — see [Apply is one-way](#apply-is-one-way) and [Closing the single-sided blind spots](#closing-the-single-sided-blind-spots-no-separate-pass).

### `Compose` inference

N-ary `Compose([f₀, f₁, …, fₙ₋₁])` is inferred by chaining: each morphism's codomain is constrained as a **subtype** of the next morphism's domain (`constrain_subtype(prev_codomain, d_i)`). This allows a refined codomain (e.g. `Refinement(T, pred)`) to feed into a base-typed domain (`T`) without a type error. The overall type is `Fun(domain(f₀), codomain(fₙ₋₁))`. This case arises when `infer` is run over output from `simplify`, which can produce `Compose` nodes.

### Variant (sum) semantic equality

The post-inference structural checks decide type equality via the solver's `constrain_subtype` (bidirectionally, in `typecheck_compatible`), which compares `Type::Variant` tag sets structurally. Nested sums never reach this comparison: `TypedExpr::copair` flattens at construction (next section), so a `Var(y)` referencing a let-bound sum still contributes a single flat variant.

### Union flattening (construction-time)

`a ++ b ++ c` in CHL parses to right- or left-associated binary AST nodes. **`TypedExpr::copair` flattens at construction time**: any operand that is itself a `TypedExprNode::Copair` is spliced into the outer operand list, so the constructor always returns a flat N-ary node. This makes the invariant **"no operand of a `Copair` is itself a `Copair`"** hold from lowering onward — inference, lambda elimination, and operator conversion never need to look through nested AST. The flat AST flows naturally into a flat `Type::Variant` domain (each operand contributes one tag). `operator_conversion` compiles the N-ary node directly to a single `UnionOperator` with N inputs.

### `check_fully_typed` validation

After coalesce, `infer` calls `check_fully_typed(expr)` to assert that every `ty` and every `TypedBinding::ty` in the tree is a concrete type — no `Type::Hole` or `Type::Infer(_)` anywhere, including inside compound types like `Fun` or `Tuple`. Returns `InferError::UnresolvedHole` or `InferError::UnresolvedInfer(id)` on failure, with the symbolic representation of the offending expression for debugging.

### TODOs

- Infer `Let.ty` from the type of `value` (required before `Let` nodes can be compiled; see [optimization.md](optimization.md#compilation)).
- CHL `match` statement lowering: desugar at lowering time using `Let(__scrut)` + guard expressions (no IR changes needed).

---

## 6. Future work

Directions the current design points toward but does not yet implement.

### General `𝑈 ⇒ 𝑇` cast

The [`Cast`](ir.md#cast--explicit-refinement-acquisition) node is named more generally than the current implementation, which only honours `Fun(Refinement(_, _), _)` targets — i.e. it can only attach a refinement to a collection function's *domain*. The name suggests the full upcast semantics `𝑈 ⇒ 𝑇` (re-view a value of any type `𝑈` at any supertype `𝑇`). Two directions are open: **generalize** `Cast` to the full `𝑈 ⇒ 𝑇` upcast (subject to `𝑈 <: 𝑇`), or **rename** it narrower (`Refine` / `AssertDomain`) to match what it does. Acquiring a *value-level* refinement (a covariant narrowing like `Int → {Int | 𝑝}`) is not an upcast — it is a runtime/SMT-checked narrowing — so the general form must keep that boundary. (An in-code `TODO` on the `Cast` node in `ccl/expr.rs` points here.)

### Pattern-match arm binder referenced by the result type

A `match` arm whose result type carries a refinement closing over an arm-local binder:

```python
def filter_against(tagged):
    match tagged:
        case Pair(a, b): return [x for x in xs if x > b]
        case Single(s):  return [x for x in xs if x > s]
```

The right answer is to *inline the case match into the refinement* — produce a refined type whose predicate is itself a `match` on `tagged`:

```
{𝑥 | match tagged:
       case Pair(a, b): 𝑥 > b
       case Single(s):  𝑥 > s }
```

so the refinement's only free variables are `𝑥` (its own binder) and `tagged` (in scope). This needs the type system to express match expressions in predicate position, the inliner to construct them, and the refinement equality/SMT machinery to handle them. Until then inference rejects this shape with a typing error ("result type references arm-local binder `b`").

---

## 7. Glossary

Consult these definitions as needed; each term is introduced in context in §1–§4 above.

| Term | Origin | Definition |
| :--- | :--- | :--- |
| **`Type::Infer` / `InferVar`** | Algebraic subtyping | An inference unknown. `Type::Infer(Rc<InferVar>)`; the shared `InferVar` carries a stable `uid`, a `level`, and a `RefCell` of lower/upper bounds. The solver works directly on `ccl::Type`, so this *is* the constraint-graph node — there is no separate "SimpleType". |
| **Position** | Algebraic subtyping | A location within a type expression where another type sits (a function domain/codomain, a record field value). Each position has a polarity determined by its path from the outermost type. |
| **Polarity** | Algebraic subtyping | Positive or negative. The outermost type is positive; codomains and field values preserve polarity, domains flip it. Polarity selects the primary bounds for compaction; [Coalescing](#coalescing-from-bounds-to-types) describes the additional opposite-side reads. |
| **Lower Bound** | Algebraic subtyping | A type `L` recorded on variable `α` such that `L <: α` must hold (a type that "flows into" `α`). Lower bounds supply the primary contributions at positive occurrences. |
| **Upper Bound** | Algebraic subtyping | A type `U` recorded on variable `α` such that `α <: U` must hold (a type `α` "must flow into"). Upper bounds supply the primary contributions at negative occurrences. |
| **Level** | Algebraic subtyping | Inference scope depth, starting at 0. Every `let` RHS and `MutDecl` initializer is emitted one level deeper; the surrounding level is restored for the body. Generalization is decided after RHS emission. |
| **Level mismatch** | Algebraic subtyping | During `constrain` involving a variable `v`, the condition that the other side contains a variable whose level is numerically higher than `v`'s. Triggers extrude. |
| **Extrude** | Algebraic subtyping | On a level mismatch, the process of copying a type down to a target level by replacing each too-high variable with a fresh proxy at that level (linked back via the polarity-appropriate bound), so the constraint can be recorded without leaking inner-scope variables. |
| **Scheme (PolyScheme)** | Algebraic subtyping | A generalized type with a cutoff level. Variables whose level is numerically greater than the cutoff are quantified; using the scheme *instantiates* (freshens) them at the current level. |
| **CompactType** | Algebraic subtyping | A flat, per-position bag of contributions (variables, atoms, an optional record shape, an optional variant shape, an optional function shape, and a refinement set) produced for simplification and co-occurrence analysis. |
| **`CompactGraph`** | Algebraic subtyping | A top-level `CompactType` plus a side-table of recursive-variable definitions; the intermediate produced by `compact_type` and consumed by `simplify_type` / `coalesce_compact`. |
| **Coalesce** | Algebraic subtyping | Materializing a `CompactGraph` back into a `ccl::Type`. Compaction selects bounds by polarity, with opposite-side shape recovery and negative-position merging as described in [Coalescing](#coalescing-from-bounds-to-types). |
| **`FieldKey`** | Algebraic subtyping | The shared key for record/tuple fields *and* variant tags: `Index(usize)` for positional (anonymous) keys, `Name(SmolStr)` for named ones. |
| **`Variant` (tagged sum)** | Both | The single sum representation: `Type::Variant`, keyed by [`FieldKey`]. Named tags are source-level `` `tag(…) ``; positional (`Index`) tags are anonymous sums (what `++` produces). Width-subtyping is the dual of records (a subtype has *fewer* tags). |
| **`ccl::Type`** | Both | The public, immutable, user-facing AST type — and, since the unification, also the solver's working representation. Inference unknowns are `Type::Infer`; `Hole` is normalized to a fresh var, while `Refinement` is kept and rides the lattice as a refinement. |
| **Refinement** | Both | A `Type::Refinement(T, r)` carries a refinement `r` (an immutable predicate `Rc<TypedExpr>`) — a refinement in its role as a black box to the subtyping lattice. A type holds a *set* of refinements, width-subtyped like records (more refinements ⇒ subtype; `{T\|p,q} <: {T\|p}`). Refinements compare by type-blind structural predicate equality (`Refinement`'s `PartialEq`; pointer-equal predicates short-circuit), with implication reached for only as a fallback (`smt_sub`). A refinement is *required* — `constrain_subtype` is strict (`T ⊀ {T\|p}`); acquiring one is an explicit runtime `Restrict` at the collection-iteration boundary, not subsumption. |
| **Let Binding Resolution** | Cambra-Specific | Ensuring a `Let` binding's fully resolved type overwrites the type of any `Var` references to it within the let body. |
| **`InferArena`** | Cambra-Specific | The single owner of every inference variable minted during one `infer()` run. Captures each mint through a thread-local sink and, on `Drop`, clears all variables' bounds to break the `Rc` cycles that mutual subtyping constraints form — the end-of-inference cleanup that reference counting alone cannot do. See §3.2. |
| **Pi type** | Both | A `Type::Fun` with `name: Some(𝑥)` — the dependent function type `(𝑥: domain) ⇒ codomain`, with `𝑥` bound in `codomain` and referenceable by nested refinement predicates. `name: None` is the ordinary function type. See §4.5. |
| **`Subst` / discharge / rename** | Cambra-Specific | A context morphism over *term* binders (`ccl::subst`), riding a constraint edge in a two-sided `Bound { self_subst, ty, ty_subst }` (native direction, never inverted at record time). A **rename** `[𝑘 ↦ 𝑥]` is invertible; a **discharge** `[𝑥 ↦ arg]` (dependent application) is one-way. Composed forward along the closure and the coalesce walk, forced at refinement predicates. See §4.5. |
| **Correspondence** | Both | The binder alignment `[𝑘 ↦ 𝑥]` *derived* by `constrain_go`'s Fun/Fun arm when relating two Pi codomains, carried on the codomain edge so a dependent refinement renames consistently. See §4.5. |

---
[^1]: For example, `def f(x): x` has the Principal Type `a -> a`, and `def map(f, collection): ...` might have the Principal Type `(a -> b) -> [a] -> [b]`, where `[a]` denotes a collection for all `a`.
[^2]: When a function like `def id(x): return x` is generalized into a PolyScheme, type variables minted inside the body are assigned a level numerically higher than the surrounding outer scope's depth — the "cutoff." Variables above the cutoff are strictly local to the function (like `x`'s type, `α`); because they are self-contained they are universally quantified and work for all types. Each call instantiates the scheme by minting a fresh variable for `α`, preventing `id(5)` from colliding with `id("hello")`. Variables at or below the cutoff are free variables captured from the enclosing environment; instantiation passes them by reference so all call sites share the same outer-scope constraints.
