# The Lean model of the CCL type system

`formal/` specifies selected operations of the
[CCL inference engine](../src/ccl/design/type-inference.md#1-algorithm-overview) in Lean 4.
Proofs establish properties of the model. Differential tests compare five modeled operations
with Rust on generated inputs. Neither form of validation establishes correctness outside its
stated fragment.

## The oracle stance: the model checks, it does not reproduce

The planned term-typing oracle checks admissibility: a type inferred by Rust must be accepted
for the term by the declarative typing judgment. It need not reproduce Rust's choice among
several valid types. This oracle is not implemented; see [The typing oracle](#the-typing-oracle).

The implemented oracles compare subtyping, polar merge, kind refusal, kind merge and coalescing.
They compare each operation's verdict or result using its wire representation and model
equivalence, rather than comparing complete inference runs.
[The differential oracles](#the-differential-oracles) describes their inputs and exclusions.

## What is pinned today, and what is not

| Solver component | Model and differential coverage | Proof coverage |
| --- | --- | --- |
| `constrain_subtype` | `Subtyping` / `subtypeCheck`; generated pairs in the modeled concrete fragment. | Reflexivity and transitivity for well-formed types; checker soundness and completeness. |
| The Σ subtyping premise | `SigmaBelow` relates a candidate list, element types and a kind. No differential of the full Σ rule. | `sigma_below_iff_elementwise` and `swapped_premise_is_unsound` specify the kind-premise direction. Binder correspondence and sums nested in types are not modeled. |
| `CompactType::merge` | `CompactTy.merge`; each generated fold step is compared. | Commutativity, idempotence, associativity and congruence; leastness and uniqueness for the induced absorption order. |
| `TypeKind::refuses` | `refuses`; generated concrete types and kinds. | `not_admits_of_refuses`: refusal implies non-membership, not the converse. |
| `CompactTypeKind::merge` | `mergeTypeKind`; encodable generated fold steps are compared. | Commutativity, idempotence and join associativity. Meet associativity is checked over a finite universe, not proved generally. |
| `coalesce_compact` | `coalesce`; generated compact bounds are materialized and compared. | Total result computation, well-formedness of successful results, and the conditional bound/leastness results described under [Materialization](#materialization-the-merge-is-a-bound-and-the-least-one). |
| Term typing | `Term` / `HasTy`; no Rust term-typing differential yet. | Progress, preservation and refinement soundness for the pure-core fragment below. |
| Bound recording, sweeping, `extrude`, traits, `simplify_type` and schemes | Not modeled or differentially checked here. | None here. |
| `compact_go` | Produces operands for the merge/coalesce differentials; its output shape is modeled by `CompactTy`. | The operation itself is not checked. |

A defect in `compact_go` can affect the shared operands before comparison and therefore escape
the merge and coalesce oracles. Agreement on those operands does not validate their construction.

[`CclFormal/Axioms.lean`](CclFormal/Axioms.lean) checks the axiom lists of named headline results
with `#guard_msgs` around `#print axioms`. The expected lists contain only `propext`,
`Classical.choice` and `Quot.sound`, with some results using only a subset. An added assumption or
`sorryAx` changes the checked output and fails the build. This is an explicit list of checked
results, not an automatic scan of every declaration.

A semantic change to modeled constraint or coalescing behavior must update the model in the same
change or record the divergence in the PR. Generated tests exercise this agreement but do not
prove it for all Rust inputs.

## The concrete type grammar

[`CclFormal/Ty.lean`](CclFormal/Ty.lean) defines `Ty`: base types, unsigned index ranges, data
source domains, `Txn`, functions, tuples, records, closed variants and refinements.
Function kinds are the two fixed values `compute` and `data`.

The grammar is a subset of concrete Rust types, not every type a fully inferred program can
contain. It has no Σ or witness-reference constructor and no open variant form. It also excludes
inference unknowns (`Hole`, `SharedHole`, `BoundedHole` and `Infer`), kind variables, and the
`History` and `ChanDom` forms. The `ty_json` encoder in
[the differential harness](../tests/differential_oracle.rs) defines the supported wire boundary:
it rejects sum-bearing function kinds and function binders other than a raw name or no name.

`Ty.WellFormed` requires unique record/variant keys, recursively well-formed children, and
nonempty refinement lists over an unrefined base. Refinements are represented as lists; the
subtype relation observes predicate membership rather than list order.

A dependent reference to an enclosing function binder is `Predicate.piBound`, corresponding to
`Name::PiBound`. Free references remain identity-bearing names. The subtype relation compares
closed codomains without a rename environment and does not read the function's binder-name slot;
the slot still participates in `Ty`'s structural equality. Closing binder references therefore
does not make the entire `Ty` representation independent of that slot.

The predicate grammar omits expression type slots. Predicate-local lambda binders use positional
references; embedded casts retain the target domain's refinement predicates. The Rust encoder
`pred_json` supplies these forms to match `eq_term_modulo_ty_slots`. The general binder
representation is specified in
[Forms](../src/ccl/design/type-inference.md#a-binder-reference-is-stored-in-one-of-two-forms).

## The declarative subtype relation

[`Subtyping.lean`](CclFormal/Subtyping.lean) defines the relation;
[`SubtypeChecker.lean`](CclFormal/SubtypeChecker.lean) implements its terminating checker.
`subtyping_of_subtypeCheck` and `subtypeCheck_of_subtyping` establish the two directions of
agreement. Rule examples are checked by `#guard` declarations.

The relation differs from the Rust implementation in three recorded ways: it has no trivial-equality
shortcut, compares closed function codomains without binder correspondence, and has no
partition-collapse arm. The module documentation states these boundaries. In particular, omitting
the equality shortcut exposes the need for unique field keys in the reflexivity theorem.

`subtyping_trans` requires `Ty.WellFormed` for all three types and two subtype derivations.
It adds no rename-environment premises. This is a theorem about the modeled grammar; it does not
extend the fragment to inference variables or dependent sums.

## Terms, typing, and safety

[`Term.lean`](CclFormal/Term.lean) defines literals, indexed variables, lambdas, application,
let-bindings, tuples/projections, tagged variants/cases and refinement casts. It defines values,
capture-free substitution, call-by-value stepping, a filter-blocked judgment and `HasTy`.

`Ty.TermFragment` restricts all refinement predicates to `Predicate.elemOnly`. Such predicates
can use the refined element but not free names, enclosing Pi binders, predicate-local lambdas or
embedded casts. `HasTy` enforces this restriction where a typing rule selects a type.

[`WellTypedTermsAreSafe.lean`](CclFormal/WellTypedTermsAreSafe.lean) proves:

- `progress`: a closed well-typed term is a value, takes a step, or is filter-blocked.
- `preservation`: a step preserves typing when the context's types are in the term fragment.
- `refinement_soundness`: if a closed refined term evaluates to a value, its predicates hold on
  that value. This does not assert that evaluation terminates or that a filter never blocks.

Composition, record terms, wildcard case arms and dependent term refinements remain outside this
calculus. `case_binder_sound` covers tagged arms, not wildcards. Extending it to wildcard payloads
requires checking the payload-binding rule; the existing tag-arm result provides no such coverage.

## The polar merge

`CclFormal/Merge.lean` defines a compact representation and a polarity-indexed merge.
It models selected fields of Rust's `CompactType`, not the complete solver state.
A function slot is `(KindMerge, CompactTy, CompactTy)`: kind, one domain and one codomain.
There is no list or optional domain inside that slot.

The domain merges at `!pol` and the codomain at `pol`. Kind accumulation uses `joinKind`:
`unknown` is its identity, `data` and `compute` are incomparable, and `conflict` absorbs
either. The model's domain merge does not select a rule from the intermediate kind.

The principal representation laws are:

| Result | Scope and hypotheses |
|---|---|
| `equiv_refl`, `equiv_symm`, `equiv_trans` | Equivalence of compact representations. |
| `merge_comm`, `merge_assoc` | Either polarity; no well-formedness premise. |
| `merge_idem` | The operand is `wellFormed`. |
| `merge_congr_left`, `merge_congr_right` | Equivalent operands give equivalent results. |
| `foldMerge_perm` | A fixed seed and permuted remaining contributions. |
| `foldMerge_dup` | The duplicated contribution is `wellFormed`. |
| `merge_is_least_absorber`, `least_absorber_unique` | Both operands are `wellFormed`; leastness and uniqueness use `absorbedBy`, not `Subtyping`. |

`equiv` compares atoms and refinements by membership, maps by key lookup and recursive payload
equivalence, and function slots componentwise. `wellFormed` requires unique map keys,
recursively well-formed children, no conflicting function kind, and a present refinement slot
at every content-bearing position.

An absent refinement slot means no contribution and is the merge identity. A present empty
set means a value with no predicates. At positive polarity, intersecting with that set removes
predicates; merging with the absent slot retains the other contribution.
The empty compact position is an identity at either polarity
(`merge_cempty_left` and `merge_cempty_right`).

### Cross-polarity laws require a semantic interpretation

The module proves laws for each fixed-polarity merge. It does not prove cross-polarity absorption
or distributivity by treating `CompactTy` as one lattice carrier.

The intended polar interpretation reads contributions as alternatives at positive polarity and
requirements at negative polarity. Using the same compact syntax at opposite polarities therefore
does not establish that it denotes the same type. A semantic lattice account would need a common
carrier and an interpretation connecting both operations to it.

The materialization theorems below state the available relationship with `Subtyping`.

### The lattice is a semantic statement

`absorbedBy pol a b` means `equiv (merge pol a b) b = true`. This is an order induced by
one representation operation. Leastness in that order does not establish that every semantic
type join has a representable `Ty` or that coalescing computes every such join.

`coalesce` is a total Lean function whose result distinguishes a type, an unresolved position
and an error. As a function from compact positions to successful types, it is partial.
For example, multiple atom contributions have no untagged union constructor in `Ty`.
An error is an outcome of the implemented model, not a theorem that a unique semantic join
exists but lacks syntax.

A full lattice semantics and a justification of `simplify_type`'s absorption/co-occurrence
rewrites remain outside the proved model. The documentation makes no claim that disabling
that Rust pass preserves all observable behavior.

### Why the model carries `CompactTy` at all

The merge differential needs the operation's input and output representation, not only
materialized types. Fixed-polarity permutation and duplication laws are also representation
properties. Agreement after materialization alone would not prove those laws.

The comparison boundary matters. Rust carries inference-variable sets, kinding constraints,
history slots, function names, sum binders, `domains_disagree` and a `combined` diagnostic
snapshot that this `CompactTy` does not model. The encoder also maps Rust's `Plain` and
`Data` kinds to the model's `data`. Model equivalence is therefore not equality of complete
Rust `CompactType` values.

The absent domain-disagreement fields are particularly relevant to acceptance: Rust can retain
evidence about the two pre-merge domains that is no longer recoverable from the merged domain.
That gap is specified under [The fn slot holds one domain](#the-fn-slot-holds-one-domain).

## Materialization: the merge is a bound, and the least one

`CclFormal/Coalesce.lean` materializes compact slots into `Ty`. Its result has three forms:

| Result | Meaning in the model |
|---|---|
| `ok (some t)` | A concrete type was produced. |
| `ok none` | A component remains unresolved; no modeled type is available. |
| `error e` | The modeled materializer rejected the position. |

An unresolved result need not be an entirely empty position. A function with an unresolved child
or a sparse index-keyed product can also remain unresolved. The Rust comparison records this
category rather than an inference-variable identity or its attached predicates.

Each occupied shape contributes an entry to `combine`, even when that entry is unresolved.
No entries produce `ok none`; one entry is returned with refinements attached; multiple entries
produce `incompatible`. Error propagation from the shape helpers occurs before this combination.

The slot rules are:

- A record slot with no fields is incompatible, not unit. Dense index keys materialize a tuple
  in index order; sparse index keys remain unresolved. Name keys materialize a record.
  Mixed index/name keys give `partialRecord` before payload traversal. Otherwise payload
  errors propagate even if the shape will remain unresolved.
- Variant payloads materialize recursively. An empty closed variant is distinct from an
  empty record slot.
- A function first materializes its codomain. `conflict` then gives `conflictedSlot`.
  A `data` function whose bare atom domain contains multiple distinct atoms gives `domainJoin`.
  Otherwise its domain materializes at opposite polarity; both children must resolve to
  produce a function type. An `unknown` kind uses the compute default.

Termination uses a lexicographic measure: `(depth t, 1)` for `coalesce` and `(depth t, 0)`
for the shape helpers. Calls from `coalesce` to a helper keep the position and decrease the
second component; recursive child calls decrease depth. There is no recursive materialization
of a folded list of domain alternatives in the current implementation.

Unit is a base type, not the result of width-subtyping a product down to zero fields; see
[The empty product is unit](../docs/chl-spec.md#66-the-empty-product-is-unit).

### Bound and leastness hypotheses

`merge_is_a_bound` in `MaterializedMergeIsABound.lean` requires:

1. `concrete a` and `concrete b`.
2. `concrete (merge pol a b)`.
3. `DataAgree pol a (merge pol a b)` and `DataAgree pol b (merge pol a b)`.

`concrete` is `wellFormed && kindResolved`. The second condition requires every function kind
to be `data` or `compute`; defaulting an unknown operand before merging can disagree with a
kind resolved by another contribution.

`DataAgree` recursively checks shared fields and function components. When the left function
kind is `data`, its domain must be `equiv` to the right domain, at either polarity.
Domain recursion checks both directions, and codomain recursion retains the current polarity.
This is a structural sufficient hypothesis used by the proof, not a proved equivalence with
existence of a subtype bound.

The theorem concludes `MergeIsBoundAt`. When both operands and their merge materialize,
the positive result is above both operand types and the negative result is below both.
If any of the three does not materialize, that Boolean statement is true without asserting
a subtype relation. The theorem does not prove successful materialization.

`merge_is_least_type` in `MaterializedMergeIsTheLeastBound.lean` has different hypotheses:
concrete operands, a well-formed candidate type `u`, successful materialization of both operands
and the merge, and the two subtype bounds involving `u`. It does not require `DataAgree`
or a concrete merged position. It proves that `u` also bounds the materialized result.
That conditional leastness statement alone does not assert that the result bounds its operands.

The induction `bounds_merge` varies the bound's side independently of merge polarity:

| Merge polarity | `u` above both operands | `u` below both operands |
|---|---|---|
| Positive | `u` is above the result: join leastness. | `u` is below the result. |
| Negative | `u` is above the result. | `u` is below the result: meet greatestness. |

The off-diagonal cases support function domains, where polarity and subtype direction reverse
and data-function domains require both directions. The proof reasons about materialized types
rather than assuming that `Subtyping` reflects into `absorbedBy`.

### The fn slot holds one domain

Both model and Rust function slots contain one compact domain. Rust additionally records
`domains_disagree` and `combined`. `data_domains_disagree` inspects input domains because a
contravariant merge can erase their distinction by combining record keys or refinements.
`coalesce_compact_go` uses the retained evidence to reject a data-domain conflict.

The model has neither field. `funShapes` recognizes the bare-multiple-atom domain case,
but cannot reconstruct every operand-level disagreement from one merged domain.
A generated sample with no reported differences does not establish agreement on these omitted
cases. No domain-list fold, `widest` tie-break, or `Option CompactTy` domain encoding describes
the current model.

### Checked samples and their limits

`MaterializedMergeIsABound.lean` contains executable `#guard` assertions for:

- 2,888 well-formed cases and 2,048 concrete cases.
- 1,844 concrete cases satisfying the bound theorem's additional hypotheses.
- No failures among those 1,844 cases.
- Eight unguarded bound failures and four monotonicity failures among the concrete cases.
- No failures of `MergeIsBoundGuarded` on that finite sample.

`MergeIsBoundGuarded` searches the finite `pool` for a candidate bound. It does not quantify
over every `Ty`. Its passing sample is not a general bound-existence theorem or a proof that
every Rust-produced compact value meets the required hypotheses.

`coalesce_wellFormed` proves well-formedness of a successfully materialized well-formed position.
`pool_wellFormed` applies it to the candidate pool, and `leastness_failures_eq_nil` derives the
sample's leastness result from `merge_is_least_type` rather than reevaluating a Boolean sample.
These proofs remain statements about the modeled fragment.

## The differential oracles

[The README](README.md#the-differential-oracles) owns the operation table, run commands and
replay instructions. [The harness](../tests/differential_oracle.rs) uses the seeded generator in
[`tests/type_gen/mod.rs`](../tests/type_gen/mod.rs). The `test-helpers` feature exposes the compact
operations needed by this integration target.

The compared fragment is bounded by the encoders, not just by whether Rust accepts a type:

- `ty_json` encodes closed variant arm sets and functions without sum binders. It has no
  representation for inference unknowns, histories, channel domains or witness references.
- `cty_json` omits inference-variable identity, the Pi binder name, variant openness and
  diagnostic domain-conflict payloads. It rejects a history slot, a function with binders, a
  sum-kind pin, and unsupported atoms or predicates.
- `KindPin::Data` and `KindPin::Plain` both encode as the model's data kind. Their distinction
  is therefore not checked by that comparison. The active
  `bug_plain_and_data_pins_have_the_same_wire_encoding` test pins this missing distinction.
- The subtype generator excludes duplicate record/variant keys, which violate
  `Ty.WellFormed`. The model's find-first field rules and Rust's equality shortcut must not be
  assumed equivalent for duplicate-keyed inputs.
- The predicate wire carries element/free/Pi references, literals, operations, projections,
  application, predicate-local lambdas and cast-domain refinements. Expression nodes without a
  corresponding predicate constructor, such as let-bindings and aggregates, are outside it.

All five drivers panic when a generated case unexpectedly falls outside their wire schema.
The generators target the modeled fragment; encoding failures are not omitted from comparisons.
The drivers check the number of returned verdicts as well as their agreement.

The documentation-reference checker scans Markdown and Rust, not Lean comments. Markdown
citations in Lean therefore require manual review when a heading changes. The Lake configuration
does not promote every warning to an error; proof elaboration, executable assertions and the
named axiom checks are separate from warning cleanliness.

## Roadmap

The following extensions are proposals, not coverage supplied by the current proofs or oracles.

### The typing oracle

Generate small CHL programs, encode Rust's typed AST, and check admissibility of the inferred root
type with the Lean typing judgment. This requires a term wire format and an explicit agreement
on the supported fragment. It would compare typing results, not require both systems to choose
the same type.

### The solver model

Represent constraint processing as state over variables and their bound lists, initially with
fuel. The intended proof obligations are:

- Bound-recording soundness and admissibility of the final inferred type.
- Termination, replacing fuel with a well-founded measure that accounts for the seen-cache
  and fresh variables introduced by extrusion.
- Scope preservation, including levels, extrusion and escaping references.

Termination is a proposed priority. A stalled build is not by itself evidence that the solver
failed to terminate; attributing one requires a reproducer or diagnostic trace.

### Σ types and `FunKind` inference

The current kind definitions and `SigmaBelow` predicate do not put dependent sums into `Ty`
or sum binders into `CompactTy`. Extending the grammar and wire format would require modeling
binder correspondence, witness scope, candidate-kind constraints and their materialization.
The current kind-merge differential is not a substitute for that extension.

The relevant Rust contracts are owned by
[What checks each premise](../src/ccl/design/type-inference.md#what-checks-each-premise) and
[Data vs compute functions](../src/ccl/design/type-inference.md#46-data-vs-compute-functions).
A formal extension must preserve their distinction between a term introducing a sum and
subtyping an existing sum. A domain disagreement must not silently acquire a sum merely because
a merge needs a representable result.

Unresolved kind variables also require a model of pinning and final defaulting. Adding sums or
kind variables does not by itself discharge `DataAgree` or supply a proof of semantic joins.

### Histories: the mutability semantic model

A history model can be developed independently of the solver-state model. Its proposed subject
is semantic equivalence between surface mutation and the emitted `letrec`/`transact` recurrence,
not admission of every pipeline transient into the concrete typing grammar.

The reference contracts are
[The model: histories and causal recursion](../src/ccl/design/mutability.md#the-model-histories-and-causal-recursion)
and [Semantics](../src/ccl/design/mutability.md#semantics).
The model would distinguish overwrite's last-write-wins and off-path carry-forward behavior
from append's accumulation law, and arbitrary transactional as-of reads from terminal reads.
`History`, `ChanDom`, `Hole` and `Infer` remain outside the current concrete typing grammar.
