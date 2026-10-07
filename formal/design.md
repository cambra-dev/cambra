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

`CclFormal/Merge.lean` models `compact.rs`'s polar merge over the fragment above: `CompactTy` mirrors
`CompactType` slot for slot, `merge` mirrors the polar `CompactType::merge` / `CompactFun::merge`,
and `equiv` mirrors `CompactType`'s own `PartialEq`, set-semantic at every layer. Its module doc
lists the laws it proves and what the mirror drops. One of those laws reaches beyond the merge:
`joinKind`, the flat semilattice the kinds join in, is also the Rust's `KindPin::join`, so the three
laws proved of it are what make a kind variable's pin independent of constraint arrival order
(`src/ccl/ty.rs`).

**A rule whose answer depends on a value the fold is still accumulating cannot be applied
pairwise.** The domain rule is such a rule, because it reads the kind. `compact.rs` therefore
accumulates the alternatives at every positive join and applies the resolved kind's rule once, at
`coalesce_compact_go` (`undetermined_kinds_join_without_deciding_the_domain_rule` pins the
behaviour). Applying it pairwise instead makes bound arrival order decide accept-vs-reject, and is
what associativity would carry a side condition for.

**`absorbedBy` is not subtyping, and is strictly finer** — which is why the merge's induced order
carries a name of its own rather than an order symbol a reader would read as subtyping. A positive
merge accumulates a function slot's domain alternatives rather than deciding between them, so
`(Int ⇒ Int)` and `({Int | __elem} ⇒ Int)` merge to a slot carrying both. That is a different
`CompactTy` from either, while `coalesce` materializes it to the second — which is their subtyping
join. Two positions can materialize to the same type and absorb neither the other, which is why
leastness over types cannot be routed through this order.

### Absorption and distributivity hold of the types, not of `CompactTy`

There is one type lattice, and `merge true` computes its join while `merge false` computes its meet.
What is polarity-indexed is the denotation: one `CompactTy` value denotes two different types, since
a contribution set means the union of its contributions read positively and their intersection read
negatively. Write `⟦a⟧⁺` for the type a position denotes read positively and `⟦a⟧⁻` for the type the
same position denotes read negatively. So `CompactTy` is not a lattice carrier but one syntax
carrying two representations.

Writing `a ⊓ (a ⊔ b) = a` over `CompactTy` needs a single syntactic `a` in both a join argument
(read positively) and a meet argument (read negatively) — that is, it needs `⟦a⟧⁺ = ⟦a⟧⁻`. That
holds for a single contribution (`{Int}` is `Int` either way) and fails as soon as a set holds two,
which is the case the law is about. Equivalently: meeting a positive result with something needs the
*negative* representation of the type that result denotes, and converting between the two
representations is not a syntactic operation on compact types. It is where distributivity does its
work, and the polar normal form exists so the conversion is never needed.

### The lattice is a semantic statement

It needs a domain of types ordered by subtyping in which ⊔ and ⊓ both exist — the lattice algebraic
subtyping is built on, of which the polarized compact form is a normal form.

The gap is not that a join is missing or ambiguous. `merge pol` is total and is the unique least
upper bound of the order it induces, so a join always exists and is one thing; `CompactTy`'s union
*node* is the contribution set itself, and `atoms = {Int, Bool}` at a positive position **is** `Int
⊔ Bool`. What is missing is a `Type` that denotes it. `Type` carries the joins and meets the
compiler can lower — `Refinement` is a meet with a predicate, and `Variant` is a *tagged* join whose
values carry a tag and whose eliminator is `variant_project` — and no constructor for an untagged
"`Int` or `String`", whose values carry nothing to distinguish the sides. So `coalesce` is a partial
function out of `CompactTy`, and `IncompatibleBounds` / `DomainJoinConflict` fire exactly where a
unique join exists with no `Type` to name it. A lattice semantics is what turns that from an
implementation behaviour into a theorem, and what would let the Σ work say which join Σ represents —
Σ being a union node restricted to domains, added because that one join is worth representing.

`simplify_type`'s atomic absorption and co-occurrence merging are rewrites whose justification *is*
a lattice identity. That pass is observationally inert today — disabling it entirely leaves the
suite passing and fails only its own unit tests in `simplify_type.rs` — and its own docs say it
becomes load-bearing once let-polymorphism introduces genuine polar asymmetry. So it is not a live
hazard; it is the consumer that would make a lattice model pay.

### Why the model carries `CompactTy` at all

Two reasons, and neither is "so the algebra has a carrier".

The differential needs a mirror of `CompactType`; that much is definitional. The substantive reason
is that **order-independence is a statement about the representation, and no semantic statement
implies it.** The solver compares compact and materialized types *structurally* — the
trivial-equality short-circuit, cache keys, `SpecKey`, the recorded-versus-recomputed walls — so two
structurally distinct results denoting mutually-subtyping types are two different identities to it.
A lattice-level "joins are unique up to ≈" would not have caught the refinement-layer ordering
defect the type-merge fuzz found at roughly one generated set in ten thousand: subtyping was
indifferent there, because refinements compare as a set, while `Type`'s derived `PartialEq` was not.

What `CompactTy` cannot carry is any statement about what a merge *means* — hence the scope note on
uniqueness above.

## Materialization: the merge is a bound, and the least one

`CclFormal/Coalesce.lean` models `coalesce_compact_go` on the concrete fragment and proves it total.
A position **materializes** when `coalesce` gives it a type — one concept under two spellings, the
operation's name and the Rust's verb for what it does to a position (`materialize_record`,
`materialize_variant`). An outcome is one of three things: a `Ty`; refused (`CoalesceError`), where
the position has no type; or unresolved, where nothing concrete reached the position and the Rust
emits a fresh `Type::Infer`. `Ty` has no `Infer` node, so such a position is compared only as
"unresolved", refinements included.

**`CoalesceError` has no `emptyProduct`.** [chl-spec.md](../docs/chl-spec.md#66-the-empty-product-is-unit),
"6.6 The empty product is unit" makes unit a base type so a product cannot reach it by width. A
positive merge that intersects two records to nothing is therefore `IncompatibleBounds` on both
sides: bounds with no common shape is what that error already says, and the empty product is that
read one level down.

Two theorems bracket the merge — `merge_is_a_bound` (`CclFormal/MaterializedMergeIsABound.lean`) and
`merge_is_least_type` (`CclFormal/MaterializedMergeIsTheLeastBound.lean`) — and each file states its
own proof. What belongs here is what they rest on and what the sample measured.

**Two hypotheses beyond `concrete`, each forced and each pinned by its own counterexample in the
module.**

- **A kind variable is not a concrete position** (`kindResolved`). `KindMerge.unknown` materializes
  by the capability default and a merge that pins the slot to `data` overrides that default, so an
  `unknown` operand's own materialization is not what the merge combined: `(Int ⤇ Int)` joined with
  an unpinned `(Int ⇒ Int)` is `(Int ⤇ Int)`, above neither operand as materialized separately.
  Excluding it is not a restriction on the merge — `wellFormed` already excludes the other
  non-concrete kind, `.conflict`.
- **`DataAgree`**: at a negative position a `data` slot's two domains agree. `subtypeCheck` reads a
  data domain invariantly, as `constrain_go` does, so no `Ty` is below both `({a: Int} ⤇ Int)` and
  `({a: Int, b: Bool} ⤇ Int)` — a type below both would need one domain mutually-sub with two that
  are not mutually-sub. Demanding that the merge be a lower bound there demands the impossible, and
  the lossless answer is the Σ over both domains that the Σ roadmap item adds. So soundness is
  guarded by the existence of a bound (`MergeIsBoundGuarded`), and `DataAgree` holds exactly when a
  bound exists. It is a condition on the *pair*, not on which types a data domain may be — a data
  domain is refined whenever a filter narrows a collection.

**Leastness over types is not routed through the absorption order.** Reflecting `Subtyping` into
`absorbedBy` is false, on the function-domain shape recorded under `absorbedBy` above, and weakening
the reflection to hold only after materialization fails on more of the sample rather than fewer;
both were measured before being believed. The proof inducts on the materializations instead.

**The side the bound sits on is a parameter of that induction, independent of the polarity**
(`bounds`). `bounds_merge` proves one statement over both parameters: a type bounding both operands'
materializations on one side bounds the merge's materialization on that same side.

| | above both operands (`above = true`) | below both operands (`above = false`) |
|---|---|---|
| positive merge (`pol = true`) | above the merge — **leastness** of the join | below the merge |
| negative merge (`pol = false`) | above the merge | below the merge — **leastness** of the meet |

Leastness is the diagonal, where `above = pol`. The off-diagonal is what the function case consumes:
a domain flips the polarity and the subtyping edge together, and a `data` domain is invariant, so
closing that case needs the bound carried on the other side as well. One induction proves all four
cells, and leastness alone would not close the function case.

### The fn slot holds one domain

`CompactFun` holds **one** domain, merged contravariantly like any other position, plus a
`domains_disagree` flag and the operand pair a merge had to combine. A candidate set lives one level
up, on the witness a Σ binds. The model followed: the slot's `List CompactTy` became a `CompactTy`,
which retired `unionDomains`, `meetDomains`, `anyEquiv`, `subtypeDomains`, `domainsEquiv`,
`OneDistinct`, `meetAll` and their theorems — `OneDistinct` in particular, since "at most one
distinct domain" is now the slot's type rather than a predicate proved about it.

Three consequences, each measured:

- **`DataAgree` states the domain edge at both polarities.** A positive merge meets the domains
  too, so the evidence that two `data` domains disagreed is erased either way, and the hypothesis
  is needed at both. Unguarded, that is 8 failures on one surface and 4 on the other, in both
  orders.
- **`merge_is_a_bound` holds on 1844 of 2048 samples.** A `compute` slot carrying two domain
  alternatives, which would materialize by meeting them, cannot arise over one domain.
- **`merge_assoc`, `merge_is_least_absorber` and `least_absorber_unique` need no
  `Classical.choice`**: their proofs are `rw` plus a triple of componentwise facts.

**What the model does not state.** The Rust reaches `DomainJoinConflict` two ways: the merged domain
denoting several alternatives, which `funShapes` mirrors through `denotesSeveralDomains`; and the
`domains_disagree` flag, which `CompactFun::merge` sets from the *operands* because the meet erases
the evidence. There is no slot for the flag here, so a disagreement whose merged position is not
several atoms is a verdict this model does not give. The coalesce differential reports 0 mismatches
over 4000 bounds, so the sampler does not reach it; closing it means a fourth component on the fn
slot and a model of `data_domains_disagree`.

**A disagreement is caught loudly exactly when the domains' join is undefined, and silently whenever
it exists.** Two distinct atoms join to a two-atom position `coalesce` rejects, so nothing
materializes and the statement is vacuous; record keys intersect, variant tags unite, and refinement
sets intersect, and each of those materializes to a domain that is neither operand's. The boundary
is the domains' agreement, which is what `coalesce_monotone_fun` assumes.

No disagreement is reachable from the programs the suite compiles. Measured by counting
negative-position `Data`-slot domain merges from `CompactFun::merge`, over every CHL program the
integration corpus compiles: 473 such merges, and in every one the two domains are identical except
for their variable sets. Four programs written to force a disagreement each typecheck and reach 48
such merges, all agreeing — a parameter read raw and filtered, one parameter under two different
filters, a source read raw and filtered, and a filtered binding filtered again. The measurement is a
one-off instrumentation of that merge rather than a standing test, so it is a reading of today's
corpus and not a gate. The conjectured mechanism: a filter does not demand a refined domain of its
source, it produces a collection whose own domain is refined.

`MaterializedMergeIsABound.lean` also carries a **bounded sample**, small enough to evaluate and
wide enough to reach every arm of `merge`: 2888 `wellFormed` pairs, of which 2048 are kind-resolved.
Both guards below run over those 2048. Guarded soundness is clean on all of them; unguarded, 4
failures survive, all the `DataAgree` shape on two surfaces in both orders (record domains `{a:
Int}` against `{a: Int, b: Bool}`, and refinement slots `Int` against `{Int | __elem}`). Of the 2048
kind-resolved pairs, 1814 satisfy `merge_is_a_bound`'s hypotheses; the 234 that do not are a merge
that left the input shape — a `compute` slot carrying two domain alternatives, which materializes by
meeting them — or a data domain the merge moved.

The sample's leastness line is no longer measured. Every candidate bound in the pool is a
`wellFormed` position's materialization, `coalesce_wellFormed` makes that a well-formed type, and
`merge_is_least_type` then applies to it — so `leastness_failures_eq_nil` proves what a `#guard`
used to evaluate, and `merge_is_least_at_of_concrete` proves it for every concrete pair rather than
the sample's 2048. The pool is drawn from the `wellFormed` members of the sample, since a
duplicate-keyed position materializes to a type `Ty.WellFormed` excludes and no such type is a
candidate bound.

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
  is therefore not checked by that comparison.
- The subtype generator excludes duplicate record/variant keys, which violate
  `Ty.WellFormed`. The model's find-first field rules and Rust's equality shortcut must not be
  assumed equivalent for duplicate-keyed inputs.
- The predicate wire carries element/free/Pi references, literals, operations, projections,
  application, predicate-local lambdas and cast-domain refinements. Expression nodes without a
  corresponding predicate constructor, such as let-bindings and aggregates, are outside it.

Subtype, polar-merge and coalesce drivers panic when a generated case unexpectedly falls outside
their wire schema. Refusal generation skips an unencodable pair; kind merging omits an
unencodable step but continues folding. Those exclusions are not successful comparisons.
The drivers check the number of returned verdicts as well as their agreement.

The documentation-reference checker scans Markdown and Rust, not Lean comments. Markdown
citations in Lean therefore require manual review when a heading changes. The Lake configuration
does not promote every warning to an error; proof elaboration, executable assertions and the
named axiom checks are separate from warning cleanliness.

## Roadmap

### The typing oracle

Have the Rust dump the typed AST for generated small programs, and check admissibility of the root
typing in Lean. This is the step at which the model would start catching inference bugs rather than
comparison bugs, and it is what the term calculus above exists for.

### The solver model

Model `constrain` and coalesce as a state monad over a store of variables with bound lists,
fuel-based at first. Two theorems would follow:

- **Soundness**: every bound the solver records is derivable in the declarative `<:`, and the
  coalesced output type is admissible for the term, which would connect back to the term calculus.
- **Termination**: replace fuel with a well-founded measure. This is the priority of the two, since
  it is the property with live field bugs — a hanging build in this repo is, as a working rule,
  solver non-termination. The measure would have to account for the seen-cache and for `extrude`
  minting fresh variables, and articulating it will either yield a proof or expose that termination
  rests on something unstated.

Levels and extrusion would enter the model at this step, and scope-escape soundness is the natural
third theorem, subordinate to the two above.

### Σ types and `FunKind` inference

What a witness ranges over is modelled: `TypeKind`, its containment order and its lattice, the
`refuses` test, and `CompactTypeKind`'s merge, each with a differential. `SigmaBelow` states the
kind premise and proves it is the elementwise reading of what a Σ denotes.

The Σ is not. `Ty` carries no witness and `CompactTy`'s function slot no binders, so a Σ is a rule
over a candidate list rather than a type, and no sum crosses the wire. The binder correspondence
`𝜌` is where that costs the most: it is the premise a var-to-sum edge was found missing, its
absence raises no error because the domain premise runs either way, and an assert in
`constrain_subtype`'s Fun/Fun arm plus the Rust tests are the whole of what stands behind it
([type-inference.md, "What checks each
premise"](../src/ccl/design/type-inference.md#what-checks-each-premise)). A binder slot on
`CompactTy` is what would put the Σ rule behind the merge differential, and it is the cheaper half
of this step.

The rest is the witness discipline — **one value = one witness**, arms α-converted onto the value's
witness (adopt if unanimous, mint on disagreement, sticky), with the join deferred to compaction —
and kind variables resolved at coalesce ([type-inference.md, "4.6 Data vs compute
functions"](../src/ccl/design/type-inference.md#46-data-vs-compute-functions)). The discipline was
established only after a constraint-time-join defect was root-caused at some expense, which is the
reason to freeze it as a theorem before the next refactor disturbs it. Modelling the kind variables
would also supply the bound `DataAgree` currently excludes, and would let the lattice statement
above say which join Σ represents. **If Σ comes to materialize multi-domain joins, the merge's
"alternatives beyond one" adjudication has to be revisited.**

### Histories: the mutability semantic model

This step is independent of the solver model and can start any time after the term calculus. It
would be a semantics model rather than a typing model: the transient variants (`History`, `ChanDom`,
`Hole`, `Infer`) are pipeline artifacts and stay **out** of the typing calculus.

Model histories as functions `𝐷 ⇒ 𝑉` per [mutability.md, "The model: histories and causal
recursion"](../src/ccl/design/mutability.md#the-model-histories-and-causal-recursion): `Overwrite`
is last-write-wins with carry-forward at off-path positions; `Append` is the append law, with no
carry-forward; and `Txn` reads are arbitrary as-of reads, with no terminal/"final value" read,
matching [mutability.md, "Semantics"](../src/ccl/design/mutability.md#semantics). The headline
theorem would be that the `letrec`/`transact` realization emitted by `mut_elim` / `plan_loops`
denotes the same function as a direct imperative semantics of the surface program.
