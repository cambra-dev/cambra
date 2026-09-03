# The Lean model of the CCL type system

`formal/` is a Lean 4 model of the CCL type system whose purpose is **catching real bugs** in the
Rust implementation. Confidence in the metatheory and bug-catching are the same goal here: every
layer of the model has an executable form and a differential oracle against the Rust. Proofs pin
down the model; the oracle pins the model to reality.

The implementation being modeled is the algebraic-subtyping engine of
[type-inference.md](../src/ccl/design/type-inference.md#1-algorithm-overview); the semantic model
the last roadmap item targets is
[mutability.md](../src/ccl/design/mutability.md#the-model-histories-and-causal-recursion).

## The oracle stance: the model checks, it does not reproduce

Monomorphization, simplification, and coalesce ordering make the Rust's inferred types
non-canonical, so demanding that a Lean model reproduce inference output bit-for-bit would drown the
project in incidental divergence. Instead:

- **Lean infers nothing; Lean checks.** The differential property is *admissibility*: whatever type
  the Rust inferred for a term, the Lean declarative system accepts that term at that type. That is
  the soundness direction, it is robust to the solver choosing any of several valid types, and a
  failure is either a solver bug or a spec gap.
- Exact agreement is demanded of the three operations that **are** functions of their inputs: the
  subtype relation, the polar merge, and materialization. None is order- or route-sensitive, so none
  needs the admissibility stance.

## What is pinned today, and what is not

Read a claim about "the model" against this table rather than against the roadmap, which describes
intent. Until a row says otherwise, a component's only coverage is ordinary Rust tests.

| Solver component | Model | Differential | Proofs |
|---|---|---|---|
| `constrain_subtype`, concrete pairs | `Subtyping` / `subtypeCheck` | yes | reflexivity, transitivity, decidability |
| `CompactType::merge` | `merge` | yes, every fold step | commutativity, idempotence, associativity, congruence, lub, uniqueness |
| `TypeKind::refuses` | `refuses` | yes, on the concrete fragment | a refusal never lands on a member (`not_admits_of_refuses`); the pair the bound arm's equality test refused while admitting it |
| `CompactTypeKind::merge` | `mergeTypeKind` | yes, every fold step | commutativity, idempotence, associativity at the join; the meet checked exhaustively over a bounded universe |
| `coalesce_compact` (`CompactType` → `Type`) | `coalesce` | yes, per materialized bound | totality; well-formedness of the result (`coalesce_wellFormed`); the merge materializes to a bound of both operands (`merge_is_a_bound`) and to the least such type (`merge_is_least_type`) |
| bound recording, sweeping, `extrude` | — | — | — |
| `traits` (operator obligations) | — | — | — |
| `compact_go` (bounds → `CompactType`) | its *output shape* is `CompactTy` | supplies operands; never itself checked | — |
| `simplify_type` | — | — | — |
| `scheme` (freshening, generalization) | — | — | — |
| term typing as the solver infers it | `Term` / `WellTypedTermsAreSafe`, a small calculus | — (the admissibility oracle is a roadmap item) | progress, preservation, refinement soundness |

One consequence: `compact_go` is unmodeled, and the merge and coalesce differentials both *use* it
to build their operands — so a `compact_go` defect is reproduced identically on both sides of those
comparisons rather than caught by them.

Every theorem cited here is **sorry-free**: no step is admitted rather than proved.
`CclFormal/Axioms.lean` states that as a gate rather than a claim — one `#print axioms` line per
headline result, each paired with the list it must report. That list is `propext`,
`Classical.choice`, and `Quot.sound`, which are Lean's own classical axioms; a fourth name would be
an assumption this development had added. `lake build` fails on a mismatch, and an admitted step is
one of those names (`sorryAx`), so it fails the same way.

The contract that keeps the table true: **a semantic change to `constrain` or coalesce either updates
`formal/` in the same change or documents the divergence in the PR.** The differential is what
detects a breach.

## The concrete type grammar

A type is **concrete** when no inference-time unknown occurs anywhere in it (`ccl::ty::Type`'s own
doc defines the term and tabulates the variants). `Ty` (`CclFormal/Ty.lean`) mirrors that fragment —
every variant a fully-inferred type can contain. `Hole`, `SharedHole`, `BoundedHole`, `Infer`,
`History`, `ChanDom`, and `FunKind::Var` are excluded: each is an inference-time transient or
unknown, outside the fragment by the same criterion that keeps it out of a checked program's types.
`Ty.variant` also carries no `Openness`, so a closed arm set is the only one the model represents.
`FunKind` is in the grammar as a static two-point flag (`⇒` vs `⤇`); kind inference is a roadmap
item, but `⇒`/`⤇` distinctness affects type equality and subtyping now.

**Concrete types are closed**, and that is the fragment property the rest of the model rests on: a
refinement's reference to its own function is a de Bruijn index (`Predicate.piBound`, mirroring
`Name::PiBound`) while free references stay uniquified names, so the relation carries no rename
environments and two α-variant function types are the same term. The design of record, and the
placements measured against it, are in
[type-inference.md](../src/ccl/design/type-inference.md#a-binder-reference-is-stored-in-one-of-two-forms),
"A binder reference is stored in one of two forms". Mid-solve, name-spelled forms still exist; the
concrete fragment is the closed one.

`Ty.lean` states the rest where it defines it: `Ty.WellFormed`'s invariants, why the refinement set
is a list whose order is proved unobservable, and the `Predicate` vocabulary — including the two
type-blind exceptions `eq_refinement_predicate` makes, α-invariance and a `Cast`'s target, which the
wire encoder discharges rather than Lean (`pred_json`, `tests/differential_oracle.rs`).

## The declarative subtype relation

`Subtyping` (`CclFormal/Subtyping.lean`) is one constructor per `constrain_go` arm — the relation the
Rust implements without ever writing down — and `subtypeCheck` (`CclFormal/SubtypeChecker.lean`) is
the executable checker that decides it, with termination proved. Each adjudicated rule is a
constructor carrying its decision in its own docstring, with a matching `#guard` in
`SubtypeChecker.lean`; the three deliberate departures from `constrain_go` are recorded in
`Subtyping.lean`'s module doc.

**Transitivity is unconditional because concrete types are closed** (`subtyping_trans`, over
well-formed types, quantifying over nothing but the three types). Chaining dependent codomains under
a name-spelled representation produces premises viewing the middle type under different renames,
composing only through a reconciliation morphism — the model analogue of `constrain.rs ::
bridge_holder_gap`. Closing into indices does not dissolve that obstruction; it never forms it. The
fragment restrictions and environment side conditions a named representation forces are the cost of
names, not of transitivity.

## Terms, typing, and safety

`CclFormal/Term.lean` holds the pure-core calculus — terms, values, capture-free substitution,
partial predicate evaluation, the call-by-value `Step`, the filter-blocked judgment, and the
declarative `HasTy` with subsumption via `Subtyping` — and `WellTypedTermsAreSafe.lean` proves
progress, preservation, and refinement soundness over it. Both files record their own adjudications.
The one that reaches outside them is the **fragment**: predicates over `__elem` only
(`Predicate.elemOnly`), enforced in the judgment rather than at the theorem boundary, which is what
keeps types closed under term substitution.

Open: `compose`, records, wildcard `case` arms, and the dependent-fragment extension, which waits on
the discharge machinery. The wildcard extension carries a calibration target — the Rust's `case _:`
payload-binder defect lives in wildcard arms, which `Term.caseE` does not yet have, so the naive
wildcard statement is refuted by a known bug and `case_binder_sound` is the tag-arm statement in the
meantime.

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

`lake build` produces `.lake/build/bin/subverdict`, and `tests/differential_oracle.rs` generates
cases with the seeded generator it shares with the type-merge fuzz (`tests/type_gen/mod.rs`),
computes the solver's answer, and diffs it. [README.md](README.md#the-differential-oracles) lists
the three operations and [README.md](README.md#running-it) how to run one case by hand; the harness's
module doc carries the generator's shape. The harness is an integration test rather than a
`#[cfg(test)]` module in the library: it is a test, and the only solver internal it cannot otherwise
reach is `CompactType::merge`, which the `test-helpers` feature opens a door to (`merge_bounds`).

**Not checked, each for a stated reason rather than by omission.** The model's abstractions are
applied by the *encoder*, so no comparison is made against a slot the model does not model.

- **Inference variables** (`vars`) and **history slots** have no field. A generated concrete `Type`
  produces neither, so the history slots' same-polarity componentwise merge is uncovered outright.
- **The Pi binder**'s first-wins selection (`a.name.or(b.name)`) is dropped, as is a **conflicted
  slot's domain payload** and **`Openness`** (every generated arm set is closed, so `meet_openness`
  is only ever exercised at `Closed`/`Closed`).
- **`ChanDom` atoms** are outside the model's `Atom`, matching `Ty`'s exclusion of the pipeline
  transients.
- **Duplicate record and variant keys** — outside `Ty.WellFormed`, and the one place the Rust's
  trivial-equality short-circuit and its find-first arms disagree. Harness sensitivity is tested
  rather than assumed: fed through the pipe by hand, the duplicate-keyed reflexivity case flags as a
  mismatch, and `dup_key_record_trips_the_uniquely_keyed_invariant` pins that the debug assert
  fires.
- **Open variant arm sets**, which `Ty` has no node for.
- **A refinement predicate node outside the modeled vocabulary.** Every `Predicate` constructor is
  exercised: `gen_pred` emits each one and `pred_json` encodes it, `lam`, `boundVar`, and `cast`
  included, so both of `eq_refinement_predicate`'s type-blind exceptions reach the comparison. What
  no case reaches is a `TypedExpr` node the vocabulary has no constructor for — a predicate built
  from a `Let` or an aggregate. `pred_json` answers `None` there and the harness panics, so this gap
  is in the generator and is loud rather than silent.

**Two gaps in the gate itself.** `./ci.sh doc_refs` scans `.rs` and `.md` only, so the eight `.md`
citations in `CclFormal/*.lean` are outside it and a renamed heading does not fail CI; extending the
checker to Lean comments is the fix. And `lake build` reports eight `unusedVariables` warnings, all
on the `match h : e with` form where the hypothesis is used in some branches and not others, so until
they are gone the Lean half cannot be gated the way the Rust half is (`-D warnings` in four
configurations).

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

Model kind variables resolved at coalesce ([type-inference.md, "4.6 Data vs compute
functions"](../src/ccl/design/type-inference.md#46-data-vs-compute-functions)), Σ formation over
candidate domains, and the witness discipline — **one value = one witness**, arms α-converted onto
the value's witness (adopt if unanimous, mint on disagreement, sticky), with the join deferred to
compaction. That invariant was established only after a constraint-time-join defect was root-caused
at some expense, which is the reason to freeze it as a theorem before the next refactor disturbs it.

Σ would also supply the bound `DataAgree` currently excludes, and would let the lattice statement
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
