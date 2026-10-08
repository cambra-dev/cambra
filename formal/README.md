# formal/ — the Lean model of the CCL type system

This directory contains a Lean 4 model, proofs about that model, and an executable oracle used
by Rust differential tests. [The design reference](design.md#what-is-pinned-today-and-what-is-not)
owns the coverage table and theorem qualifications. This README owns build, test and replay
instructions.

## What is stated, and what is proved

The model covers selected concrete types and operations, not the complete inference engine.
It neither infers program types nor checks Rust's inferred term typings yet. The latter is a
[planned oracle](design.md#the-typing-oracle).
[The concrete type grammar](design.md#the-concrete-type-grammar) lists exclusions, including
dependent sums as grammar nodes; `SigmaBelow` instead states a separate rule for their kind premise.

The proof families have distinct scopes:

- Subtyping, term safety, compact merging and materialization are summarized in
  [the coverage table](design.md#what-is-pinned-today-and-what-is-not).
- [`TypeKind.lean`](CclFormal/TypeKind.lean) defines membership, containment and refusal.
  Containment transports membership; refusal implies non-membership.
- [`TypeKindIsALattice.lean`](CclFormal/TypeKindIsALattice.lean) states kind bounds by cases.
  Cases that require a bound in the underlying type order assume that bound exists. Associativity
  follows from the corresponding leastness/greatestness premises, not from an unconditional
  executable lattice operation.
- [`TypeKindMerge.lean`](CclFormal/TypeKindMerge.lean) proves laws up to `equivTypeKind`.
  Join associativity is proved; meet associativity is exhaustively checked only over its finite
  `checkTys` universe. A `subtypesOf` parameter must denote one shape; parameters with no shape or
  conflicting shapes contribute no candidates to a meet. The file also states the range-test and
  atom-membership invariance lemmas on which those cases depend.

[The axiom gate](CclFormal/Axioms.lean) checks named headline results for unexpected axioms.
A successful proof build validates those Lean declarations, not their correspondence to every
Rust execution. Differential tests separately sample that correspondence.

## Record-width subtyping in the model and implementation

Record-width subtyping connects four definitions:

1. Rust's `constrain_go` checks every field demanded by the right-hand record against the
   matching left-hand field.
2. The `record` constructor in [`Subtyping.lean`](CclFormal/Subtyping.lean) states that relation
   using find-first field lookup.
3. [`SubtypeChecker.lean`](CclFormal/SubtypeChecker.lean) computes a verdict.
   [`SubtypeCheckDecidesSubtyping.lean`](CclFormal/SubtypeCheckDecidesSubtyping.lean) proves its
   equivalence to the relation.
4. [The Rust harness](../tests/differential_oracle.rs) sends the encoded pair to the oracle and
   compares that verdict with `constrain_subtype`.

Thus a record with `a: Int` and `b: Bool` is below a record requiring only `a: Int`, but not
conversely. Unique field keys are part of the modeled well-formed fragment; duplicate-key behavior
is not generalized from this example.

## The differential oracles

[`Main.lean`](Main.lean) reads one JSON object per line and returns one verdict line.
[`CclFormal/Json.lean`](CclFormal/Json.lean) defines the wire codec.

| Operation tag | Compared operation | Oracle response |
| --- | --- | --- |
| `sub` | `constrain_subtype` versus `subtypeCheck` | `true` or `false` |
| `merge` | `CompactType::merge` versus `CompactTy.merge` | `ok` or a mismatch with the model result |
| `mergeKind` | `CompactTypeKind::merge` versus `mergeTypeKind` | `ok` or a mismatch with the model result |
| `refuses` | `TypeKind::refuses` versus `refuses` | `ok` or a mismatch with the model verdict |
| `coalesce` | Materialization versus `CompactTy.coalesce` | `ok` or a mismatch with the model outcome |

Merge comparisons use `equiv` or `equivTypeKind` rather than bytewise JSON equality.
Coalescing compares successful types, unresolved results and error kinds. The kind-merge oracle
is separate because the compact-type wire has no Σ binder slot.

Coverage is limited by both the generators and encoders.
[The design reference](design.md#the-differential-oracles) owns these exclusions. In particular,
encoding failure is not uniformly fatal: subtype, polar-merge and coalesce drivers panic on
unexpected unencodable generated cases, while refusal generation skips unencodable pairs.
Kind merging continues its fold but omits any step that cannot be encoded. A passing run does
not validate those omitted cases.

## Running it

From the repository root:

```bash
(cd formal && lake build)
./ci.sh formal
```

[`lean-toolchain`](lean-toolchain) pins the Lean version. Lake's default targets build the
`CclFormal` library and `subverdict` executable according to [`lakefile.toml`](lakefile.toml).
The library imports its proofs and axiom checks through [`CclFormal.lean`](CclFormal.lean).
Building checks those declarations and evaluates their `#guard` assertions.

`./ci.sh formal` builds the model and then names the Rust integration target explicitly:

```bash
cargo test --test differential_oracle -- --nocapture
CAMBRA_DIFF_N=20000 CAMBRA_DIFF_SEED=7 cargo test --test differential_oracle -- --nocapture
```

`Cargo.toml` sets `test = false` for this target, so a plain `cargo test` does not run it.
The harness expects `formal/.lake/build/bin/subverdict`. Without that binary, the five
differentials print skips locally and fail if the `CI` environment variable exists.
The shell gate separately skips a missing `lake` locally and fails when `CI` is nonempty.
Running the Rust target directly does not rebuild a stale oracle; use the full gate after edits.

`CAMBRA_DIFF_SEED` overrides each driver's default seed; `CAMBRA_DIFF_N` defaults to 4,000.
The count applies to accepted cases or fold steps, not raw generator attempts. A complete merge
fold can take its step count past the requested threshold. Refusal tests also require both
refused and non-refused samples, so very small counts are not useful smoke tests.

### Reading a mismatch

The failure message includes the operation's JSON case and the differing answers. Replay the JSON
object, not the entire diagnostic line, through `formal/.lake/build/bin/subverdict`.
For example, this subtype query asks whether `Int` is below `Bool`:

```bash
echo '{"op":"sub","lhs":{"k":"base","base":"Int"},"rhs":{"k":"base","base":"Bool"}}' \
  | formal/.lake/build/bin/subverdict
```

`CAMBRA_DIFF_DUMP=<path>` appends the subtype driver's generated JSONL cases only.
Open/write failures are ignored by that dump path; verify that the file was written.
Keep the failing seed and source revision for replay. Unknown operation tags and malformed JSON
produce error verdicts rather than a subtype answer.

## Reading order

Start with [the coverage table](design.md#what-is-pinned-today-and-what-is-not), then select the
definition/proof family relevant to the operation being changed.

| Files under `CclFormal/` | Purpose |
| --- | --- |
| `Ty.lean` | Type/predicate grammar, equality and well-formedness. |
| `Subtyping.lean`, `SubtypingIsReflexive.lean` | Relation and reflexivity for well-formed types. |
| `SubtypeChecker.lean`, `SubtypeCheckDecidesSubtyping.lean` | Executable checker and its equivalence to the relation. |
| `SubtypingIsTransitive.lean` | Transitivity assuming well-formed input types. |
| `Term.lean`, `WellTypedTermsAreSafe.lean` | Pure-core typing, evaluation and safety. |
| `Merge.lean` | Compact representation, polar merge, absorption order and algebraic laws. |
| `Coalesce.lean` | Total computation of a type, unresolved outcome or error. |
| `MaterializedMergeIsABound.lean`, `MaterializedMergeIsTheLeastBound.lean` | Materialized bound and leastness statements with their hypotheses. |
| `TypeKind.lean`, `TypeKindIsALattice.lean`, `TypeKindMerge.lean` | Kind membership, bounds and compact-kind merging. |
| `SigmaIsTheElementwiseReading.lean` | The kind-premise direction for the separate Σ rule. |
| `Json.lean`, `Axioms.lean` | Codec and named-result axiom checks. |

Term safety and compact materialization are separate developments over the same type grammar.
For merging, read refinement-slot and `joinKind` laws before the merge laws; then read coalescing
and the materialized-bound proofs. Local lookup, peeling and well-formedness lemmas stay beside
their definitions rather than in a separate utility module.
