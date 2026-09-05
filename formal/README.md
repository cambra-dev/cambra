# formal/ — the Lean model of the CCL type system

The subtype relation, the solver's polar merge, and its materialization exist only operationally in
the Rust: `constrain_go`, `CompactType::merge`, and `coalesce_compact_go` implement them without
ever writing them down. This is a Lean 4 model that **states** them declaratively, proves their
metatheory, and is diffed against the Rust operation-by-operation so the two cannot drift apart
silently.

Two things hold it honest, and they check different failures. **Proofs** say the model has the
properties claimed of it. A **differential oracle** says the model is a model *of this code* —
without it, both halves stay internally consistent while describing different systems.

## What is stated, and what is proved

| Subject | Model | Headline results |
|---|---|---|
| Subtyping (`constrain_go`) | `Subtyping`, `subtypeCheck` | reflexivity; decidability; transitivity |
| The polar merge (`CompactType::merge`) | `CompactTy`, `merge` | commutativity; idempotence; congruence; associativity; the merge is the unique least upper bound of the order it induces |
| Materialization (`coalesce_compact`) | `coalesce` | totality; the result is well-formed; the merge materializes to a bound of both operands where one exists, and to the least such type |
| Terms and typing (a small pure core) | `Term`, `HasTy`, `Step` | progress (a well-typed term is a value, steps, or is filter-blocked), preservation (a step keeps the term's type), refinement soundness |
| What a Σ's witness ranges over (`TypeKind`) | `TypeKind`, `Admits`, `ContainedIn`, `refuses` | containment transports membership; reflexivity; transitivity; and a **refusal is sound** — what `TypeKind::refuses` rejects is never a member, which is what every caller raising `NotOfKind` rests on, with the pair the bound arm's old equality test refused while admitting it |
| Type kinds are a **lattice** | `IsKindLub`, `IsKindGlb` | every pair has a least upper and greatest lower bound, named row by row and proved in **both** directions — wherever the type order the kinds are built on has the bound they need, and unconditionally elsewhere; both bounds are associative from leastness alone (`kind_glb_assoc`, `kind_lub_assoc`), which is what made the compact merge's loss of it a fact about that merge rather than about the order |
| The kind premise (`constrain_type_kinds`) | `SigmaBelow` | the premise **is** the elementwise reading of what a Σ denotes, which is what fixes its direction; the swapped premise is a different relation |
| A binder's range when contributions meet (`CompactTypeKind::merge`) | `CompactTypeKind`, `mergeTypeKind` | `equivTypeKind` is an equivalence; the merge is commutative, idempotent and **associative** — the join proved, the meet checked over every triple of the kinds built from six positions, since a proof would need the two polar orders to relate and `Merge.lean` proves one polarity at a time; a `subtypesOf` parameter must name exactly one shape, and both failures answer the empty candidate list, so the meet is a lower bound as well; the range test is invariant under `equiv`, and a union names only ranges exactly when both sides do; mutual containment is equality of the atom *sets*, so a predicate over them is invariant by construction |

A type is **concrete** when no inference-time unknown occurs anywhere in it — what a checked program
exhibits, and the fragment everything above is stated over. The model has no node for any of the
unknowns; [design.md](design.md#the-concrete-type-grammar) lists which `ccl::ty::Type` variants
those are.

Three things the model does not do: infer a type — it checks one it is given — reproduce the
solver's choice where several types are valid, or say anything about those transients.

A Σ is stated as a **rule** rather than as a grammar node: `SigmaBelow` relates a candidate
list and an element type to a kind and an element type, and `Ty` carries no witness. Putting
one in the grammar makes `Ty` and `TypeKind` mutually inductive — a kind names types and a
type contains Σs — which the Rust hides behind an `Rc` and Lean would need a hand-written
mutual `BEq` for. What the rule form already settles is the premise's direction; what it
leaves open is any statement about a Σ *inside* a larger type.

## One rule, end to end

Record width, in the four forms it takes. `constrain_go`'s record arm
(`src/ccl/infer/solver/constrain.rs`), with the error payload elided:

```rust
(Type::Record(a), Type::Record(b)) => {
    for (name, t1) in b {
        match a.iter().find(|(n, _)| n == name) {
            Some((_, t0)) => constrain_go(t0, t1, sl, sr, cache)?,
            None => return Err(ConstrainError::MissingField { .. }),
        }
    }
    Ok(())
}
```

The Lean constructor it is stated as (`CclFormal/Subtyping.lean`), one per arm:

```lean
/-- Named width: every field the rhs demands is present (find-first) in
the lhs and covariantly below it. -/
| record {a b} :
    (∀ n t1, (n, t1) ∈ b → (lookupBy a n).isSome) →
    (∀ n t0 t1, (n, t1) ∈ b → lookupBy a n = some t0 → Subtyping t0 t1) →
    Subtyping (.record a) (.record b)
```

The executable checker `subtypeCheck` (`CclFormal/SubtypeChecker.lean`) decides exactly that
relation — `subtyping_of_subtypeCheck` and `subtypeCheck_of_subtyping` are the two directions — so a
`#guard` against the checker is a fact about the relation. A `#guard` is a compile-time assertion
that a decidable proposition evaluates to `true`; `lake build` fails when one does not, which is why
building the model is what checks it.

One generated case as it crosses the wire, and the verdict the oracle answers:

```
{"op":"sub","lhs":{"k":"record","fields":[["a",{"k":"base","base":"Int"}],
                                          ["b",{"k":"base","base":"Bool"}]]},
            "rhs":{"k":"record","fields":[["a",{"k":"base","base":"Int"}]]}}
→ true      # {a: Int, b: Bool} <: {a: Int}: dropping a field is width subsumption
→ false     # the same pair reversed: the rhs demands `b` and the lhs has none
```

`tests/differential_oracle.rs` computes `constrain_subtype`'s verdict on the same pair and fails the
test when the two disagree.

## The differential oracles

`lake build` produces `.lake/build/bin/subverdict`, which reads one JSONL case per line tagged by
`"op"` and answers one verdict per line (`Main.lean` documents each case shape).
`tests/differential_oracle.rs` generates the cases, computes the solver's answer, and diffs:

- `"sub"` — type pairs, `constrain_subtype`'s verdict against `subtypeCheck`.
- `"merge"` — every step of a fold over one variable's bounds through `CompactType::merge`, against
  `merge`, up to the model's `equiv` (the equality every merge theorem is stated over).
- `"mergeKind"` — every step of a fold through `CompactTypeKind::merge`, against `mergeTypeKind`,
  up to `equivTypeKind`. The `"merge"` oracle cannot reach this: `CompactTy` has no Σ binder slot,
  so the wire encoder refuses a bound carrying binders and every case that would exercise a kind
  is filtered out before it. Verified sensitive by reverting each of the two readings a bound
  naming no shape gets — one answers 68 mismatches, the other trips `is_below`'s own assertion.
- `"refuses"` — `TypeKind::refuses` against `refuses`, on the concrete fragment. `Ty` carries no
  `Infer` and no `Hole`, so what the wire expresses of `Type::holds_an_unresolved_position` is
  its refinement disjunct — the one that decides real cases, a refined range being what the
  range test exists to refuse. Verified sensitive on all three deciding arms: restoring the
  bound's equality test gives 415 mismatches of 4000, dropping the candidate list's abstention
  448, and peeling refinements before the range test 15.
- `"coalesce"` — each folded bound materialized, against `coalesce`.

Each oracle found a real defect on its first sweep. The subtype oracle caught a capture in the
solver's Fun/Fun opening; the merge oracle caught the model intersecting away refinements a hole
should have passed through; the coalesce oracle caught the model materializing a record's payloads
before checking its key kinds.

[design.md](design.md#the-differential-oracles) carries what each oracle covers and what it does
not.

## Running it

```bash
(cd formal && lake build)   # elaborates every theorem, evaluates every #guard, builds the oracle
./ci.sh formal              # the gate: lake build, then the differential suite
```

Elaborating is Lean's word for checking: `lake build` replays every proof, so a broken proof and a
broken `#guard` both surface as a build failure.

The toolchain is pinned by `lean-toolchain`; `elan` fetches it on first build. The Rust harness is
an integration test that **skips loudly** when the oracle binary is absent, so a machine with no
Lean toolchain stays green — `./ci.sh formal` is what turns that skip back into a gate, and it fails
rather than skips under CI.

```bash
cargo test --test differential_oracle                      # the three oracles
CAMBRA_DIFF_N=20000 CAMBRA_DIFF_SEED=7 \
  cargo test --test differential_oracle -- --nocapture     # a longer run, replayable from its seed
```

`CAMBRA_DIFF_SEED` and `CAMBRA_DIFF_N` set the seed and case count for every oracle in the binary;
`CAMBRA_DIFF_DUMP=<path>` appends the subtype oracle's cases to a file.

### Reading a mismatch

A failure prints the case and both answers: the merge and coalesce oracles carry the model's own
result in the verdict line, so the diff is in the message rather than in a second run. To re-ask the
model about one case, pipe that line back in:

```bash
echo '{"op":"sub","lhs":{"k":"base","base":"Int"},"rhs":{"k":"base","base":"Bool"}}' \
  | formal/.lake/build/bin/subverdict          # => false
```

`CAMBRA_DIFF_DUMP` plus the failing seed is how to get the line; a case the encoder cannot express
panics rather than being skipped, so a harness gap fails loudly too.

## Reading order

`design.md` is the plan of record: the coverage table (what is pinned today and what is not), the
adjudicated rules, and the roadmap. Then the model itself, where **a file that defines a construct
is named for it and a file that proves something is named for the sentence it proves**:

| File | Contents |
|---|---|
| `Ty.lean` | the concrete grammar, `Ty.WellFormed`, and the refinement-predicate vocabulary |
| `Subtyping.lean` | the relation, one constructor per `constrain_go` arm |
| `SubtypingIsReflexive.lean` | a leaf off the relation, under `Ty.WellFormed` |
| `SubtypeChecker.lean` | `subtypeCheck`, and the adjudicated rules as `#guard`s |
| `SubtypeCheckDecidesSubtyping.lean` | soundness, completeness, and the `Decidable` instance |
| `SubtypingIsTransitive.lean` | transitivity, with no fragment restriction and no side conditions |
| `Term.lean` | the term calculus: terms, values, substitution, stepping, typing |
| `WellTypedTermsAreSafe.lean` | progress, preservation, refinement soundness |
| `Merge.lean` | `CompactTy`, the polar merge, `absorbedBy`, and the algebra laws |
| `Coalesce.lean` | `coalesce`, which materializes a position into a type, and its totality |
| `MaterializedMergeIsABound.lean` | `coalesce` carries `absorbedBy` into subtyping, so the merge lands above both operands at a positive position and below both at a negative one |
| `MaterializedMergeIsTheLeastBound.lean` | and it lands below every well-formed type that bounds both |
| `Json.lean` | the wire codec shared with the Rust harness |
| `Axioms.lean` | the axiom gate |

Two chains run over the same grammar and are independent of each other: `Term.lean` →
`WellTypedTermsAreSafe.lean`, and `Merge.lean` → `Coalesce.lean` → the two bound files. The second
rejoins the subtyping metatheory, since a bound is stated with `subtypeCheck` and leastness is
proved with transitivity. Within `Merge.lean`, read the refinement-slot laws and `joinKind` before
the `merge` theorems that use them; the order and uniqueness section is last and depends only on the
semilattice laws. In each bound file, read the four case lemmas — `coalesce_monotone_*` and
`bounds_*` — before the assembly that uses them.

A lemma lives with the definition it is about: `Ty.WellFormed`'s member extractors are in `Ty.lean`,
and the `peel` / `lookupBy` / `kindOk` / `deficit` facts are in `Subtyping.lean` beside those
definitions. `Merge.lean` follows the same rule at a larger scale, each operation followed by its
laws.
