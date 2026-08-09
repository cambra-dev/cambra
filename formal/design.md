# Formalizing the CCL type system in Lean

This document is the plan of record for `formal/`: a Lean 4 model of the CCL type system, grown milestone by milestone, whose purpose is **catching real bugs** in the Rust implementation. Confidence in the metatheory and bug-catching are treated as the same goal: every layer of the model gets an executable form and a differential oracle against the Rust from day one. Proofs pin down the model; the oracle pins the model to reality.

The implementation being modeled is the algebraic-subtyping engine described in [type-inference.md](../src/ccl/design/type-inference.md#1-algorithm-overview); the semantic model targeted by the final milestone is described in [mutability.md](../src/ccl/design/mutability.md#the-model-histories-and-causal-recursion).

## The oracle stance: the model checks, it does not reproduce

The central architectural decision. Monomorphization, simplification, and coalesce ordering make the Rust's inferred types non-canonical — demanding that a Lean model reproduce inference output bit-for-bit would drown the project in incidental divergence. Instead:

- **Lean infers nothing; Lean checks.** The differential property is *admissibility*: whatever type the Rust inferred for a term, the Lean declarative system accepts that term at that type. This is exactly the soundness direction, it is robust to the solver choosing any of several valid types, and a failure is almost always a real finding — either a solver bug or a spec gap, both of which are the point.
- The one place exact agreement is demanded is the **ground subtype relation** (no `Infer` variables on either side): `constrain(𝑇, 𝑈)` on ground types succeeds iff the Lean checker decides `𝑇 <: 𝑈`. A crisp boolean oracle, and it exercises the nastiest comparison code — `without_pi_names` α-handling, `Variant` width subtyping, refinement equality, `UIntRange`.

Mechanically:

- a `test-helpers`-gated Rust binary speaking a JSON encoding of `Type` / `TypedExpr` over stdin, answering subtype and typing queries;
- a Lean executable (`lake` builds real binaries) as the checker;
- case generation on the Rust side with `proptest`, so the generators can be biased toward the corners we already know are nasty (refinement predicates closing over Pi binders, shared sources, `case` payload binders);
- the whole harness wired as an ordinary `cargo test`, so it rides `./ci.sh` like everything else.

## Milestones

Each milestone produces (a) Lean definitions and theorems, and (b) where marked, a differential oracle. Later milestones depend on earlier ones except where noted.

### M0 — Types and the declarative subtype relation

Grammar: `Base`, `UIntRange`, `Fun` (carrying the optional Pi binder), `Tuple`, `Record`, `Variant`, `Refinement` with syntactic-equality predicates. `FunKind` is included **in the grammar from the start** as a static two-point flag (`⇒` vs `⤇`) — kind *inference* waits for M5, but `⇒`/`⤇` distinctness affects type equality and subtyping now, and retrofitting a grammar field into a Lean development touches every proof while an unused constructor argument costs nothing.

Deliverables:

- the declarative relation `𝑇 <: 𝑈` — which does not exist in any standalone form today; the Rust operationalizes subsumption inside `constrain` without ever stating the relation it implements;
- reflexivity and transitivity;
- an executable checker with soundness and completeness against the relation (i.e. decidability);
- the JSON codec matching the Rust `Type`.

Merely stating the rules will force decisions the implementation currently makes implicitly. The questions raised at planning time are adjudicated below.

Binder representation: **named binders with explicit rename environments**, not de Bruijn. This was revised on contact with the Rust: `Refinement` fixes the single reserved binder `__elem` (so refinement equality is bare structural equality, no α-renaming), and `constrain_go` compares dependent refinements after transporting them through the Pi-binder rename the codomain edge mints (`extended_rename`). A pair of rename environments that swap at contravariant edges mirrors that mechanism one-to-one; de Bruijn would be farther from the thing being modeled.

#### M0 status and adjudicated decisions

Landed: the lake project (toolchain pinned to v4.32.2), the ground grammar `Ty` + the `WF` (uniquely-keyed) invariant, the declarative relation `Sub`, the executable checker `subCheck` (termination proved), the hand-written JSON codec with round-trip guards, executable spec examples (one `#guard` per decision below), and `Sub.refl`. Still open within M0: the `beq ↔ eq` bridge for the derived `BEq Ty`, checker soundness/completeness against `Sub`, and the transitivity attempt.

**Base of record.** The model mirrors `constrain_go` as of the mutable-register-typing / binder-annotations stack (branched from `dmills/subtype-annotations`), not current `main` — the `strip_refinements` rework builds on that stack. On the ground fragment the two differ only in error payloads (the tuple width error's reported key), which the relation does not observe.

**Grammar exclusions.** `Infer`, `SharedHole`, `History`, `ChanDom`, `App`, `Below`, and `FunKind::Var` are all inference-time transients or unknowns — outside the ground fragment by the same criterion that keeps them out of a fully-inferred program's types.

**Adjudications** (each is a `Sub` rule with a matching `#guard` in `CclFormal/Decide.lean`):

- **`UIntRange` is equality-only.** No range inclusion, no `UIntRange <: Int` — a range is a data domain (a loop bound), and the solver treats it nominally. `[0,3) ⊀ [0,4)`.
- **Refinements**: `{𝑏₁ | 𝑆₁} <: {𝑏₂ | 𝑆₂}` iff `𝑆₂ ⊆ 𝑆₁` (structural, type-blind predicate equality, after transport through each side's rename — never implication) and `𝑏₁ <: 𝑏₂`. So dropping refinements is subsumption, conjuring one is not (that is an explicit `Restrict`), and the **base is covariant**.
- **Refinements do not distribute over `Variant`** (or anything else): they are compared layer-wise where they sit; the peel is only of *outer* layers on both sides.
- **Function kinds form the lattice `data ⊑ compute`**: a data function satisfies a compute demand, never the reverse. Kind subtyping, not kind equality.
- **Domains**: contravariant, except **data-data pairs are invariant** (both directions — the domain *is* the data). Codomains covariant, under the Pi-binder correspondence extended onto the **lhs** rename.
- **Products/sums**: tuple positional width; record named width with **find-first** lookup; variant is the dual (lhs tags looked up find-first in rhs). Payload depth covariant throughout.
- **Reflexivity is a theorem, not a rule** (`Sub.refl`) — the model omits `constrain_go`'s trivial-equality short-circuit and proves it derivable. The proof requires `Ty.WF` (unique record/variant keys): on a duplicate-keyed product the short-circuit and the find-first arms genuinely disagree, so the model names a builder invariant the Rust leaves implicit.

- **The gated-partition bridge rule** (`is_index_partition_of`: `⧺`-of-refined-legs `<:` plain data function) **is modeled** (`Sub.fnBridge`, with the negated guard on the general function rules preserving the Rust `match`'s commit-to-first-arm determinism, and `Ty.stripRefinements` mirroring the deep strip). Modeling it faithfully surfaced a confirmed behavioral inconsistency — see the finding below.

**Finding: the bridge arm drops the Pi-binder correspondence.** The bridge arm's codomain edge recurses under the *unchanged* lhs morphism (`constrain_go(c0, c1, sl, sr)`) where the general `Fun` arm extends it with the binder correspondence (`cod_sl`). Consequence, confirmed on the Rust by a pinned test (`bridge_arm_skips_pi_correspondence` in `src/ccl/infer/solver/differential.rs`) and mirrored by a `#guard` in `CclFormal/Decide.lean`: two α-equivalent dependent codomains — `(𝑥: 𝐷) ⤇ {Int | __elem == 𝑥}` demanded at binder `𝑦` — reconcile through the general arm but **fail through the bridge**, so the verdict on the same value flips depending only on whether the supplier's domain happens to be partition-shaped. (The arm also skips the kind edge, but that is provably benign: its lhs is always `Data`, the lattice bottom.) Whether a real program reaches the dependent-codomain-through-bridge shape is the cleanup-time question; the model and both pinned tests will flag the moment the arm's behavior changes.

**Tracked divergences and observations:**

- **`Subst::extended_rename` shadowing** is modeled as prepend-with-first-match-wins; confirming that against the Rust's composition semantics is an M1 fuzz target.
- `formal/` is not yet wired into `./ci.sh` — that adds a Lean toolchain dependency to everyone's gate, so it is a deliberate pending decision, not an oversight.

### M1 — Ground-subtype differential fuzz *(oracle)*

The M0 checker vs `constrain` on ground type pairs. The cheapest real-bug detector in the whole plan.

#### M1 status

Landed and running. The pieces:

- **Oracle**: `lake build` produces `subverdict` (`formal/Main.lean`), which answers `true`/`false` per JSONL `{"lhs", "rhs"}` line using the model's `subCheck` under identity morphisms.
- **Harness**: `src/ccl/infer/solver/differential.rs`, an ordinary solver unit test (unit tests see `constrain_subtype` directly — no public-API churn). It skips loudly when the oracle binary is absent, so machines and CI without a Lean toolchain stay green. Knobs: `CAMBRA_DIFF_SEED` / `CAMBRA_DIFF_N`.
- **Generation**: a hand-rolled seeded xorshift generator — deterministic and dependency-free (`proptest` was planned; a new dev-dependency wasn't warranted for this). Three pair modes: identical pairs (exercises the claim that reflexivity is derivable), top-level directed edits (width/refinement near-misses), and **correlated pairs** — both sides built together, usually identical, occasionally diverging in exactly one nested aspect (a leaf, a kind flag, a binder name, a predicate target, a width). Deep near-misses are where subtle rule divergence hides. Dependent refinements are generated referencing each side's *own* Pi binder, so the α-correspondence (`extended_rename` vs the model's `Ren`) is exercised at every nesting depth, shadowing included.
- **Emitter**: `Type` → the wire schema of `formal/CclFormal/Json.lean`, total on the ground fragment, refusing (not mis-serializing) anything outside it or outside the `Pred` vocabulary.

Results at the time of writing: **~800k cases across nine seeds, zero verdict mismatches** — roughly half before the bridge rule was modeled and half after, with `gen_bridge_pair` aiming directly at the gated-partition arm and its guard boundary (shifted indices, stripped-payload misses, empty tag lists, α-renamed dependent codomains). Verdict mix is roughly 42–44% accept, so both classes are well exercised. Harness sensitivity is proven, not assumed: the duplicate-keyed-record reflexivity case — the one known deliberate divergence, outside `Ty.WF` — flags as a mismatch when fed through the pipe by hand, and is pinned as its own unit test (`dup_key_record_reflexivity_diverges_from_model`) so a change to either the short-circuit or the record arm surfaces immediately. The `extended_rename` prepend-shadow assumption listed above is now empirically backed by the fuzz (within the generated vocabulary: two binder names, arbitrary nesting, deliberate misaims).

The generator's one remaining deliberate exclusion is duplicate record/variant keys (outside `WF`) — a documented gap, not a silent one. The bridge-arm Pi-correspondence finding that fell out of modeling the arm is recorded under M0 above and pinned as `bridge_arm_skips_pi_correspondence`.

### M2 — Terms, typing, and safety

Declarative typing `Γ ⊢ 𝑒 : 𝑇` for the pure core — λ, apply, compose, let, literals, tuples/records, variants, `case`, refinements — plus a small-step semantics, and **progress + preservation**. Two corollaries earn their keep against known bug classes:

- **Refinement soundness**: `⊢ 𝑒 : {𝑇 | 𝑝}` and `𝑒 ⇓ 𝑣` implies `𝑝(𝑣) ⇓ true`. The theorem form of "a refinement is a fact about a value", and the property the literal-singleton-types work leans on.
- **Case-binder preservation**: the `case` payload binder retains its scrutinee-derived bound through reduction. A previously-observed defect — the wildcard `case _:` arm's payload binder losing its scrutinee bound — is precisely a counterexample to a lemma of this shape; retroactively rediscovering that known bug is the calibration test for the whole model.

### M3 — Typing oracle *(oracle)*

The Rust dumps the typed AST for generated small programs; Lean checks admissibility of the root typing. This is where the model starts catching *inference* bugs rather than comparison bugs.

### M4 — The solver model

`constrain` / coalesce modeled as a state monad over a store of variables with bound lists, fuel-based at first. Two theorems:

- **Soundness**: every bound the solver records is derivable in the declarative `<:` — and the coalesced output type is admissible for the term (connecting M4 back to M2).
- **Termination**: replace fuel with a well-founded measure. Prioritized because it is the property with live field bugs (a hanging build in this repo is, as a working rule, solver non-termination). The measure has to account for the seen-cache *and* for `extrude` minting fresh variables; being forced to articulate it will either yield a proof or expose that termination is currently contingent on something unstated.

Levels and extrusion enter the model here (scope-escape soundness is a natural third theorem, but is subordinate to the two above).

### M5 — Σ types and `FunKind` inference

The recent machinery, added to the M0–M4 model: kind variables resolved at coalesce ([type-inference.md, "4.6 Data vs compute functions"](../src/ccl/design/type-inference.md#46-data-vs-compute-functions)), Σ formation over candidate domains, and the witness discipline — **one value = one witness**, arms α-converted onto the value's witness (adopt if unanimous, mint on disagreement, sticky), with the join deferred to compaction. That invariant was established only after a constraint-time-join defect was root-caused at some expense; it is exactly the kind of subtle, recently-hand-verified argument worth freezing as a theorem before the next refactor disturbs it.

### M6 — Histories: the mutability semantic model

Independent of M4/M5; can start any time after M2 if the mutability workstream heats up first. This is a *semantics* model, not a typing model — the transient variants (`History`, `ChanDom`, `Hole`, `Infer`) are pipeline artifacts and deliberately stay **out** of the typing calculus.

Model histories as functions `𝐷 ⇒ 𝑉` per [mutability.md, "The model: histories and causal recursion"](../src/ccl/design/mutability.md#the-model-histories-and-causal-recursion):

- `Overwrite` = last-write-wins merge with carry-forward at off-path positions;
- `Append` = the append law, no carry-forward;
- `Txn` reads are arbitrary as-of reads — there is deliberately no terminal/"final value" read in the model, matching [mutability.md, "Semantics"](../src/ccl/design/mutability.md#semantics).

Headline theorem: the `letrec`/`transact` realization emitted by `mut_elim` / `plan_loops` denotes the same function as a direct imperative semantics of the surface program.

## Non-goals

- **Principality.** Dolan-style principality proofs are thesis-scale, and monomorphization means principal types are not shipped anyway.
- **Verifying the Rust directly.** Rust→Lean translation (Aeneas) handles interior mutability and shared graphs worst of all fragments, and the solver core is `Rc<RefCell<InferVar>>`. Not planned around.
- **Reproducing inference output.** Per the oracle stance above: admissibility, not identity (ground subtyping excepted).

## Keeping the model honest

- `formal/` lives in-repo as a `lake` project with a pinned `lean-toolchain`; CI runs `lake build` plus the differential suite.
- The contract: **a semantic change to `constrain` / coalesce either updates `formal/` in the same change or documents the divergence in the PR.** Solver code implementing a modeled rule cites the Lean declaration by name; the doc-refs discipline extends to these citations.
- The differential harness is the enforcement mechanism of last resort: even when proofs lag behind, the executable model diverging from the Rust fails CI.
