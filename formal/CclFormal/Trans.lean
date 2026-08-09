import CclFormal.Equiv
import CclFormal.Props

/-!
# Transitivity: the bridge counterexample, repaired

Under the retired target-relative bridge arm, ground subtyping was **not
transitive**: the chain below held hop-by-hop while its direct edge failed,
machine-checked at the time as `sub_not_trans` (see the history in
`formal/design.md`). With partition collapse re-homed as a *normalization*
(`Sub.fnNorm` mirroring `constrain_go`'s normalize-then-recurse arm), the
direct edge exists; this file machine-checks all three edges of the
formerly-broken triangle.

General transitivity is now a live conjecture rather than a refuted one:
the chain fuzz (`differential.rs :: transitivity_chain_fuzz`, zero
tolerated violations) has found no counterexample since the rewrite. The
proof is future work — its interesting obligations are rename composition
through Pi correspondences and refinement-set containment.
-/

namespace CclFormal

namespace transCex

/-- `{a: Int}` — the partition's shared domain. -/
def recA : Ty := .record [("a", .base .int)]

/-- `{a: Int, b: Bool}` — a strict width-subtype of `recA`. -/
def recAB : Ty := .record [("a", .base .int), ("b", .base .bool)]

/-- One gated leg over `recA`. -/
def gate : Ty := .refined recA (.litBool true)

/-- `⧺{recA | true} ⤇ Int` — the partition-domained data function. -/
def a : Ty := .fn none .data (.variant [(.idx 0, gate)]) (.base .int)

/-- `recA ⤇ Int` — its plain (normal) form. -/
def b : Ty := .fn none .data recA (.base .int)

/-- `recAB ⇒ Int` — a compute demand over the *wider* record. -/
def c : Ty := .fn none .compute recAB (.base .int)

theorem norm_a : normFun a = some b := rfl

theorem norm_b : normFun b = none := rfl

theorem norm_c : normFun c = none := rfl

theorem sub_recA_recA : Sub .id .id recA recA := by
  refine Sub.record (fun n t1 hm => ?_) (fun n t0 t1 hm hlk => ?_)
  · simp at hm
    obtain ⟨rfl, rfl⟩ := hm
    rfl
  · simp at hm
    obtain ⟨rfl, rfl⟩ := hm
    simp [lookupBy] at hlk
    subst hlk
    exact Sub.base _

theorem sub_recAB_recA : Sub .id .id recAB recA := by
  refine Sub.record (fun n t1 hm => ?_) (fun n t0 t1 hm hlk => ?_)
  · simp at hm
    obtain ⟨rfl, rfl⟩ := hm
    rfl
  · simp at hm
    obtain ⟨rfl, rfl⟩ := hm
    simp [lookupBy] at hlk
    subst hlk
    exact Sub.base _

theorem sub_b_b : Sub .id .id b b := by
  refine Sub.fnData norm_b norm_b sub_recA_recA sub_recA_recA (Sub.base _)

/-- Edge one: the partition is below its plain form, through normalization. -/
theorem sub_a_b : Sub .id .id a b := by
  refine Sub.fnNorm (.inl ?_) ?_
  · show (normFun a).isSome = true
    rw [norm_a]
    rfl
  · show Sub .id .id ((normFun a).getD a) ((normFun b).getD b)
    rw [norm_a, norm_b]
    simpa using sub_b_b

/-- Edge two, through the general rule: `data ⊑ compute` on kinds, and the
wider record flows contravariantly into the narrower domain. -/
theorem sub_b_c : Sub .id .id b c := by
  refine Sub.fnCompute norm_b norm_c trivial ?_ sub_recAB_recA (Sub.base _)
  rintro ⟨-, hk⟩
  exact nomatch hk

/-- **The direct edge exists**: the formerly-broken composition now holds,
again through normalization. -/
theorem sub_a_c : Sub .id .id a c := by
  refine Sub.fnNorm (.inl ?_) ?_
  · show (normFun a).isSome = true
    rw [norm_a]
    rfl
  · show Sub .id .id ((normFun a).getD a) ((normFun c).getD c)
    rw [norm_a, norm_c]
    simpa using sub_b_c

end transCex

end CclFormal
