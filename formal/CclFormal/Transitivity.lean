import CclFormal.Equiv
import CclFormal.Props
import CclFormal.Trans

/-!
# Transitivity of the ground subtype relation

Transitivity was **refuted** while the gated-partition bridge arm was a
target-relative comparison (`CclFormal/Trans.lean` records the history); with
partition collapse re-homed as a normalization it became a live conjecture,
and the chain fuzz (`differential.rs :: transitivity_chain_fuzz`, zero
tolerated violations) has found no counterexample since.

This file proves it for the **non-dependent fragment** (`NoPi`: no function
type carries a Pi binder), under a single ambient rename environment. That
covers every rule of the relation — including partition normalization, the
kind lattice, data-domain invariance, and refinement-set containment — and
leaves exactly one obligation open, stated at the bottom: reconciling the
*middle view* when dependent codomains chain, which is the model's analogue
of `constrain.rs :: bridge_holder_gap`.
-/

namespace CclFormal

/-- The non-dependent fragment: no function type carries a Pi binder.

With no binder anywhere, `codRen n0 n1 ρ = ρ` at every function edge, so one
ambient rename environment serves the whole derivation and the middle view
of a chain needs no reconciliation. -/
def NoPi : Ty → Prop
  | .fn n _ d c => n = none ∧ NoPi d ∧ NoPi c
  | .tuple ts => ∀ t ∈ ts, NoPi t
  | .record fs => ∀ e ∈ fs, NoPi e.2
  | .variant tags => ∀ e ∈ tags, NoPi e.2
  | .refined b _ => NoPi b
  | .base _ | .uintRange _ | .dataSource _ | .txn => True
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
      | (rename_i h
         obtain ⟨a, b⟩ := e
         have := List.sizeOf_lt_of_mem h
         try simp at this
         try simp
         omega)

/-- A type with no top-level refinement layer is its own peel. -/
theorem peel_nil_self : {t : Ty} → t.peel.2 = [] → t.peel.1 = t
  | .base _, _ | .uintRange _, _ | .dataSource _, _ | .txn, _
  | .fn .., _ | .tuple _, _ | .record _, _ | .variant _, _ => rfl
  | .refined b p, h => by simp [Ty.peel] at h

theorem noPi_peel_fst : (t : Ty) → NoPi t → NoPi t.peel.1
  | .base _, h => h
  | .uintRange _, h => h
  | .dataSource _, h => h
  | .txn, h => h
  | .fn .., h => h
  | .tuple _, h => h
  | .record _, h => h
  | .variant _, h => h
  | .refined b _, h => by
      have hb : NoPi b := by rw [NoPi] at h; exact h
      simpa [Ty.peel] using noPi_peel_fst b hb
termination_by t => sizeOf t
decreasing_by simp_wf; omega

theorem noPi_legUnder : (t : Ty) → NoPi t → NoPi (legUnder t)
  | .base _, h => h
  | .uintRange _, h => h
  | .dataSource _, h => h
  | .txn, h => h
  | .fn .., h => h
  | .tuple _, h => h
  | .record _, h => h
  | .variant _, h => h
  | .refined b _, h => by rw [NoPi] at h; simpa [legUnder] using h

theorem noPi_partitionDomain {d u : Ty} (h : NoPi d)
    (hd : partitionDomain d = some u) : NoPi u := by
  match d, hd with
  | .variant ((k0, p0) :: rest), hd =>
      simp only [partitionDomain] at hd
      split at hd
      · injection hd with hd
        subst hd
        have hp0 : NoPi p0 := by
          rw [NoPi] at h
          exact h (k0, p0) (List.mem_cons_self ..)
        exact noPi_legUnder p0 hp0
      · exact absurd hd (by simp)

theorem noPi_normFun {t t' : Ty} (h : NoPi t) (hn : normFun t = some t') :
    NoPi t' := by
  match t, hn with
  | .fn n k d c, hn =>
      simp only [normFun, Option.map_eq_some_iff] at hn
      obtain ⟨d', hd, rfl⟩ := hn
      rw [NoPi] at h ⊢
      exact ⟨h.1, noPi_partitionDomain h.2.1 hd, h.2.2⟩

/-- `getD` form: normalization stays inside the fragment. -/
theorem noPi_normFun_getD {t : Ty} (h : NoPi t) : NoPi ((normFun t).getD t) := by
  cases hn : normFun t with
  | none => simpa using h
  | some t' => simpa using noPi_normFun h hn

theorem deficit_eq_nil_iff {ρl ρr : Ren} {l r : List Pred} :
    deficit ρl ρr l r = [] ↔
      ∀ p ∈ r, ∃ q ∈ l, q.rename ρl = p.rename ρr := by
  unfold deficit
  rw [List.filter_eq_nil_iff]
  constructor
  · intro h p hp
    have := h p hp
    simp only [Bool.not_eq_true', Bool.not_eq_false] at this
    have hmem := List.mem_of_elem_eq_true this
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hmem
    exact ⟨q, hq, hqe⟩
  · intro h p hp
    obtain ⟨q, hq, hqe⟩ := h p hp
    simp only [Bool.not_eq_true', Bool.not_eq_false]
    exact List.elem_eq_true_of_mem (List.mem_map.mpr ⟨q, hq, hqe⟩)

/-- Refinement-set containment composes (single ambient environment). -/
theorem deficit_trans {ρ : Ren} {l m r : List Pred}
    (h1 : deficit ρ ρ l m = []) (h2 : deficit ρ ρ m r = []) :
    deficit ρ ρ l r = [] := by
  rw [deficit_eq_nil_iff] at h1 h2 ⊢
  intro p hp
  obtain ⟨q, hq, hqe⟩ := h2 p hp
  obtain ⟨s, hs, hse⟩ := h1 q hq
  exact ⟨s, hs, hse.trans hqe⟩

/-- Universal peel inversion: **every** rule leaves the peeled bases related
and the peeled refinement sets contained. For the head-constructor rules
both peels are `(t, [])`, so this is the derivation itself; for the
refinement rule it is exactly its premises. -/
theorem sub_peel_inv {ρ : Ren} {x y : Ty} (h : Sub ρ ρ x y) :
    deficit ρ ρ x.peel.2 y.peel.2 = [] ∧ Sub ρ ρ x.peel.1 y.peel.1 := by
  cases h with
  | base b => exact ⟨rfl, .base b⟩
  | uintRange n => exact ⟨rfl, .uintRange n⟩
  | dataSource s => exact ⟨rfl, .dataSource s⟩
  | txn => exact ⟨rfl, .txn⟩
  | fnNorm h1 h2 => exact ⟨rfl, .fnNorm h1 h2⟩
  | fnCompute h1 h2 h3 h4 h5 h6 => exact ⟨rfl, .fnCompute h1 h2 h3 h4 h5 h6⟩
  | fnData h1 h2 h3 h4 h5 => exact ⟨rfl, .fnData h1 h2 h3 h4 h5⟩
  | tuple h1 h2 => exact ⟨rfl, .tuple h1 h2⟩
  | record h1 h2 => exact ⟨rfl, .record h1 h2⟩
  | variant h1 h2 => exact ⟨rfl, .variant h1 h2⟩
  | refined hpl hpr _ hdef hbase =>
      rw [hpl, hpr]
      exact ⟨hdef, hbase⟩

/-- Every function-to-function edge relates the two sides' **normal forms**:
`fnNorm` says so directly, and the general rules only fire when both sides
are already normal. -/
theorem sub_normFun {ρ : Ren} {n0 k0 d0 c0 n1 k1 d1 c1}
    (h : Sub ρ ρ (.fn n0 k0 d0 c0) (.fn n1 k1 d1 c1)) :
    Sub ρ ρ ((normFun (.fn n0 k0 d0 c0)).getD (.fn n0 k0 d0 c0))
      ((normFun (.fn n1 k1 d1 c1)).getD (.fn n1 k1 d1 c1)) := by
  cases h with
  | fnNorm _ hplain => exact hplain
  | fnCompute hnl hnr h3 h4 h5 h6 =>
      rw [hnl, hnr]
      exact .fnCompute hnl hnr h3 h4 h5 h6
  | fnData hnl hnr h3 h4 h5 =>
      rw [hnl, hnr]
      exact .fnData hnl hnr h3 h4 h5
  | refined hpl hpr hg _ _ =>
      simp only [Ty.peel, Prod.mk.injEq] at hpl hpr
      obtain ⟨-, hl⟩ := hpl
      obtain ⟨-, hr⟩ := hpr
      subst hl; subst hr
      rcases hg with hg | hg <;> exact absurd rfl hg

/-- De Morgan for a decidable conjunction (no Mathlib in this development). -/
theorem not_and_or' {a b : Prop} [Decidable a] (h : ¬(a ∧ b)) : ¬a ∨ ¬b := by
  by_cases ha : a
  · exact Or.inr fun hb => h ⟨ha, hb⟩
  · exact Or.inl ha

theorem one_le_sizeOf (t : Ty) : 1 ≤ sizeOf t := by
  cases t <;> simp <;> omega

theorem kindOk_trans {k0 km k1 : FunKind}
    (h1 : kindOk k0 km) (h2 : kindOk km k1) : kindOk k0 k1 := by
  cases k0 <;> cases km <;> cases k1 <;> simp_all [kindOk]

theorem lookupBy_mem [BEq α] [LawfulBEq α] {l : List (α × Ty)} {k : α} {t : Ty}
    (h : lookupBy l k = some t) : (k, t) ∈ l := by
  unfold lookupBy at h
  cases hf : l.find? (fun e => e.1 == k) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some e =>
      obtain ⟨a, b⟩ := e
      rw [hf] at h
      simp only [Option.map_some] at h
      injection h with hb
      subst hb
      have hmem := List.mem_of_find?_eq_some hf
      have hkey : a = k := by
        have := List.find?_some hf
        simpa using eq_of_beq (by simpa using this)
      subst hkey
      exact hmem

/-- Shape inversion: a bare type below a function type is a function type. -/
theorem sub_fn_rhs_shape {ρ : Ren} {x : Ty} {nm km dm cm}
    (h : Sub ρ ρ x (.fn nm km dm cm)) (hx : x.peel.2 = []) :
    ∃ n0 k0 d0 c0, x = .fn n0 k0 d0 c0 := by
  cases h with
  | fnNorm _ _ => exact ⟨_, _, _, _, rfl⟩
  | fnCompute _ _ _ _ _ _ => exact ⟨_, _, _, _, rfl⟩
  | fnData _ _ _ _ _ => exact ⟨_, _, _, _, rfl⟩
  | refined hpl hpr hg _ _ =>
      rw [hpl] at hx
      simp only [Ty.peel, Prod.mk.injEq] at hpr hx
      obtain ⟨-, hr⟩ := hpr
      subst hr
      rcases hg with hg | hg
      · exact absurd hx hg
      · exact absurd rfl hg

/-- Shape inversion: a bare type above a function type is a function type. -/
theorem sub_fn_lhs_shape {ρ : Ren} {z : Ty} {nm km dm cm}
    (h : Sub ρ ρ (.fn nm km dm cm) z) (hz : z.peel.2 = []) :
    ∃ n1 k1 d1 c1, z = .fn n1 k1 d1 c1 := by
  cases h with
  | fnNorm _ _ => exact ⟨_, _, _, _, rfl⟩
  | fnCompute _ _ _ _ _ _ => exact ⟨_, _, _, _, rfl⟩
  | fnData _ _ _ _ _ => exact ⟨_, _, _, _, rfl⟩
  | refined hpl hpr hg _ _ =>
      rw [hpr] at hz
      simp only [Ty.peel, Prod.mk.injEq] at hpl hz
      obtain ⟨-, hl⟩ := hpl
      subst hl
      rcases hg with hg | hg
      · exact absurd rfl hg
      · exact absurd hz hg

theorem noPi_fn_binder {n k d c} (h : NoPi (.fn n k d c)) : n = none := by
  rw [NoPi] at h; exact h.1

theorem noPi_fn_dom {n k d c} (h : NoPi (.fn n k d c)) : NoPi d := by
  rw [NoPi] at h; exact h.2.1

theorem noPi_fn_cod {n k d c} (h : NoPi (.fn n k d c)) : NoPi c := by
  rw [NoPi] at h; exact h.2.2

/-- The function case of transitivity, with the induction hypothesis passed
in explicitly (`IH`) so the three ways of concluding a function edge —
`fnNorm`, `fnCompute`, `fnData` — are handled once rather than per caller. -/
theorem sub_trans_fn {ρ : Ren} {n : Nat} {n0 k0 d0 c0 nm km dm cm : _} {z : Ty}
    (IH : ∀ a b c : Ty, sizeOf a + sizeOf b + sizeOf c ≤ n →
      NoPi a → NoPi b → NoPi c → Sub ρ ρ a b → Sub ρ ρ b c → Sub ρ ρ a c)
    (hbound : sizeOf (Ty.fn n0 k0 d0 c0) + sizeOf (Ty.fn nm km dm cm)
      + sizeOf z ≤ n + 1)
    (hx : NoPi (.fn n0 k0 d0 c0)) (hy : NoPi (.fn nm km dm cm)) (hz : NoPi z)
    (hzb : z.peel.2 = [])
    (h1 : Sub ρ ρ (.fn n0 k0 d0 c0) (.fn nm km dm cm))
    (h2 : Sub ρ ρ (.fn nm km dm cm) z) :
    Sub ρ ρ (.fn n0 k0 d0 c0) z := by
  obtain ⟨n1, k1, d1, c1, rfl⟩ := sub_fn_lhs_shape h2 hzb
  have e1 := sub_normFun h1
  have e2 := sub_normFun h2
  -- Sizes: a normalized side never grows, and shrinks when it normalizes.
  have hlex : sizeOf ((normFun (Ty.fn n0 k0 d0 c0)).getD (Ty.fn n0 k0 d0 c0))
      ≤ sizeOf (Ty.fn n0 k0 d0 c0) := by
    cases hn : normFun (Ty.fn n0 k0 d0 c0) with
    | none => simp
    | some t => simpa using Nat.le_of_lt (normFun_sizeOf hn)
  have hley : sizeOf ((normFun (Ty.fn nm km dm cm)).getD (Ty.fn nm km dm cm))
      ≤ sizeOf (Ty.fn nm km dm cm) := by
    cases hn : normFun (Ty.fn nm km dm cm) with
    | none => simp
    | some t => simpa using Nat.le_of_lt (normFun_sizeOf hn)
  have hlez : sizeOf ((normFun (Ty.fn n1 k1 d1 c1)).getD (Ty.fn n1 k1 d1 c1))
      ≤ sizeOf (Ty.fn n1 k1 d1 c1) := by
    cases hn : normFun (Ty.fn n1 k1 d1 c1) with
    | none => simp
    | some t => simpa using Nat.le_of_lt (normFun_sizeOf hn)
  by_cases hnorm : (normFun (Ty.fn n0 k0 d0 c0)).isSome ∨
      (normFun (Ty.fn n1 k1 d1 c1)).isSome
  · -- At least one side normalizes: collapse both and recurse.
    refine Sub.fnNorm hnorm (IH _ _ _ ?_ (noPi_normFun_getD hx)
      (noPi_normFun_getD hy) (noPi_normFun_getD hz) e1 e2)
    have hstrict : sizeOf ((normFun (Ty.fn n0 k0 d0 c0)).getD (Ty.fn n0 k0 d0 c0))
        + sizeOf ((normFun (Ty.fn n1 k1 d1 c1)).getD (Ty.fn n1 k1 d1 c1))
        < sizeOf (Ty.fn n0 k0 d0 c0) + sizeOf (Ty.fn n1 k1 d1 c1) := by
      rcases hnorm with hs | hs
      · cases hn : normFun (Ty.fn n0 k0 d0 c0) with
        | none => rw [hn] at hs; exact absurd hs (by simp)
        | some t =>
            have := normFun_sizeOf hn
            simp only [Option.getD_some]
            omega
      · cases hn : normFun (Ty.fn n1 k1 d1 c1) with
        | none => rw [hn] at hs; exact absurd hs (by simp)
        | some t =>
            have := normFun_sizeOf hn
            simp only [Option.getD_some]
            omega
    omega
  · have hnx : normFun (Ty.fn n0 k0 d0 c0) = none := by
      cases hn : normFun (Ty.fn n0 k0 d0 c0) with
      | none => rfl
      | some t => exact absurd (Or.inl (by rw [hn]; simp)) hnorm
    have hnz : normFun (Ty.fn n1 k1 d1 c1) = none := by
      cases hn : normFun (Ty.fn n1 k1 d1 c1) with
      | none => rfl
      | some t => exact absurd (Or.inr (by rw [hn]; simp)) hnorm
    rw [hnx] at e1
    rw [hnz] at e2
    simp only [Option.getD_none] at e1 e2
    by_cases hny : (normFun (Ty.fn nm km dm cm)).isSome
    · -- Only the middle normalizes: recurse through its normal form.
      refine IH _ _ _ ?_ hx (noPi_normFun_getD hy) hz e1 e2
      have hstrict : sizeOf ((normFun (Ty.fn nm km dm cm)).getD (Ty.fn nm km dm cm))
          < sizeOf (Ty.fn nm km dm cm) := by
        cases hn : normFun (Ty.fn nm km dm cm) with
        | none => rw [hn] at hny; exact absurd hny (by simp)
        | some t =>
            have := normFun_sizeOf hn
            simp only [Option.getD_some]
            omega
      omega
    · -- Nothing normalizes: the structural rules, edge by edge.
      have hnyn : normFun (Ty.fn nm km dm cm) = none := by
        cases hn : normFun (Ty.fn nm km dm cm) with
        | none => rfl
        | some t => rw [hn] at hny; simp at hny
      have hb0 : n0 = none := noPi_fn_binder hx
      have hbm : nm = none := noPi_fn_binder hy
      have hb1 : n1 = none := noPi_fn_binder hz
      subst hb0; subst hbm; subst hb1
      -- Sizes for the domain and codomain recursions.
      have hdom_sz : sizeOf d1 + sizeOf dm + sizeOf d0 ≤ n := by
        simp only [Ty.fn.sizeOf_spec] at hbound
        omega
      have hcod_sz : sizeOf c0 + sizeOf cm + sizeOf c1 ≤ n := by
        simp only [Ty.fn.sizeOf_spec] at hbound
        omega
      cases h1 with
      | fnNorm hg _ =>
          rcases hg with hg | hg
          · rw [hnx] at hg; exact absurd hg (by simp)
          · rw [hnyn] at hg; exact absurd hg (by simp)
      | refined hpl hpr hg _ _ =>
          simp only [Ty.peel, Prod.mk.injEq] at hpl hpr
          obtain ⟨-, hl⟩ := hpl
          obtain ⟨-, hr⟩ := hpr
          subst hl; subst hr
          rcases hg with hg | hg <;> exact absurd rfl hg
      | fnCompute _ _ hok1 hnd1 hdom1 hcod1 =>
          simp only [codRen] at hcod1
          cases h2 with
          | fnNorm hg _ =>
              rcases hg with hg | hg
              · rw [hnyn] at hg; exact absurd hg (by simp)
              · rw [hnz] at hg; exact absurd hg (by simp)
          | refined hpl hpr hg _ _ =>
              simp only [Ty.peel, Prod.mk.injEq] at hpl hpr
              obtain ⟨-, hl⟩ := hpl
              obtain ⟨-, hr⟩ := hpr
              subst hl; subst hr
              rcases hg with hg | hg <;> exact absurd rfl hg
          | fnCompute _ _ hok2 hnd2 hdom2 hcod2 =>
              simp only [codRen] at hcod2
              have hdom := IH d1 dm d0 hdom_sz (noPi_fn_dom hz) (noPi_fn_dom hy)
                (noPi_fn_dom hx) hdom2 hdom1
              have hcod := IH c0 cm c1 hcod_sz (noPi_fn_cod hx) (noPi_fn_cod hy)
                (noPi_fn_cod hz) hcod1 hcod2
              refine Sub.fnCompute hnx hnz (kindOk_trans hok1 hok2) ?_ hdom hcod
              rintro ⟨rfl, rfl⟩
              -- k0 = k1 = data forces km = compute (h1) and then h2's kind
              -- edge is `compute <: data`, which the lattice rejects.
              have hkm : km ≠ FunKind.data := fun h => hnd1 ⟨rfl, h⟩
              cases km with
              | data => exact hkm rfl
              | compute => exact hok2
          | fnData _ _ _ _ _ =>
              -- h2 pins km = data, so h1's `¬(k0 = data ∧ km = data)` forces
              -- k0 = compute — and then h1's kind edge is `compute <: data`.
              have hk0 : k0 ≠ FunKind.data := fun h => hnd1 ⟨h, rfl⟩
              cases k0 with
              | data => exact absurd rfl hk0
              | compute => exact absurd hok1 (by simp [kindOk])
      | fnData _ _ hdom1a hdom1b hcod1 =>
          simp only [codRen] at hcod1
          cases h2 with
          | fnNorm hg _ =>
              rcases hg with hg | hg
              · rw [hnyn] at hg; exact absurd hg (by simp)
              · rw [hnz] at hg; exact absurd hg (by simp)
          | refined hpl hpr hg _ _ =>
              simp only [Ty.peel, Prod.mk.injEq] at hpl hpr
              obtain ⟨-, hl⟩ := hpl
              obtain ⟨-, hr⟩ := hpr
              subst hl; subst hr
              rcases hg with hg | hg <;> exact absurd rfl hg
          | fnCompute _ _ hok2 hnd2 hdom2 hcod2 =>
              simp only [codRen] at hcod2
              have hdom := IH d1 dm d0 hdom_sz (noPi_fn_dom hz) (noPi_fn_dom hy)
                (noPi_fn_dom hx) hdom2 hdom1a
              have hcod := IH c0 cm c1 hcod_sz (noPi_fn_cod hx) (noPi_fn_cod hy)
                (noPi_fn_cod hz) hcod1 hcod2
              refine Sub.fnCompute hnx hnz hok2 ?_ hdom hcod
              rintro ⟨-, rfl⟩
              exact hnd2 ⟨rfl, rfl⟩
          | fnData _ _ hdom2a hdom2b hcod2 =>
              simp only [codRen] at hcod2
              have hdomA := IH d1 dm d0 hdom_sz (noPi_fn_dom hz) (noPi_fn_dom hy)
                (noPi_fn_dom hx) hdom2a hdom1a
              have hdomB := IH d0 dm d1 (by omega) (noPi_fn_dom hx)
                (noPi_fn_dom hy) (noPi_fn_dom hz) hdom1b hdom2b
              have hcod := IH c0 cm c1 hcod_sz (noPi_fn_cod hx) (noPi_fn_cod hy)
                (noPi_fn_cod hz) hcod1 hcod2
              exact Sub.fnData hnx hnz hdomA hdomB hcod

/-- Fuel-bounded transitivity: `n` bounds the summed size, so the induction
hypothesis is an ordinary function that the helper above can take. -/
theorem sub_trans_aux : (n : Nat) → (ρ : Ren) → (x y z : Ty) →
    sizeOf x + sizeOf y + sizeOf z ≤ n →
    NoPi x → NoPi y → NoPi z →
    Sub ρ ρ x y → Sub ρ ρ y z → Sub ρ ρ x z
  | 0, _, x, y, z, hn, _, _, _, _, _ => by
      have := one_le_sizeOf x
      have := one_le_sizeOf y
      have := one_le_sizeOf z
      omega
  | n + 1, ρ, x, y, z, hn, hx, hy, hz, h1, h2 => by
    have IH : ∀ a b c : Ty, sizeOf a + sizeOf b + sizeOf c ≤ n →
        NoPi a → NoPi b → NoPi c → Sub ρ ρ a b → Sub ρ ρ b c → Sub ρ ρ a c :=
      fun a b c hb ha hbb hc s1 s2 => sub_trans_aux n ρ a b c hb ha hbb hc s1 s2
    by_cases hbare : x.peel.2 = [] ∧ y.peel.2 = [] ∧ z.peel.2 = []
    · -- No top-level refinement anywhere: the head-constructor rules.
      obtain ⟨hxb, hyb, hzb⟩ := hbare
      cases h1 with
      | base b =>
          cases h2 with
          | base _ => exact .base b
          | refined hpl hpr hg _ _ =>
              rw [hpr] at hzb
              simp only [Ty.peel, Prod.mk.injEq] at hpl hzb
              obtain ⟨-, hl⟩ := hpl
              subst hl
              rcases hg with hg | hg
              · exact absurd rfl hg
              · exact absurd hzb hg
      | uintRange m =>
          cases h2 with
          | uintRange _ => exact .uintRange m
          | refined hpl hpr hg _ _ =>
              rw [hpr] at hzb
              simp only [Ty.peel, Prod.mk.injEq] at hpl hzb
              obtain ⟨-, hl⟩ := hpl
              subst hl
              rcases hg with hg | hg
              · exact absurd rfl hg
              · exact absurd hzb hg
      | dataSource s =>
          cases h2 with
          | dataSource _ => exact .dataSource s
          | refined hpl hpr hg _ _ =>
              rw [hpr] at hzb
              simp only [Ty.peel, Prod.mk.injEq] at hpl hzb
              obtain ⟨-, hl⟩ := hpl
              subst hl
              rcases hg with hg | hg
              · exact absurd rfl hg
              · exact absurd hzb hg
      | txn =>
          cases h2 with
          | txn => exact .txn
          | refined hpl hpr hg _ _ =>
              rw [hpr] at hzb
              simp only [Ty.peel, Prod.mk.injEq] at hpl hzb
              obtain ⟨-, hl⟩ := hpl
              subst hl
              rcases hg with hg | hg
              · exact absurd rfl hg
              · exact absurd hzb hg
      | fnNorm hg hp =>
          exact sub_trans_fn IH (by omega) hx hy hz hzb (.fnNorm hg hp) h2
      | fnCompute a b c d e f =>
          exact sub_trans_fn IH (by omega) hx hy hz hzb
            (.fnCompute a b c d e f) h2
      | fnData a b c d e =>
          exact sub_trans_fn IH (by omega) hx hy hz hzb (.fnData a b c d e) h2
      | tuple hlen1 hpt1 =>
          cases h2 with
          | tuple hlen2 hpt2 =>
              refine Sub.tuple (Nat.le_trans hlen2 hlen1) ?_
              intro i t0 t1 h0 h1'
              rename_i as bs cs
              have hi1 : i < cs.length := by
                obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h1'
                exact hlt
              have hi2 : i < bs.length := Nat.lt_of_lt_of_le hi1 hlen2
              have hb : bs[i]? = some bs[i] := List.getElem?_eq_getElem hi2
              have hm0 : t0 ∈ as := List.mem_of_getElem? h0
              have hmm : bs[i] ∈ bs := List.getElem_mem hi2
              have hm1 : t1 ∈ cs := List.mem_of_getElem? h1'
              have s0 := List.sizeOf_lt_of_mem hm0
              have sm := List.sizeOf_lt_of_mem hmm
              have s1 := List.sizeOf_lt_of_mem hm1
              refine IH t0 bs[i] t1 ?_ ?_ ?_ ?_ (hpt1 i t0 bs[i] h0 hb)
                (hpt2 i bs[i] t1 hb h1')
              · simp only [Ty.tuple.sizeOf_spec] at hn
                omega
              · rw [NoPi] at hx; exact hx t0 hm0
              · rw [NoPi] at hy; exact hy bs[i] hmm
              · rw [NoPi] at hz; exact hz t1 hm1
          | refined hpl hpr hg _ _ =>
              rw [hpr] at hzb
              simp only [Ty.peel, Prod.mk.injEq] at hpl hzb
              obtain ⟨-, hl⟩ := hpl
              subst hl
              rcases hg with hg | hg
              · exact absurd rfl hg
              · exact absurd hzb hg
      | record hsome1 hsub1 =>
          cases h2 with
          | record hsome2 hsub2 =>
              rename_i as bs cs
              refine Sub.record (fun nkey t1 hm => ?_) (fun nkey t0 t1 hm hlk => ?_)
              · have h2s := hsome2 nkey t1 hm
                obtain ⟨tm, htm⟩ := Option.isSome_iff_exists.mp h2s
                exact hsome1 nkey tm (lookupBy_mem htm)
              · have h2s := hsome2 nkey t1 hm
                obtain ⟨tm, htm⟩ := Option.isSome_iff_exists.mp h2s
                have hmm : (nkey, tm) ∈ bs := lookupBy_mem htm
                have hm0 : (nkey, t0) ∈ as := lookupBy_mem hlk
                have s0 := List.sizeOf_lt_of_mem hm0
                have sm := List.sizeOf_lt_of_mem hmm
                have s1 := List.sizeOf_lt_of_mem hm
                refine IH t0 tm t1 ?_ ?_ ?_ ?_ (hsub1 nkey t0 tm hmm hlk)
                  (hsub2 nkey tm t1 hm htm)
                · simp only [Ty.record.sizeOf_spec] at hn
                  simp only [Prod.mk.sizeOf_spec] at s0 sm s1
                  omega
                · rw [NoPi] at hx; exact hx (nkey, t0) hm0
                · rw [NoPi] at hy; exact hy (nkey, tm) hmm
                · rw [NoPi] at hz; exact hz (nkey, t1) hm
          | refined hpl hpr hg _ _ =>
              rw [hpr] at hzb
              simp only [Ty.peel, Prod.mk.injEq] at hpl hzb
              obtain ⟨-, hl⟩ := hpl
              subst hl
              rcases hg with hg | hg
              · exact absurd rfl hg
              · exact absurd hzb hg
      | variant hsome1 hsub1 =>
          cases h2 with
          | variant hsome2 hsub2 =>
              rename_i as bs cs
              refine Sub.variant (fun key t0 hm => ?_) (fun key t0 t1 hm hlk => ?_)
              · have h1s := hsome1 key t0 hm
                obtain ⟨tm, htm⟩ := Option.isSome_iff_exists.mp h1s
                exact hsome2 key tm (lookupBy_mem htm)
              · have h1s := hsome1 key t0 hm
                obtain ⟨tm, htm⟩ := Option.isSome_iff_exists.mp h1s
                have hmm : (key, tm) ∈ bs := lookupBy_mem htm
                have hm1 : (key, t1) ∈ cs := lookupBy_mem hlk
                have s0 := List.sizeOf_lt_of_mem hm
                have sm := List.sizeOf_lt_of_mem hmm
                have s1 := List.sizeOf_lt_of_mem hm1
                refine IH t0 tm t1 ?_ ?_ ?_ ?_ (hsub1 key t0 tm hm htm)
                  (hsub2 key tm t1 hmm hlk)
                · simp only [Ty.variant.sizeOf_spec] at hn
                  simp only [Prod.mk.sizeOf_spec] at s0 sm s1
                  omega
                · rw [NoPi] at hx; exact hx (key, t0) hm
                · rw [NoPi] at hy; exact hy (key, tm) hmm
                · rw [NoPi] at hz; exact hz (key, t1) hm1
          | refined hpl hpr hg _ _ =>
              rw [hpr] at hzb
              simp only [Ty.peel, Prod.mk.injEq] at hpl hzb
              obtain ⟨-, hl⟩ := hpl
              subst hl
              rcases hg with hg | hg
              · exact absurd rfl hg
              · exact absurd hzb hg
      | refined hpl hpr hg _ _ =>
          rw [hpl] at hxb
          rw [hpr] at hyb
          simp at hxb hyb
          rcases hg with hg | hg
          · exact absurd hxb hg
          · exact absurd hyb hg
    · -- Some side carries a refinement layer: peel all three, recurse, re-wrap.
      obtain ⟨hd1, hs1⟩ := sub_peel_inv h1
      obtain ⟨hd2, hs2⟩ := sub_peel_inv h2
      have hlt : sizeOf x.peel.1 + sizeOf y.peel.1 + sizeOf z.peel.1
          < sizeOf x + sizeOf y + sizeOf z := by
        have hax := Ty.peel_fst_sizeOf_le x
        have hay := Ty.peel_fst_sizeOf_le y
        have haz := Ty.peel_fst_sizeOf_le z
        rcases not_and_or' hbare with h' | h'
        · have := Ty.peel_fst_sizeOf_lt x h'; omega
        · rcases not_and_or' h' with h'' | h''
          · have := Ty.peel_fst_sizeOf_lt y h''; omega
          · have := Ty.peel_fst_sizeOf_lt z h''; omega
      have hbase := IH x.peel.1 y.peel.1 z.peel.1 (by omega)
        (noPi_peel_fst x hx) (noPi_peel_fst y hy) (noPi_peel_fst z hz) hs1 hs2
      have hdef := deficit_trans hd1 hd2
      by_cases hxz : x.peel.2 = [] ∧ z.peel.2 = []
      · rw [peel_nil_self hxz.1, peel_nil_self hxz.2] at hbase
        exact hbase
      · exact Sub.refined rfl rfl (not_and_or' hxz) hdef hbase

/-- **Transitivity of ground subtyping on the non-dependent fragment.** -/
theorem sub_trans {ρ : Ren} {x y z : Ty}
    (hx : NoPi x) (hy : NoPi y) (hz : NoPi z)
    (h1 : Sub ρ ρ x y) (h2 : Sub ρ ρ y z) : Sub ρ ρ x z :=
  sub_trans_aux (sizeOf x + sizeOf y + sizeOf z) ρ x y z (Nat.le_refl _) hx hy hz h1 h2

/-- End-to-end: the triangle that **refuted** transitivity under the bridge
arm is now an instance of the general theorem, not just three hand-built
derivations (`CclFormal/Trans.lean`). -/
example : Sub .id .id transCex.a transCex.c :=
  sub_trans
    (by simp [NoPi, transCex.a, transCex.gate, transCex.recA])
    (by simp [NoPi, transCex.b, transCex.recA])
    (by simp [NoPi, transCex.c, transCex.recAB])
    transCex.sub_a_b transCex.sub_b_c

/-!
## The remaining obligation: dependent codomains

`sub_trans` is restricted to `NoPi` because the dependent case needs a
reconciliation step the statement above cannot express. Chaining two
function edges gives codomain premises

* `Sub (codRen 𝑛₀ 𝑛ₘ ρl) ρm 𝑐₀ 𝑐ₘ`  (from `𝑥 <: 𝑦`), and
* `Sub (codRen 𝑛ₘ 𝑛₁ ρm) ρr 𝑐ₘ 𝑐₁`  (from `𝑦 <: 𝑧`),

while the conclusion needs `Sub (codRen 𝑛₀ 𝑛₁ ρl) ρr 𝑐₀ 𝑐₁`. The two
premises disagree about the **middle view**: the first sees `𝑦`'s codomain
under `ρm`, the second under `ρm.extend 𝑛ₘ 𝑛₁`. They compose only through
the rename `σ = [𝑛ₘ ↦ 𝑛₁]` that relates those views, and then the
conclusion's left view is the first premise's left view composed with `σ`
— `σ ∘ (ρl.extend 𝑛₀ 𝑛ₘ) = ρl.extend 𝑛₀ 𝑛₁` — which holds only under a
freshness side condition (`ρl` must not already produce `𝑛ₘ`).

So the dependent statement is not `Sub ρl ρm 𝑥 𝑦 → Sub ρm ρr 𝑦 𝑧 → …` but
the σ-indexed generalization

```
Sub ρl ρm 𝑥 𝑦 → Sub (σ ∘ ρm) ρr 𝑦 𝑧 → Sub (σ ∘ ρl) ρr 𝑥 𝑧
```

which is precisely what `constrain.rs :: bridge_holder_gap` computes when
two bounds recorded under different morphisms meet at one variable — the
implementation already invented this reconciliation; the metatheory needs
the same one. Proving it additionally requires stating the freshness
discipline the Rust gets for free from globally-uniquified `Name`s
(Barendregt convention) but never writes down. Recorded as the next
milestone rather than attempted here.
-/

/-- The unrestricted conjecture, stated but **not proved**: transitivity
without the `NoPi` restriction. The chain fuzz
(`differential.rs :: transitivity_chain_fuzz`) exercises it with dependent
refinements and has found no counterexample; the σ-gap above is what a
proof must supply. -/
def TransitivityConjecture : Prop :=
  ∀ (ρ : Ren) (x y z : Ty), Sub ρ ρ x y → Sub ρ ρ y z → Sub ρ ρ x z


end CclFormal
