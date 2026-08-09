import CclFormal.Equiv
import CclFormal.Props
import CclFormal.Trans

/-!
# Transitivity of the ground subtype relation

Transitivity was **refuted** while the gated-partition bridge arm was a
target-relative comparison (`CclFormal/Trans.lean` records the history),
became a live conjecture once the collapse was re-homed as a normalization,
and was first proved for the binder-free fragment (`NoPi`). The remaining
obstruction was the **σ-gap**: chaining dependent codomains produces
premises that view the middle type under different renames, which compose
only through a reconciliation morphism — the model analogue of
`constrain.rs :: bridge_holder_gap`.

Canonical Pi binders dissolved the gap. The solver now names every arrow's
binder by its depth (`__pi0`, `__pi1`, … — `ReservedName::Pi`, the
`REFINEMENT_BINDER` move applied to arrows), so any two types compared at
the same position carry the *same* binder when both carry one. Every binder
correspondence a canonical chain mints is therefore **diagonal**
(`__piK ↦ __piK`), and diagonal extensions act as the identity on rename
environments. This file proves transitivity for that fragment (`Canon`),
with the environments generalized to six independent identity-acting ones —
which is what makes the diagonal observation compositional. Pure
transitivity at the identity environment (`sub_trans_id` at the bottom)
covers every type the solver emits; the former `NoPi` fragment is the
special case where every binder is `none`.
-/

namespace CclFormal

/-- The canonical spelling of the Pi binder at `depth` — mirror of
`ReservedName::Pi` (`names.rs`). -/
def piName (d : Nat) : String := "__pi" ++ toString d

/-- The **canonical fragment**, mirroring what `compact_go` emits: at depth
`d` every arrow's binder is absent or the reserved `piName d`; codomains
live one deeper, everything else at the same depth (exactly the walk
`compact.rs` performs). Two `Canon` types compared at one position
therefore carry the *same* binder whenever both carry one. -/
def Canon : Nat → Ty → Prop
  | d, .fn n _ dom cod =>
      (n = none ∨ n = some (piName d)) ∧ Canon d dom ∧ Canon (d + 1) cod
  | d, .tuple ts => ∀ t ∈ ts, Canon d t
  | d, .record fs => ∀ e ∈ fs, Canon d e.2
  | d, .variant tags => ∀ e ∈ tags, Canon d e.2
  -- Claims are non-empty, mirroring `Type::refined`'s invariant: an empty
  -- claim set is not a refinement, it is the base, and the solver's flattening
  -- layer never emits one.
  | d, .refined b ps => ps ≠ [] ∧ Canon d b
  | _, .base _ | _, .uintRange _ | _, .dataSource _ | _, .txn => True
termination_by _ t => sizeOf t
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

/-- De Morgan for a decidable conjunction (no Mathlib in this development). -/
theorem not_and_or' {a b : Prop} [Decidable a] (h : ¬(a ∧ b)) : ¬a ∨ ¬b := by
  by_cases ha : a
  · exact Or.inr fun hb => h ⟨ha, hb⟩
  · exact Or.inl ha

theorem one_le_sizeOf (t : Ty) : 1 ≤ sizeOf t := by
  cases t <;> simp <;> omega

/-- A type with no top-level refinement layer is its own peel. Canonical
because a `refined` node whose claim set is empty would peel to nothing while
remaining a distinct term — a shape `Canon` excludes exactly as
`Type::refined` does. -/
theorem peel_nil_self {d : Nat} : {t : Ty} → Canon d t → t.peel.2 = [] → t.peel.1 = t
  | .base _, _, _ | .uintRange _, _, _ | .dataSource _, _, _ | .txn, _, _
  | .fn .., _, _ | .tuple _, _, _ | .record _, _, _ | .variant _, _, _ => rfl
  | .refined b p, hc, h => by
      rw [Canon] at hc
      simp [Ty.peel] at h
      exact absurd h.1 hc.1

theorem canon_peel_fst : (d : Nat) → (t : Ty) → Canon d t → Canon d t.peel.1
  | _, .base _, h => h
  | _, .uintRange _, h => h
  | _, .dataSource _, h => h
  | _, .txn, h => h
  | _, .fn .., h => h
  | _, .tuple _, h => h
  | _, .record _, h => h
  | _, .variant _, h => h
  | d, .refined b _, h => by
      have hb : Canon d b := by rw [Canon] at h; exact h.2
      simpa [Ty.peel] using canon_peel_fst d b hb
termination_by _ t => sizeOf t
decreasing_by simp_wf; omega

theorem canon_legNormal (d : Nat) (t : Ty) (rest : List (FieldKey × Ty))
    (h : Canon d t) : Canon d (legNormal t rest) := by
  cases t <;> simp [legNormal] <;> try exact h
  case refined b ps =>
    rw [Canon] at h
    split
    · exact h.2
    · split
      · exact h.2
      · rename_i hEmpty
        rw [Canon]
        exact ⟨by simpa using hEmpty, h.2⟩

theorem canon_legUnder : (d : Nat) → (t : Ty) → Canon d t → Canon d (legUnder t)
  | _, .base _, h => h
  | _, .uintRange _, h => h
  | _, .dataSource _, h => h
  | _, .txn, h => h
  | _, .fn .., h => h
  | _, .tuple _, h => h
  | _, .record _, h => h
  | _, .variant _, h => h
  | d, .refined b _, h => by rw [Canon] at h; simpa [legUnder] using h.2

theorem canon_partitionDomain {d : Nat} {t u : Ty} (h : Canon d t)
    (hd : partitionDomain t = some u) : Canon d u := by
  match t, hd with
  | .variant ((k0, p0) :: rest), hd =>
      simp only [partitionDomain] at hd
      split at hd
      · injection hd with hd
        subst hd
        have hp0 : Canon d p0 := by
          rw [Canon] at h
          exact h (k0, p0) (List.mem_cons_self ..)
        exact canon_legNormal d p0 rest hp0
      · exact absurd hd (by simp)

theorem canon_normFun {d : Nat} {t t' : Ty} (h : Canon d t)
    (hn : normFun t = some t') : Canon d t' := by
  match t, hn with
  | .fn n k dom c, hn =>
      simp only [normFun, Option.map_eq_some_iff] at hn
      obtain ⟨d', hd, rfl⟩ := hn
      rw [Canon] at h ⊢
      exact ⟨h.1, canon_partitionDomain h.2.1 hd, h.2.2⟩

theorem canon_normFun_getD {d : Nat} {t : Ty} (h : Canon d t) :
    Canon d ((normFun t).getD t) := by
  cases hn : normFun t with
  | none => simpa using h
  | some t' => simpa using canon_normFun h hn

theorem canon_fn_binder {d n k dom c} (h : Canon d (.fn n k dom c)) :
    n = none ∨ n = some (piName d) := by
  rw [Canon] at h; exact h.1

theorem canon_fn_dom {d n k dom c} (h : Canon d (.fn n k dom c)) :
    Canon d dom := by
  rw [Canon] at h; exact h.2.1

theorem canon_fn_cod {d n k dom c} (h : Canon d (.fn n k dom c)) :
    Canon (d + 1) c := by
  rw [Canon] at h; exact h.2.2

/-- The codomain correspondence a **canonical** edge mints acts as the
identity: both binders (when present) are the same reserved name, so the
extension is diagonal. This is the whole reason the σ-gap dissolves. -/
theorem codRen_canon_isId {d : Nat} {n0 n1 : Option String} {ρ : Ren}
    (h0 : n0 = none ∨ n0 = some (piName d))
    (h1 : n1 = none ∨ n1 = some (piName d)) (hρ : ρ.IsId) :
    (codRen n0 n1 ρ).IsId := by
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;>
    first
      | exact hρ
      | exact hρ.extend_diag _

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

/-- Under identity-acting environments the deficit is plain set
containment — so any two identity-acting environment pairs agree on it. -/
theorem deficit_isId_nil_iff {ρl ρr : Ren} (hl : ρl.IsId) (hr : ρr.IsId)
    {S T : List Pred} : deficit ρl ρr S T = [] ↔ ∀ p ∈ T, p ∈ S := by
  rw [deficit_eq_nil_iff]
  constructor
  · intro h p hp
    obtain ⟨q, hq, hqe⟩ := h p hp
    rw [Pred.rename_isId hl q, Pred.rename_isId hr p] at hqe
    exact hqe ▸ hq
  · intro h p hp
    exact ⟨p, h p hp, by rw [Pred.rename_isId hl p, Pred.rename_isId hr p]⟩

/-- Universal peel inversion: **every** rule leaves the peeled bases related
and the peeled refinement sets contained. For the head-constructor rules
both peels are `(t, [])`, so this is the derivation itself; for the
refinement rule it is exactly its premises. -/
theorem sub_peel_inv {ρl ρr : Ren} {x y : Ty} (h : Sub ρl ρr x y) :
    deficit ρl ρr x.peel.2 y.peel.2 = [] ∧ Sub ρl ρr x.peel.1 y.peel.1 := by
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
theorem sub_normFun {ρl ρr : Ren} {n0 k0 d0 c0 n1 k1 d1 c1}
    (h : Sub ρl ρr (.fn n0 k0 d0 c0) (.fn n1 k1 d1 c1)) :
    Sub ρl ρr ((normFun (.fn n0 k0 d0 c0)).getD (.fn n0 k0 d0 c0))
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
theorem sub_fn_rhs_shape {ρl ρr : Ren} {x : Ty} {nm km dm cm}
    (h : Sub ρl ρr x (.fn nm km dm cm)) (hx : x.peel.2 = []) :
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
theorem sub_fn_lhs_shape {ρl ρr : Ren} {z : Ty} {nm km dm cm}
    (h : Sub ρl ρr (.fn nm km dm cm) z) (hz : z.peel.2 = []) :
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

/-- Bundled induction hypothesis: transitivity for anything smaller, with
all six environments free (each identity-acting). The freedom is the point:
a chain's premises arrive under *their* environments and the conclusion is
wanted under a third pair, and for canonical types all of them act as the
identity, so no reconciliation morphism (σ) is ever needed. -/
def TransIH (n : Nat) : Prop :=
  ∀ (d : Nat) (a b c : Ty), sizeOf a + sizeOf b + sizeOf c ≤ n →
    Canon d a → Canon d b → Canon d c →
    ∀ {ρ1l ρ1r ρ2l ρ2r ρl ρr : Ren},
      ρ1l.IsId → ρ1r.IsId → ρ2l.IsId → ρ2r.IsId → ρl.IsId → ρr.IsId →
      Sub ρ1l ρ1r a b → Sub ρ2l ρ2r b c → Sub ρl ρr a c

/-- The function case, factored out so the three ways of concluding a
function edge are handled once. -/
theorem sub_trans_fn {n d : Nat} {n0 k0 d0 c0 nm km dm cm : _} {z : Ty}
    {ρ1l ρ1r ρ2l ρ2r ρl ρr : Ren}
    (IH : TransIH n)
    (hbound : sizeOf (Ty.fn n0 k0 d0 c0) + sizeOf (Ty.fn nm km dm cm)
      + sizeOf z ≤ n + 1)
    (hx : Canon d (.fn n0 k0 d0 c0)) (hy : Canon d (.fn nm km dm cm))
    (hz : Canon d z) (hzb : z.peel.2 = [])
    (h1l : ρ1l.IsId) (h1r : ρ1r.IsId) (h2l : ρ2l.IsId) (h2r : ρ2r.IsId)
    (hρl : ρl.IsId) (hρr : ρr.IsId)
    (h1 : Sub ρ1l ρ1r (.fn n0 k0 d0 c0) (.fn nm km dm cm))
    (h2 : Sub ρ2l ρ2r (.fn nm km dm cm) z) :
    Sub ρl ρr (.fn n0 k0 d0 c0) z := by
  obtain ⟨n1, k1, d1, c1, rfl⟩ := sub_fn_lhs_shape h2 hzb
  have e1 := sub_normFun h1
  have e2 := sub_normFun h2
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
  · -- At least one outer side normalizes: collapse and recurse.
    refine Sub.fnNorm hnorm (IH d _ _ _ ?_ (canon_normFun_getD hx)
      (canon_normFun_getD hy) (canon_normFun_getD hz)
      h1l h1r h2l h2r hρl hρr e1 e2)
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
      refine IH d _ _ _ ?_ hx (canon_normFun_getD hy) hz
        h1l h1r h2l h2r hρl hρr e1 e2
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
      have hdom_sz : sizeOf d1 + sizeOf dm + sizeOf d0 ≤ n := by
        simp only [Ty.fn.sizeOf_spec] at hbound
        omega
      have hcod_sz : sizeOf c0 + sizeOf cm + sizeOf c1 ≤ n := by
        simp only [Ty.fn.sizeOf_spec] at hbound
        omega
      -- Canonical binder facts feed the diagonal-correspondence lemma:
      -- every codomain environment in sight is identity-acting.
      have hb0 := canon_fn_binder hx
      have hbm := canon_fn_binder hy
      have hb1 := canon_fn_binder hz
      have hcod1_id : (codRen n0 nm ρ1l).IsId := codRen_canon_isId hb0 hbm h1l
      have hcod2_id : (codRen nm n1 ρ2l).IsId := codRen_canon_isId hbm hb1 h2l
      have hcodC_id : (codRen n0 n1 ρl).IsId := codRen_canon_isId hb0 hb1 hρl
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
              have hdom := IH d d1 dm d0 hdom_sz (canon_fn_dom hz)
                (canon_fn_dom hy) (canon_fn_dom hx)
                h2r h2l h1r h1l hρr hρl hdom2 hdom1
              have hcod := IH (d + 1) c0 cm c1 hcod_sz (canon_fn_cod hx)
                (canon_fn_cod hy) (canon_fn_cod hz)
                hcod1_id h1r hcod2_id h2r hcodC_id hρr hcod1 hcod2
              refine Sub.fnCompute hnx hnz (kindOk_trans hok1 hok2) ?_ hdom hcod
              rintro ⟨rfl, rfl⟩
              have hkm : km ≠ FunKind.data := fun h => hnd1 ⟨rfl, h⟩
              cases km with
              | data => exact hkm rfl
              | compute => exact hok2
          | fnData _ _ _ _ _ =>
              have hk0 : k0 ≠ FunKind.data := fun h => hnd1 ⟨h, rfl⟩
              cases k0 with
              | data => exact absurd rfl hk0
              | compute => exact absurd hok1 (by simp [kindOk])
      | fnData _ _ hdom1a hdom1b hcod1 =>
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
              have hdom := IH d d1 dm d0 hdom_sz (canon_fn_dom hz)
                (canon_fn_dom hy) (canon_fn_dom hx)
                h2r h2l h1r h1l hρr hρl hdom2 hdom1a
              have hcod := IH (d + 1) c0 cm c1 hcod_sz (canon_fn_cod hx)
                (canon_fn_cod hy) (canon_fn_cod hz)
                hcod1_id h1r hcod2_id h2r hcodC_id hρr hcod1 hcod2
              refine Sub.fnCompute hnx hnz hok2 ?_ hdom hcod
              rintro ⟨-, rfl⟩
              exact hnd2 ⟨rfl, rfl⟩
          | fnData _ _ hdom2a hdom2b hcod2 =>
              have hdomA := IH d d1 dm d0 hdom_sz (canon_fn_dom hz)
                (canon_fn_dom hy) (canon_fn_dom hx)
                h2r h2l h1r h1l hρr hρl hdom2a hdom1a
              have hdomB := IH d d0 dm d1 (by omega) (canon_fn_dom hx)
                (canon_fn_dom hy) (canon_fn_dom hz)
                h1l h1r h2l h2r hρl hρr hdom1b hdom2b
              have hcod := IH (d + 1) c0 cm c1 hcod_sz (canon_fn_cod hx)
                (canon_fn_cod hy) (canon_fn_cod hz)
                hcod1_id h1r hcod2_id h2r hcodC_id hρr hcod1 hcod2
              exact Sub.fnData hnx hnz hdomA hdomB hcod

/-- Fuel-bounded transitivity for the canonical fragment. -/
theorem sub_trans_aux : (n : Nat) → TransIH n
  | 0 => by
      intro d x y z hn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      have := one_le_sizeOf x
      have := one_le_sizeOf y
      have := one_le_sizeOf z
      omega
  | n + 1 => by
    intro d x y z hn hx hy hz ρ1l ρ1r ρ2l ρ2r ρl ρr h1l h1r h2l h2r hρl hρr
      h1 h2
    have IH : TransIH n := sub_trans_aux n
    by_cases hbare : x.peel.2 = [] ∧ y.peel.2 = [] ∧ z.peel.2 = []
    · obtain ⟨hxb, hyb, hzb⟩ := hbare
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
          exact sub_trans_fn IH (by omega) hx hy hz hzb
            h1l h1r h2l h2r hρl hρr (.fnNorm hg hp) h2
      | fnCompute a b c d' e f =>
          exact sub_trans_fn IH (by omega) hx hy hz hzb
            h1l h1r h2l h2r hρl hρr (.fnCompute a b c d' e f) h2
      | fnData a b c d' e =>
          exact sub_trans_fn IH (by omega) hx hy hz hzb
            h1l h1r h2l h2r hρl hρr (.fnData a b c d' e) h2
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
              refine IH d t0 bs[i] t1 ?_ ?_ ?_ ?_
                h1l h1r h2l h2r hρl hρr (hpt1 i t0 bs[i] h0 hb)
                (hpt2 i bs[i] t1 hb h1')
              · simp only [Ty.tuple.sizeOf_spec] at hn
                omega
              · rw [Canon] at hx; exact hx t0 hm0
              · rw [Canon] at hy; exact hy bs[i] hmm
              · rw [Canon] at hz; exact hz t1 hm1
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
                refine IH d t0 tm t1 ?_ ?_ ?_ ?_
                  h1l h1r h2l h2r hρl hρr (hsub1 nkey t0 tm hmm hlk)
                  (hsub2 nkey tm t1 hm htm)
                · simp only [Ty.record.sizeOf_spec] at hn
                  simp only [Prod.mk.sizeOf_spec] at s0 sm s1
                  omega
                · rw [Canon] at hx; exact hx (nkey, t0) hm0
                · rw [Canon] at hy; exact hy (nkey, tm) hmm
                · rw [Canon] at hz; exact hz (nkey, t1) hm
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
                refine IH d t0 tm t1 ?_ ?_ ?_ ?_
                  h1l h1r h2l h2r hρl hρr (hsub1 key t0 tm hm htm)
                  (hsub2 key tm t1 hmm hlk)
                · simp only [Ty.variant.sizeOf_spec] at hn
                  simp only [Prod.mk.sizeOf_spec] at s0 sm s1
                  omega
                · rw [Canon] at hx; exact hx (key, t0) hm
                · rw [Canon] at hy; exact hy (key, tm) hmm
                · rw [Canon] at hz; exact hz (key, t1) hm1
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
    · -- Some side carries a refinement layer: peel all three, compose the
      -- set containments, recurse on the bases, re-wrap.
      obtain ⟨hd1, hs1⟩ := sub_peel_inv h1
      obtain ⟨hd2, hs2⟩ := sub_peel_inv h2
      have hc1 := (deficit_isId_nil_iff h1l h1r).mp hd1
      have hc2 := (deficit_isId_nil_iff h2l h2r).mp hd2
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
      have hbase := IH d x.peel.1 y.peel.1 z.peel.1 (by omega)
        (canon_peel_fst d x hx) (canon_peel_fst d y hy) (canon_peel_fst d z hz)
        h1l h1r h2l h2r hρl hρr hs1 hs2
      have hdef : deficit ρl ρr x.peel.2 z.peel.2 = [] :=
        (deficit_isId_nil_iff hρl hρr).mpr fun p hp => hc1 p (hc2 p hp)
      by_cases hxz : x.peel.2 = [] ∧ z.peel.2 = []
      · rw [peel_nil_self hx hxz.1, peel_nil_self hz hxz.2] at hbase
        exact hbase
      · exact Sub.refined rfl rfl (not_and_or' hxz) hdef hbase

/-- **Transitivity for the canonical fragment**, environments free: any
chain composes under any identity-acting environments — no `NoPi`
restriction, no σ-side condition. Canonical binders are what every type
leaving the solver carries (`compact.rs` / `spec_key.rs`), so this is
transitivity for the system's actual types. -/
theorem sub_trans {d : Nat} {x y z : Ty}
    (hx : Canon d x) (hy : Canon d y) (hz : Canon d z)
    {ρ1l ρ1r ρ2l ρ2r ρl ρr : Ren}
    (h1l : ρ1l.IsId) (h1r : ρ1r.IsId) (h2l : ρ2l.IsId) (h2r : ρ2r.IsId)
    (hρl : ρl.IsId) (hρr : ρr.IsId)
    (h1 : Sub ρ1l ρ1r x y) (h2 : Sub ρ2l ρ2r y z) : Sub ρl ρr x z :=
  sub_trans_aux (sizeOf x + sizeOf y + sizeOf z) d x y z (Nat.le_refl _)
    hx hy hz h1l h1r h2l h2r hρl hρr h1 h2

/-- **Pure transitivity** at the identity environment — the form the ground
oracle exercises. -/
theorem sub_trans_id {d : Nat} {x y z : Ty}
    (hx : Canon d x) (hy : Canon d y) (hz : Canon d z)
    (h1 : Sub .id .id x y) (h2 : Sub .id .id y z) : Sub .id .id x z :=
  sub_trans hx hy hz Ren.isId_id Ren.isId_id Ren.isId_id Ren.isId_id
    Ren.isId_id Ren.isId_id h1 h2

/-- End-to-end: the triangle that **refuted** transitivity under the bridge
arm is an instance of the general theorem (its binders are all `none`,
which is canonical at any depth). -/
example : Sub .id .id transCex.a transCex.c :=
  sub_trans_id (d := 0)
    (by simp [Canon, transCex.a, transCex.gate, transCex.recA])
    (by simp [Canon, transCex.b, transCex.recA])
    (by simp [Canon, transCex.c, transCex.recAB])
    transCex.sub_a_b transCex.sub_b_c

/-! ## Claim order is not observable

`Type::Refinement` carries a `RefinementSet` — unordered and deduplicated —
while the model *represents* the claims as a `List Pred` so that `Ty.beq` stays
propositional equality. The two agree only if the relation genuinely cannot
see the list structure, which is what this section proves rather than asserts.

The statements are in terms of **containment**, not permutation, because that
is what `deficit` actually uses: it asks whether each demanded claim has *some*
supplier, so a supplier list may be reordered, duplicated, or widened freely.
Permutation and dedup-invariance are corollaries (`sub_claims_perm`), which is
exactly the latitude the Rust representation takes.
-/

/-- Widening (hence reordering or duplicating) the **supplied** claims
preserves the relation. -/
theorem sub_claims_left {ρl ρr : Ren} {b z : Ty} {ps qs : List Pred}
    (hne : qs ≠ []) (hsupp : ∀ p ∈ ps, p ∈ qs)
    (h : Sub ρl ρr (.refined b ps) z) : Sub ρl ρr (.refined b qs) z := by
  obtain ⟨hdef, hbase⟩ := sub_peel_inv h
  refine Sub.refined rfl rfl (.inl ?_) ?_ hbase
  · simp
    exact fun hc => absurd hc hne
  · rw [deficit_eq_nil_iff] at hdef ⊢
    intro p hp
    obtain ⟨q, hq, hqe⟩ := hdef p hp
    refine ⟨q, ?_, hqe⟩
    simp [Ty.peel] at hq ⊢
    rcases hq with hq | hq
    · exact Or.inl (hsupp q hq)
    · exact Or.inr hq

/-- Narrowing (hence reordering or deduplicating) the **demanded** claims
preserves the relation. -/
theorem sub_claims_right {ρl ρr : Ren} {x b : Ty} {ps qs : List Pred}
    (hne : qs ≠ []) (hdem : ∀ p ∈ qs, p ∈ ps)
    (h : Sub ρl ρr x (.refined b ps)) : Sub ρl ρr x (.refined b qs) := by
  obtain ⟨hdef, hbase⟩ := sub_peel_inv h
  refine Sub.refined rfl rfl (.inr ?_) ?_ hbase
  · simp
    exact fun hc => absurd hc hne
  · rw [deficit_eq_nil_iff] at hdef ⊢
    intro p hp
    simp at hp
    refine hdef p ?_
    simp [Ty.peel]
    rcases hp with hp | hp
    · exact Or.inl (hdem p hp)
    · exact Or.inr hp

/-- **Claim order is not observable**: two claim lists with the same members
are interchangeable on either side of the relation. This is the model's
statement of what `RefinementSet` guarantees — that making the representation
unordered changed no verdict, so the arrival order two bounds happened to meet
in cannot reach typing. -/
theorem sub_claims_perm {ρl ρr : Ren} {b z : Ty} {ps qs : List Pred}
    (hne : qs ≠ []) (hmem : ∀ p, p ∈ ps ↔ p ∈ qs) :
    Sub ρl ρr (.refined b ps) z ↔ Sub ρl ρr (.refined b qs) z := by
  have hqne : ps ≠ [] := by
    intro hc
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil qs hne
    exact absurd ((hmem q).mpr hq) (by simp [hc])
  exact ⟨sub_claims_left hne (fun p hp => (hmem p).mp hp),
         sub_claims_left hqne (fun p hp => (hmem p).mpr hp)⟩

/-- The same, in demand position. -/
theorem sub_claims_perm_right {ρl ρr : Ren} {x b : Ty} {ps qs : List Pred}
    (hne : qs ≠ []) (hmem : ∀ p, p ∈ ps ↔ p ∈ qs) :
    Sub ρl ρr x (.refined b ps) ↔ Sub ρl ρr x (.refined b qs) := by
  have hqne : ps ≠ [] := by
    intro hc
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil qs hne
    exact absurd ((hmem q).mpr hq) (by simp [hc])
  exact ⟨sub_claims_right hne (fun p hp => (hmem p).mpr hp),
         sub_claims_right hqne (fun p hp => (hmem p).mp hp)⟩

end CclFormal
