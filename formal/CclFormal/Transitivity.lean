import CclFormal.Equiv
import CclFormal.Props

/-!
# Transitivity of the ground subtype relation

`Sub` is transitive on well-formed types — stated directly, with no fragment
restriction and no environment side conditions.

The history is the point (see `src/ccl/design/type-inference.md`, "Scoped
inference variables: stored fragments close against a telescope"). With
refinements referencing their binders by *name*, chaining dependent codomains
produced premises that viewed the middle type under different renames,
composing only through a reconciliation morphism — the σ-gap, the model
analogue of `constrain.rs :: bridge_holder_gap` — and transitivity was
provable only for a canonical-spelling fragment under identity-acting
environments. With refinements closed into indices at construction
(`Pred.piBound`), the relation carries no environments, two α-variant
function types are the same term, and the gap is not dissolved but never formed:
this file's statement quantifies over nothing but the three types.

Well-formedness is the one hypothesis, and only its refinements-non-emptiness is
load-bearing here: a degenerate `refined b []` is a distinct term that peels
to its base, so the re-wrap step could not restate it — and it is not a type
(`Type::refined` never builds one; it is not even reflexive, since
`Sub.refined`'s guard demands a real layer).
-/

namespace CclFormal

/-- De Morgan for a decidable conjunction (no Mathlib in this development). -/
theorem not_and_or' {a b : Prop} [Decidable a] (h : ¬(a ∧ b)) : ¬a ∨ ¬b := by
  by_cases ha : a
  · exact Or.inr fun hb => h ⟨ha, hb⟩
  · exact Or.inl ha

theorem one_le_sizeOf (t : Ty) : 1 ≤ sizeOf t := by
  cases t <;> simp <;> omega

/-- A type with no top-level refinement layer is its own peel — for
well-formed types, whose refinement sets are non-empty (`Type::refined` never
builds a `refined b []`, which would peel to its base while remaining a
distinct term). -/
theorem peel_nil_self : {t : Ty} → t.WF → t.peel.2 = [] → t.peel.1 = t
  | .base _, _, _ | .uintRange _, _, _ | .dataSource _, _, _ | .txn, _, _
  | .fn .., _, _ | .tuple _, _, _ | .record _, _, _ | .variant _, _, _ => rfl
  | .refined _ _, .refined hne _ _, h => by
      simp [Ty.peel] at h
      exact absurd h.1 hne

theorem deficit_eq_nil_iff {l r : List Pred} :
    deficit l r = [] ↔ ∀ p ∈ r, p ∈ l := by
  unfold deficit
  rw [List.filter_eq_nil_iff]
  constructor
  · intro h p hp
    have := h p hp
    simp only [Bool.not_eq_true', Bool.not_eq_false] at this
    exact List.mem_of_elem_eq_true this
  · intro h p hp
    simp only [Bool.not_eq_true', Bool.not_eq_false]
    exact List.elem_eq_true_of_mem (h p hp)

/-- Universal peel inversion: **every** rule leaves the peeled bases related
and the peeled refinement sets contained. For the head-constructor rules
both peels are `(t, [])`, so this is the derivation itself; for the
refinement rule it is exactly its premises. -/
theorem sub_peel_inv {x y : Ty} (h : Sub x y) :
    deficit x.peel.2 y.peel.2 = [] ∧ Sub x.peel.1 y.peel.1 := by
  cases h with
  | base b => exact ⟨rfl, .base b⟩
  | uintRange n => exact ⟨rfl, .uintRange n⟩
  | dataSource s => exact ⟨rfl, .dataSource s⟩
  | txn => exact ⟨rfl, .txn⟩
  | fnCompute h1 h2 h3 h4 => exact ⟨rfl, .fnCompute h1 h2 h3 h4⟩
  | fnData h1 h2 h3 => exact ⟨rfl, .fnData h1 h2 h3⟩
  | tuple h1 h2 => exact ⟨rfl, .tuple h1 h2⟩
  | record h1 h2 => exact ⟨rfl, .record h1 h2⟩
  | variant h1 h2 => exact ⟨rfl, .variant h1 h2⟩
  | refined hpl hpr _ hdef hbase =>
      rw [hpl, hpr]
      exact ⟨hdef, hbase⟩

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
theorem sub_fn_rhs_shape {x : Ty} {nm km dm cm}
    (h : Sub x (.fn nm km dm cm)) (hx : x.peel.2 = []) :
    ∃ n0 k0 d0 c0, x = .fn n0 k0 d0 c0 := by
  cases h with
  | fnCompute _ _ _ _ => exact ⟨_, _, _, _, rfl⟩
  | fnData _ _ _ => exact ⟨_, _, _, _, rfl⟩
  | refined hpl hpr hg _ _ =>
      rw [hpl] at hx
      simp only [Ty.peel, Prod.mk.injEq] at hpr hx
      obtain ⟨-, hr⟩ := hpr
      subst hr
      rcases hg with hg | hg
      · exact absurd hx hg
      · exact absurd rfl hg

/-- Shape inversion: a bare type above a function type is a function type. -/
theorem sub_fn_lhs_shape {z : Ty} {nm km dm cm}
    (h : Sub (.fn nm km dm cm) z) (hz : z.peel.2 = []) :
    ∃ n1 k1 d1 c1, z = .fn n1 k1 d1 c1 := by
  cases h with
  | fnCompute _ _ _ _ => exact ⟨_, _, _, _, rfl⟩
  | fnData _ _ _ => exact ⟨_, _, _, _, rfl⟩
  | refined hpl hpr hg _ _ =>
      rw [hpr] at hz
      simp only [Ty.peel, Prod.mk.injEq] at hpl hz
      obtain ⟨-, hl⟩ := hpl
      subst hl
      rcases hg with hg | hg
      · exact absurd rfl hg
      · exact absurd hz hg

/-- Member well-formedness extractors, the recursion's plumbing. -/
theorem Ty.WF.fn_dom {n k d c} (h : Ty.WF (.fn n k d c)) : d.WF := by
  cases h with | fn hd _ => exact hd

theorem Ty.WF.fn_cod {n k d c} (h : Ty.WF (.fn n k d c)) : c.WF := by
  cases h with | fn _ hc => exact hc

theorem Ty.WF.tuple_mem {ts t} (h : Ty.WF (.tuple ts)) (hm : t ∈ ts) : t.WF := by
  cases h with | tuple hts => exact hts t hm

theorem Ty.WF.record_mem {fs : List (String × Ty)} {n t}
    (h : Ty.WF (.record fs)) (hm : (n, t) ∈ fs) : t.WF := by
  cases h with | record _ hf => exact hf (n, t) hm

theorem Ty.WF.variant_mem {tags : List (FieldKey × Ty)} {k t}
    (h : Ty.WF (.variant tags)) (hm : (k, t) ∈ tags) : t.WF := by
  cases h with | variant _ ht => exact ht (k, t) hm

/-- Bundled induction hypothesis: transitivity for anything smaller. -/
def TransIH (n : Nat) : Prop :=
  ∀ (a b c : Ty), sizeOf a + sizeOf b + sizeOf c ≤ n →
    a.WF → b.WF → c.WF → Sub a b → Sub b c → Sub a c

/-- The function case, factored out so the three ways of concluding a
function edge are handled once. -/
theorem sub_trans_fn {n : Nat} {n0 k0 d0 c0 nm km dm cm : _} {z : Ty}
    (IH : TransIH n)
    (hbound : sizeOf (Ty.fn n0 k0 d0 c0) + sizeOf (Ty.fn nm km dm cm)
      + sizeOf z ≤ n + 1)
    (hx : Ty.WF (.fn n0 k0 d0 c0)) (hy : Ty.WF (.fn nm km dm cm))
    (hz : Ty.WF z) (hzb : z.peel.2 = [])
    (h1 : Sub (.fn n0 k0 d0 c0) (.fn nm km dm cm))
    (h2 : Sub (.fn nm km dm cm) z) :
    Sub (.fn n0 k0 d0 c0) z := by
  obtain ⟨n1, k1, d1, c1, rfl⟩ := sub_fn_lhs_shape h2 hzb
  have hdom_sz : sizeOf d1 + sizeOf dm + sizeOf d0 ≤ n := by
    simp only [Ty.fn.sizeOf_spec] at hbound
    omega
  have hcod_sz : sizeOf c0 + sizeOf cm + sizeOf c1 ≤ n := by
    simp only [Ty.fn.sizeOf_spec] at hbound
    omega
  cases h1 with
  | refined hpl hpr hg _ _ =>
      simp only [Ty.peel, Prod.mk.injEq] at hpl hpr
      obtain ⟨-, hl⟩ := hpl
      obtain ⟨-, hr⟩ := hpr
      subst hl; subst hr
      rcases hg with hg | hg <;> exact absurd rfl hg
  | fnCompute hok1 hnd1 hdom1 hcod1 =>
      cases h2 with
      | refined hpl hpr hg _ _ =>
          simp only [Ty.peel, Prod.mk.injEq] at hpl hpr
          obtain ⟨-, hl⟩ := hpl
          obtain ⟨-, hr⟩ := hpr
          subst hl; subst hr
          rcases hg with hg | hg <;> exact absurd rfl hg
      | fnCompute hok2 hnd2 hdom2 hcod2 =>
          have hdom := IH d1 dm d0 hdom_sz hz.fn_dom hy.fn_dom hx.fn_dom
            hdom2 hdom1
          have hcod := IH c0 cm c1 hcod_sz hx.fn_cod hy.fn_cod hz.fn_cod
            hcod1 hcod2
          refine Sub.fnCompute (kindOk_trans hok1 hok2) ?_ hdom hcod
          rintro ⟨rfl, rfl⟩
          have hkm : km ≠ FunKind.data := fun h => hnd1 ⟨rfl, h⟩
          cases km with
          | data => exact hkm rfl
          | compute => exact hok2
      | fnData _ _ _ =>
          have hk0 : k0 ≠ FunKind.data := fun h => hnd1 ⟨h, rfl⟩
          cases k0 with
          | data => exact absurd rfl hk0
          | compute => exact absurd hok1 (by simp [kindOk])
  | fnData hdom1a hdom1b hcod1 =>
      cases h2 with
      | refined hpl hpr hg _ _ =>
          simp only [Ty.peel, Prod.mk.injEq] at hpl hpr
          obtain ⟨-, hl⟩ := hpl
          obtain ⟨-, hr⟩ := hpr
          subst hl; subst hr
          rcases hg with hg | hg <;> exact absurd rfl hg
      | fnCompute hok2 hnd2 hdom2 hcod2 =>
          have hdom := IH d1 dm d0 hdom_sz hz.fn_dom hy.fn_dom hx.fn_dom
            hdom2 hdom1a
          have hcod := IH c0 cm c1 hcod_sz hx.fn_cod hy.fn_cod hz.fn_cod
            hcod1 hcod2
          refine Sub.fnCompute hok2 ?_ hdom hcod
          rintro ⟨-, rfl⟩
          exact hnd2 ⟨rfl, rfl⟩
      | fnData hdom2a hdom2b hcod2 =>
          have hdomA := IH d1 dm d0 hdom_sz hz.fn_dom hy.fn_dom hx.fn_dom
            hdom2a hdom1a
          have hdomB := IH d0 dm d1 (by omega) hx.fn_dom hy.fn_dom hz.fn_dom
            hdom1b hdom2b
          have hcod := IH c0 cm c1 hcod_sz hx.fn_cod hy.fn_cod hz.fn_cod
            hcod1 hcod2
          exact Sub.fnData hdomA hdomB hcod

/-- Fuel-bounded transitivity. -/
theorem sub_trans_aux : (n : Nat) → TransIH n
  | 0 => by
      intro x y z hn _ _ _ _ _
      have := one_le_sizeOf x
      have := one_le_sizeOf y
      have := one_le_sizeOf z
      omega
  | n + 1 => by
    intro x y z hn hx hy hz h1 h2
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
      | fnCompute a b c d' =>
          exact sub_trans_fn IH (by omega) hx hy hz hzb
            (.fnCompute a b c d') h2
      | fnData a b c =>
          exact sub_trans_fn IH (by omega) hx hy hz hzb
            (.fnData a b c) h2
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
              refine IH t0 bs[i] t1 ?_ (hx.tuple_mem hm0) (hy.tuple_mem hmm)
                (hz.tuple_mem hm1) (hpt1 i t0 bs[i] h0 hb)
                (hpt2 i bs[i] t1 hb h1')
              simp only [Ty.tuple.sizeOf_spec] at hn
              omega
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
                refine IH t0 tm t1 ?_ (hx.record_mem hm0) (hy.record_mem hmm)
                  (hz.record_mem hm) (hsub1 nkey t0 tm hmm hlk)
                  (hsub2 nkey tm t1 hm htm)
                simp only [Ty.record.sizeOf_spec] at hn
                simp only [Prod.mk.sizeOf_spec] at s0 sm s1
                omega
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
                refine IH t0 tm t1 ?_ (hx.variant_mem hm) (hy.variant_mem hmm)
                  (hz.variant_mem hm1) (hsub1 key t0 tm hm htm)
                  (hsub2 key tm t1 hmm hlk)
                simp only [Ty.variant.sizeOf_spec] at hn
                simp only [Prod.mk.sizeOf_spec] at s0 sm s1
                omega
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
      have hc1 := deficit_eq_nil_iff.mp hd1
      have hc2 := deficit_eq_nil_iff.mp hd2
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
        hx.peel_fst hy.peel_fst hz.peel_fst hs1 hs2
      have hdef : deficit x.peel.2 z.peel.2 = [] :=
        deficit_eq_nil_iff.mpr fun p hp => hc1 p (hc2 p hp)
      by_cases hxz : x.peel.2 = [] ∧ z.peel.2 = []
      · rw [peel_nil_self hx hxz.1, peel_nil_self hz hxz.2] at hbase
        exact hbase
      · exact Sub.refined rfl rfl (not_and_or' hxz) hdef hbase

/-- **Transitivity**, with no fragment restriction: any chain of well-formed
types composes. The former canonical-fragment statement and its six
identity-acting environments are subsumed — closing into indices leaves the
relation nothing to reconcile. -/
theorem sub_trans {x y z : Ty} (hx : x.WF) (hy : y.WF) (hz : z.WF)
    (h1 : Sub x y) (h2 : Sub y z) : Sub x z :=
  sub_trans_aux (sizeOf x + sizeOf y + sizeOf z) x y z (Nat.le_refl _)
    hx hy hz h1 h2

/-! ## Claim order is not observable

`Type::Refinement` layers carry refinements whose order is an artifact of
arrival, while the model *represents* the refinements as a `List Pred` so that
`Ty.beq` stays propositional equality. The two agree only if the relation
genuinely cannot see the list structure, which is what this section proves
rather than asserts.

The statements are in terms of **containment**, not permutation, because that
is what `deficit` actually uses: it asks whether each demanded refinement has *some*
supplier, so a supplier list may be reordered, duplicated, or widened freely.
Permutation and dedup-invariance are corollaries (`sub_refinements_perm`), which is
exactly the latitude the Rust representation takes.
-/

/-- Widening (hence reordering or duplicating) the **supplied** refinements
preserves the relation. -/
theorem sub_refinements_left {b z : Ty} {ps qs : List Pred}
    (hne : qs ≠ []) (hsupp : ∀ p ∈ ps, p ∈ qs)
    (h : Sub (.refined b ps) z) : Sub (.refined b qs) z := by
  obtain ⟨hdef, hbase⟩ := sub_peel_inv h
  refine Sub.refined rfl rfl (.inl ?_) ?_ hbase
  · simp
    exact fun hc => absurd hc hne
  · rw [deficit_eq_nil_iff] at hdef ⊢
    intro p hp
    have hq := hdef p hp
    simp [Ty.peel] at hq ⊢
    rcases hq with hq | hq
    · exact Or.inl (hsupp p hq)
    · exact Or.inr hq

/-- Narrowing (hence reordering or deduplicating) the **demanded** refinements
preserves the relation. -/
theorem sub_refinements_right {x b : Ty} {ps qs : List Pred}
    (hne : qs ≠ []) (hdem : ∀ p ∈ qs, p ∈ ps)
    (h : Sub x (.refined b ps)) : Sub x (.refined b qs) := by
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

/-- **Claim order is not observable**: two refinement lists with the same members
are interchangeable on either side of the relation — the arrival order two
bounds happened to meet in cannot reach typing. -/
theorem sub_refinements_perm {b z : Ty} {ps qs : List Pred}
    (hne : qs ≠ []) (hmem : ∀ p, p ∈ ps ↔ p ∈ qs) :
    Sub (.refined b ps) z ↔ Sub (.refined b qs) z := by
  have hqne : ps ≠ [] := by
    intro hc
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil qs hne
    exact absurd ((hmem q).mpr hq) (by simp [hc])
  exact ⟨sub_refinements_left hne (fun p hp => (hmem p).mp hp),
         sub_refinements_left hqne (fun p hp => (hmem p).mpr hp)⟩

/-- The same, in demand position. -/
theorem sub_refinements_perm_right {x b : Ty} {ps qs : List Pred}
    (hne : qs ≠ []) (hmem : ∀ p, p ∈ ps ↔ p ∈ qs) :
    Sub x (.refined b ps) ↔ Sub x (.refined b qs) := by
  have hqne : ps ≠ [] := by
    intro hc
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil qs hne
    exact absurd ((hmem q).mpr hq) (by simp [hc])
  exact ⟨sub_refinements_right hne (fun p hp => (hmem p).mpr hp),
         sub_refinements_right hqne (fun p hp => (hmem p).mp hp)⟩

end CclFormal
