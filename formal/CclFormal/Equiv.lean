import CclFormal.Decide

/-!
# Checker ↔ relation: soundness, completeness, decidability

`subCheck_iff_sub` proves the executable checker decides exactly the
declarative relation, giving `Decidable (Sub ρl ρr lhs rhs)` — the ground
subtype relation is decidable, and every `#guard` in `Decide.lean` is
therefore a fact about `Sub` itself, not just about the checker.
-/

namespace CclFormal

theorem kindOkB_iff {k0 k1 : FunKind} : kindOkB k0 k1 = true ↔ kindOk k0 k1 := by
  cases k0 <;> cases k1 <;> simp [kindOkB, kindOk]

theorem subSeq_iff (ρl ρr : Ren) :
    ∀ a b, subSeq ρl ρr a b = true ↔
      (b.length ≤ a.length ∧
        ∀ (i : Nat) t0 t1, a[i]? = some t0 → b[i]? = some t1 →
          subCheck ρl ρr t0 t1 = true)
  | a, [] => by simp [subSeq]
  | [], _ :: _ => by simp [subSeq]
  | t0 :: a, t1 :: b => by
      simp only [subSeq, Bool.and_eq_true, subSeq_iff ρl ρr a b,
        List.length_cons]
      constructor
      · rintro ⟨h0, hlen, hrest⟩
        refine ⟨Nat.succ_le_succ hlen, ?_⟩
        intro i u0 u1 hu0 hu1
        match i with
        | 0 =>
            simp at hu0 hu1
            subst hu0; subst hu1
            exact h0
        | j + 1 =>
            simp at hu0 hu1
            exact hrest j u0 u1 hu0 hu1
      · intro ⟨hlen, hall⟩
        refine ⟨hall 0 t0 t1 (by simp) (by simp),
          Nat.le_of_succ_le_succ hlen, ?_⟩
        intro j u0 u1 h0 h1
        exact hall (j + 1) u0 u1 (by simpa using h0) (by simpa using h1)

theorem subFields_iff (ρl ρr : Ren) (a : List (String × Ty)) :
    ∀ b, subFields ρl ρr a b = true ↔
      ((∀ n t1, (n, t1) ∈ b → (lookupBy a n).isSome) ∧
        ∀ n t0 t1, (n, t1) ∈ b → lookupBy a n = some t0 →
          subCheck ρl ρr t0 t1 = true)
  | [] => by simp [subFields]
  | (n1, t1) :: rest => by
      simp only [subFields, Bool.and_eq_true, subFields_iff ρl ρr a rest]
      cases hlk : lookupBy a n1 with
      | none =>
          simp only [Bool.false_eq_true, false_and]
          constructor
          · exact fun h => h.elim
          · rintro ⟨hsome, _⟩
            have := hsome n1 t1 (List.mem_cons_self ..)
            rw [hlk] at this
            exact absurd this (by simp)
      | some t0 =>
          constructor
          · rintro ⟨h0, hsome, hsub⟩
            constructor
            · intro n u hm
              rcases List.mem_cons.mp hm with heq | hmem
              · injection heq with h1 h2
                subst h1
                rw [hlk]; rfl
              · exact hsome n u hmem
            · intro n u0 u1 hm hl
              rcases List.mem_cons.mp hm with heq | hmem
              · injection heq with h1 h2
                subst h1; subst h2
                rw [hlk] at hl
                injection hl with h
                subst h
                exact h0
              · exact hsub n u0 u1 hmem hl
          · rintro ⟨hsome, hsub⟩
            exact ⟨hsub n1 t0 t1 (List.mem_cons_self ..) hlk,
              fun n u hm => hsome n u (List.mem_cons_of_mem _ hm),
              fun n u0 u1 hm hl => hsub n u0 u1 (List.mem_cons_of_mem _ hm) hl⟩

theorem subTags_iff (ρl ρr : Ren) (b : List (FieldKey × Ty)) :
    ∀ a, subTags ρl ρr b a = true ↔
      ((∀ k t0, (k, t0) ∈ a → (lookupBy b k).isSome) ∧
        ∀ k t0 t1, (k, t0) ∈ a → lookupBy b k = some t1 →
          subCheck ρl ρr t0 t1 = true)
  | [] => by simp [subTags]
  | (k0, t0) :: rest => by
      simp only [subTags, Bool.and_eq_true, subTags_iff ρl ρr b rest]
      cases hlk : lookupBy b k0 with
      | none =>
          simp only [Bool.false_eq_true, false_and]
          constructor
          · exact fun h => h.elim
          · rintro ⟨hsome, _⟩
            have := hsome k0 t0 (List.mem_cons_self ..)
            rw [hlk] at this
            exact absurd this (by simp)
      | some t1 =>
          constructor
          · rintro ⟨h0, hsome, hsub⟩
            constructor
            · intro k u hm
              rcases List.mem_cons.mp hm with heq | hmem
              · injection heq with h1 h2
                subst h1
                rw [hlk]; rfl
              · exact hsome k u hmem
            · intro k u0 u1 hm hl
              rcases List.mem_cons.mp hm with heq | hmem
              · injection heq with h1 h2
                subst h1; subst h2
                rw [hlk] at hl
                injection hl with h
                subst h
                exact h0
              · exact hsub k u0 u1 hmem hl
          · rintro ⟨hsome, hsub⟩
            exact ⟨hsub k0 t0 t1 (List.mem_cons_self ..) hlk,
              fun k u hm => hsome k u (List.mem_cons_of_mem _ hm),
              fun k u0 u1 hm hl => hsub k u0 u1 (List.mem_cons_of_mem _ hm) hl⟩

/-- **Soundness**: an accepting run of the checker is a derivation. -/
theorem sub_of_subCheck :
    ∀ (lhs rhs : Ty) (ρl ρr : Ren),
      subCheck ρl ρr lhs rhs = true → Sub ρl ρr lhs rhs
  | lhs, rhs, ρl, ρr, h => by
    rw [subCheck.eq_def] at h
    split at h
    -- Leaves.
    · exact eq_of_beq h ▸ Sub.base _
    · exact eq_of_beq h ▸ Sub.uintRange _
    · exact eq_of_beq h ▸ Sub.dataSource _
    · exact Sub.txn
    -- Function edge.
    · rename_i n0 k0 d0 c0 n1 k1 d1 c1
      rw [Bool.and_eq_true, Bool.and_eq_true] at h
      obtain ⟨⟨hok, hdom⟩, hcod⟩ := h
      have hcodS := sub_of_subCheck c0 c1 (codRen n0 n1 ρl) ρr hcod
      split at hdom
      · -- data-data: invariant domains.
        rename_i hdd
        rw [Bool.and_eq_true] at hdd
        have hk0 : k0 = .data := by simpa using hdd.1
        have hk1 : k1 = .data := by simpa using hdd.2
        subst hk0; subst hk1
        rw [Bool.and_eq_true] at hdom
        exact Sub.fnData
          (sub_of_subCheck d1 d0 ρr ρl hdom.1)
          (sub_of_subCheck d0 d1 ρl ρr hdom.2) hcodS
      · rename_i hdd
        have hnd : ¬(k0 = .data ∧ k1 = .data) := by
          rintro ⟨rfl, rfl⟩
          exact hdd (by simp)
        exact Sub.fnCompute (kindOkB_iff.mp hok) hnd
          (sub_of_subCheck d1 d0 ρr ρl hdom) hcodS
    -- Tuple.
    · rename_i a b
      obtain ⟨hlen, hpt⟩ := (subSeq_iff ρl ρr a b).mp h
      refine Sub.tuple hlen fun i t0 t1 h0 h1 => ?_
      have hm0 := List.mem_of_getElem? h0
      have hm1 := List.mem_of_getElem? h1
      have hs0 := List.sizeOf_lt_of_mem hm0
      have hs1 := List.sizeOf_lt_of_mem hm1
      exact sub_of_subCheck t0 t1 ρl ρr (hpt i t0 t1 h0 h1)
    -- Record.
    · rename_i a b
      obtain ⟨hsome, hsub⟩ := (subFields_iff ρl ρr a b).mp h
      refine Sub.record hsome fun n t0 t1 hm hlk => ?_
      have hs0 := lookupBy_sizeOf hlk
      have hs1 : sizeOf t1 < sizeOf b := by
        have h' := List.sizeOf_lt_of_mem hm
        rw [Prod.mk.sizeOf_spec] at h'
        omega
      exact sub_of_subCheck t0 t1 ρl ρr (hsub n t0 t1 hm hlk)
    -- Variant.
    · rename_i a b
      obtain ⟨hsome, hsub⟩ := (subTags_iff ρl ρr b a).mp h
      refine Sub.variant hsome fun k t0 t1 hm hlk => ?_
      have hs1 := lookupBy_sizeOf hlk
      have hs0 : sizeOf t0 < sizeOf a := by
        have h' := List.sizeOf_lt_of_mem hm
        rw [Prod.mk.sizeOf_spec] at h'
        omega
      exact sub_of_subCheck t0 t1 ρl ρr (hsub k t0 t1 hm hlk)
    -- Refinement arm / mismatch catch-all. `lhs`/`rhs` stay un-substituted
    -- here (the catch-all pins no constructors), which is exactly what
    -- `Sub.refined`'s generic conclusion wants.
    · split at h
      · exact absurd h (by simp)
      · rename_i hne
        rw [Bool.and_eq_true] at h
        obtain ⟨hdef, hbase⟩ := h
        have hlt := Ty.peel_sum_lt lhs rhs hne
        refine Sub.refined rfl rfl ?_ ?_
          (sub_of_subCheck lhs.peel.1 rhs.peel.1 ρl ρr hbase)
        · cases hl : lhs.peel.2 with
          | nil =>
              cases hr : rhs.peel.2 with
              | nil => exact absurd ⟨hl, hr⟩ hne
              | cons _ _ => exact .inr (by simp)
          | cons _ _ => exact .inl (by simp)
        · simpa using hdef
termination_by lhs rhs _ _ _ => sizeOf lhs + sizeOf rhs
decreasing_by
  all_goals try subst_vars
  all_goals simp_wf
  all_goals first
    | omega
    | (simp at hsz; omega)

/-- **Completeness**: a derivation makes the checker accept. -/
theorem subCheck_of_sub {ρl ρr : Ren} {lhs rhs : Ty}
    (h : Sub ρl ρr lhs rhs) : subCheck ρl ρr lhs rhs = true := by
  induction h with
  | base b => simp [subCheck]
  | uintRange n => simp [subCheck]
  | dataSource s => simp [subCheck]
  | txn => simp [subCheck]
  | @fnCompute ρl ρr n0 n1 k0 k1 d0 c0 d1 c1 hok hnd hdom hcod ihdom ihcod =>
      have hdd : (k0 == FunKind.data && k1 == FunKind.data) = false := by
        rw [Bool.and_eq_false_iff]
        by_cases hk : k0 = .data
        · subst hk
          refine .inr ?_
          rw [Bool.eq_false_iff]
          intro hp
          exact hnd ⟨rfl, by simpa using hp⟩
        · exact .inl (by simpa using hk)
      simp only [subCheck]
      simp [hdd, kindOkB_iff.mpr hok, ihdom, ihcod]
  | @fnData ρl ρr n0 n1 d0 c0 d1 c1 hdom1 hdom2 hcod ih1 ih2 ihcod =>
      simp only [subCheck]
      simp [kindOkB, ih1, ih2, ihcod]
  | tuple hlen hpt ihpt =>
      simp only [subCheck]
      exact (subSeq_iff _ _ _ _).mpr ⟨hlen, ihpt⟩
  | record hsome hsub ihsub =>
      simp only [subCheck]
      exact (subFields_iff _ _ _ _).mpr ⟨hsome, ihsub⟩
  | variant hsome hsub ihsub =>
      simp only [subCheck]
      exact (subTags_iff _ _ _ _).mpr ⟨hsome, ihsub⟩
  | @refined ρl ρr lhs rhs lb lrefs rb rrefs hpl hpr hguard hdef hbase ihbase =>
      -- The conclusion's sides are generic; every non-catch-all checker arm
      -- has both sides peeling to `(·, [])`, refuting the guard, and the
      -- catch-all's else-branch is supplied by the premises.
      rw [subCheck.eq_def]
      split
      all_goals try
        (simp only [Ty.peel, Prod.mk.injEq] at hpl hpr
         obtain ⟨-, hl2⟩ := hpl
         obtain ⟨-, hr2⟩ := hpr
         subst hl2; subst hr2
         rcases hguard with hg | hg <;> exact absurd rfl hg)
      -- The catch-all: the dite's condition is false by the guard.
      rw [dif_neg]
      · simp only [Bool.and_eq_true]
        refine ⟨?_, ?_⟩
        · rw [hpl, hpr]
          simpa using hdef
        · have hb : lhs.peel.1 = lb := by rw [hpl]
          have hb' : rhs.peel.1 = rb := by rw [hpr]
          rw [hb, hb']
          exact ihbase
      · rintro ⟨hl, hr⟩
        rw [hpl] at hl
        rw [hpr] at hr
        simp at hl hr
        subst hl; subst hr
        rcases hguard with hg | hg <;> exact absurd rfl hg

/-- The checker decides exactly the relation. -/
theorem subCheck_iff_sub (ρl ρr : Ren) (lhs rhs : Ty) :
    subCheck ρl ρr lhs rhs = true ↔ Sub ρl ρr lhs rhs :=
  ⟨sub_of_subCheck lhs rhs ρl ρr, subCheck_of_sub⟩

/-- **The ground subtype relation is decidable.** -/
instance (ρl ρr : Ren) (lhs rhs : Ty) : Decidable (Sub ρl ρr lhs rhs) :=
  decidable_of_iff _ (subCheck_iff_sub ρl ρr lhs rhs)

end CclFormal
