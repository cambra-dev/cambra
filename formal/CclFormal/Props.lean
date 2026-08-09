import CclFormal.Sub

/-!
# First metatheory: reflexivity

`constrain_go` opens with a trivial-equality short-circuit (`lhs == rhs`
under identity morphisms → `Ok`). The model deliberately has no such rule;
`Sub.refl` proves it *derivable* — which is the faithfulness condition for
omitting it. The proof goes through only for `Ty.WF` (uniquely-keyed) types:
on a duplicate-keyed record the short-circuit and the find-first record arm
genuinely disagree, so the hypothesis is the model naming a builder
invariant the Rust leaves implicit.
-/

namespace CclFormal

theorem Ren.isId_id : Ren.IsId Ren.id := fun _ => rfl

theorem Ren.IsId.extend_diag {ρ : Ren} (h : ρ.IsId) (k : String) :
    (ρ.extend k k).IsId := by
  intro x
  by_cases hk : k = x
  · subst hk
    simp [Ren.apply, Ren.extend]
  · have hb : ((k, k).1 == x) = false := by simpa using hk
    have := h x
    simp [Ren.apply, Ren.extend, hb] at this ⊢
    exact this

/-- The codomain morphism of a reflexive function edge still acts as the
identity: a Pi binder corresponds to itself. -/
theorem codRen_diag_isId (n : Option String) {ρ : Ren} (h : ρ.IsId) :
    (codRen n n ρ).IsId := by
  cases n with
  | none => exact h
  | some k => exact h.extend_diag k

theorem Pred.rename_isId {ρ : Ren} (h : ρ.IsId) : (p : Pred) → p.rename ρ = p
  | .elem | .litInt _ | .litBool _ | .litStr _ | .litUnit => rfl
  | .var x => by simp [Pred.rename, h x]
  | .unop op a => by simp [Pred.rename, rename_isId h a]
  | .binop op a b => by simp [Pred.rename, rename_isId h a, rename_isId h b]
  | .proj a k => by simp [Pred.rename, rename_isId h a]
  | .app f a => by simp [Pred.rename, rename_isId h f, rename_isId h a]

/-- Identical refinement sets have no deficit (under identity-acting
morphisms). -/
theorem deficit_self {ρl ρr : Ren} (hl : ρl.IsId) (hr : ρr.IsId)
    (S : List Pred) : deficit ρl ρr S S = [] := by
  unfold deficit
  have hmap : S.map (Pred.rename ρl) = S := by
    simpa using List.map_congr_left (fun p _ => Pred.rename_isId hl p)
  rw [hmap]
  apply List.filter_eq_nil_iff.mpr
  intro r hm
  rw [Pred.rename_isId hr r]
  simpa using hm

/-- Find-first lookup returns the member itself when keys are unique. -/
theorem lookupBy_of_mem_nodup [BEq α] [LawfulBEq α] {l : List (α × Ty)}
    {k : α} {t : Ty} (hnd : (l.map (·.1)).Nodup) (hm : (k, t) ∈ l) :
    lookupBy l k = some t := by
  induction l with
  | nil => cases hm
  | cons e rest ih =>
      obtain ⟨a, u⟩ := e
      have hnd' : (∀ (x : Ty), (a, x) ∉ rest) ∧
          (List.map (fun x => x.fst) rest).Nodup := by simpa using hnd
      rcases List.mem_cons.mp hm with heq | hmem
      · injection heq with h1 h2
        subst h1; subst h2
        simp [lookupBy]
      · have hak : (a == k) = false := by
          cases hab : a == k with
          | false => rfl
          | true =>
              have ha : a = k := eq_of_beq hab
              subst ha
              exact absurd hmem (hnd'.1 t)
        have hfind : ((a, u) :: rest).find? (fun e => e.1 == k) =
            rest.find? (fun e => e.1 == k) := by
          rw [List.find?_cons_of_neg]
          simpa using hak
        have := ih hnd'.2 hmem
        unfold lookupBy at this ⊢
        rw [hfind]
        exact this

/-- Normalization preserves well-formedness: the common domain is (under)
the first leg, whose well-formedness the variant carries. -/
theorem partitionDomain_wf {d u : Ty} (hwf : d.WF)
    (h : partitionDomain d = some u) : u.WF := by
  match d, h with
  | .variant ((k0, p0) :: rest), h =>
      simp only [partitionDomain] at h
      split at h
      · injection h with h
        subst h
        cases hwf with
        | variant hnd hts =>
            have hp0 : p0.WF := hts (k0, p0) (List.mem_cons_self ..)
            cases hp : p0 with
            | refined b p =>
                rw [hp] at hp0
                cases hp0 with
                | refined hb => simpa [legUnder] using hb
            | _ => simpa [legUnder, ← hp] using hp0
      · exact absurd h (by simp)

theorem normFun_wf {t t' : Ty} (hwf : t.WF) (h : normFun t = some t') :
    t'.WF := by
  match t, h with
  | .fn n k d c, h =>
      simp only [normFun, Option.map_eq_some_iff] at h
      obtain ⟨d', hd, rfl⟩ := h
      cases hwf with
      | fn hd0 hc => exact .fn (partitionDomain_wf hd0 hd) hc

/-- The refined case's termination shape: peeling the base stays under the
refined node's size, whatever the predicate contributes. -/
theorem Ty.peel_fst_lt_one_add (b : Ty) (n : Nat) :
    sizeOf b.peel.1 < 1 + sizeOf b + n := by
  have := Ty.peel_fst_sizeOf_le b
  omega

/-- Peeling preserves well-formedness. -/
theorem Ty.WF.peel_fst : {t : Ty} → t.WF → t.peel.1.WF
  | .base _, h | .uintRange _, h | .dataSource _, h | .txn, h
  | .fn .., h | .tuple _, h | .record _, h | .variant _, h => by
      simpa [Ty.peel] using h
  | .refined _ _, .refined hb => by
      simpa [Ty.peel] using hb.peel_fst

/-- **Reflexivity is derivable** (for uniquely-keyed types, under
identity-acting morphisms): the model needs no analog of `constrain_go`'s
trivial-equality short-circuit. -/
theorem Sub.refl : (t : Ty) → t.WF → (ρl ρr : Ren) → ρl.IsId → ρr.IsId →
    Sub ρl ρr t t
  | .base b, _, _, _, _, _ => .base b
  | .uintRange n, _, _, _, _, _ => .uintRange n
  | .dataSource s, _, _, _, _, _ => .dataSource s
  | .txn, _, _, _, _, _ => .txn
  | .fn n k d c, hwf, ρl, ρr, hl, hr => by
      cases hn : normFun (.fn n k d c) with
      | some t' =>
          -- A partition-typed function is reflexively below itself through
          -- its (shared) normal form.
          refine Sub.fnNorm (.inl (by simp [hn])) ?_
          rw [hn]
          simp only [Option.getD_some]
          have hsz := normFun_sizeOf hn
          exact Sub.refl t' (normFun_wf hwf hn) ρl ρr hl hr
      | none =>
          cases hwf with
          | fn hd hc =>
            have hcod :=
              Sub.refl c hc (codRen n n ρl) ρr (codRen_diag_isId n hl) hr
            cases k with
            | data =>
                exact .fnData hn hn (Sub.refl d hd ρr ρl hr hl)
                  (Sub.refl d hd ρl ρr hl hr) hcod
            | compute =>
                exact .fnCompute hn hn trivial (fun h => nomatch h.1)
                  (Sub.refl d hd ρr ρl hr hl) hcod
  | .tuple ts, hwf, ρl, ρr, hl, hr => by
      cases hwf with
      | tuple hts =>
        refine .tuple (Nat.le_refl _) fun i t0 t1 h0 h1 => ?_
        rw [h0] at h1
        injection h1 with h
        subst h
        have hm : t0 ∈ ts := List.mem_of_getElem? h0
        have hsz : sizeOf t0 < sizeOf ts := List.sizeOf_lt_of_mem hm
        exact Sub.refl t0 (hts t0 hm) ρl ρr hl hr
  | .record fs, hwf, ρl, ρr, hl, hr => by
      cases hwf with
      | record hnd hf =>
        refine .record (fun n t1 hm => ?_) (fun n t0 t1 hm hlk => ?_)
        · rw [lookupBy_of_mem_nodup hnd hm]; rfl
        · rw [lookupBy_of_mem_nodup hnd hm] at hlk
          injection hlk with h
          subst h
          exact Sub.refl t1 (hf (n, t1) hm) ρl ρr hl hr
  | .variant tags, hwf, ρl, ρr, hl, hr => by
      cases hwf with
      | variant hnd ht =>
        refine .variant (fun k t0 hm => ?_) (fun k t0 t1 hm hlk => ?_)
        · rw [lookupBy_of_mem_nodup hnd hm]; rfl
        · rw [lookupBy_of_mem_nodup hnd hm] at hlk
          injection hlk with h
          subst h
          exact Sub.refl t0 (ht (k, t0) hm) ρl ρr hl hr
  | .refined b p, hwf, ρl, ρr, hl, hr => by
      cases hwf with
      | refined hb =>
        refine .refined rfl rfl (.inl (by simp)) (deficit_self hl hr _) ?_
        show Sub ρl ρr b.peel.1 b.peel.1
        exact Sub.refl b.peel.1 (Ty.WF.peel_fst hb) ρl ρr hl hr
termination_by t _ _ _ _ _ => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals try simp
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp at this; omega)
    | apply Ty.peel_fst_lt_one_add
    | (simp at hsz; omega)

end CclFormal
