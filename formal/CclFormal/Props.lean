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

With refinements closed into indices this file is most of what the rename machinery's
deletion buys: the old proof threaded identity-acting morphisms through
every rule (`Ren.IsId`, its preservation under the diagonal codomain
extension, and predicate-transport invariance); with refinements closed there is
no transport, and reflexivity needs only well-formedness.
-/

namespace CclFormal

/-- Identical refinement sets have no deficit. -/
theorem deficit_self (S : List Pred) : deficit S S = [] := by
  unfold deficit
  apply List.filter_eq_nil_iff.mpr
  intro r hm
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
  | .refined _ _, .refined _ _ hb => by
      simpa [Ty.peel] using hb.peel_fst

/-- **Reflexivity is derivable** (for uniquely-keyed types): the model needs
no analog of `constrain_go`'s trivial-equality short-circuit. -/
theorem Sub.refl : (t : Ty) → t.WF → Sub t t
  | .base b, _ => .base b
  | .uintRange n, _ => .uintRange n
  | .dataSource s, _ => .dataSource s
  | .txn, _ => .txn
  | .fn n k d c, hwf => by
      cases hwf with
      | fn hd hc =>
        have hcod := Sub.refl c hc
        cases k with
        | data => exact .fnData (Sub.refl d hd) (Sub.refl d hd) hcod
        | compute =>
            exact .fnCompute trivial (fun h => nomatch h.1) (Sub.refl d hd) hcod
  | .tuple ts, hwf => by
      cases hwf with
      | tuple hts =>
        refine .tuple (Nat.le_refl _) fun i t0 t1 h0 h1 => ?_
        rw [h0] at h1
        injection h1 with h
        subst h
        have hm : t0 ∈ ts := List.mem_of_getElem? h0
        have hsz : sizeOf t0 < sizeOf ts := List.sizeOf_lt_of_mem hm
        exact Sub.refl t0 (hts t0 hm)
  | .record fs, hwf => by
      cases hwf with
      | record hnd hf =>
        refine .record (fun n t1 hm => ?_) (fun n t0 t1 hm hlk => ?_)
        · rw [lookupBy_of_mem_nodup hnd hm]; rfl
        · rw [lookupBy_of_mem_nodup hnd hm] at hlk
          injection hlk with h
          subst h
          exact Sub.refl t1 (hf (n, t1) hm)
  | .variant tags, hwf => by
      cases hwf with
      | variant hnd ht =>
        refine .variant (fun k t0 hm => ?_) (fun k t0 t1 hm hlk => ?_)
        · rw [lookupBy_of_mem_nodup hnd hm]; rfl
        · rw [lookupBy_of_mem_nodup hnd hm] at hlk
          injection hlk with h
          subst h
          exact Sub.refl t0 (ht (k, t0) hm)
  | .refined b ps, hwf => by
      cases hwf with
      | refined hne _ hb =>
        refine .refined rfl rfl
          (.inl (by simp; exact fun hc => absurd hc hne))
          (deficit_self _) ?_
        show Sub b.peel.1 b.peel.1
        exact Sub.refl b.peel.1 (Ty.WF.peel_fst hb)
termination_by t _ => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals try simp
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp at this; omega)
    | apply Ty.peel_fst_lt_one_add
    | (simp at hsz; omega)

end CclFormal
