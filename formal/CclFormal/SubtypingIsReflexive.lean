import CclFormal.Subtyping

/-!
# Reflexivity of the concrete subtype relation

`constrain_go` opens with a trivial-equality short-circuit (`lhs == rhs` under identity morphisms →
`Ok`). The model deliberately has no such rule; `Subtyping.refl` proves it *derivable* — which is
the faithfulness condition for omitting it. The proof goes through only for `Ty.WellFormed`
(uniquely-keyed) types: on a duplicate-keyed record the short-circuit and the find-first record arm
genuinely disagree, so the hypothesis is the model naming a builder invariant the Rust leaves
implicit.

Well-formedness is the only hypothesis. A refinement's binding is its index, so the relation
transports nothing between the two sides and the proof is a structural recursion: each head
constructor relates to itself from its children, and the refined case peels and recurses. Under a
name-spelled representation the same proof carries identity-acting morphisms through every rule and
needs their preservation under the codomain extension.
-/

namespace CclFormal

/-- **Reflexivity is derivable** (for uniquely-keyed types): the model needs
no analog of `constrain_go`'s trivial-equality short-circuit. -/
theorem Subtyping.refl : (t : Ty) → t.WellFormed → Subtyping t t
  | .base b, _ => .base b
  | .uintRange n, _ => .uintRange n
  | .dataSource s, _ => .dataSource s
  | .txn, _ => .txn
  | .fn n k d c, hwf => by
      cases hwf with
      | fn hd hc =>
        have hcod := Subtyping.refl c hc
        cases k with
        | data => exact .fnData (Subtyping.refl d hd) (Subtyping.refl d hd) hcod
        | compute =>
            exact .fnCompute trivial (fun h => nomatch h.1) (Subtyping.refl d hd) hcod
  | .tuple ts, hwf => by
      cases hwf with
      | tuple hts =>
        refine .tuple (Nat.le_refl _) fun i t0 t1 h0 h1 => ?_
        rw [h0] at h1
        injection h1 with h
        subst h
        have hm : t0 ∈ ts := List.mem_of_getElem? h0
        have hsz : sizeOf t0 < sizeOf ts := List.sizeOf_lt_of_mem hm
        exact Subtyping.refl t0 (hts t0 hm)
  | .record fs, hwf => by
      cases hwf with
      | record hnd hf =>
        refine .record (fun n t1 hm => ?_) (fun n t0 t1 hm hlk => ?_)
        · rw [lookupBy_of_mem_nodup hnd hm]; rfl
        · rw [lookupBy_of_mem_nodup hnd hm] at hlk
          injection hlk with h
          subst h
          exact Subtyping.refl t1 (hf (n, t1) hm)
  | .variant tags, hwf => by
      cases hwf with
      | variant hnd ht =>
        refine .variant (fun k t0 hm => ?_) (fun k t0 t1 hm hlk => ?_)
        · rw [lookupBy_of_mem_nodup hnd hm]; rfl
        · rw [lookupBy_of_mem_nodup hnd hm] at hlk
          injection hlk with h
          subst h
          exact Subtyping.refl t0 (ht (k, t0) hm)
  | .refined b ps, hwf => by
      cases hwf with
      | refined hne _ hb =>
        refine .refined rfl rfl
          (.inl (by simp; exact fun hc => absurd hc hne))
          (deficit_self _) ?_
        show Subtyping b.peel.1 b.peel.1
        exact Subtyping.refl b.peel.1 (Ty.WellFormed.peel_fst hb)
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
