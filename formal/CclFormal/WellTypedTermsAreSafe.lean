import CclFormal.Term

/-!
# Well-typed terms are safe: progress, preservation, and refinement soundness

The proof battery over `Term.lean`'s judgment: weakening and the substitution lemma (the de Bruijn
payoff), `Subtyping` inversion and canonical forms modulo refinement peeling, progress (a well-typed
closed term is a value, steps, or is filter-blocked at a cast), preservation, and the two
corollaries — refinement soundness and case-binder soundness.

Two structural choices keep the proofs out of transitivity's territory:

- **`Subtyping` inversions are case analyses, not inductions.** Every `Subtyping`
  constructor pins both sides' head constructors, and the `refined` arm recurses on fully-peeled
  bases — so `subtyping_peel_inv` (peel both sides) plus one non-recursive `cases` per head is all
  the inversion there is.
- **Typing inversions absorb subsumption chains with typing transport, not
  `Subtyping` composition.** Inverting a derivation that ends in `sub` would otherwise lean on
  transitivity of `Subtyping`. Instead `HasTy.lam_inv` returns implications of the form "whatever is
  typed at `X` is typed at `Y`" — reflexive without `Subtyping.refl`'s `WellFormed` side condition,
  and composable across a chain link-by-link, each link re-entering the typing via `HasTy.sub`
  directly. The relation carries no environments, so the transport needs no rename-invariance lemma.
-/

namespace CclFormal

/-! ## Peeling -/

theorem Ty.TermFragment.peel_fst : {t : Ty} → t.TermFragment → t.peel.1.TermFragment
  | .refined _ _, .refined _ hb => by simpa [Ty.peel] using hb.peel_fst
  | .base _, h | .uintRange _, h | .dataSource _, h | .txn, h
  | .fn .., h | .tuple _, h | .record _, h | .variant _, h => by
      simpa [Ty.peel] using h

theorem Ty.TermFragment.peel_refinements : {t : Ty} → t.TermFragment →
    ∀ p ∈ t.peel.2, p.elemOnly = true
  | .refined _ _, .refined hps hb => by
      intro p hp
      simp [Ty.peel] at hp
      rcases hp with hp | hp
      · exact hps p hp
      · exact hb.peel_refinements p hp
  | .base _, h | .uintRange _, h | .dataSource _, h | .txn, h
  | .fn .., h | .tuple _, h | .record _, h | .variant _, h => by
      simp [Ty.peel]

/-! ## `Subtyping` inversion: peel, then one `cases` per head -/

/-- Claim containment at identity morphisms: everything the supertype
refinements (across all its peeled layers), the subtype already claimed. -/
theorem Subtyping.refinements_mono {S W : Ty} (h : Subtyping S W) :
    ∀ p ∈ W.peel.2, p ∈ S.peel.2 := by
  cases h with
  | refined hl hr _ hdef _ =>
      rw [hl, hr]
      exact deficit_eq_nil_iff.mp hdef
  | base b => simp [Ty.peel]
  | uintRange n => simp [Ty.peel]
  | dataSource s => simp [Ty.peel]
  | txn => simp [Ty.peel]
  | fnCompute h1 h2 h3 h4 => simp [Ty.peel]
  | fnData h1 h2 h3 => simp [Ty.peel]
  | tuple h1 h2 => simp [Ty.peel]
  | record h1 h2 => simp [Ty.peel]
  | variant h1 h2 => simp [Ty.peel]

/-- An unrefined subtype of a function type is a function type. (The
`refined` arm cannot apply: both sides peel trivially, starving its
at-least-one-layer guard.) -/
theorem Subtyping.fn_src {S : Ty} {n k d c}
    (h : Subtyping S (.fn n k d c)) (hS : S.isRefined = false) :
    ∃ n' k' d' c', S = .fn n' k' d' c' := by
  cases h with
  | fnCompute _ _ _ _ => exact ⟨_, _, _, _, rfl⟩
  | fnData _ _ _ => exact ⟨_, _, _, _, rfl⟩
  | refined hl hr hne _ _ =>
      rw [Ty.peel_of_not_refined hS] at hl
      simp [Ty.peel] at hl hr
      obtain ⟨-, hl2⟩ := hl
      obtain ⟨-, hr2⟩ := hr
      simp [hl2, hr2] at hne

/-- Function edge inversion: exactly the contravariant domain and the
codomain edge. -/
theorem Subtyping.fn_inv {n0 n1 : Option String} {k0 k1 : FunKind}
    {d0 d1 c0 c1 : Ty}
    (h : Subtyping (.fn n0 k0 d0 c0) (.fn n1 k1 d1 c1)) :
    Subtyping d1 d0 ∧ Subtyping c0 c1 := by
  cases h with
  | fnCompute _ _ hdom hcod => exact ⟨hdom, hcod⟩
  | fnData hd1 _ hcod => exact ⟨hd1, hcod⟩
  | refined hl hr hne _ _ =>
      simp [Ty.peel] at hl hr
      obtain ⟨-, hl2⟩ := hl
      obtain ⟨-, hr2⟩ := hr
      simp [hl2, hr2] at hne

/-- An unrefined subtype of a tuple type is a tuple type, at least as wide,
elementwise below it. -/
theorem Subtyping.tuple_inv {S : Ty} {Ts : List Ty}
    (h : Subtyping S (.tuple Ts)) (hS : S.isRefined = false) :
    ∃ Ss, S = .tuple Ss ∧ Ts.length ≤ Ss.length ∧
      ∀ (i : Nat) t0 t1, Ss[i]? = some t0 → Ts[i]? = some t1 →
        Subtyping t0 t1 := by
  cases h with
  | tuple hlen helem => exact ⟨_, rfl, hlen, helem⟩
  | refined hl hr hne _ _ =>
      rw [Ty.peel_of_not_refined hS] at hl
      simp [Ty.peel] at hl hr
      obtain ⟨-, hl2⟩ := hl
      obtain ⟨-, hr2⟩ := hr
      simp [hl2, hr2] at hne

/-- An unrefined subtype of a variant type is a variant type, every tag it
may produce accepted (find-first) with its payload below the acceptor's. -/
theorem Subtyping.variant_inv {S : Ty} {tagsW : List (FieldKey × Ty)}
    (h : Subtyping S (.variant tagsW)) (hS : S.isRefined = false) :
    ∃ tagsS, S = .variant tagsS ∧
      ∀ tg t0, (tg, t0) ∈ tagsS →
        ∃ t1, lookupBy tagsW tg = some t1 ∧ Subtyping t0 t1 := by
  cases h with
  | variant hcov hpay =>
      refine ⟨_, rfl, fun tg t0 hmem => ?_⟩
      obtain ⟨t1, ht1⟩ := Option.isSome_iff_exists.mp (hcov tg t0 hmem)
      exact ⟨t1, ht1, hpay tg t0 t1 hmem ht1⟩
  | refined hl hr hne _ _ =>
      rw [Ty.peel_of_not_refined hS] at hl
      simp [Ty.peel] at hl hr
      obtain ⟨-, hl2⟩ := hl
      obtain ⟨-, hr2⟩ := hr
      simp [hl2, hr2] at hne

/-! ## The fragment is a derivation invariant -/

/-- Under a fragment context, every derivable type is in the fragment: the
free-choice premises on `lam`/`variant`/`caseE`/`sub` are exactly what
closes the loop. -/
theorem hasTy_fragment {Γ : List Ty} {e : Term} {T : Ty} (h : HasTy Γ e T) :
    (∀ X ∈ Γ, X.TermFragment) → T.TermFragment := by
  induction h with
  | lit l => exact fun _ => by cases l <;> exact .base _
  | var hn => exact fun hΓ => hΓ _ (List.mem_of_getElem? hn)
  | lam hfrag _ ih =>
      intro hΓ
      refine .fn hfrag (ih fun X hX => ?_)
      rcases List.mem_cons.mp hX with rfl | hX
      · exact hfrag
      · exact hΓ _ hX
  | app _ _ ihf _ =>
      intro hΓ
      cases ihf hΓ with | fn _ hc => exact hc
  | letE _ _ ihb ihbody =>
      intro hΓ
      refine ihbody fun X hX => ?_
      rcases List.mem_cons.mp hX with rfl | hX
      · exact ihb hΓ
      · exact hΓ _ hX
  | @tuple Γ es Ts hlen _ ih =>
      intro hΓ
      refine .tuple fun t ht => ?_
      obtain ⟨i, hi⟩ := List.getElem?_of_mem ht
      have hilt : i < Ts.length := (List.getElem?_eq_some_iff.mp hi).1
      have hes : es[i]? = some es[i] :=
        List.getElem?_eq_getElem (by omega)
      exact ih i es[i] t hes hi hΓ
  | proj _ hi ih =>
      intro hΓ
      cases ih hΓ with | tuple ha => exact ha _ (List.mem_of_getElem? hi)
  | variant hfrag _ _ _ => exact fun _ => hfrag
  | caseE hU _ _ _ _ _ => exact fun _ => hU
  | cast _ _ hrefinements _ ih => exact fun hΓ => .refined hrefinements (ih hΓ)
  | refineV _ _ _ _ hrefinements _ ih => exact fun hΓ => .refined hrefinements (ih hΓ)
  | sub _ _ hfrag _ => exact fun _ => hfrag

/-! ## Shift and substitution, constructor-wise

`shift`/`subst` recurse through lists via `attach` (their termination device); these unfoldings
restate them as plain `map`s so the typing
proofs never see a subtype. -/

namespace Term

@[simp] theorem shift_lit {c : Nat} {l : Lit} :
    (Term.lit l).shift c = .lit l := by simp [Term.shift]

@[simp] theorem shift_var {c n : Nat} :
    (Term.var n).shift c = if n < c then .var n else .var (n + 1) := by
  simp [Term.shift]

@[simp] theorem shift_lam {c : Nat} {dom : Ty} {body : Term} :
    (Term.lam dom body).shift c = .lam dom (body.shift (c + 1)) := by
  simp [Term.shift]

@[simp] theorem shift_app {c : Nat} {f a : Term} :
    (Term.app f a).shift c = .app (f.shift c) (a.shift c) := by
  simp [Term.shift]

@[simp] theorem shift_letE {c : Nat} {bound body : Term} :
    (Term.letE bound body).shift c = .letE (bound.shift c) (body.shift (c + 1)) := by
  simp [Term.shift]

@[simp] theorem shift_tuple {c : Nat} {es : List Term} :
    (Term.tuple es).shift c = .tuple (es.map (Term.shift c)) := by
  rw [Term.shift]
  congr 1
  exact List.attach_map_val

@[simp] theorem shift_proj {c : Nat} {e : Term} {i : Nat} :
    (Term.proj e i).shift c = .proj (e.shift c) i := by
  simp [Term.shift]

@[simp] theorem shift_variant {c : Nat} {tag : FieldKey} {e : Term} :
    (Term.variant tag e).shift c = .variant tag (e.shift c) := by
  simp [Term.shift]

@[simp] theorem shift_caseE {c : Nat} {scrut : Term} {arms : List (FieldKey × Term)} :
    (Term.caseE scrut arms).shift c =
      .caseE (scrut.shift c) (arms.map fun a => (a.1, a.2.shift (c + 1))) := by
  rw [Term.shift]
  congr 1
  show arms.attach.map (fun x => (x.1.1, Term.shift (c + 1) x.1.2)) = _
  rw [List.map_attach_eq_pmap]
  show arms.pmap (fun a _ => (a.1, Term.shift (c + 1) a.2)) _ = _
  exact List.pmap_eq_map _

@[simp] theorem shift_cast {c : Nat} {refinements : List Predicate} {e : Term} :
    (Term.cast refinements e).shift c = .cast refinements (e.shift c) := by
  simp [Term.shift]

@[simp] theorem subst_lit {k : Nat} {v : Term} {l : Lit} :
    Term.subst k v (.lit l) = .lit l := by rw [Term.subst.eq_def]

@[simp] theorem subst_var {k : Nat} {v : Term} {n : Nat} :
    Term.subst k v (.var n) =
      if n = k then v else if n < k then .var n else .var (n - 1) := by
  rw [Term.subst.eq_def]

@[simp] theorem subst_lam {k : Nat} {v : Term} {dom : Ty} {body : Term} :
    Term.subst k v (.lam dom body) =
      .lam dom (Term.subst (k + 1) (v.shift 0) body) := by
  rw [Term.subst.eq_def]

@[simp] theorem subst_app {k : Nat} {v f a : Term} :
    Term.subst k v (.app f a) = .app (Term.subst k v f) (Term.subst k v a) := by
  rw [Term.subst.eq_def]

@[simp] theorem subst_letE {k : Nat} {v bound body : Term} :
    Term.subst k v (.letE bound body) =
      .letE (Term.subst k v bound) (Term.subst (k + 1) (v.shift 0) body) := by
  rw [Term.subst.eq_def]

@[simp] theorem subst_tuple {k : Nat} {v : Term} {es : List Term} :
    Term.subst k v (.tuple es) = .tuple (es.map (Term.subst k v)) := by
  rw [Term.subst.eq_def]
  show Term.tuple (es.attach.map fun x => Term.subst k v x.1) = _
  congr 1
  exact List.attach_map_val

@[simp] theorem subst_proj {k : Nat} {v e : Term} {i : Nat} :
    Term.subst k v (.proj e i) = .proj (Term.subst k v e) i := by
  rw [Term.subst.eq_def]

@[simp] theorem subst_variant {k : Nat} {v : Term} {tag : FieldKey} {e : Term} :
    Term.subst k v (.variant tag e) = .variant tag (Term.subst k v e) := by
  rw [Term.subst.eq_def]

@[simp] theorem subst_caseE {k : Nat} {v scrut : Term}
    {arms : List (FieldKey × Term)} :
    Term.subst k v (.caseE scrut arms) =
      .caseE (Term.subst k v scrut)
        (arms.map fun a => (a.1, Term.subst (k + 1) (v.shift 0) a.2)) := by
  rw [Term.subst.eq_def]
  show Term.caseE (Term.subst k v scrut)
      (arms.attach.map fun x => (x.1.1, Term.subst (k + 1) (Term.shift 0 v) x.1.2)) = _
  congr 1
  rw [List.map_attach_eq_pmap]
  show arms.pmap (fun a _ => (a.1, Term.subst (k + 1) (Term.shift 0 v) a.2)) _ = _
  exact List.pmap_eq_map _

@[simp] theorem subst_cast {k : Nat} {v : Term} {refinements : List Predicate} {e : Term} :
    Term.subst k v (.cast refinements e) = .cast refinements (Term.subst k v e) := by
  rw [Term.subst.eq_def]

/-! ## Values, refinements, and the two term transports -/

theorem IsVal.shift {v : Term} (hv : v.IsVal) (c : Nat) : (v.shift c).IsVal := by
  induction hv generalizing c with
  | lit l => simpa using .lit l
  | lam dom body => simpa using .lam dom (body.shift (c + 1))
  | tuple _ ih =>
      rw [shift_tuple]
      refine .tuple fun e he => ?_
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      exact ih x hx c
  | variant tag hv ih =>
      rw [shift_variant]
      exact .variant tag (ih c)

theorem IsVal.subst {v : Term} (hv : v.IsVal) (k : Nat) (u : Term) :
    (Term.subst k u v).IsVal := by
  induction hv generalizing k u with
  | lit l => simpa using .lit l
  | lam dom body => simpa using .lam dom (Term.subst (k + 1) (u.shift 0) body)
  | tuple _ ih =>
      rw [subst_tuple]
      refine .tuple fun e he => ?_
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      exact ih x hx k u
  | variant tag hv ih =>
      rw [subst_variant]
      exact .variant tag (ih k u)

/-- Predicate evaluation reads a value only through its literal shape, and
shifting never changes that shape. -/
theorem eval_shift {v : Term} (c : Nat) : (p : Predicate) →
    Predicate.eval (v.shift c) p = Predicate.eval v p
  | .elem => by
      cases v with
      | var n => by_cases h : n < c <;> simp [h, Predicate.eval]
      | lit l => simp [Predicate.eval]
      | lam dom body => simp [Predicate.eval]
      | app f a => simp [Predicate.eval]
      | letE b body => simp [Predicate.eval]
      | tuple es => simp [Predicate.eval]
      | proj e i => simp [Predicate.eval]
      | variant tag e => simp [Predicate.eval]
      | caseE sc arms => simp [Predicate.eval]
      | cast cl e => simp [Predicate.eval]
  | .unop _ a => by simp [Predicate.eval, eval_shift c a]
  | .binop _ a b => by simp [Predicate.eval, eval_shift c a, eval_shift c b]
  | .proj _ _ | .app _ _ | .var _ | .piBound _ | .litInt _ | .litBool _
  | .litStr _ | .litUnit | .lam _ | .boundVar _ | .cast _ _ => by simp [Predicate.eval]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; omega)

/-- Same for substitution into a *value*: values have no free variables at
their literal-observable surface. -/
theorem eval_subst {v : Term} (hv : v.IsVal) (k : Nat) (u : Term) : (p : Predicate) →
    Predicate.eval (Term.subst k u v) p = Predicate.eval v p
  | .elem => by cases hv <;> simp [Predicate.eval]
  | .unop _ a => by simp [Predicate.eval, eval_subst hv k u a]
  | .binop _ a b => by simp [Predicate.eval, eval_subst hv k u a, eval_subst hv k u b]
  | .proj _ _ | .app _ _ | .var _ | .piBound _ | .litInt _ | .litBool _
  | .litStr _ | .litUnit | .lam _ | .boundVar _ | .cast _ _ => by simp [Predicate.eval]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; omega)

theorem refinementsHold_shift {v : Term} {refinements : List Predicate} (c : Nat) :
    Term.refinementsHold refinements (v.shift c) = Term.refinementsHold refinements v := by
  unfold Term.refinementsHold
  congr 1
  funext p
  rw [eval_shift]

theorem refinementsHold_subst {v : Term} (hv : v.IsVal) {refinements : List Predicate}
    (k : Nat) (u : Term) :
    Term.refinementsHold refinements (Term.subst k u v) = Term.refinementsHold refinements v := by
  unfold Term.refinementsHold
  congr 1
  funext p
  rw [eval_subst hv]

end Term

/-- `List.lookup` through a second-component map. -/
theorem lookup_map_snd {α β γ : Type} [BEq α] {l : List (α × β)} {f : β → γ}
    {k : α} :
    (l.map fun a => (a.1, f a.2)).lookup k = (l.lookup k).map f := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      obtain ⟨x, y⟩ := a
      simp only [List.map_cons, List.lookup]
      split <;> simp [ih]

/-! ## Weakening -/

/-- Inserting `U` at cut `Γ₁.length` retypes the shifted term. -/
theorem HasTy.weaken {Γ : List Ty} {e : Term} {W : Ty} (h : HasTy Γ e W) :
    ∀ (Γ₁ Γ₂ : List Ty) (U : Ty), Γ = Γ₁ ++ Γ₂ →
      HasTy (Γ₁ ++ U :: Γ₂) (e.shift Γ₁.length) W := by
  induction h with
  | lit l =>
      intro Γ₁ Γ₂ U hΓ
      rw [Term.shift_lit]; exact .lit l
  | @var Γ n T hn =>
      intro Γ₁ Γ₂ U hΓ
      subst hΓ
      rw [Term.shift_var]
      by_cases hc : n < Γ₁.length
      · rw [if_pos hc]
        refine .var ?_
        rw [List.getElem?_append_left hc] at hn ⊢
        exact hn
      · rw [if_neg hc]
        replace hc := Nat.le_of_not_lt hc
        refine .var ?_
        rw [List.getElem?_append_right hc] at hn
        rw [List.getElem?_append_right (by omega : Γ₁.length ≤ n + 1)]
        have hidx : n + 1 - Γ₁.length = (n - Γ₁.length) + 1 := by omega
        rw [hidx, List.getElem?_cons_succ]
        exact hn
  | @lam Γ dom body cod hfrag _ ih =>
      intro Γ₁ Γ₂ U hΓ
      subst hΓ
      rw [Term.shift_lam]
      exact .lam hfrag (by simpa using ih (dom :: Γ₁) Γ₂ U rfl)
  | app _ _ ihf iha =>
      intro Γ₁ Γ₂ U hΓ
      rw [Term.shift_app]
      exact .app (ihf Γ₁ Γ₂ U hΓ) (iha Γ₁ Γ₂ U hΓ)
  | @letE Γ bound body T' U' _ _ ihb ihbody =>
      intro Γ₁ Γ₂ U hΓ
      subst hΓ
      rw [Term.shift_letE]
      exact .letE (ihb Γ₁ Γ₂ U rfl) (by simpa using ihbody (T' :: Γ₁) Γ₂ U rfl)
  | @tuple Γ es Ts hlen _ ih =>
      intro Γ₁ Γ₂ U hΓ
      rw [Term.shift_tuple]
      refine .tuple (by simpa using hlen) ?_
      intro i e T h1 h2
      rw [List.getElem?_map] at h1
      cases hes : es[i]? with
      | none => rw [hes] at h1; simp at h1
      | some e0 =>
          rw [hes] at h1
          simp at h1
          subst h1
          exact ih i e0 T hes h2 Γ₁ Γ₂ U hΓ
  | proj _ hi ih =>
      intro Γ₁ Γ₂ U hΓ
      rw [Term.shift_proj]
      exact .proj (ih Γ₁ Γ₂ U hΓ) hi
  | variant hfrag _ hlk ih =>
      intro Γ₁ Γ₂ U hΓ
      rw [Term.shift_variant]
      exact .variant hfrag (ih Γ₁ Γ₂ U hΓ) hlk
  | @caseE Γ scrut arms U' tags hU _ hcov _ ihscrut iharms =>
      intro Γ₁ Γ₂ U hΓ
      subst hΓ
      rw [Term.shift_caseE]
      refine .caseE hU (ihscrut Γ₁ Γ₂ U rfl) ?_ ?_
      · intro tag T hlk
        rw [lookup_map_snd]
        simpa using hcov tag T hlk
      · intro tag T body' hlk harm
        rw [lookup_map_snd] at harm
        cases harms0 : arms.lookup tag with
        | none => rw [harms0] at harm; simp at harm
        | some body0 =>
            rw [harms0] at harm
            simp at harm
            subst harm
            exact (by simpa using iharms tag T body0 hlk harms0 (T :: Γ₁) Γ₂ U rfl)
  | cast _ hne hcl hbase ih =>
      intro Γ₁ Γ₂ U hΓ
      rw [Term.shift_cast]
      exact .cast (ih Γ₁ Γ₂ U hΓ) hne hcl hbase
  | refineV _ hval hch hne hcl hbase ih =>
      intro Γ₁ Γ₂ U hΓ
      exact .refineV (ih Γ₁ Γ₂ U hΓ) (hval.shift _)
        (by rw [Term.refinementsHold_shift]; exact hch) hne hcl hbase
  | sub _ hsub hfrag ih =>
      intro Γ₁ Γ₂ U hΓ
      exact .sub (ih Γ₁ Γ₂ U hΓ) hsub hfrag

/-! ## The substitution lemma

No value restriction and no fragment hypothesis: the fragment premises ride the rules untouched
(types contain no terms in this fragment), and the
substituend only needs the type the cut assumed. -/

theorem HasTy.subst_preserves {Γ : List Ty} {e : Term} {W : Ty}
    (h : HasTy Γ e W) :
    ∀ (Γ₁ Γ₂ : List Ty) (T : Ty) (v : Term), Γ = Γ₁ ++ T :: Γ₂ →
      HasTy (Γ₁ ++ Γ₂) v T →
      HasTy (Γ₁ ++ Γ₂) (Term.subst Γ₁.length v e) W := by
  induction h with
  | lit l =>
      intro Γ₁ Γ₂ T v hΓ hv
      rw [Term.subst_lit]; exact .lit l
  | @var Γ n T' hn =>
      intro Γ₁ Γ₂ T v hΓ hv
      subst hΓ
      rw [Term.subst_var]
      by_cases he : n = Γ₁.length
      · subst he
        rw [if_pos rfl]
        rw [List.getElem?_append_right (Nat.le_refl _)] at hn
        simp at hn
        subst hn
        exact hv
      · rw [if_neg he]
        by_cases hlt : n < Γ₁.length
        · rw [if_pos hlt]
          refine .var ?_
          rw [List.getElem?_append_left hlt] at hn ⊢
          exact hn
        · rw [if_neg hlt]
          replace hlt := Nat.le_of_not_lt hlt
          refine .var ?_
          rw [List.getElem?_append_right hlt] at hn
          have h1 : n - Γ₁.length = (n - Γ₁.length - 1) + 1 := by omega
          rw [h1, List.getElem?_cons_succ] at hn
          rw [List.getElem?_append_right (by omega : Γ₁.length ≤ n - 1)]
          have h2 : n - 1 - Γ₁.length = n - Γ₁.length - 1 := by omega
          rw [h2]
          exact hn
  | @lam Γ dom body cod hfrag _ ih =>
      intro Γ₁ Γ₂ T v hΓ hv
      subst hΓ
      rw [Term.subst_lam]
      refine .lam hfrag ?_
      have hv' : HasTy (dom :: (Γ₁ ++ Γ₂)) (v.shift 0) T := by
        simpa using hv.weaken [] (Γ₁ ++ Γ₂) dom rfl
      exact (by simpa using ih (dom :: Γ₁) Γ₂ T (v.shift 0) rfl hv')
  | app _ _ ihf iha =>
      intro Γ₁ Γ₂ T v hΓ hv
      rw [Term.subst_app]
      exact .app (ihf Γ₁ Γ₂ T v hΓ hv) (iha Γ₁ Γ₂ T v hΓ hv)
  | @letE Γ bound body T' U' _ _ ihb ihbody =>
      intro Γ₁ Γ₂ T v hΓ hv
      subst hΓ
      rw [Term.subst_letE]
      refine .letE (ihb Γ₁ Γ₂ T v rfl hv) ?_
      have hv' : HasTy (T' :: (Γ₁ ++ Γ₂)) (v.shift 0) T := by
        simpa using hv.weaken [] (Γ₁ ++ Γ₂) T' rfl
      exact (by simpa using ihbody (T' :: Γ₁) Γ₂ T (v.shift 0) rfl hv')
  | @tuple Γ es Ts hlen _ ih =>
      intro Γ₁ Γ₂ T v hΓ hv
      rw [Term.subst_tuple]
      refine .tuple (by simpa using hlen) ?_
      intro i e T' h1 h2
      rw [List.getElem?_map] at h1
      cases hes : es[i]? with
      | none => rw [hes] at h1; simp at h1
      | some e0 =>
          rw [hes] at h1
          simp at h1
          subst h1
          exact ih i e0 T' hes h2 Γ₁ Γ₂ T v hΓ hv
  | proj _ hi ih =>
      intro Γ₁ Γ₂ T v hΓ hv
      rw [Term.subst_proj]
      exact .proj (ih Γ₁ Γ₂ T v hΓ hv) hi
  | variant hfrag _ hlk ih =>
      intro Γ₁ Γ₂ T v hΓ hv
      rw [Term.subst_variant]
      exact .variant hfrag (ih Γ₁ Γ₂ T v hΓ hv) hlk
  | @caseE Γ scrut arms U' tags hU _ hcov _ ihscrut iharms =>
      intro Γ₁ Γ₂ T v hΓ hv
      subst hΓ
      rw [Term.subst_caseE]
      refine .caseE hU (ihscrut Γ₁ Γ₂ T v rfl hv) ?_ ?_
      · intro tag T' hlk
        rw [lookup_map_snd]
        simpa using hcov tag T' hlk
      · intro tag T' body' hlk harm
        rw [lookup_map_snd] at harm
        cases harms0 : arms.lookup tag with
        | none => rw [harms0] at harm; simp at harm
        | some body0 =>
            rw [harms0] at harm
            simp at harm
            subst harm
            have hv' : HasTy (T' :: (Γ₁ ++ Γ₂)) (v.shift 0) T := by
              simpa using hv.weaken [] (Γ₁ ++ Γ₂) T' rfl
            have harm' := iharms tag T' body0 hlk harms0 (T' :: Γ₁) Γ₂ T
              (v.shift 0) rfl hv'
            simpa using harm'
  | cast _ hne hcl hbase ih =>
      intro Γ₁ Γ₂ T v hΓ hv
      rw [Term.subst_cast]
      exact .cast (ih Γ₁ Γ₂ T v hΓ hv) hne hcl hbase
  | refineV _ hval hch hne hcl hbase ih =>
      intro Γ₁ Γ₂ T v hΓ hv
      exact .refineV (ih Γ₁ Γ₂ T v hΓ hv) (hval.subst _ _)
        (by rw [Term.refinementsHold_subst hval]; exact hch) hne hcl hbase
  | sub _ hsub hfrag ih =>
      intro Γ₁ Γ₂ T v hΓ hv
      exact .sub (ih Γ₁ Γ₂ T v hΓ hv) hsub hfrag

/-- The working corollary: substituting a term of the binder's type under
one binder. -/
theorem HasTy.subst_one {Γ : List Ty} {body v : Term} {T U : Ty}
    (hbody : HasTy (T :: Γ) body U) (hv : HasTy Γ v T) :
    HasTy Γ (Term.subst 0 v body) U := by
  simpa using hbody.subst_preserves [] Γ T v rfl (by simpa using hv)

/-! ## Canonical forms (modulo refinement peeling)

Each is an induction over the typing derivation: the head rule supplies the shape, `refineV` peels a
layer, and `sub` crosses one relation link via `subtyping_peel_inv` plus the head inversion. `IsVal`
dismisses every non-value
rule. -/

theorem HasTy.canonical_fn {Γ : List Ty} {v : Term} {W : Ty}
    (h : HasTy Γ v W) :
    v.IsVal → ∀ n k d c, W.peel.1 = .fn n k d c →
      ∃ dom body, v = .lam dom body := by
  induction h with
  | lit l =>
      intro _ n k d c hW
      cases l <;> simp [Lit.ty, Ty.peel] at hW
  | lam _ _ _ => exact fun _ n k d c _ => ⟨_, _, rfl⟩
  | var _ => intro hv; cases hv
  | app _ _ _ _ => intro hv; cases hv
  | letE _ _ _ _ => intro hv; cases hv
  | tuple _ _ _ =>
      intro _ n k d c hW
      simp [Ty.peel] at hW
  | proj _ _ _ => intro hv; cases hv
  | variant _ _ _ _ =>
      intro _ n k d c hW
      simp [Ty.peel] at hW
  | caseE _ _ _ _ _ _ => intro hv; cases hv
  | cast _ _ _ _ _ => intro hv; cases hv
  | refineV _ _ _ _ _ _ ih =>
      intro hv n k d c hW
      simp only [Ty.peel] at hW
      exact ih hv n k d c hW
  | @sub Γ' e S W' _ hsub hfrag ih =>
      intro hv n k d c hW
      have hpeel := (subtyping_peel_inv hsub).2
      rw [hW] at hpeel
      obtain ⟨n', k', d', c', hS⟩ := hpeel.fn_src (Ty.peel_fst_not_refined _)
      exact ih hv n' k' d' c' hS

theorem HasTy.canonical_tuple {Γ : List Ty} {v : Term} {W : Ty}
    (h : HasTy Γ v W) :
    v.IsVal → ∀ Ts, W.peel.1 = .tuple Ts →
      ∃ es, v = .tuple es ∧ Ts.length ≤ es.length ∧
        (∀ (i : Nat) e T, es[i]? = some e → Ts[i]? = some T → HasTy Γ e T) := by
  induction h with
  | lit l =>
      intro _ Ts hW
      cases l <;> simp [Lit.ty, Ty.peel] at hW
  | lam _ _ _ =>
      intro _ Ts hW
      simp [Ty.peel] at hW
  | var _ => intro hv; cases hv
  | app _ _ _ _ => intro hv; cases hv
  | letE _ _ _ _ => intro hv; cases hv
  | @tuple Γ' es Ts' hlen helem _ =>
      intro _ Ts hW
      rw [Ty.peel_of_not_refined (by simp [Ty.isRefined])] at hW
      injection hW with hTs
      subst hTs
      exact ⟨es, rfl, Nat.le_of_eq hlen.symm, helem⟩
  | proj _ _ _ => intro hv; cases hv
  | variant _ _ _ _ =>
      intro _ Ts hW
      simp [Ty.peel] at hW
  | caseE _ _ _ _ _ _ => intro hv; cases hv
  | cast _ _ _ _ _ => intro hv; cases hv
  | refineV _ _ _ _ _ _ ih =>
      intro hv Ts hW
      simp only [Ty.peel] at hW
      exact ih hv Ts hW
  | @sub Γ' e S W' _ hsub hfrag ih =>
      intro hv Ts hW
      have hpeel := (subtyping_peel_inv hsub).2
      rw [hW] at hpeel
      obtain ⟨Ss, hS, hwidth, hsubel⟩ :=
        hpeel.tuple_inv (Ty.peel_fst_not_refined _)
      obtain ⟨es, hes, hlen', hty⟩ := ih hv Ss hS
      have hWp : (Ty.tuple Ts).TermFragment := hW ▸ hfrag.peel_fst
      refine ⟨es, hes, Nat.le_trans hwidth hlen', ?_⟩
      intro i e T h1 h2
      have hiS : i < Ss.length := by
        have := (List.getElem?_eq_some_iff.mp h2).1
        omega
      have hSs : Ss[i]? = some Ss[i] := List.getElem?_eq_getElem hiS
      have hTfrag : T.TermFragment := by
        cases hWp with | tuple ha => exact ha _ (List.mem_of_getElem? h2)
      exact (hty i e Ss[i] h1 hSs).sub (hsubel i Ss[i] T hSs h2) hTfrag

theorem HasTy.canonical_variant {Γ : List Ty} {v : Term} {W : Ty}
    (h : HasTy Γ v W) :
    v.IsVal → ∀ tags, W.peel.1 = .variant tags →
      ∃ tag w T, v = .variant tag w ∧ lookupBy tags tag = some T ∧
        HasTy Γ w T := by
  induction h with
  | lit l =>
      intro _ tags hW
      cases l <;> simp [Lit.ty, Ty.peel] at hW
  | lam _ _ _ =>
      intro _ tags hW
      simp [Ty.peel] at hW
  | var _ => intro hv; cases hv
  | app _ _ _ _ => intro hv; cases hv
  | letE _ _ _ _ => intro hv; cases hv
  | tuple _ _ _ =>
      intro _ tags hW
      simp [Ty.peel] at hW
  | proj _ _ _ => intro hv; cases hv
  | @variant Γ' e tag T tags' hfrag hty hlk =>
      intro _ tags hW
      rw [Ty.peel_of_not_refined (by simp [Ty.isRefined])] at hW
      injection hW with htags
      subst htags
      exact ⟨tag, e, T, rfl, by rw [lookupBy_eq_lookup]; exact hlk, hty⟩
  | caseE _ _ _ _ _ _ => intro hv; cases hv
  | cast _ _ _ _ _ => intro hv; cases hv
  | refineV _ _ _ _ _ _ ih =>
      intro hv tags hW
      simp only [Ty.peel] at hW
      exact ih hv tags hW
  | @sub Γ' e S W' _ hsub hfrag ih =>
      intro hv tags hW
      have hpeel := (subtyping_peel_inv hsub).2
      rw [hW] at hpeel
      obtain ⟨tagsS, hS, hpay⟩ :=
        hpeel.variant_inv (Ty.peel_fst_not_refined _)
      obtain ⟨tag, w, T', hw, hlkS, hty⟩ := ih hv tagsS hS
      obtain ⟨T, hlkW, hsubT⟩ := hpay tag T' (lookupBy_mem hlkS)
      have hWp : (Ty.variant tags).TermFragment := hW ▸ hfrag.peel_fst
      have hTfrag : T.TermFragment := by
        cases hWp with | variant ha => exact ha _ (lookupBy_mem hlkW)
      exact ⟨tag, w, T, hw, hlkW, hty.sub hsubT hTfrag⟩

/-! ## Lambda inversion by typing transport -/

/-- Typing transport: whatever is typed at `X` (in any context) is typed at
`Y`. The inversion's slack — reflexive without `Subtyping.refl`'s `WellFormed` side condition, and
composable across a subsumption chain without transitivity
of `Subtyping`. -/
def TyImplication (X Y : Ty) : Prop := ∀ (Δ : List Ty) (a : Term), HasTy Δ a X → HasTy Δ a Y

theorem HasTy.lam_inv {Γ : List Ty} {L : Term} {W : Ty} (h : HasTy Γ L W) :
    ∀ {d body}, L = .lam d body → (∀ X ∈ Γ, X.TermFragment) →
      ∀ n k dom cod, W.peel.1 = .fn n k dom cod →
        ∃ c₀, HasTy (d :: Γ) body c₀ ∧ TyImplication dom d ∧ TyImplication c₀ cod := by
  induction h with
  | lit l => intro d body hL; simp at hL
  | var _ => intro d body hL; simp at hL
  | @lam Γ' dom' body' cod' hfrag hbody =>
      intro d body hL hΓ n k dom cod hW
      injection hL with h1 h2
      subst h1; subst h2
      rw [Ty.peel_of_not_refined (by simp [Ty.isRefined])] at hW
      injection hW with hn hk hdom hcod
      subst hdom; subst hcod
      exact ⟨_, hbody, fun Δ a ha => ha, fun Δ a ha => ha⟩
  | app _ _ _ _ => intro d body hL; simp at hL
  | letE _ _ _ _ => intro d body hL; simp at hL
  | tuple _ _ _ => intro d body hL; simp at hL
  | proj _ _ _ => intro d body hL; simp at hL
  | variant _ _ _ _ => intro d body hL; simp at hL
  | caseE _ _ _ _ _ _ => intro d body hL; simp at hL
  | cast _ _ _ _ _ => intro d body hL; simp at hL
  | refineV _ _ _ _ _ _ ih =>
      intro d body hL hΓ n k dom cod hW
      simp only [Ty.peel] at hW
      exact ih hL hΓ n k dom cod hW
  | @sub Γ' e S W' hty hsub hfrag ih =>
      intro d body hL hΓ n k dom cod hW
      subst hL
      have hpeel := (subtyping_peel_inv hsub).2
      rw [hW] at hpeel
      obtain ⟨n', k', d', c', hS⟩ := hpeel.fn_src (Ty.peel_fst_not_refined _)
      rw [hS] at hpeel
      have hSfrag : S.TermFragment := hasTy_fragment hty hΓ
      have hSp : (Ty.fn n' k' d' c').TermFragment := hS ▸ hSfrag.peel_fst
      have hWp : (Ty.fn n k dom cod).TermFragment := hW ▸ hfrag.peel_fst
      cases hSp with | fn hd' hc' =>
      cases hWp with | fn hdW hcW =>
      obtain ⟨hdom_sub, hcod_sub⟩ := hpeel.fn_inv
      have hcod_id : Subtyping c' cod := hcod_sub
      obtain ⟨c₀, hbody, himp_dom, himp_cod⟩ := ih rfl hΓ n' k' d' c' hS
      refine ⟨c₀, hbody, ?_, ?_⟩
      · exact fun Δ a ha => himp_dom Δ a (ha.sub hdom_sub hd')
      · exact fun Δ a ha => (himp_cod Δ a ha).sub hcod_id hcW

/-! ## Progress -/

/-- Per-element progress split: a list of progressing terms is all values,
or has a first non-value element that steps or blocks. -/
theorem progress_split {es : List Term}
    (h : ∀ e ∈ es, e.IsVal ∨ (∃ e', Term.Step e e') ∨ Term.Blocked e) :
    (∀ e ∈ es, e.IsVal) ∨
      ∃ pre e post, es = pre ++ e :: post ∧ (∀ x ∈ pre, x.IsVal) ∧
        ((∃ e', Term.Step e e') ∨ Term.Blocked e) := by
  induction es with
  | nil => exact .inl (by simp)
  | cons a t ih =>
      rcases h a (by simp) with hva | hst
      · rcases ih (fun e he => h e (by simp [he])) with hall | hsplit
        · refine .inl fun e he => ?_
          rcases List.mem_cons.mp he with rfl | he
          · exact hva
          · exact hall e he
        · obtain ⟨pre, e0, post, heq, hpre, hact⟩ := hsplit
          refine .inr ⟨a :: pre, e0, post, by rw [heq]; rfl, ?_, hact⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hva
          · exact hpre x hx
      · exact .inr ⟨[], a, t, rfl, by simp, hst⟩

theorem progress_aux {Γ : List Ty} {e : Term} {T : Ty} (h : HasTy Γ e T) :
    Γ = [] → e.IsVal ∨ (∃ e', Term.Step e e') ∨ Term.Blocked e := by
  induction h with
  | lit l => exact fun _ => .inl (.lit l)
  | var hn => intro hΓ; subst hΓ; simp at hn
  | lam _ _ _ => exact fun _ => .inl (.lam _ _)
  | @app Γ' f a n k dom cod hf ha ihf iha =>
      intro hΓ; subst hΓ
      rcases ihf rfl with hvf | hstf
      · rcases iha rfl with hva | hsta
        · obtain ⟨domL, body, rfl⟩ :=
            hf.canonical_fn hvf n k dom cod (by simp [Ty.peel])
          exact .inr (.inl ⟨_, .beta hva⟩)
        · rcases hsta with ⟨a', hsa⟩ | hba
          · exact .inr (.inl ⟨_, .appR hvf hsa⟩)
          · exact .inr (.inr (.appR hvf hba))
      · rcases hstf with ⟨f', hsf⟩ | hbf
        · exact .inr (.inl ⟨_, .appL hsf⟩)
        · exact .inr (.inr (.appL hbf))
  | letE _ _ ihb _ =>
      intro hΓ; subst hΓ
      rcases ihb rfl with hvb | hstb
      · exact .inr (.inl ⟨_, .letV hvb⟩)
      · rcases hstb with ⟨b', hsb⟩ | hbb
        · exact .inr (.inl ⟨_, .letL hsb⟩)
        · exact .inr (.inr (.letL hbb))
  | @tuple Γ' es Ts hlen _ ih =>
      intro hΓ; subst hΓ
      have hprog : ∀ e ∈ es, e.IsVal ∨ (∃ e', Term.Step e e') ∨ Term.Blocked e := by
        intro e he
        obtain ⟨i, hi⟩ := List.getElem?_of_mem he
        have hilt : i < es.length := (List.getElem?_eq_some_iff.mp hi).1
        have hTs : Ts[i]? = some Ts[i] := List.getElem?_eq_getElem (by omega)
        exact ih i e Ts[i] hi hTs rfl
      rcases progress_split hprog with hall | hsplit
      · exact .inl (.tuple hall)
      · obtain ⟨pre, e0, post, rfl, hpre, hact⟩ := hsplit
        rcases hact with ⟨e', hs⟩ | hb
        · exact .inr (.inl ⟨_, .tupleAt hpre hs⟩)
        · exact .inr (.inr (.tupleAt hpre hb))
  | @proj Γ' e0 i Ts T he hi ih =>
      intro hΓ; subst hΓ
      rcases ih rfl with hve | hste
      · obtain ⟨es, rfl, hwidth, _⟩ :=
          he.canonical_tuple hve Ts (by simp [Ty.peel])
        have hilt : i < es.length := by
          have := (List.getElem?_eq_some_iff.mp hi).1
          omega
        have hes : es[i]? = some es[i] := List.getElem?_eq_getElem hilt
        cases hve with
        | tuple hall => exact .inr (.inl ⟨_, .projV hall hes⟩)
      · rcases hste with ⟨e', hs⟩ | hb
        · exact .inr (.inl ⟨_, .projE hs⟩)
        · exact .inr (.inr (.projE hb))
  | variant _ _ _ ih =>
      intro hΓ; subst hΓ
      rcases ih rfl with hve | hste
      · exact .inl (.variant _ hve)
      · rcases hste with ⟨e', hs⟩ | hb
        · exact .inr (.inl ⟨_, .variantE hs⟩)
        · exact .inr (.inr (.variantE hb))
  | @caseE Γ' scrut arms U tags hU hscrut hcov _ ihscrut _ =>
      intro hΓ; subst hΓ
      rcases ihscrut rfl with hvs | hsts
      · obtain ⟨tag, w, T', rfl, hlk, _⟩ :=
          hscrut.canonical_variant hvs tags (by simp [Ty.peel])
        rw [lookupBy_eq_lookup] at hlk
        obtain ⟨body, hbody⟩ := Option.isSome_iff_exists.mp (hcov tag T' hlk)
        have hw : w.IsVal := by cases hvs with | variant _ hw => exact hw
        exact .inr (.inl ⟨_, .caseV hw hbody⟩)
      · rcases hsts with ⟨s', hs⟩ | hb
        · exact .inr (.inl ⟨_, .caseS hs⟩)
        · exact .inr (.inr (.caseS hb))
  | @cast Γ' e0 T0 refinements _ _ _ _ ih =>
      intro hΓ; subst hΓ
      rcases ih rfl with hve | hste
      · cases hch : Term.refinementsHold refinements e0 with
        | true => exact .inr (.inl ⟨_, .castV hve hch⟩)
        | false => exact .inr (.inr (.castV hve hch))
      · rcases hste with ⟨e', hs⟩ | hb
        · exact .inr (.inl ⟨_, .castE hs⟩)
        · exact .inr (.inr (.castE hb))
  | refineV _ hval _ _ _ _ _ => exact fun _ => .inl hval
  | sub _ _ _ ih => exact ih

/-- **Progress**, modulo filtering: a well-typed closed term is a value,
steps, or is filter-blocked at a cast (the scalar face of a `Restrict`
dropping the element). -/
theorem progress {e : Term} {T : Ty} (h : HasTy [] e T) :
    e.IsVal ∨ (∃ e', Term.Step e e') ∨ Term.Blocked e :=
  progress_aux h rfl

/-! ## Preservation -/

theorem preservation_aux {Γ : List Ty} {e : Term} {T : Ty} (h : HasTy Γ e T) :
    ∀ e', Term.Step e e' → (∀ X ∈ Γ, X.TermFragment) → HasTy Γ e' T := by
  induction h with
  | lit l => intro e' hs; cases hs
  | var _ => intro e' hs; cases hs
  | lam _ _ _ => intro e' hs; cases hs
  | @app Γ' f a n k dom cod hf ha ihf iha =>
      intro e' hs hΓ
      cases hs with
      | appL hsf => exact .app (ihf _ hsf hΓ) ha
      | appR hvf hsa => exact .app hf (iha _ hsa hΓ)
      | beta hva =>
          obtain ⟨c₀, hbody, himp_dom, himp_cod⟩ :=
            hf.lam_inv rfl hΓ n k dom cod (by simp [Ty.peel])
          exact himp_cod _ _ (hbody.subst_one (himp_dom _ _ ha))
  | @letE Γ' bound body T' U' hb hbody ihb _ =>
      intro e' hs hΓ
      cases hs with
      | letL hsb => exact .letE (ihb _ hsb hΓ) hbody
      | letV hvb => exact hbody.subst_one hb
  | @tuple Γ' es Ts hlen helem ih =>
      intro e' hs hΓ
      cases hs with
      | @tupleAt pre e0 e0' post hpre hstep =>
          refine .tuple (by simpa using hlen) ?_
          intro i e T h1 h2
          by_cases hip : i = pre.length
          · subst hip
            rw [List.getElem?_append_right (Nat.le_refl _)] at h1
            simp at h1
            subst h1
            have h0 : (pre ++ e0 :: post)[pre.length]? = some e0 := by
              rw [List.getElem?_append_right (Nat.le_refl _)]; simp
            exact ih _ e0 T h0 h2 _ hstep hΓ
          · have hsame : (pre ++ e0' :: post)[i]? = (pre ++ e0 :: post)[i]? := by
              by_cases hlt : i < pre.length
              · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
              · have hge : pre.length ≤ i := Nat.le_of_not_lt hlt
                rw [List.getElem?_append_right hge,
                  List.getElem?_append_right hge]
                have hi1 : i - pre.length = (i - pre.length - 1) + 1 := by omega
                rw [hi1, List.getElem?_cons_succ, List.getElem?_cons_succ]
            rw [hsame] at h1
            exact helem i e T h1 h2
  | @proj Γ' e0 i Ts T he hi ih =>
      intro e' hs hΓ
      cases hs with
      | projE hse => exact .proj (ih _ hse hΓ) hi
      | projV hall hes =>
          obtain ⟨es', heq, _, hty⟩ :=
            he.canonical_tuple (.tuple hall) Ts (by simp [Ty.peel])
          injection heq with heq
          subst heq
          exact hty i _ T hes hi
  | variant hfrag _ hlk ih =>
      intro e' hs hΓ
      cases hs with
      | variantE hse => exact .variant hfrag (ih _ hse hΓ) hlk
  | @caseE Γ' scrut arms U tags hU hscrut hcov harms ihs _ =>
      intro e' hs hΓ
      cases hs with
      | caseS hss => exact .caseE hU (ihs _ hss hΓ) hcov harms
      | caseV hw hbody =>
          obtain ⟨tag', w', T', heq, hlk, hwty⟩ :=
            hscrut.canonical_variant (.variant _ hw) tags (by simp [Ty.peel])
          injection heq with heq1 heq2
          subst heq1
          subst heq2
          rw [lookupBy_eq_lookup] at hlk
          exact (harms _ T' _ hlk hbody).subst_one hwty
  | cast hty hne hcl hbase ih =>
      intro e' hs hΓ
      cases hs with
      | castE hse => exact .cast (ih _ hse hΓ) hne hcl hbase
      | castV hve hch => exact .refineV hty hve hch hne hcl hbase
  | refineV _ hval _ _ _ _ _ =>
      intro e' hs
      exact absurd hs hval.not_step
  | sub _ hsub hfrag ih =>
      intro e' hs hΓ
      exact .sub (ih _ hs hΓ) hsub hfrag

/-- **Preservation**: one step keeps the type, under a fragment context. -/
theorem preservation {Γ : List Ty} {e e' : Term} {T : Ty}
    (hΓ : ∀ X ∈ Γ, X.TermFragment) (h : HasTy Γ e T) (hs : Term.Step e e') :
    HasTy Γ e' T :=
  preservation_aux h e' hs hΓ

/-! ## Multi-step evaluation and refinement soundness -/

/-- Reflexive-transitive closure of `Step`. -/
inductive Term.Steps : Term → Term → Prop
  | refl (e : Term) : Term.Steps e e
  | head {e e' e''} : Term.Step e e' → Term.Steps e' e'' → Term.Steps e e''

theorem preservation_star {Γ : List Ty} {e e' : Term}
    (hs : Term.Steps e e') (hΓ : ∀ X ∈ Γ, X.TermFragment) :
    ∀ {T : Ty}, HasTy Γ e T → HasTy Γ e' T := by
  induction hs with
  | refl _ => exact fun h => h
  | head hstep _ ih => exact fun h => ih (preservation hΓ h hstep)

/-- A value's ascribed refinements all evaluate true on it: `refineV` supplies
them checked, `sub` only ever shrinks them (`Subtyping.refinements_mono`), and no
other rule types a value at a refined type. -/
theorem HasTy.value_refinements {Γ : List Ty} {v : Term} {W : Ty}
    (h : HasTy Γ v W) :
    v.IsVal → ∀ p ∈ W.peel.2, Predicate.eval v p = some (.bool true) := by
  induction h with
  | lit l => intro _ p hp; cases l <;> simp [Lit.ty, Ty.peel] at hp
  | lam _ _ _ => intro _ p hp; simp [Ty.peel] at hp
  | var _ => intro hv; cases hv
  | app _ _ _ _ => intro hv; cases hv
  | letE _ _ _ _ => intro hv; cases hv
  | tuple _ _ _ => intro _ p hp; simp [Ty.peel] at hp
  | proj _ _ _ => intro hv; cases hv
  | variant _ _ _ _ => intro _ p hp; simp [Ty.peel] at hp
  | caseE _ _ _ _ _ _ => intro hv; cases hv
  | cast _ _ _ _ _ => intro hv; cases hv
  | refineV _ _ hch _ _ _ ih =>
      intro hv p hp
      simp only [Ty.peel, List.mem_append] at hp
      rcases hp with hp | hp
      · exact eq_of_beq (List.all_eq_true.mp hch p hp)
      · exact ih hv p hp
  | sub _ hsub _ ih =>
      intro hv p hp
      exact ih hv p (hsub.refinements_mono p hp)

/-- **Refinement soundness**: a closed term of refined type that evaluates
to a value satisfies every refinement — the cast is the only door, and the
`castV` step checks exactly this set. -/
theorem refinement_soundness {e v : Term} {T : Ty} {refinements : List Predicate}
    (h : HasTy [] e (.refined T refinements)) (hs : Term.Steps e v)
    (hv : v.IsVal) : Term.refinementsHold refinements v = true := by
  have hty := preservation_star hs (by simp) h
  have hcl := hty.value_refinements hv
  unfold Term.refinementsHold
  rw [List.all_eq_true]
  intro p hp
  have := hcl p (by simp [Ty.peel]; exact .inl hp)
  rw [this]
  rfl

/-! ## Case-binder soundness -/

/-- The naive case-binder statement, for tag arms: the payload of a
well-typed variant value really has the type the scrutinee's tag table assigns — so `caseV`'s
substitution feeds each arm's binder a value of the bound it was typed under. The Rust's `case _:`
payload-binder defect lives in *wildcard* arms, which this model does not yet have; refuting the
naive statement there needs that extension (recorded in `Term.lean`'s module
docs as a later increment). -/
theorem case_binder_sound {Γ : List Ty} {v : Term} {tag : FieldKey}
    {tags : List (FieldKey × Ty)}
    (h : HasTy Γ (.variant tag v) (.variant tags))
    (hv : (Term.variant tag v).IsVal) :
    ∃ T, lookupBy tags tag = some T ∧ HasTy Γ v T := by
  obtain ⟨tag', w, T, heq, hlk, hty⟩ :=
    h.canonical_variant hv tags (by simp [Ty.peel])
  injection heq with h1 h2
  subst h1
  subst h2
  exact ⟨T, hlk, hty⟩

end CclFormal
