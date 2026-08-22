import CclFormal.Coalesce
import CclFormal.Equiv

/-!
# M4c — the bridge: `merge` is the subtyping join

`Merge.lean` proves `merge pol` is the least upper bound of the order it induces
(`merge_isLub`), and that order is defined *by* the merge. This module states the
theorem that names the order independently: the merged position materializes to
the `Sub`-least upper bound of what its operands materialize to, and dually at a
negative position.

The statements are `Bool`-valued on purpose. `subCheck` decides `Sub`
(`subCheck_iff_sub`) and `coalesce` is total, so each is measurable over a
bounded sample before it is proved, and the sample is what caught the shapes
recorded in `formal/design.md`, "M4c — the lattice, and what a merge means".
-/

namespace CclFormal
namespace CTy

/-- The soundness half at one pair: where all three positions materialize, a
positive merge lands above both operands and a negative one below both.

Conditional on materializing, which is the honest form — `coalesce` is partial,
and its failures are exactly the joins no `Ty` names. -/
def LubSoundAt (pol : Bool) (a b : CTy) : Bool :=
  match coalesce pol a, coalesce pol b, coalesce pol (merge pol a b) with
  | .ok (some ta), .ok (some tb), .ok (some tm) =>
      if pol then subCheck ta tm && subCheck tb tm
      else subCheck tm ta && subCheck tm tb
  | _, _, _ => true

/-! ## Ground positions

`wf` excludes `KindM.conflict`. `KindM.unknown` is the other non-ground kind — a
kind variable nothing has pinned — and it is not a subject for a subtyping
statement: `coalesce` materializes it by applying the capability default, a merge
that pins the slot to `data` overrides that default, and so the operand's own
materialization is not what the merge combined. `kindResolved` is what "ground"
means for the kind slot, and the bridge theorem assumes it. -/

mutual

def kindResolved : CTy → Bool
  | .mk _ r v f _ =>
    (match r with
     | none => true
     | some m => kindResolvedKeys m (m.map Prod.fst))
      && (match v with
          | none => true
          | some m => kindResolvedKeys m (m.map Prod.fst))
      && (match f with
          | none => true
          | some (k, d, cod) =>
            (k == .data || k == .compute) && kindResolvedAll d && kindResolved cod)
termination_by t => (sizeOf t, 0)

/-- All payloads of a map are `kindResolved` (worklist form, as `wfKeys`). -/
def kindResolvedKeys (m : List (FieldKey × CTy)) : List FieldKey → Bool
  | [] => true
  | k :: ks =>
    (match h : m.lookup k with
     | some v => kindResolved v
     | none => true)
      && kindResolvedKeys m ks
termination_by ks => (sizeOf m, ks.length)
decreasing_by
  · have := lookup_sizeOf h
    apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    simp

/-- Every domain alternative of a slot is `kindResolved`. -/
def kindResolvedAll : List CTy → Bool
  | [] => true
  | d :: ds => kindResolved d && kindResolvedAll ds
termination_by ds => (sizeOf ds, 0)
decreasing_by
  · apply Prod.Lex.left
    simp
    omega
  · apply Prod.Lex.left
    simp
    omega

end

/-- Ground: the input-bound invariant plus a concrete kind at every function
slot. What the bridge theorem assumes of a single position. -/
def ground (t : CTy) : Bool := wf t && kindResolved t

/-- Pointwise reading of `kindResolvedKeys`, as `wfKeys_iff`. -/
theorem kindResolvedKeys_iff {m : List (FieldKey × CTy)} {ks : List FieldKey} :
    kindResolvedKeys m ks = true ↔
      ∀ k ∈ ks, ∀ v, m.lookup k = some v → kindResolved v = true := by
  induction ks with
  | nil => simp [kindResolvedKeys]
  | cons k ks ih =>
    rw [kindResolvedKeys, Bool.and_eq_true, ih]
    constructor
    · intro ⟨hhead, htail⟩ k' hk'
      rcases List.mem_cons.mp hk' with h | h
      · subst h
        intro v hv
        rw [hv] at hhead
        exact hhead
      · exact htail k' h
    · intro h
      refine ⟨?_, fun k' hk' => h k' (by simp [hk'])⟩
      rcases hv : m.lookup k with _ | v
      · rfl
      · exact h k (by simp) v hv

/-- The lemma both halves factor through: `coalesce pol` carries `le pol` to
`Sub` at a positive position and to its converse at a negative one. Soundness is
this applied to `le_merge_left`/`le_merge_right`; leastness is `merge_le`
transported back through an embedding of `Ty` into `CTy`. -/
def MonoAt (pol : Bool) (a b : CTy) : Bool :=
  if eqv (merge pol a b) b then
    match coalesce pol a, coalesce pol b with
    | .ok (some ta), .ok (some tb) => if pol then subCheck ta tb else subCheck tb ta
    | _, _ => true
  else true

/-! ## One slot at a time

A position with a single populated slot materializes to that slot's contribution
with the position's refinements attached: the other three helpers answer `none` and
their `if` drops them, so `combine` sees one entry. -/

theorem coalesce_atoms_only (pol : Bool) (as : List Atom) (c : Option (List Pred)) :
    coalesce pol (.mk as none none none c) =
      combine ((as.map atomTy).eraseDups.map some) c := by
  rw [coalesce, recShapes_none, varShapes_none, funShapes_none]
  show combine ((as.map atomTy).eraseDups.map some ++ [] ++ [] ++ []) c = _
  simp

theorem coalesce_rec_only (pol : Bool) (m : List (FieldKey × CTy)) (c : Option (List Pred)) :
    coalesce pol (.mk [] (some m) none none c) =
      (do
        let x ← recShapes pol (.mk [] (some m) none none c)
        .ok (x.map (attachRefinements · c))) := by
  rw [coalesce, varShapes_none, funShapes_none]
  rcases h : recShapes pol (.mk [] (some m) none none c) with e | x
  · rfl
  · show combine ([] ++ [x] ++ [] ++ []) c = _
    simp [combine]
    rfl

theorem coalesce_var_only (pol : Bool) (m : List (FieldKey × CTy)) (c : Option (List Pred)) :
    coalesce pol (.mk [] none (some m) none c) =
      (do
        let x ← varShapes pol (.mk [] none (some m) none c)
        .ok (x.map (attachRefinements · c))) := by
  rw [coalesce, recShapes_none, funShapes_none]
  rcases h : varShapes pol (.mk [] none (some m) none c) with e | x
  · rfl
  · show combine ([] ++ [] ++ [x] ++ []) c = _
    simp [combine]
    rfl

theorem coalesce_fun_only (pol : Bool) (g : KindM × List CTy × CTy) (c : Option (List Pred)) :
    coalesce pol (.mk [] none none (some g) c) =
      (do
        let x ← funShapes pol (.mk [] none none (some g) c)
        .ok (x.map (attachRefinements · c))) := by
  rw [coalesce, recShapes_none, varShapes_none]
  rcases h : funShapes pol (.mk [] none none (some g) c) with e | x
  · rfl
  · show combine ([] ++ [] ++ [] ++ [x]) c = _
    simp [combine]
    rfl

/-! ## The atoms case

The first case of `MonoAt`'s proof. Materializing at all means exactly one of the
atom, record, variant, and function shapes is populated, and `le pol a b` forces
the same one on both sides, so each case reasons about a single slot. -/

/-- `coalesce` on a position whose only content is atoms and refinements. -/
theorem coalesce_atoms (pol : Bool) (as : List Atom) (c : Option (List Pred)) :
    coalesce pol (.mk as none none none c) =
      (match (as.map atomTy).eraseDups with
       | [] => .ok none
       | [t] => .ok (some (attachRefinements t c))
       | _ => .error .incompatible) := by
  rw [coalesce_atoms_only]
  rcases h : (as.map atomTy).eraseDups with _ | ⟨x, xs⟩
  · simp [combine]
  · rcases xs with _ | ⟨y, ys⟩
    · simp [combine]
    · simp [combine]

/-- Refinements ride a subtyping edge: the side with more refinements stays the subtype, and
the sets compare by membership, as `RefinementSet` does. -/
theorem subCheck_attachRefinements {t u : Ty} {p q : List Pred}
    (hnrt : t.isRefined = false) (hnru : u.isRefined = false)
    (htu : subCheck t u = true) (hq : ∀ x ∈ q, x ∈ p) :
    subCheck (attachRefinements t (some p)) (attachRefinements u (some q)) = true := by
  have hpt : t.peel = (t, []) := Ty.peel_of_not_refined hnrt
  have hpu : u.peel = (u, []) := Ty.peel_of_not_refined hnru
  rcases p with _ | ⟨x, xs⟩
  · rcases q with _ | ⟨y, ys⟩
    · simpa [attachRefinements] using htu
    · exact absurd (hq y (by simp)) (by simp)
  · have hlhs : attachRefinements t (some (x :: xs)) = .refined t (x :: xs) := by
      cases t <;> simp_all [attachRefinements, Ty.isRefined]
    rcases q with _ | ⟨y, ys⟩
    · rw [hlhs]
      simp only [attachRefinements, subCheck, Ty.peel, hpt, hpu, deficit]
      simpa using htu
    · have hrhs : attachRefinements u (some (y :: ys)) = .refined u (y :: ys) := by
        cases u <;> simp_all [attachRefinements, Ty.isRefined]
      rw [hlhs, hrhs]
      simp only [subCheck, Ty.peel, hpt, hpu, deficit, List.append_nil]
      simp_all
      exact ⟨fun h => hq.1.resolve_left h, fun a ha h => (hq.2 a ha).resolve_left h⟩

/-! ## Keyed slots

A keyed slot materializes its payloads in the map's order, so the shape's fields
are the map's keys carrying the payloads' types. `KeyedRel` is that relation, and
the three keyed cases all read their slot through it. -/

/-- Two keyed lists carrying the same keys in the same order, payloads related by
`R`. -/
def KeyedRel {α β} (R : α → β → Prop) : List (FieldKey × α) → List (FieldKey × β) → Prop
  | [], [] => True
  | (k, v) :: m, (k', t) :: kvs => k = k' ∧ R v t ∧ KeyedRel R m kvs
  | _, _ => False

/-- A key resolving on the left resolves on the right, to a related payload. -/
theorem KeyedRel.lookup {α β} {R : α → β → Prop} :
    ∀ {m : List (FieldKey × α)} {kvs : List (FieldKey × β)}, KeyedRel R m kvs →
      ∀ {k v}, m.lookup k = some v → ∃ t, kvs.lookup k = some t ∧ R v t
  | [], [], _, _, _, hl => by simp at hl
  | [], _ :: _, h, _, _, _ => by simp [KeyedRel] at h
  | _ :: _, [], h, _, _, _ => by simp [KeyedRel] at h
  | (k, v) :: m, (k', t) :: kvs, h, k₀, v₀, hl => by
    obtain ⟨hk, hR, hrest⟩ := h
    subst hk
    simp only [List.lookup_cons] at hl ⊢
    by_cases hbeq : (k₀ == k) = true
    · rw [hbeq] at hl ⊢
      simp only at hl ⊢
      cases hl
      exact ⟨t, rfl, hR⟩
    · simp only [Bool.not_eq_true] at hbeq
      rw [hbeq] at hl ⊢
      simp only at hl ⊢
      exact KeyedRel.lookup hrest hl

/-- A key resolving on the right resolves on the left, to a related payload —
the converse of [`KeyedRel.lookup`]. -/
theorem KeyedRel.lookup' {α β} {R : α → β → Prop} :
    ∀ {m : List (FieldKey × α)} {kvs : List (FieldKey × β)}, KeyedRel R m kvs →
      ∀ {k t}, kvs.lookup k = some t → ∃ v, m.lookup k = some v ∧ R v t
  | [], [], _, _, _, hl => by simp at hl
  | [], _ :: _, h, _, _, _ => by simp [KeyedRel] at h
  | _ :: _, [], h, _, _, _ => by simp [KeyedRel] at h
  | (k, v) :: m, (k', t) :: kvs, h, k₀, t₀, hl => by
    obtain ⟨hk, hR, hrest⟩ := h
    subst hk
    simp only [List.lookup_cons] at hl ⊢
    by_cases hbeq : (k₀ == k) = true
    · rw [hbeq] at hl ⊢
      simp only at hl ⊢
      cases hl
      exact ⟨v, rfl, hR⟩
    · simp only [Bool.not_eq_true] at hbeq
      rw [hbeq] at hl ⊢
      simp only at hl ⊢
      exact KeyedRel.lookup' hrest hl

/-- The keys of a related pair agree, so a key missing on the left is missing on
the right. -/
theorem KeyedRel.keys {α β} {R : α → β → Prop} :
    ∀ {m : List (FieldKey × α)} {kvs : List (FieldKey × β)}, KeyedRel R m kvs →
      kvs.map Prod.fst = m.map Prod.fst
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [KeyedRel] at h
  | _ :: _, [], h => by simp [KeyedRel] at h
  | (k, v) :: m, (k', t) :: kvs, h => by
    obtain ⟨hk, -, hrest⟩ := h
    subst hk
    simpa using KeyedRel.keys hrest

/-- `coalesce` materializes a keyed slot pointwise: the two `mapM`s it runs give
exactly `KeyedRel`. -/
theorem coalesce_keyed_rel (pol : Bool) :
    ∀ (m : List (FieldKey × CTy)) (payloads : List (Option Ty)) (ts : List Ty),
      m.mapM (fun kv => coalesce pol kv.2) = .ok payloads → payloads.mapM id = some ts →
      KeyedRel (fun v t => coalesce pol v = .ok (some t)) m ((m.map Prod.fst).zip ts)
  | [], payloads, ts, hm, hp => by
    cases mapM_ok_nil hm
    cases mapM_some_nil hp
    trivial
  | (k, v) :: m, payloads, ts, hm, hp => by
    obtain ⟨o, ps, hov, hps, rfl⟩ := mapM_ok_cons hm
    obtain ⟨t, ts', hot, hpts, rfl⟩ := mapM_some_cons hp
    have ho : o = some t := hot
    subst ho
    refine ⟨rfl, hov, ?_⟩
    exact coalesce_keyed_rel pol m ps ts' hps hpts

/-- `coalesce` on a position whose only content is a variant slot and refinements. -/
theorem coalesce_variant_ok (pol : Bool) {m : List (FieldKey × CTy)}
    {c : Option (List Pred)} {ty : Ty}
    (h : coalesce pol (.mk [] none (some m) none c) = .ok (some ty)) :
    ∃ kvs, ty = attachRefinements (.variant kvs) c ∧
      KeyedRel (fun v t => coalesce pol v = .ok (some t)) m kvs := by
  have hattach : m.attach.mapM (fun vp => coalesce pol vp.val.snd)
      = m.mapM (fun kv => coalesce pol kv.2) := by
    have hgen : ∀ (f : FieldKey × CTy → Except CoErr (Option Ty)),
        m.attach.mapM (fun x => f x.1) = m.mapM f := by
      intro f
      simp
    exact hgen (fun kv => coalesce pol kv.2)
  -- Case on the slot's contribution first: that reduces the outer bind, so the
  -- contribution's own shape is read off `hv` rather than through it.
  rcases hv : varShapes pol (.mk [] none (some m) none c) with e | x <;>
    rw [coalesce_var_only, hv] at h
  · cases h
  rcases x with _ | base
  · cases h
  cases h
  rw [varShapes, hattach] at hv
  rcases hpay : m.mapM (fun kv => coalesce pol kv.2) with e | payloads <;> rw [hpay] at hv
  · cases hv
  · -- The remaining bind reduces definitionally, which a type ascription is
    -- enough to say.
    replace hv : (Except.ok ((payloads.mapM id).map
        (fun ts => Ty.variant ((m.map Prod.fst).zip ts))) : Except CoErr (Option Ty))
        = .ok (some base) := hv
    rcases hts : payloads.mapM id with _ | ts <;> rw [hts] at hv
    · cases hv
    · cases hv
      exact ⟨(m.map Prod.fst).zip ts, rfl, coalesce_keyed_rel pol m payloads ts hpay hts⟩

/-- `coalesce` on a position whose only content is a record slot and refinements: the
payloads materialize pointwise, and the shape is a tuple when the keys are dense
indices and a record when they are names. The two refusals — an empty field set and
mixed keys — do not materialize, and the sparse-index shape is unresolved. -/
theorem coalesce_record_ok (pol : Bool) {m : List (FieldKey × CTy)}
    {c : Option (List Pred)} {ty : Ty}
    (h : coalesce pol (.mk [] (some m) none none c) = .ok (some ty)) :
    m ≠ [] ∧ ∃ (ts : List Ty) (base : Ty), ty = attachRefinements base c ∧
      KeyedRel (fun v t => coalesce pol v = .ok (some t)) m ((m.map Prod.fst).zip ts) ∧
      ((∃ idxs, indexKeys m = some idxs ∧ byIndex m.length (idxs.zip ts) = some base) ∨
       (∃ names, nameKeys m = some names ∧ base = .record (names.zip ts))) := by
  have hattach : m.attach.mapM (fun rp => coalesce pol rp.val.snd)
      = m.mapM (fun kv => coalesce pol kv.2) := by
    have hgen : ∀ (f : FieldKey × CTy → Except CoErr (Option Ty)),
        m.attach.mapM (fun x => f x.1) = m.mapM f := by
      intro f
      simp
    exact hgen (fun kv => coalesce pol kv.2)
  rcases hr : recShapes pol (.mk [] (some m) none none c) with e | x <;>
    rw [coalesce_rec_only, hr] at h
  · cases h
  rcases x with _ | base
  · cases h
  cases h
  rw [recShapes, hattach] at hr
  by_cases hm : m.isEmpty = true
  · rw [if_pos hm] at hr
    cases hr
  rw [if_neg hm] at hr
  refine ⟨fun hnil => hm (by simp [hnil]), ?_⟩
  rcases hidx : indexKeys m with _ | idxs <;> rw [hidx] at hr <;> try simp only at hr
  · rcases hnm : nameKeys m with _ | names <;> rw [hnm] at hr <;> try simp only at hr
    · cases hr
    · rcases hpay : m.mapM (fun kv => coalesce pol kv.2) with e | payloads <;> rw [hpay] at hr
      · cases hr
      · replace hr : (Except.ok ((payloads.mapM id).map (fun ts => Ty.record (names.zip ts)))
            : Except CoErr (Option Ty)) = .ok (some base) := hr
        rcases hts : payloads.mapM id with _ | ts <;> rw [hts] at hr
        · cases hr
        · cases hr
          exact ⟨ts, _, rfl, coalesce_keyed_rel pol m payloads ts hpay hts,
            Or.inr ⟨names, rfl, rfl⟩⟩
  · rcases hpay : m.mapM (fun kv => coalesce pol kv.2) with e | payloads <;> rw [hpay] at hr
    · cases hr
    · replace hr : (if (idxs.length == m.length &&
            (List.range m.length).all (idxs.contains ·)) = true
          then Except.ok ((payloads.mapM id).bind (fun ts => byIndex m.length (idxs.zip ts)))
          else Except.ok none : Except CoErr (Option Ty)) = .ok (some base) := hr
      by_cases hd :
        (idxs.length == m.length && (List.range m.length).all (idxs.contains ·)) = true
      · rw [if_pos hd] at hr
        rcases hts : payloads.mapM id with _ | ts <;> rw [hts] at hr <;>
          try simp only [Option.bind_some] at hr
        · cases hr
        · rcases htup : byIndex m.length (idxs.zip ts) with _ | tup <;> rw [htup] at hr
          · cases hr
          · cases hr
            exact ⟨ts, base, rfl, coalesce_keyed_rel pol m payloads ts hpay hts,
              Or.inl ⟨idxs, rfl, htup⟩⟩
      · rw [if_neg hd] at hr
        cases hr

/-- Dedup keeps a non-empty list non-empty, so a position with atoms contributes
a shape. -/
theorem eraseDups_ne_nil {α} [BEq α] [LawfulBEq α] :
    ∀ {l : List α}, l ≠ [] → l.eraseDups ≠ []
  | [], h => absurd rfl h
  | x :: xs, _ => by
    intro hz
    have hmem : x ∈ (x :: xs).eraseDups := List.mem_eraseDups.mpr (by simp)
    rw [hz] at hmem
    simp at hmem

/-- **Materializing means exactly one slot carries the position.** The four
contributions concatenate and `combine` accepts only a singleton, so a position
with two populated slots has no type — which is what lets every case of the
monotonicity lemma be about a single slot. -/
theorem coalesce_shape (pol : Bool) {as : List Atom}
    {r v : Option (List (FieldKey × CTy))} {f : Option (KindM × List CTy × CTy)}
    {c : Option (List Pred)} {ty : Ty}
    (h : coalesce pol (.mk as r v f c) = .ok (some ty)) :
    (as ≠ [] ∧ r = none ∧ v = none ∧ f = none) ∨
    (as = [] ∧ (∃ m, r = some m) ∧ v = none ∧ f = none) ∨
    (as = [] ∧ r = none ∧ (∃ m, v = some m) ∧ f = none) ∨
    (as = [] ∧ r = none ∧ v = none ∧ ∃ g, f = some g) := by
  rw [coalesce] at h
  rcases hr : recShapes pol (.mk as r v f c) with e | rx <;> rw [hr] at h
  · cases h
  rcases hv : varShapes pol (.mk as r v f c) with e | vx <;> rw [hv] at h
  · cases h
  rcases hf : funShapes pol (.mk as r v f c) with e | fx <;> rw [hf] at h
  · cases h
  obtain ⟨t, hlen, -⟩ := combine_ok h
  -- One shape survives, so the four contributions' lengths sum to one. The atom
  -- contribution is non-empty exactly when the atom list is.
  have hcount := congrArg List.length hlen
  have hzero : ((as.map atomTy).eraseDups).length = 0 → as = [] := by
    intro hz
    rcases as with _ | ⟨a, as'⟩
    · rfl
    · exact absurd (List.eq_nil_of_length_eq_zero hz) (eraseDups_ne_nil (by simp))
  have hpos : as ≠ [] → 0 < ((as.map atomTy).eraseDups).length := by
    intro hne
    rcases hd : ((as.map atomTy).eraseDups) with _ | ⟨x, xs⟩
    · exact absurd hd (eraseDups_ne_nil (by simpa using hne))
    · simp [hd]
  rcases r with _ | mr <;> rcases v with _ | mv <;> rcases f with _ | g <;>
    simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, if_false, if_true,
      List.length_append, List.length_map, List.length_nil, List.length_cons,
      Nat.add_zero, Nat.zero_add] at hcount
  · exact Or.inl ⟨fun hnil => by rw [hnil] at hcount; simp at hcount, rfl, rfl, rfl⟩
  · refine Or.inr (Or.inr (Or.inr ⟨?_, rfl, rfl, ⟨g, rfl⟩⟩))
    exact hzero (by omega)
  · refine Or.inr (Or.inr (Or.inl ⟨?_, rfl, ⟨mv, rfl⟩, rfl⟩))
    exact hzero (by omega)
  · exact absurd hcount (by omega)
  · refine Or.inr (Or.inl ⟨?_, ⟨mr, rfl⟩, rfl, rfl⟩)
    exact hzero (by omega)
  · exact absurd hcount (by omega)
  · exact absurd hcount (by omega)
  · exact absurd hcount (by omega)

/-! ## Where the merge had to move a data domain

The function case needs one thing `le` does not give it: at a negative position a
`data` slot's two domains agree. This is not a restriction on which types a data
domain may be — a data domain is refined whenever a filter narrows a collection,
which is most of them. It is a condition on the *pair*, saying the merge did not
have to move a data domain, and that is exactly when a bound exists: `subCheck`
reads a data domain invariantly, as `constrain_go` does when it reports
`ConstrainError::DataDomainMismatch`, so two collections over different domains
have nothing below both. Their join is the Σ over both candidates, which M5 adds.
-/

mutual

def DataAgree (pol : Bool) : CTy → CTy → Bool
  | .mk _ r₁ v₁ f₁ _, .mk _ r₂ v₂ f₂ _ =>
    (match r₁, r₂ with
     | some m₁, some m₂ => DataAgreeKeys pol m₁ m₂ (m₁.map Prod.fst)
     | _, _ => true)
      && (match v₁, v₂ with
          | some m₁, some m₂ => DataAgreeKeys pol m₁ m₂ (m₁.map Prod.fst)
          | _, _ => true)
      && (match f₁, f₂ with
          | some (k₁, [d₁], cod₁), some (_, [d₂], cod₂) =>
            (if pol then true else if k₁ == KindM.data then eqv d₁ d₂ else true)
              -- Both orders, because the function case reads its hypothesis in
              -- both: a `data` slot needs the domain edge each way.
              && DataAgree (!pol) d₁ d₂ && DataAgree (!pol) d₂ d₁
              && DataAgree pol cod₁ cod₂
          | _, _ => true)
termination_by a b => (sizeOf a + sizeOf b, 0)

/-- The condition on the payloads a pair of keyed slots share (worklist form, as
`wfKeys`). A key only one side carries imposes nothing: the merge cannot move a
domain it did not combine. -/
def DataAgreeKeys (pol : Bool) (m₁ m₂ : List (FieldKey × CTy)) : List FieldKey → Bool
  | [] => true
  | k :: ks =>
    (match h₁ : m₁.lookup k, h₂ : m₂.lookup k with
     | some x, some y => DataAgree pol x y
     | _, _ => true)
      && DataAgreeKeys pol m₁ m₂ ks
termination_by ks => (sizeOf m₁ + sizeOf m₂, ks.length)
decreasing_by
  · have h1 := lookup_sizeOf h₁
    have h2 := lookup_sizeOf h₂
    apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    simp

end

/-- Pointwise reading of `DataAgreeKeys`, as `wfKeys_iff`. -/
theorem DataAgreeKeys_iff {pol : Bool} {m₁ m₂ : List (FieldKey × CTy)} {ks : List FieldKey} :
    DataAgreeKeys pol m₁ m₂ ks = true ↔
      ∀ k ∈ ks, ∀ x y, m₁.lookup k = some x → m₂.lookup k = some y →
        DataAgree pol x y = true := by
  induction ks with
  | nil => simp [DataAgreeKeys]
  | cons k ks ih =>
    rw [DataAgreeKeys, Bool.and_eq_true, ih]
    constructor
    · intro ⟨hhead, htail⟩ k' hk'
      rcases List.mem_cons.mp hk' with h | h
      · subst h
        intro x y hx hy
        rw [hx, hy] at hhead
        exact hhead
      · exact htail k' h
    · intro h
      refine ⟨?_, fun k' hk' => h k' (by simp [hk'])⟩
      rcases hx : m₁.lookup k with _ | x
      · rfl
      · rcases hy : m₂.lookup k with _ | y
        · rfl
        · exact h k (by simp) x y hx hy

/-! ## The shapes of two related positions agree

`eqv` requires the same slot *presence* on both sides, and a merge leaves a slot
absent only when both operands do, so a slot the lower operand carries and the
upper one lacks refutes `le` outright. The atom lists are the one slot that
compares by containment rather than presence. -/

theorem le_atoms_sub {pol : Bool} {as bs : List Atom} {r v f c r' v' f' c'}
    (hle : le pol (.mk as r v f c) (.mk bs r' v' f' c')) : ∀ x ∈ as, x ∈ bs := by
  rw [le, merge.eq_def, eqv.eq_def] at hle
  simp only [Bool.and_eq_true] at hle
  obtain ⟨⟨⟨⟨⟨hat, -⟩, -⟩, -⟩, -⟩, -⟩ := hle
  intro x hx
  have := (List.all_eq_true.mp hat) x (by simp [hx])
  simpa using this

theorem le_rec_absurd {pol : Bool} {as bs : List Atom} {mr : List (FieldKey × CTy)}
    {v f c v' f' c'} (hle : le pol (.mk as (some mr) v f c) (.mk bs none v' f' c')) : False := by
  rw [le, merge.eq_def, eqv.eq_def] at hle
  simp only [Bool.and_eq_true] at hle
  obtain ⟨⟨⟨⟨-, hrec⟩, -⟩, -⟩, -⟩ := hle
  simp at hrec

theorem le_var_absurd {pol : Bool} {as bs : List Atom} {mv : List (FieldKey × CTy)}
    {r f c r' f' c'} (hle : le pol (.mk as r (some mv) f c) (.mk bs r' none f' c')) : False := by
  rw [le, merge.eq_def, eqv.eq_def] at hle
  simp only [Bool.and_eq_true] at hle
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hvar⟩, -⟩, -⟩ := hle
  simp at hvar

theorem le_fun_absurd {pol : Bool} {as bs : List Atom} {g : KindM × List CTy × CTy}
    {r v c r' v' c'} (hle : le pol (.mk as r v (some g) c) (.mk bs r' v' none c')) : False := by
  rw [le, merge.eq_def, eqv.eq_def] at hle
  simp only [Bool.and_eq_true] at hle
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hfn⟩, -⟩ := hle
  simp at hfn

/-! ## Inverting `le` on a keyed slot

A slot's merge is one of two keyed operations, and which one it is depends on the
slot and the polarity together: records intersect at a positive position and unite
at a negative one, variants the other way. The two inversions below are stated on
the map operation rather than the slot, so each slot's four cases are two
applications apiece. -/

/-- A united map is `eqv` to the upper operand only if the lower operand's keys
are all the upper's, with the shared payloads related. A key held by the lower
operand alone survives the union, and the upper operand has nothing to match it. -/
theorem le_of_unionMap {pol : Bool} {m₁ m₂ : List (FieldKey × CTy)}
    (h₁ : subKeys (unionMap pol m₁ m₂) m₂ ((unionMap pol m₁ m₂).map Prod.fst) = true) :
    ∀ k v, m₁.lookup k = some v → ∃ w, m₂.lookup k = some w ∧ le pol v w := by
  intro k v hv
  rcases hw : m₂.lookup k with _ | w
  · have hM : (unionMap pol m₁ m₂).lookup k = some v := by
      rw [unionMap_lookup, hv, hw]
    obtain ⟨x, y, -, hy, -⟩ := subKeys_iff.mp h₁ k (mem_keys_of_lookup hM)
    rw [hw] at hy
    cases hy
  · have hM : (unionMap pol m₁ m₂).lookup k = some (merge pol v w) := by
      rw [unionMap_lookup, hv, hw]
    refine ⟨w, rfl, ?_⟩
    obtain ⟨x, y, hx, hy, heq⟩ := subKeys_iff.mp h₁ k (mem_keys_of_lookup hM)
    rw [hM] at hx
    rw [hw] at hy
    cases hx
    cases hy
    exact heq

/-- An intersected map is `eqv` to the upper operand only if the upper operand's
keys are all the lower's, with the payloads related. The intersection drops a key
the lower operand lacks, and then the upper operand has a key it cannot match. -/
theorem le_of_interMap {pol : Bool} {m₁ m₂ : List (FieldKey × CTy)}
    (h₁ : subKeys (interMap pol m₁ m₂) m₂ ((interMap pol m₁ m₂).map Prod.fst) = true)
    (h₂ : subKeys m₂ (interMap pol m₁ m₂) (m₂.map Prod.fst) = true) :
    ∀ k w, m₂.lookup k = some w → ∃ v, m₁.lookup k = some v ∧ le pol v w := by
  intro k w hw
  obtain ⟨x, y, -, hy, -⟩ := subKeys_iff.mp h₂ k (mem_keys_of_lookup hw)
  rcases hv : m₁.lookup k with _ | v
  · rw [interMap_lookup, hv, hw] at hy
    simp at hy
  · refine ⟨v, rfl, ?_⟩
    have hM : (interMap pol m₁ m₂).lookup k = some (merge pol v w) := by
      rw [interMap_lookup, hv, hw]
    obtain ⟨x', y', hx', hy', heq⟩ := subKeys_iff.mp h₁ k (mem_keys_of_lookup hM)
    rw [hM] at hx'
    rw [hw] at hy'
    cases hx'
    cases hy'
    exact heq

/-- The record slot's two `subKeys` facts, with the merge's shape reduced. Records
intersect at a positive position and unite at a negative one — the opposite of the
variant slot, which is what makes their variance opposite. -/
theorem eqv_record_slot {pol : Bool} {m₁ m₂ : List (FieldKey × CTy)}
    {ca cb : Option (List Pred)}
    (hle : le pol (.mk [] (some m₁) none none ca) (.mk [] (some m₂) none none cb)) :
    (if pol then
      subKeys (interMap pol m₁ m₂) m₂ ((interMap pol m₁ m₂).map Prod.fst) = true ∧
        subKeys m₂ (interMap pol m₁ m₂) (m₂.map Prod.fst) = true
    else
      subKeys (unionMap pol m₁ m₂) m₂ ((unionMap pol m₁ m₂).map Prod.fst) = true ∧
        subKeys m₂ (unionMap pol m₁ m₂) (m₂.map Prod.fst) = true) := by
  rw [le, merge.eq_def, eqv.eq_def] at hle
  simp only [Bool.and_eq_true] at hle
  obtain ⟨⟨⟨⟨⟨-, -⟩, hrec⟩, -⟩, -⟩, -⟩ := hle
  cases pol
  · simp only [Bool.false_eq_true, if_false] at hrec
    rw [← unionMap] at hrec
    simpa using hrec
  · simpa only [if_true] using hrec

/-- The variant slot's two `subKeys` facts, with the merge's shape reduced. -/
theorem eqv_variant_slot {pol : Bool} {m₁ m₂ : List (FieldKey × CTy)}
    {ca cb : Option (List Pred)}
    (hle : le pol (.mk [] none (some m₁) none ca) (.mk [] none (some m₂) none cb)) :
    (if pol then
      subKeys (unionMap pol m₁ m₂) m₂ ((unionMap pol m₁ m₂).map Prod.fst) = true ∧
        subKeys m₂ (unionMap pol m₁ m₂) (m₂.map Prod.fst) = true
    else
      subKeys (interMap pol m₁ m₂) m₂ ((interMap pol m₁ m₂).map Prod.fst) = true ∧
        subKeys m₂ (interMap pol m₁ m₂) (m₂.map Prod.fst) = true) := by
  rw [le, merge.eq_def, eqv.eq_def] at hle
  simp only [Bool.and_eq_true] at hle
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hvar⟩, -⟩, -⟩ := hle
  cases pol
  · simpa only [Bool.false_eq_true, if_false] using hvar
  · simp only [if_true] at hvar
    rw [← unionMap] at hvar
    simpa using hvar

/-- `subCheck`'s keyed lookups agree with `List.lookup`: both find the first
binding, and `BEq` on the key is lawful. -/
theorem lookupBy_eq_lookup {α} [BEq α] [LawfulBEq α] (l : List (α × Ty)) (k : α) :
    lookupBy l k = List.lookup k l := by
  induction l with
  | nil => simp [lookupBy]
  | cons hd tl ih =>
    obtain ⟨k', t⟩ := hd
    simp only [lookupBy, List.find?_cons, List.lookup_cons]
    by_cases hk : k = k'
    · subst hk
      simp
    · rw [beq_eq_false_iff_ne.mpr hk, beq_eq_false_iff_ne.mpr (Ne.symm hk)]
      simpa [lookupBy] using ih

/-- Every entry of a related pair's right side resolves on the left, given
duplicate-free keys — which `wf` supplies. -/
theorem KeyedRel.mem {α β} {R : α → β → Prop} :
    ∀ {m : List (FieldKey × α)} {kvs : List (FieldKey × β)}, KeyedRel R m kvs →
      nodupKeys (m.map Prod.fst) = true →
      ∀ e ∈ kvs, ∃ v, m.lookup e.1 = some v ∧ R v e.2
  | [], [], _, _, _, he => by simp at he
  | [], _ :: _, h, _, _, _ => by simp [KeyedRel] at h
  | _ :: _, [], h, _, _, _ => by simp [KeyedRel] at h
  | (k, v) :: m, (k', t) :: kvs, h, hnd, e, he => by
    obtain ⟨hk, hR, hrest⟩ := h
    subst hk
    simp only [List.map_cons, nodupKeys, Bool.and_eq_true] at hnd
    rcases List.mem_cons.mp he with rfl | he'
    · exact ⟨v, by simp, hR⟩
    · obtain ⟨v', hv', hR'⟩ := KeyedRel.mem hrest hnd.2 e he'
      have hne : e.1 ≠ k := by
        intro heq
        have hmem : k ∈ m.map Prod.fst := by
          rw [← heq, ← KeyedRel.keys hrest]
          exact List.mem_map_of_mem he'
        simp [hmem] at hnd
      refine ⟨v', ?_, hR'⟩
      rw [List.lookup_cons, beq_eq_false_iff_ne.mpr hne]
      exact hv'

/-- `subTags` from a per-entry statement: it walks the left type's tags in order,
so an entry-wise fact is exactly what it consumes. -/
theorem subTags_of_mem : ∀ {a b : List (FieldKey × Ty)},
    (∀ e ∈ a, ∃ u, List.lookup e.1 b = some u ∧ subCheck e.2 u = true) → subTags b a = true
  | [], b, _ => by rw [subTags]
  | (k, t) :: rest, b, h => by
    obtain ⟨u, hu, hsub⟩ := h (k, t) (by simp)
    rw [subTags, Bool.and_eq_true]
    refine ⟨?_, subTags_of_mem fun e he => h e (List.mem_cons_of_mem _ he)⟩
    split
    · rename_i t0 hlk
      rw [lookupBy_eq_lookup] at hlk
      simp only [hu, Option.some.injEq] at hlk
      subst hlk
      exact hsub
    · rename_i hlk
      rw [lookupBy_eq_lookup] at hlk
      rw [hu] at hlk
      cases hlk

/-- Looking a key up through an injective re-tagging of the key list. -/
theorem lookup_zip_map_key {α β γ} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (g : α → β) (hg : ∀ x y, g x = g y → x = y) :
    ∀ (ks : List α) (vs : List γ) (k : α),
      List.lookup (g k) ((ks.map g).zip vs) = List.lookup k (ks.zip vs)
  | [], vs, k => by simp
  | k' :: ks, [], k => by simp
  | k' :: ks, v :: vs, k => by
    simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons]
    by_cases hk : k = k'
    · subst hk
      simp
    · rw [beq_eq_false_iff_ne.mpr hk, beq_eq_false_iff_ne.mpr (fun h => hk (hg _ _ h))]
      exact lookup_zip_map_key g hg ks vs k

/-- A dense index map's tuple, read back: its payloads are the map's, by index. -/
theorem byIndex_get {n : Nat} {kvs : List (Nat × Ty)} {tup : Ty}
    (h : byIndex n kvs = some tup) :
    ∃ ts, tup = .tuple ts ∧ ts.length = n ∧
      ∀ (i : Nat) (y : Ty), i < n → ts[i]? = some y → List.lookup i kvs = some y := by
  rw [byIndex] at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨ts, hts, rfl⟩ := h
  obtain ⟨hlen, hget⟩ := mapM_some_get hts
  refine ⟨ts, rfl, by simpa using hlen, fun i y hi hy => ?_⟩
  exact hget i i y (by simp [hi]) hy

/-- `subSeq` from a positional statement: it pairs the tuples off from the front
and stops at the shorter right-hand side, which is tuple width subtyping. -/
theorem subSeq_of_get : ∀ {a b : List Ty}, b.length ≤ a.length →
    (∀ (i : Nat) (x y : Ty), a[i]? = some x → b[i]? = some y → subCheck x y = true) →
    subSeq a b = true
  | _, [], _, _ => by rw [subSeq]
  | [], _ :: _, hlen, _ => by simp at hlen
  | x :: xs, y :: ys, hlen, h => by
    rw [subSeq, Bool.and_eq_true]
    refine ⟨h 0 x y (by simp) (by simp), subSeq_of_get (by simpa using hlen) fun i u v hu hv => ?_⟩
    exact h (i + 1) u v (by simpa using hu) (by simpa using hv)

/-- `subFields` from a per-field statement: it walks the right type's fields and
demands each on the left, which is record width subtyping. -/
theorem subFields_of_mem : ∀ {a b : List (String × Ty)},
    (∀ e ∈ b, ∃ u, List.lookup e.1 a = some u ∧ subCheck u e.2 = true) → subFields a b = true
  | _, [], _ => by rw [subFields]
  | a, (n, t) :: rest, h => by
    obtain ⟨u, hu, hsub⟩ := h (n, t) (by simp)
    rw [subFields, Bool.and_eq_true]
    refine ⟨?_, subFields_of_mem fun e he => h e (List.mem_cons_of_mem _ he)⟩
    split
    · rename_i t0 hlk
      rw [lookupBy_eq_lookup] at hlk
      simp only [hu, Option.some.injEq] at hlk
      subst hlk
      exact hsub
    · rename_i hlk
      rw [lookupBy_eq_lookup] at hlk
      rw [hu] at hlk
      cases hlk

/-- A list of duplicate-free keys is no longer than one containing all of them. -/
theorem nodupKeys_length_le : ∀ {a b : List FieldKey}, nodupKeys a = true →
    (∀ x ∈ a, x ∈ b) → a.length ≤ b.length
  | [], _, _, _ => by simp
  | x :: as, b, hnd, hsub => by
    simp only [nodupKeys, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hnd
    have hxb : x ∈ b := hsub x (by simp)
    have hsub' : ∀ y ∈ as, y ∈ b.erase x := by
      intro y hy
      have hne : y ≠ x := by
        intro heq
        subst heq
        simp [hy] at hnd
      exact (List.mem_erase_of_ne hne).mpr (hsub y (by simp [hy]))
    have hle := nodupKeys_length_le hnd.2 hsub'
    rw [List.length_erase_of_mem hxb] at hle
    have hpos : 0 < b.length := List.length_pos_of_mem hxb
    simp only [List.length_cons]
    omega

/-- Re-tagging a key list distributes over the zip. -/
theorem zip_map_left {α β γ} (g : α → β) :
    ∀ (ks : List α) (vs : List γ),
      (ks.map g).zip vs = (ks.zip vs).map (fun kv => (g kv.1, kv.2))
  | [], vs => by simp
  | k :: ks, [] => by simp
  | k :: ks, v :: vs => by simpa using zip_map_left g ks vs

/-- An index key is not a name key. -/
theorem idx_ne_name {k : FieldKey} {idxs : List Nat} {names : List String}
    (hi : k ∈ idxs.map FieldKey.idx) (hn : k ∈ names.map FieldKey.name) : False := by
  obtain ⟨n, -, rfl⟩ := List.mem_map.mp hi
  obtain ⟨s, -, hs⟩ := List.mem_map.mp hn
  cases hs

/-- A non-empty contained map shares a key, so key lists that cannot share one
refute the containment. Two record slots related by `le` therefore materialize at
the same shape: a map of names shares no key with a map of indices. -/
theorem keys_disjoint_absurd {ms ss : List (FieldKey × CTy)}
    (hsub : ∀ k ∈ ss.map Prod.fst, k ∈ ms.map Prod.fst) (hne : ss ≠ [])
    (hdisj : ∀ k, k ∈ ms.map Prod.fst → k ∈ ss.map Prod.fst → False) : False := by
  rcases ss with _ | ⟨⟨k, w⟩, rest⟩
  · exact hne rfl
  · have hk : k ∈ ((k, w) :: rest).map Prod.fst := by simp
    exact hdisj k (hsub k hk) hk

/-- The record slot's comparison, stated once for both polarities: the contained
map's materialization is the right-hand side, because a record with more fields is
the subtype and a merge narrows the field set toward whichever operand `le` puts
above. `R` is materialization and `Q` is the payload relation. -/
theorem subCheck_record_shapes {R : CTy → Ty → Prop} {Q : CTy → CTy → Prop}
    {ms ss : List (FieldKey × CTy)} {tsm tss : List Ty} {tm tsub : Ty}
    (hndm : nodupKeys (ms.map Prod.fst) = true)
    (hnds : nodupKeys (ss.map Prod.fst) = true)
    (hrelm : KeyedRel R ms ((ms.map Prod.fst).zip tsm))
    (hrels : KeyedRel R ss ((ss.map Prod.fst).zip tss))
    (hnes : ss ≠ [])
    (hsub : ∀ k w, ss.lookup k = some w → ∃ v, ms.lookup k = some v ∧ Q v w)
    (hstep : ∀ k v w tv tw, ms.lookup k = some v → ss.lookup k = some w → Q v w →
      R v tv → R w tw → subCheck tv tw = true)
    (hm : (∃ idxs, indexKeys ms = some idxs ∧ byIndex ms.length (idxs.zip tsm) = some tm) ∨
          (∃ names, nameKeys ms = some names ∧ tm = .record (names.zip tsm)))
    (hs : (∃ idxs, indexKeys ss = some idxs ∧ byIndex ss.length (idxs.zip tss) = some tsub) ∨
          (∃ names, nameKeys ss = some names ∧ tsub = .record (names.zip tss))) :
    subCheck tm tsub = true ∧ tm.isRefined = false ∧ tsub.isRefined = false := by
  have hkeys : ∀ k ∈ ss.map Prod.fst, k ∈ ms.map Prod.fst := by
    intro k hk
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (lookup_of_mem_keys hk)
    obtain ⟨v, hv, -⟩ := hsub k w hw
    exact mem_keys_of_lookup hv
  rcases hm with ⟨idxs₁, hi₁, hb₁⟩ | ⟨names₁, hn₁, rfl⟩ <;>
    rcases hs with ⟨idxs₂, hi₂, hb₂⟩ | ⟨names₂, hn₂, rfl⟩
  · -- Both index-keyed: tuples, compared position by position.
    obtain ⟨u₁, rfl, hlen₁, hget₁⟩ := byIndex_get hb₁
    obtain ⟨u₂, rfl, hlen₂, hget₂⟩ := byIndex_get hb₂
    have hlen : u₂.length ≤ u₁.length := by
      have hkl := nodupKeys_length_le hnds hkeys
      simp only [List.length_map] at hkl
      omega
    refine ⟨?_, by simp [Ty.isRefined], by simp [Ty.isRefined]⟩
    rw [subCheck]
    refine subSeq_of_get hlen fun i x y hx hy => ?_
    have hinj : ∀ a b : Nat, FieldKey.idx a = FieldKey.idx b → a = b := by
      intro a b h
      cases h
      rfl
    have hix : i < u₁.length := by
      rcases Nat.lt_or_ge i u₁.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hx
        cases hx
    have hiy : i < u₂.length := by
      rcases Nat.lt_or_ge i u₂.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hy
        cases hy
    have hkss : ((ss.map Prod.fst).zip tss).lookup (FieldKey.idx i) = some y := by
      rw [indexKeys_keys hi₂, lookup_zip_map_key FieldKey.idx hinj]
      exact hget₂ i y (by omega) hy
    have hkms : ((ms.map Prod.fst).zip tsm).lookup (FieldKey.idx i) = some x := by
      rw [indexKeys_keys hi₁, lookup_zip_map_key FieldKey.idx hinj]
      exact hget₁ i x (by omega) hx
    obtain ⟨w, hw, hRw⟩ := hrels.lookup' hkss
    obtain ⟨v, hv, hQ⟩ := hsub _ w hw
    obtain ⟨u, hu, hRv⟩ := hrelm.lookup hv
    rw [hkms] at hu
    simp only [Option.some.injEq] at hu
    subst hu
    exact hstep _ v w x y hv hw hQ hRv hRw
  · exact absurd (keys_disjoint_absurd hkeys hnes fun k hk₁ hk₂ =>
      idx_ne_name (indexKeys_keys hi₁ ▸ hk₁) (nameKeys_keys hn₂ ▸ hk₂)) not_false
  · exact absurd (keys_disjoint_absurd hkeys hnes fun k hk₁ hk₂ =>
      idx_ne_name (indexKeys_keys hi₂ ▸ hk₂) (nameKeys_keys hn₁ ▸ hk₁)) not_false
  · -- Both name-keyed: records, compared field by field.
    refine ⟨?_, by simp [Ty.isRefined], by simp [Ty.isRefined]⟩
    rw [subCheck]
    refine subFields_of_mem fun e he => ?_
    have hmem : (FieldKey.name e.1, e.2) ∈ (ss.map Prod.fst).zip tss := by
      rw [nameKeys_keys hn₂, zip_map_left]
      exact List.mem_map_of_mem he
    obtain ⟨w, hw, hRw⟩ := hrels.mem hnds _ hmem
    obtain ⟨v, hv, hQ⟩ := hsub _ w hw
    obtain ⟨u, hu, hRv⟩ := hrelm.lookup hv
    refine ⟨u, ?_, hstep _ v w u e.2 hv hw hQ hRv hRw⟩
    rw [nameKeys_keys hn₁] at hu
    rw [lookup_zip_map_key FieldKey.name (fun _ _ h => by cases h; rfl)] at hu
    exact hu

/-- The record case of `MonoAt`. A record's fields are covariant and its field set
contravariant, and the merge intersects the set at a positive position and unites
it at a negative one, so in both the contained map's materialization is the
right-hand side. -/
theorem mono_record (pol : Bool) {m₁ m₂ : List (FieldKey × CTy)}
    {ca cb : Option (List Pred)} {ta tb : Ty}
    (hwa : wf (.mk [] (some m₁) none none ca) = true)
    (hwb : wf (.mk [] (some m₂) none none cb) = true)
    (ih : ∀ k v w tv tw, m₁.lookup k = some v → m₂.lookup k = some w → le pol v w →
      coalesce pol v = .ok (some tv) → coalesce pol w = .ok (some tw) →
      (if pol then subCheck tv tw else subCheck tw tv) = true)
    (hle : le pol (.mk [] (some m₁) none none ca) (.mk [] (some m₂) none none cb))
    (ha : coalesce pol (.mk [] (some m₁) none none ca) = .ok (some ta))
    (hb : coalesce pol (.mk [] (some m₂) none none cb) = .ok (some tb)) :
    (if pol then subCheck ta tb else subCheck tb ta) = true := by
  obtain ⟨hne₁, ts₁, base₁, rfl, hrel₁, hshape₁⟩ := coalesce_record_ok pol ha
  obtain ⟨hne₂, ts₂, base₂, rfl, hrel₂, hshape₂⟩ := coalesce_record_ok pol hb
  rw [wf.eq_def] at hwa hwb
  simp only [Bool.and_eq_true] at hwa hwb
  have hnd₁ : nodupKeys (m₁.map Prod.fst) = true := hwa.1.1.1.2
  have hnd₂ : nodupKeys (m₂.map Prod.fst) = true := hwb.1.1.1.2
  have hrefinements : refinementsEqv (mergeRefinements pol ca cb) cb = true := by
    rw [le, merge.eq_def, eqv.eq_def] at hle
    simp only [Bool.and_eq_true] at hle
    exact hle.2
  rcases ca with _ | p
  · exact absurd hwa.2 (by simp)
  rcases cb with _ | q
  · exact absurd hwb.2 (by simp)
  cases pol
  · simp only [mergeRefinements, refinementsEqv_iff] at hrefinements
    obtain ⟨hsc, hnr₂, hnr₁⟩ :=
      subCheck_record_shapes (R := fun v t => coalesce false v = .ok (some t))
        (Q := fun a b => le false b a) hnd₂ hnd₁ hrel₂ hrel₁ hne₁
        (fun k w hw => le_of_unionMap (eqv_record_slot hle).1 k w hw)
        (fun k v w tv tw hv hw hQ hRv hRw => by
          simpa using ih k w v tw tv hw hv hQ hRw hRv)
        hshape₂ hshape₁
    exact subCheck_attachRefinements hnr₂ hnr₁ hsc fun x hx =>
      hrefinements.1 x (List.mem_append_left _ hx)
  · simp only [mergeRefinements, refinementsEqv_iff] at hrefinements
    obtain ⟨hsc, hnr₁, hnr₂⟩ :=
      subCheck_record_shapes (R := fun v t => coalesce true v = .ok (some t))
        (Q := le true) hnd₁ hnd₂ hrel₁ hrel₂ hne₂
        (fun k w hw =>
          le_of_interMap (eqv_record_slot hle).1 (eqv_record_slot hle).2 k w hw)
        (fun k v w tv tw hv hw hQ hRv hRw => by
          simpa using ih k v w tv tw hv hw hQ hRv hRw)
        hshape₁ hshape₂
    exact subCheck_attachRefinements hnr₁ hnr₂ hsc fun x hx =>
      (List.mem_filter.mp (hrefinements.2 x hx)).1

/-- The variant case of `MonoAt`, taking the payloads' monotonicity as `ih`. The
tags of a variant are contravariant in `subCheck`, and the merge unions them at a
positive position and intersects them at a negative one, which is the same
direction read twice. -/
theorem mono_variant (pol : Bool) {m₁ m₂ : List (FieldKey × CTy)}
    {ca cb : Option (List Pred)} {ta tb : Ty}
    (hwa : wf (.mk [] none (some m₁) none ca) = true)
    (hwb : wf (.mk [] none (some m₂) none cb) = true)
    (ih : ∀ k v w tv tw, m₁.lookup k = some v → m₂.lookup k = some w → le pol v w →
      coalesce pol v = .ok (some tv) → coalesce pol w = .ok (some tw) →
      (if pol then subCheck tv tw else subCheck tw tv) = true)
    (hle : le pol (.mk [] none (some m₁) none ca) (.mk [] none (some m₂) none cb))
    (ha : coalesce pol (.mk [] none (some m₁) none ca) = .ok (some ta))
    (hb : coalesce pol (.mk [] none (some m₂) none cb) = .ok (some tb)) :
    (if pol then subCheck ta tb else subCheck tb ta) = true := by
  obtain ⟨kvs₁, rfl, hrel₁⟩ := coalesce_variant_ok pol ha
  obtain ⟨kvs₂, rfl, hrel₂⟩ := coalesce_variant_ok pol hb
  rw [wf.eq_def] at hwa hwb
  simp only [Bool.and_eq_true] at hwa hwb
  have hnd₁ : nodupKeys (m₁.map Prod.fst) = true := hwa.1.1.2.2
  have hnd₂ : nodupKeys (m₂.map Prod.fst) = true := hwb.1.1.2.2
  have hrefinements : refinementsEqv (mergeRefinements pol ca cb) cb = true := by
    rw [le, merge.eq_def, eqv.eq_def] at hle
    simp only [Bool.and_eq_true] at hle
    exact hle.2
  have hnr : ∀ kvs : List (FieldKey × Ty), (Ty.variant kvs).isRefined = false := by
    intro kvs
    simp [Ty.isRefined]
  rcases ca with _ | p
  · exact absurd hwa.2 (by simp)
  rcases cb with _ | q
  · exact absurd hwb.2 (by simp)
  cases pol
  · -- Negative: the tags intersect, so `m₂`'s entries drive the comparison.
    simp only [mergeRefinements, refinementsEqv_iff] at hrefinements
    refine subCheck_attachRefinements (hnr _) (hnr _) ?_ fun x hx =>
      hrefinements.1 x (List.mem_append_left _ hx)
    rw [subCheck]
    refine subTags_of_mem fun e he => ?_
    obtain ⟨w, hw, hcw⟩ := hrel₂.mem hnd₂ e he
    obtain ⟨v, hv, hlevw⟩ := le_of_interMap (eqv_variant_slot hle).1 (eqv_variant_slot hle).2 e.1 w hw
    obtain ⟨u, hu, hcv⟩ := hrel₁.lookup hv
    exact ⟨u, hu, ih e.1 v w u e.2 hv hw hlevw hcv hcw⟩
  · -- Positive: the tags union, so `m₁`'s entries drive it.
    simp only [mergeRefinements, refinementsEqv_iff] at hrefinements
    refine subCheck_attachRefinements (hnr _) (hnr _) ?_ fun x hx =>
      (List.mem_filter.mp (hrefinements.2 x hx)).1
    rw [subCheck]
    refine subTags_of_mem fun e he => ?_
    obtain ⟨v, hv, hcv⟩ := hrel₁.mem hnd₁ e he
    obtain ⟨w, hw, hlevw⟩ := le_of_unionMap (eqv_variant_slot hle).1 e.1 v hv
    obtain ⟨u, hu, hcw⟩ := hrel₂.lookup hw
    exact ⟨u, hu, ih e.1 v w e.2 u hv hw hlevw hcv hcw⟩

/-- An atom materializes to a leaf: never a refinement, and a subtype of itself. -/
theorem atomTy_leaf (α : Atom) :
    (atomTy α).isRefined = false ∧ subCheck (atomTy α) (atomTy α) = true := by
  cases α <;> simp [atomTy, Ty.isRefined, subCheck]

/-- The atoms case of `MonoAt`: a position whose only content is atoms and
refinements. Both operands materialize to the same atom, because the merge unions the
atom lists and `le` says the union is the upper operand's, and the refinement slots
then compare by containment in the polarity's direction. -/
theorem mono_atoms (pol : Bool) {as bs : List Atom} {ca cb : Option (List Pred)}
    {ta tb : Ty}
    (hwa : wf (.mk as none none none ca) = true)
    (hwb : wf (.mk bs none none none cb) = true)
    (hle : le pol (.mk as none none none ca) (.mk bs none none none cb))
    (ha : coalesce pol (.mk as none none none ca) = .ok (some ta))
    (hb : coalesce pol (.mk bs none none none cb) = .ok (some tb)) :
    (if pol then subCheck ta tb else subCheck tb ta) = true := by
  rw [coalesce_atoms] at ha hb
  -- Exactly one atom survives dedup on each side, or the position did not
  -- materialize.
  rcases hda : (as.map atomTy).eraseDups with _ | ⟨α, αs⟩ <;> rw [hda] at ha
  · exact absurd ha (by simp)
  rcases αs with _ | ⟨_, _⟩
  case cons.cons => exact absurd ha (by simp)
  rcases hdb : (bs.map atomTy).eraseDups with _ | ⟨β, βs⟩ <;> rw [hdb] at hb
  · exact absurd hb (by simp)
  rcases βs with _ | ⟨_, _⟩
  case cons.cons => exact absurd hb (by simp)
  simp only [Except.ok.injEq, Option.some.injEq] at ha hb
  subst ha hb
  rw [le, merge.eq_def, eqv.eq_def] at hle
  simp only [Bool.and_eq_true] at hle
  obtain ⟨⟨⟨⟨⟨hat, -⟩, -⟩, -⟩, -⟩, hcl⟩ := hle
  -- The atom lists union, so `le` forces `as ⊆ bs`, and a singleton dedup on
  -- each side then pins one atom on both.
  have hmemα : α ∈ as.map atomTy := List.mem_eraseDups.mp (by rw [hda]; simp)
  obtain ⟨a, hain, rfl⟩ := List.mem_map.mp hmemα
  have hab : a ∈ bs := by
    have := (List.all_eq_true.mp hat) a (by simp [hain])
    simpa using this
  have hαβ : atomTy a = β := by
    have := List.mem_eraseDups.mpr (List.mem_map_of_mem (f := atomTy) hab)
    rw [hdb] at this
    simpa using this
  subst hαβ
  -- A position with atoms has a refinement slot (`wf`), so both sides are `some`.
  have hasne : ¬ as.isEmpty = true := by
    intro h
    rw [List.isEmpty_iff.mp h] at hain
    simp at hain
  have hbsne : ¬ bs.isEmpty = true := by
    intro h
    rw [List.isEmpty_iff.mp h] at hab
    simp at hab
  rw [wf.eq_def] at hwa hwb
  simp only [Bool.and_eq_true] at hwa hwb
  rcases ca with _ | p
  · exact absurd hwa.2 (by simp [hasne])
  rcases cb with _ | q
  · exact absurd hwb.2 (by simp [hbsne])
  obtain ⟨hnr, hrefl⟩ := atomTy_leaf a
  -- The refinement slots then compare by containment, in the polarity's direction:
  -- a positive merge intersects and a negative one appends.
  cases pol
  · simp only [mergeRefinements, refinementsEqv_iff] at hcl
    simpa using subCheck_attachRefinements hnr hnr hrefl fun x hx =>
      hcl.1 x (List.mem_append_left _ hx)
  · simp only [mergeRefinements, refinementsEqv_iff] at hcl
    simpa using subCheck_attachRefinements hnr hnr hrefl fun x hx =>
      (List.mem_filter.mp (hcl.2 x hx)).1

/-- The atoms case, as an instance of the gate the sample measures. -/
theorem monoAt_atoms (pol : Bool) {as bs : List Atom} {ca cb : Option (List Pred)}
    (hwa : wf (.mk as none none none ca) = true)
    (hwb : wf (.mk bs none none none cb) = true) :
    MonoAt pol (.mk as none none none ca) (.mk bs none none none cb) = true := by
  rw [MonoAt]
  split
  · rename_i hle
    split
    · rename_i ta tb ha hb
      exact mono_atoms pol hwa hwb hle ha hb
    · rfl
  · rfl

/-! ## The function case

Under `wf` a function slot carries one domain, so both readings coincide: a `data`
slot's single alternative survives dedup, and a `compute` slot's meet-fold over an
empty tail is that alternative. -/

/-- `coalesce` on a position whose only content is a `data` function slot. -/
theorem coalesce_fun_data_ok (pol : Bool) {d cod : CTy} {c : Option (List Pred)}
    {ty : Ty} (h : coalesce pol (.mk [] none none (some (.data, [d], cod)) c) = .ok (some ty)) :
    ∃ dt ct, coalesce (!pol) d = .ok (some dt) ∧ coalesce pol cod = .ok (some ct) ∧
      ty = attachRefinements (.fn none .data dt ct) c := by
  rcases hf : funShapes pol (.mk [] none none (some (KindM.data, [d], cod)) c) with e | x <;>
    rw [coalesce_fun_only, hf] at h
  · cases h
  rcases x with _ | base
  · cases h
  cases h
  rw [funShapes] at hf
  simp at hf
  rcases hc : coalesce pol cod with e | oc
  · simp [hc] at hf
    cases hf
  rcases hd : coalesce (!pol) d with e | od
  · simp [hc, hd] at hf
    cases hf
  rcases od with _ | dt
  · simp [hc, hd, funTy, Functor.map, Except.map, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop] at hf
    cases hf
  rcases oc with _ | ct
  · simp [hc, hd, funTy, Functor.map, Except.map, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop] at hf
    cases hf
  refine ⟨dt, ct, rfl, rfl, ?_⟩
  rw [hc, hd] at hf
  replace hf : (Except.ok (some (Ty.fn none FunKind.data dt ct)) : Except CoErr (Option Ty))
      = .ok (some base) := hf
  cases hf
  rfl

/-- `coalesce` on a position whose only content is a `compute` function slot. -/
theorem coalesce_fun_compute_ok (pol : Bool) {d cod : CTy} {c : Option (List Pred)}
    {ty : Ty}
    (h : coalesce pol (.mk [] none none (some (.compute, [d], cod)) c) = .ok (some ty)) :
    ∃ dt ct, coalesce (!pol) d = .ok (some dt) ∧ coalesce pol cod = .ok (some ct) ∧
      ty = attachRefinements (.fn none .compute dt ct) c := by
  rcases hf : funShapes pol (.mk [] none none (some (KindM.compute, [d], cod)) c) with e | x <;>
    rw [coalesce_fun_only, hf] at h
  · cases h
  rcases x with _ | base
  · cases h
  cases h
  rw [funShapes] at hf
  simp at hf
  have hmeet : meetAll (!pol) d [] = d := rfl
  rw [hmeet] at hf
  rcases hc : coalesce pol cod with e | oc
  · simp [hc] at hf
    cases hf
  rcases hd : coalesce (!pol) d with e | od
  · simp [hc, hd] at hf
    cases hf
  rcases od with _ | dt
  · simp [hc, hd, funTy, Functor.map, Except.map] at hf
    cases hf
  rcases oc with _ | ct
  · simp [hc, hd, funTy, Functor.map, Except.map] at hf
    cases hf
  refine ⟨dt, ct, rfl, rfl, ?_⟩
  rw [hc, hd] at hf
  replace hf : (Except.ok (some (Ty.fn none FunKind.compute dt ct)) : Except CoErr (Option Ty))
      = .ok (some base) := hf
  cases hf
  rfl

/-- Equivalent positions are below each other, at either polarity. -/
theorem le_of_eqv (p : Bool) {x y : CTy} (h : eqv x y = true) (hwy : wf y = true) :
    le p x y :=
  eqv_trans _ _ _ (merge_congr_left p x y y h) (merge_idem p y hwy)

/-- `le` on a function-slot position, read off slot by slot. The kinds must agree,
because a mixed join is `conflict` and `wf` excludes that; the codomains are
related at the outer polarity; and the domains are equivalent at a positive
position, where they accumulate, and related at the flipped polarity at a negative
one, where they meet. -/
theorem eqv_fun_slot {pol : Bool} {k₁ k₂ : KindM} {d₁ d₂ cod₁ cod₂ : CTy}
    {ca cb : Option (List Pred)}
    (hk₁ : k₁ ≠ .conflict) (hk₂ : k₂ ≠ .conflict) (hu₁ : k₁ ≠ .unknown)
    (hle : le pol (.mk [] none none (some (k₁, [d₁], cod₁)) ca)
                  (.mk [] none none (some (k₂, [d₂], cod₂)) cb)) :
    k₁ = k₂ ∧ le pol cod₁ cod₂ ∧ (if pol then eqv d₁ d₂ = true else le true d₁ d₂) := by
  rw [le, merge.eq_def, eqv.eq_def] at hle
  simp only [Bool.and_eq_true] at hle
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, ⟨⟨hkind, hsd, -⟩, hcod⟩⟩, -⟩ := hle
  have hmeet : meetDoms [d₁] [d₂] = some [merge true d₁ d₂] := by simp [meetDoms, subDoms]
  have hkk : k₁ = k₂ := by
    rcases k₁ <;> rcases k₂ <;> cases pol <;>
      simp_all [joinKind, mergeFun, meetDoms, subDoms]
  subst hkk
  have hnc : (joinKind k₁ k₁ == KindM.conflict) = false := by
    rcases k₁ <;> simp_all [joinKind]
  cases pol
  · simp only [mergeFun, hnc, Bool.false_eq_true, if_false, hmeet] at hsd hcod
    refine ⟨rfl, by simpa [le] using hcod, ?_⟩
    obtain ⟨y, hy, heq⟩ := subDoms_iff.mp hsd (merge true d₁ d₂) (by simp)
    simp only [List.mem_singleton] at hy
    subst hy
    simpa [le] using heq
  · simp only [mergeFun, hnc, if_true, if_false] at hsd hcod
    refine ⟨rfl, by simpa [le] using hcod, ?_⟩
    simp only [if_true]
    obtain ⟨y, hy, heq⟩ :=
      subDoms_iff.mp hsd d₁ (by simp only [unionDoms]; exact List.mem_append_left _ (by simp))
    simp only [List.mem_singleton] at hy
    subst hy
    exact heq

/-- A function edge from its parts: the domain is contravariant, and invariant when
both sides are `data`, because a collection's domain is its data. -/
theorem subCheck_fn (kf : FunKind) {dt₁ dt₂ ct₁ ct₂ : Ty}
    (hdom : subCheck dt₂ dt₁ = true)
    (hinv : kf = .data → subCheck dt₁ dt₂ = true)
    (hcod : subCheck ct₁ ct₂ = true) :
    subCheck (.fn none kf dt₁ ct₁) (.fn none kf dt₂ ct₂) = true := by
  cases kf
  · simpa [subCheck, kindOkB] using ⟨hdom, hcod⟩
  · simpa [subCheck, kindOkB] using ⟨⟨hdom, hinv rfl⟩, hcod⟩

/-- The function case of `MonoAt`. The domains merge at the flipped polarity, so
the domain edge runs the other way — contravariance — and a `data` slot needs it in
both directions, because `subCheck` reads a data domain invariantly. A positive
merge accumulates the alternatives and `le` collapses them to one, which supplies
that agreement; a negative merge takes their meet and supplies only one direction,
so it is assumed (`hagree`), and the shape it excludes is the one `Ty` gives no
bound for. -/
theorem mono_fun (pol : Bool) {k₁ k₂ : KindM} {d₁ d₂ cod₁ cod₂ : CTy}
    {ca cb : Option (List Pred)} {ta tb : Ty}
    (hwa : wf (.mk [] none none (some (k₁, [d₁], cod₁)) ca) = true)
    (hwb : wf (.mk [] none none (some (k₂, [d₂], cod₂)) cb) = true)
    (hk₁ : k₁ = .data ∨ k₁ = .compute) (hk₂ : k₂ = .data ∨ k₂ = .compute)
    (hagree : pol = false → k₁ = .data → eqv d₁ d₂ = true)
    (ihd : ∀ (x y : CTy) (tx ty' : Ty), ((x = d₁ ∧ y = d₂) ∨ (x = d₂ ∧ y = d₁)) →
      le (!pol) x y → coalesce (!pol) x = .ok (some tx) →
      coalesce (!pol) y = .ok (some ty') →
      (if !pol then subCheck tx ty' else subCheck ty' tx) = true)
    (ihc : ∀ (tx ty' : Ty), le pol cod₁ cod₂ →
      coalesce pol cod₁ = .ok (some tx) → coalesce pol cod₂ = .ok (some ty') →
      (if pol then subCheck tx ty' else subCheck ty' tx) = true)
    (hle : le pol (.mk [] none none (some (k₁, [d₁], cod₁)) ca)
                  (.mk [] none none (some (k₂, [d₂], cod₂)) cb))
    (ha : coalesce pol (.mk [] none none (some (k₁, [d₁], cod₁)) ca) = .ok (some ta))
    (hb : coalesce pol (.mk [] none none (some (k₂, [d₂], cod₂)) cb) = .ok (some tb)) :
    (if pol then subCheck ta tb else subCheck tb ta) = true := by
  rw [wf.eq_def] at hwa hwb
  simp only [Bool.and_eq_true] at hwa hwb
  have hwd₁ : wf d₁ = true := hwa.1.2.1.2
  have hwd₂ : wf d₂ = true := hwb.1.2.1.2
  obtain ⟨rfl, hlec, hdom⟩ :=
    eqv_fun_slot (by rcases hk₁ with rfl | rfl <;> simp) (by rcases hk₂ with rfl | rfl <;> simp)
      (by rcases hk₁ with rfl | rfl <;> simp) hle
  have hrefinements : refinementsEqv (mergeRefinements pol ca cb) cb = true := by
    rw [le, merge.eq_def, eqv.eq_def] at hle
    simp only [Bool.and_eq_true] at hle
    exact hle.2
  -- The two domains agree whenever the kind demands invariance.
  have heqd : k₁ = .data → eqv d₁ d₂ = true := by
    intro hkd
    cases pol
    · exact hagree rfl hkd
    · simpa using hdom
  rcases ca with _ | p
  · exact absurd hwa.2 (by simp)
  rcases cb with _ | q
  · exact absurd hwb.2 (by simp)
  have hnr : ∀ (kf : FunKind) (x y : Ty), (Ty.fn none kf x y).isRefined = false := by
    intro kf x y
    simp [Ty.isRefined]
  rcases hk₁ with rfl | rfl
  · obtain ⟨dt₁, ct₁, hd₁, hc₁, rfl⟩ := coalesce_fun_data_ok pol ha
    obtain ⟨dt₂, ct₂, hd₂, hc₂, rfl⟩ := coalesce_fun_data_ok pol hb
    have hfwd := ihd d₁ d₂ dt₁ dt₂ (Or.inl ⟨rfl, rfl⟩)
      (le_of_eqv _ (heqd rfl) hwd₂) hd₁ hd₂
    have hbwd := ihd d₂ d₁ dt₂ dt₁ (Or.inr ⟨rfl, rfl⟩)
      (le_of_eqv _ (eqv_symm _ _ (heqd rfl)) hwd₁) hd₂ hd₁
    have hcc := ihc ct₁ ct₂ hlec hc₁ hc₂
    cases pol
    · simp only [Bool.false_eq_true, if_false, Bool.not_false, if_true] at hfwd hbwd hcc ⊢
      exact subCheck_attachRefinements (hnr _ _ _) (hnr _ _ _)
        (subCheck_fn .data hfwd (fun _ => hbwd) hcc)
        (fun x hx => by
          simp only [mergeRefinements, refinementsEqv_iff] at hrefinements
          exact hrefinements.1 x (List.mem_append_left _ hx))
    · simp only [if_true, Bool.not_true, Bool.false_eq_true, if_false] at hfwd hbwd hcc ⊢
      exact subCheck_attachRefinements (hnr _ _ _) (hnr _ _ _)
        (subCheck_fn .data hfwd (fun _ => hbwd) hcc)
        (fun x hx => by
          simp only [mergeRefinements, refinementsEqv_iff] at hrefinements
          exact (List.mem_filter.mp (hrefinements.2 x hx)).1)
  · obtain ⟨dt₁, ct₁, hd₁, hc₁, rfl⟩ := coalesce_fun_compute_ok pol ha
    obtain ⟨dt₂, ct₂, hd₂, hc₂, rfl⟩ := coalesce_fun_compute_ok pol hb
    have hcc := ihc ct₁ ct₂ hlec hc₁ hc₂
    cases pol
    · have hd := ihd d₁ d₂ dt₁ dt₂ (Or.inl ⟨rfl, rfl⟩) (by simpa using hdom) hd₁ hd₂
      simp only [Bool.false_eq_true, if_false, Bool.not_false, if_true] at hd hcc ⊢
      exact subCheck_attachRefinements (hnr _ _ _) (hnr _ _ _)
        (subCheck_fn .compute hd (fun h => absurd h (by simp)) hcc)
        (fun x hx => by
          simp only [mergeRefinements, refinementsEqv_iff] at hrefinements
          exact hrefinements.1 x (List.mem_append_left _ hx))
    · have hd := ihd d₁ d₂ dt₁ dt₂ (Or.inl ⟨rfl, rfl⟩)
        (le_of_eqv _ (by simpa using hdom) hwd₂) hd₁ hd₂
      simp only [if_true, Bool.not_true, Bool.false_eq_true, if_false] at hd hcc ⊢
      exact subCheck_attachRefinements (hnr _ _ _) (hnr _ _ _)
        (subCheck_fn .compute hd (fun h => absurd h (by simp)) hcc)
        (fun x hx => by
          simp only [mergeRefinements, refinementsEqv_iff] at hrefinements
          exact (List.mem_filter.mp (hrefinements.2 x hx)).1)

/-- `ground`, projected onto a record slot's key walk. -/
theorem ground_rec_keys {as : List Atom} {ma : List (FieldKey × CTy)} {v f c}
    (h : ground (.mk as (some ma) v f c) = true) :
    wfKeys ma (ma.map Prod.fst) = true ∧ kindResolvedKeys ma (ma.map Prod.fst) = true := by
  simp only [ground, Bool.and_eq_true] at h
  obtain ⟨hw, hk⟩ := h
  rw [wf.eq_def] at hw
  rw [kindResolved.eq_def] at hk
  simp only [Bool.and_eq_true] at hw hk
  exact ⟨hw.1.1.1.1, hk.1.1⟩

/-- `ground`, projected onto a variant slot's key walk. -/
theorem ground_var_keys {as : List Atom} {ma : List (FieldKey × CTy)} {r f c}
    (h : ground (.mk as r (some ma) f c) = true) :
    wfKeys ma (ma.map Prod.fst) = true ∧ kindResolvedKeys ma (ma.map Prod.fst) = true := by
  simp only [ground, Bool.and_eq_true] at h
  obtain ⟨hw, hk⟩ := h
  rw [wf.eq_def] at hw
  rw [kindResolved.eq_def] at hk
  simp only [Bool.and_eq_true] at hw hk
  exact ⟨hw.1.1.2.1, hk.1.2⟩

/-- `ground`, projected onto a function slot: `wf` forces one domain and a kind
that is not `conflict`, and `kindResolved` forces one that is not `unknown`. -/
theorem ground_fun {as : List Atom} {k : KindM} {ds : List CTy} {cod : CTy} {c}
    (h : ground (.mk as none none (some (k, ds, cod)) c) = true) :
    ∃ d, ds = [d] ∧ ground d = true ∧ ground cod = true ∧ (k = .data ∨ k = .compute) := by
  simp only [ground, Bool.and_eq_true] at h
  obtain ⟨hw, hk⟩ := h
  rw [wf.eq_def] at hw
  rw [kindResolved.eq_def] at hk
  simp only [Bool.and_eq_true] at hw hk
  obtain ⟨⟨-, hwf⟩, -⟩ := hw
  obtain ⟨-, hkf⟩ := hk
  rcases ds with _ | ⟨d, rest⟩
  · simp at hwf
  rcases rest with _ | ⟨_, _⟩
  · simp only [bne_iff_ne, ne_eq, Bool.and_eq_true] at hwf
    simp only [Bool.and_eq_true, kindResolvedAll, Bool.or_eq_true, beq_iff_eq] at hkf
    refine ⟨d, rfl, ?_, ?_, hkf.1.1⟩
    · simp only [ground, Bool.and_eq_true]
      exact ⟨hwf.1.2, hkf.1.2.1⟩
    · simp only [ground, Bool.and_eq_true]
      exact ⟨hwf.2, hkf.2⟩
  · simp at hwf

/-! ## The lemma, assembled

Fuel on the summed size, symmetric because the function case applies the
hypothesis to its domains in both directions. Materializing pins each position to
one of four shapes (`coalesce_shape`), and `le` refutes every pairing of different
ones, so each surviving case is the matching slot's. -/

theorem mono : ∀ (n : Nat) (pol : Bool) (a b : CTy), sizeOf a + sizeOf b < n →
    ground a = true → ground b = true → DataAgree pol a b = true → le pol a b →
    ∀ (ta tb : Ty), coalesce pol a = .ok (some ta) → coalesce pol b = .ok (some tb) →
    (if pol then subCheck ta tb else subCheck tb ta) = true := by
  intro n
  induction n with
  | zero =>
    intro _ _ _ hfuel
    exact absurd hfuel (by omega)
  | succ n ih =>
    intro pol a b hfuel hga hgb hagree hle ta tb ha hb
    obtain ⟨as, ra, va, fa, ca⟩ := a
    obtain ⟨bs, rb, vb, fb, cb⟩ := b
    -- `ground` and the pair condition, projected onto a shared keyed payload.
    have hkeyed : ∀ (ma mb : List (FieldKey × CTy)),
        wfKeys ma (ma.map Prod.fst) = true → wfKeys mb (mb.map Prod.fst) = true →
        kindResolvedKeys ma (ma.map Prod.fst) = true →
        kindResolvedKeys mb (mb.map Prod.fst) = true →
        DataAgreeKeys pol ma mb (ma.map Prod.fst) = true →
        sizeOf ma + sizeOf mb < n →
        ∀ k v w tv tw, ma.lookup k = some v → mb.lookup k = some w → le pol v w →
          coalesce pol v = .ok (some tv) → coalesce pol w = .ok (some tw) →
          (if pol then subCheck tv tw else subCheck tw tv) = true := by
      intro ma mb hwa hwb hka hkb hda hsz k v w tv tw hv hw hlevw hcv hcw
      have hsv := lookup_sizeOf hv
      have hsw := lookup_sizeOf hw
      refine ih pol v w (by omega) ?_ ?_ ?_ hlevw tv tw hcv hcw
      · simp only [ground, Bool.and_eq_true]
        exact ⟨wfKeys_iff.mp hwa k (mem_keys_of_lookup hv) v hv,
          kindResolvedKeys_iff.mp hka k (mem_keys_of_lookup hv) v hv⟩
      · simp only [ground, Bool.and_eq_true]
        exact ⟨wfKeys_iff.mp hwb k (mem_keys_of_lookup hw) w hw,
          kindResolvedKeys_iff.mp hkb k (mem_keys_of_lookup hw) w hw⟩
      · exact DataAgreeKeys_iff.mp hda k (mem_keys_of_lookup hv) v w hv hw
    rcases coalesce_shape pol ha with
        ⟨hane, rfl, rfl, rfl⟩ | ⟨rfl, ⟨ma, rfl⟩, rfl, rfl⟩ | ⟨rfl, rfl, ⟨ma, rfl⟩, rfl⟩
      | ⟨rfl, rfl, rfl, ⟨ga, rfl⟩⟩ <;>
      rcases coalesce_shape pol hb with
          ⟨hbne, rfl, rfl, rfl⟩ | ⟨rfl, ⟨mb, rfl⟩, rfl, rfl⟩ | ⟨rfl, rfl, ⟨mb, rfl⟩, rfl⟩
        | ⟨rfl, rfl, rfl, ⟨gb, rfl⟩⟩
    · simp only [ground, Bool.and_eq_true] at hga hgb
      exact mono_atoms pol hga.1 hgb.1 hle ha hb
    · exact absurd (List.eq_nil_iff_forall_not_mem.mpr
        (fun x hx => by simpa using le_atoms_sub hle x hx)) hane
    · exact absurd (List.eq_nil_iff_forall_not_mem.mpr
        (fun x hx => by simpa using le_atoms_sub hle x hx)) hane
    · exact absurd (List.eq_nil_iff_forall_not_mem.mpr
        (fun x hx => by simpa using le_atoms_sub hle x hx)) hane
    · exact absurd hle (fun h => le_rec_absurd h)
    · obtain ⟨hwka, hkka⟩ := ground_rec_keys hga
      obtain ⟨hwkb, hkkb⟩ := ground_rec_keys hgb
      have hda : DataAgreeKeys pol ma mb (ma.map Prod.fst) = true := by
        simp only [DataAgree, Bool.and_eq_true] at hagree
        exact hagree.1.1
      have hsz : sizeOf ma + sizeOf mb < n := by
        simp at hfuel
        omega
      simp only [ground, Bool.and_eq_true] at hga hgb
      exact mono_record pol hga.1 hgb.1
        (hkeyed ma mb hwka hwkb hkka hkkb hda hsz) hle ha hb
    · exact absurd hle (fun h => le_rec_absurd h)
    · exact absurd hle (fun h => le_rec_absurd h)
    · exact absurd hle (fun h => le_var_absurd h)
    · exact absurd hle (fun h => le_var_absurd h)
    · obtain ⟨hwka, hkka⟩ := ground_var_keys hga
      obtain ⟨hwkb, hkkb⟩ := ground_var_keys hgb
      have hda : DataAgreeKeys pol ma mb (ma.map Prod.fst) = true := by
        simp only [DataAgree, Bool.and_eq_true] at hagree
        exact hagree.1.2
      have hsz : sizeOf ma + sizeOf mb < n := by
        simp at hfuel
        omega
      simp only [ground, Bool.and_eq_true] at hga hgb
      exact mono_variant pol hga.1 hgb.1
        (hkeyed ma mb hwka hwkb hkka hkkb hda hsz) hle ha hb
    · exact absurd hle (fun h => le_var_absurd h)
    · exact absurd hle (fun h => le_fun_absurd h)
    · exact absurd hle (fun h => le_fun_absurd h)
    · exact absurd hle (fun h => le_fun_absurd h)
    · obtain ⟨k₁, ds₁, cod₁⟩ := ga
      obtain ⟨k₂, ds₂, cod₂⟩ := gb
      obtain ⟨d₁, rfl, hgd₁, hgc₁, hk₁⟩ := ground_fun hga
      obtain ⟨d₂, rfl, hgd₂, hgc₂, hk₂⟩ := ground_fun hgb
      simp only [DataAgree, Bool.and_eq_true] at hagree
      obtain ⟨-, ⟨⟨hkind, hdd⟩, hddrev⟩, hdc⟩ := hagree
      have ihd : ∀ (x y : CTy) (tx ty' : Ty), ((x = d₁ ∧ y = d₂) ∨ (x = d₂ ∧ y = d₁)) →
          le (!pol) x y → coalesce (!pol) x = .ok (some tx) →
          coalesce (!pol) y = .ok (some ty') →
          (if !pol then subCheck tx ty' else subCheck ty' tx) = true := by
        intro x y tx ty' hxy hlexy hcx hcy
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ih (!pol) x y (by simp at hfuel; omega) hgd₁ hgd₂ hdd hlexy tx ty' hcx hcy
        · exact ih (!pol) x y (by simp at hfuel; omega) hgd₂ hgd₁ hddrev hlexy tx ty' hcx hcy
      have ihc : ∀ (tx ty' : Ty), le pol cod₁ cod₂ →
          coalesce pol cod₁ = .ok (some tx) → coalesce pol cod₂ = .ok (some ty') →
          (if pol then subCheck tx ty' else subCheck ty' tx) = true := by
        intro tx ty' hlec hcx hcy
        exact ih pol cod₁ cod₂ (by simp at hfuel; omega) hgc₁ hgc₂ hdc hlec tx ty' hcx hcy
      have hagr : pol = false → k₁ = KindM.data → eqv d₁ d₂ = true := by
        intro hp hkd
        subst hp
        subst hkd
        simpa using hkind
      simp only [ground, Bool.and_eq_true] at hga hgb
      exact mono_fun pol hga.1 hgb.1 hk₁ hk₂ hagr ihd ihc hle ha hb

/-! ## Transport: soundness is monotonicity, twice

`le_merge_left` and `le_merge_right` put both operands below the merge in the
order the merge induces, and monotonicity carries that order to `Sub`. So the
soundness half is not a separate argument — it is two instances of `MonoAt`. -/

theorem lubSound_of_mono (pol : Bool) (a b : CTy) (hwa : wf a = true) (hwb : wf b = true)
    (hma : MonoAt pol a (merge pol a b) = true)
    (hmb : MonoAt pol b (merge pol a b) = true) :
    LubSoundAt pol a b = true := by
  rw [LubSoundAt]
  rcases ha : coalesce pol a with ea | oa
  · rfl
  rcases oa with _ | ta
  · rfl
  rcases hb : coalesce pol b with eb | ob
  · rfl
  rcases ob with _ | tb
  · rfl
  rcases hm : coalesce pol (merge pol a b) with em | om
  · rfl
  rcases om with _ | tm
  · rfl
  -- Both operands are below the merge, so both `MonoAt` guards discharge.
  have hla : eqv (merge pol a (merge pol a b)) (merge pol a b) = true :=
    le_merge_left pol a b hwa
  have hlb : eqv (merge pol b (merge pol a b)) (merge pol a b) = true :=
    le_merge_right pol a b hwb
  rw [MonoAt, if_pos hla, ha, hm] at hma
  rw [MonoAt, if_pos hlb, hb, hm] at hmb
  cases pol
  · simp only [Bool.false_eq_true, if_false] at hma hmb ⊢
    simp [hma, hmb]
  · simp only [if_true] at hma hmb ⊢
    simp [hma, hmb]

/-- `MonoAt`, discharged by `mono`. -/
theorem monoAt_of_mono (pol : Bool) (a b : CTy) (hga : ground a = true)
    (hgb : ground b = true) (hda : DataAgree pol a b = true) : MonoAt pol a b = true := by
  rw [MonoAt]
  split
  · rename_i hle
    split
    · rename_i ta tb hca hcb
      exact mono (sizeOf a + sizeOf b + 1) pol a b (by omega) hga hgb hda hle ta tb hca hcb
    · rfl
  · rfl

/-- **The bridge's soundness half.** Where all three positions materialize, a
positive merge lands above both operands under `Sub` and a negative one below
both, on ground positions whose merge did not have to move a data domain. -/
theorem lubSound (pol : Bool) (a b : CTy) (hga : ground a = true) (hgb : ground b = true)
    (hgm : ground (merge pol a b) = true)
    (hda : DataAgree pol a (merge pol a b) = true)
    (hdb : DataAgree pol b (merge pol a b) = true) :
    LubSoundAt pol a b = true := by
  have hwa : wf a = true := by
    simp only [ground, Bool.and_eq_true] at hga
    exact hga.1
  have hwb : wf b = true := by
    simp only [ground, Bool.and_eq_true] at hgb
    exact hgb.1
  exact lubSound_of_mono pol a b hwa hwb
    (monoAt_of_mono pol a (merge pol a b) hga hgm hda)
    (monoAt_of_mono pol b (merge pol a b) hgb hgm hdb)

/-- **Leastness, among positions.** A position above both operands materializes to
a type above the merge's materialization, so the merge is the least of the bounds
the representation can express.

Stated over positions rather than over all of `Ty`, which is where it stops: the
step from "above both, as a position" to "above both, as a type" needs an
embedding `Ty → CTy` and the reflection of `Sub` into `le`, the converse of
monotonicity. Neither is proved here. -/
theorem lubLeast (pol : Bool) (a b u : CTy) (hgu : ground u = true)
    (hgm : ground (merge pol a b) = true)
    (hdm : DataAgree pol (merge pol a b) u = true)
    (hau : le pol a u) (hbu : le pol b u)
    {tm tu : Ty} (hm : coalesce pol (merge pol a b) = .ok (some tm))
    (hu : coalesce pol u = .ok (some tu)) :
    (if pol then subCheck tm tu else subCheck tu tm) = true :=
  mono (sizeOf (merge pol a b) + sizeOf u + 1) pol (merge pol a b) u (by omega) hgm hgu hdm
    (merge_le pol hau hbu) tm tu hm hu

/-! ## A bounded sample

Small enough to evaluate and wide enough to reach every arm of `merge`: each slot
at its identity (`none`), at its absorbing empty shape (`some []`), and
populated; the refinement slot at both of its `none` readings; and a function slot at
each kind over domains that agree and domains that do not. -/

private def intC : CTy := .mk [.prim .int] none none none (some [])
private def boolC : CTy := .mk [.prim .bool] none none none (some [])

private def leaves : List CTy :=
  [ cempty
  , .mk [] none none none (some [])
  , intC
  , boolC
  , .mk [.uintRange 3] none none none (some [])
  , .mk [.uintRange 4] none none none (some [])
  , .mk [.source "s"] none none none (some [])
  , .mk [.txn] none none none (some [])
  , .mk [.prim .int] none none none (some [.elem])
  , .mk [] (some []) none none (some [])
  , .mk [] (some [(.name "a", intC)]) none none (some [])
  , .mk [] (some [(.name "a", intC), (.name "b", boolC)]) none none (some [])
  , .mk [] (some [(.idx 0, intC)]) none none (some [])
  , .mk [] (some [(.idx 0, intC), (.idx 1, boolC)]) none none (some [])
  , .mk [] (some [(.idx 1, boolC), (.idx 0, intC)]) none none (some [])
  , .mk [] (some [(.name "b", boolC), (.name "a", intC)]) none none (some [])
  , .mk [] none (some [(.name "t1", boolC), (.name "t0", intC)]) none (some [])
  , .mk [] none (some [(.name "t0", intC), (.name "t0", boolC)]) none (some [])
  , .mk [] (some [(.name "a", intC), (.name "a", boolC)]) none none (some [])
  , .mk [] (some [(.idx 0, intC), (.idx 0, boolC)]) none none (some [])
  , .mk [] none (some []) none (some [])
  , .mk [] none (some [(.name "t0", intC)]) none (some [])
  , .mk [] none (some [(.name "t0", intC), (.name "t1", boolC)]) none (some [])
  ]

private def funs : List CTy :=
  let kinds : List KindM := [.data, .compute, .unknown]
  let doms : List CTy :=
    [ intC
    , .mk [.prim .int] none none none (some [.elem])
    , .mk [.uintRange 3] none none none (some [])
    , .mk [.uintRange 4] none none none (some [])
    , .mk [] (some [(.name "a", intC)]) none none (some [])
    , .mk [] (some [(.name "a", intC), (.name "b", boolC)]) none none (some [])
    ]
  kinds.flatMap fun k => doms.map fun d => .mk [] none none (some (k, [d], intC)) (some [])

private def sample : List CTy := leaves ++ funs

private def cases (gate : CTy → Bool) : List (Bool × CTy × CTy) :=
  [true, false].flatMap fun pol =>
    sample.flatMap fun a =>
      sample.filterMap fun b =>
        if gate a && gate b then some (pol, a, b) else none

private def failures (gate : CTy → Bool) : List (Bool × CTy × CTy) :=
  (cases gate).filter fun (pol, a, b) => !LubSoundAt pol a b




/-! ## The pool of candidate bounds

`Ty` is a partial order, not a lattice: a negative merge of two data functions
over distinct domains has *no* lower bound, because a data function's domain is
invariant, so a type below both would need one domain equal to two. Demanding
soundness there demands the impossible, and the lossless answer is the Σ over
both domains that M5 adds. So the soundness half is guarded by the existence of a
bound, and leastness is stated against every candidate.

The pool is what the sample materializes to, which is finite and so decides the
guard only for the shapes it contains — enough to measure, not to prove. -/

private def pool : List Ty :=
  ((sample.filterMap fun t =>
      match coalesce true t with
      | .ok (some ty) => some ty
      | _ => none) ++
   (sample.filterMap fun t =>
      match coalesce false t with
      | .ok (some ty) => some ty
      | _ => none)).eraseDups

/-- Some candidate bounds both operands: above both at a positive position,
below both at a negative one. -/
private def hasBound (pol : Bool) (ta tb : Ty) : Bool :=
  pool.any fun t => if pol then subCheck ta t && subCheck tb t
                    else subCheck t ta && subCheck t tb

/-- The guarded soundness half: where a bound exists, the merge is one. -/
def LubSoundGuarded (pol : Bool) (a b : CTy) : Bool :=
  match coalesce pol a, coalesce pol b, coalesce pol (merge pol a b) with
  | .ok (some ta), .ok (some tb), .ok (some tm) =>
      !hasBound pol ta tb ||
        (if pol then subCheck ta tm && subCheck tb tm
         else subCheck tm ta && subCheck tm tb)
  | _, _, _ => true

/-- Leastness against every candidate: a bound of both operands bounds the
merge. Unconditional — no existence guard, since the quantifier is over
candidates that already bound both. -/
def LubLeastAt (pol : Bool) (a b : CTy) : Bool :=
  match coalesce pol a, coalesce pol b, coalesce pol (merge pol a b) with
  | .ok (some ta), .ok (some tb), .ok (some tm) =>
      pool.all fun t =>
        if pol then !(subCheck ta t && subCheck tb t) || subCheck tm t
        else !(subCheck t ta && subCheck t tb) || subCheck t tm
  | _, _, _ => true

private def guardedFailures : List (Bool × CTy × CTy) :=
  (cases ground).filter fun (pol, a, b) => !LubSoundGuarded pol a b

private def leastFailures : List (Bool × CTy × CTy) :=
  (cases ground).filter fun (pol, a, b) => !LubLeastAt pol a b

private def monoFailures (gate : CTy → Bool) : List (Bool × CTy × CTy) :=
  (cases gate).filter fun (pol, a, b) => !MonoAt pol a b

/-! ## What the sample measures

Three statements, each `#guard`ed over the sample, and the two hypotheses each
pinned by the counterexample that forces it. -/

-- Coverage: a change that shrinks the sample shows up here rather than as a
-- silently easier check.
private def provedCovered : List (Bool × CTy × CTy) :=
  (cases ground).filter fun (pol, a, b) =>
    ground (merge pol a b) && DataAgree pol a (merge pol a b)
      && DataAgree pol b (merge pol a b)

-- What `lubSound` proves, against what the sample checks: of the kind-resolved
-- pairs, these are the ones whose merge stays ground and whose data domains did
-- not move, so the theorem applies to them. The rest are a merge that left the
-- input shape — a `compute` slot carrying two domain alternatives, which
-- materializes by meeting them — or a data domain the merge moved.
#guard (provedCovered).length == 1814
#guard (provedCovered.filter fun (pol, a, b) => !LubSoundAt pol a b).isEmpty

#guard (cases wf).length == 2888
#guard (cases ground).length == 2048

-- In general, over kind-resolved positions: the merge is a bound wherever one
-- exists, and it is below every bound of both operands.
#guard guardedFailures.isEmpty
#guard leastFailures.isEmpty

-- Unguarded, one shape survives on every fragment, in both orders: a negative
-- merge of two `data` slots whose domains disagree. `subCheck` reads a data
-- domain invariantly, so nothing in `Ty` is below both operands and no merge
-- result could be. Restricting the domain to atoms does not exclude it — the
-- disagreement can sit in the refinement slot, and a refined collection domain is
-- what a filtered source has.
-- Unguarded, one phenomenon survives, on two surfaces and in both orders: a
-- negative merge of two `data` slots whose domains disagree. A disagreement is
-- caught loudly exactly when the domains' join is undefined — two distinct atoms
-- give a two-atom position `coalesce` rejects, so nothing materializes and the
-- statement is vacuous — and silently whenever the join exists: record keys
-- intersect, variant tags unite, refinement sets intersect. So the boundary is the
-- domains' agreement, which is what `mono_fun` assumes, and not the shape of a
-- domain.
#guard (failures ground).length == 4
#guard (monoFailures ground).length == 2
#guard !LubSoundAt false
  (.mk [] none none (some (.data, [.mk [.prim .int] none none none (some [])], intC))
    (some []))
  (.mk [] none none
    (some (.data, [.mk [.prim .int] none none none (some [.elem])], intC)) (some []))
#guard LubSoundGuarded false
  (.mk [] none none (some (.data, [.mk [.prim .int] none none none (some [])], intC))
    (some []))
  (.mk [] none none
    (some (.data, [.mk [.prim .int] none none none (some [.elem])], intC)) (some []))

-- On the fragment `compact_go` produces — kind-resolved, and every `data` slot's
-- domain atoms only — the merge is the lub with no guard at all.

-- In general, over kind-resolved positions: the merge is a bound wherever one
-- exists, and it is below every bound of both operands.

-- The route to the proof: monotonicity holds outright on the same fragment, and
-- fails on exactly the shape the existence guard covers.

-- Neither a duplicate key nor a content-bearing position without a refinement slot is
-- `wf`, and each breaks the bridge. A duplicate is invisible to `eqv`, which
-- compares by `lookup`, and visible in the type, which carries every entry.
#guard !wf (.mk [] none (some [(.name "t0", intC), (.name "t0", boolC)]) none (some []))

-- On the fragment `compact_go` produces — kind-resolved, and every `data` slot's
-- domain atoms only — the merge is the lub with no guard at all.

-- In general, over kind-resolved positions: the merge is a bound wherever one
-- exists, and it is below every bound of both operands.

-- The route to the proof: monotonicity holds outright on the same fragment, and
-- fails on exactly the shape the existence guard covers.

-- On the fragment `compact_go` produces — kind-resolved, and every `data` slot's
-- domain atoms only — the merge is the lub with no guard at all.

-- In general, over kind-resolved positions: the merge is a bound wherever one
-- exists, and it is below every bound of both operands.

-- The route to the proof: monotonicity holds outright on the same fragment, and
-- fails on exactly the shape the existence guard covers.

-- A position with content and no refinement slot is not `wf`, and this is the pair
-- that forces the invariant: at a positive position the merge keeps `__elem`,
-- because the `none` slot is the merge identity rather than a value that
-- guarantees nothing, so the join of `{Int | __elem}` and `Int` is not `Int`.
#guard !wf (.mk [.prim .int] none none none none)
#guard !LubSoundAt true (.mk [.prim .int] none none none (some [.elem]))
  (.mk [.prim .int] none none none none)

-- On the fragment `compact_go` produces — kind-resolved, and every `data` slot's
-- domain atoms only — the merge is the lub with no guard at all.

-- In general, over kind-resolved positions: the merge is a bound wherever one
-- exists, and it is below every bound of both operands.

-- `kindResolved` is what excludes the artifact: an `unknown` slot materializes by
-- the capability default, and the merge that pins it to `data` contradicts that
-- default, so the operand's own type is not what the merge combined.
#guard !LubSoundAt true
  (.mk [] none none (some (.data, [intC], intC)) (some []))
  (.mk [] none none (some (.unknown, [intC], intC)) (some []))

-- The route to the proof: monotonicity holds outright on the same fragment, and
-- fails on exactly the shape the existence guard covers.

-- The guard is what excludes the shape `Ty` gives no bound: a data function's
-- domain is invariant, so nothing is below both of these, and no merge result
-- could be. The Σ over both domains is the type that would be, which is M5.
#guard !LubSoundAt false
  (.mk [] none none (some (.data, [.mk [] (some [(.name "a", intC)]) none none (some [])], intC))
    (some []))
  (.mk [] none none
    (some (.data,
      [.mk [] (some [(.name "a", intC), (.name "b", boolC)]) none none (some [])], intC))
    (some []))
#guard LubSoundGuarded false
  (.mk [] none none (some (.data, [.mk [] (some [(.name "a", intC)]) none none (some [])], intC))
    (some []))
  (.mk [] none none
    (some (.data,
      [.mk [] (some [(.name "a", intC), (.name "b", boolC)]) none none (some [])], intC))
    (some []))

end CTy
end CclFormal
