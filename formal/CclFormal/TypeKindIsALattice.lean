import CclFormal.TypeKind

/-!
# Type kinds are a lattice

[`ContainedIn`](CclFormal/TypeKind.lean) is the order the kind premise draws. This says it
is a **lattice**: every pair of kinds has a least upper bound and a greatest lower bound, and
names them.

Stated one row at a time rather than as a single `join`/`meet` function, because two rows need
a bound on the *types* the kinds carry — `subtypesOf a` and `subtypesOf b` are ordered by `a`
and `b`, so their least upper bound is `subtypesOf` of the least upper bound of the two types.
The model has no operation computing that (`Merge.lean` computes it in compact form and
`coalesce` materializes it or fails), so those rows take it as a hypothesis. The claim is
therefore exact: **the kind order is a lattice wherever the type order it is built on is one**,
and unconditionally everywhere else.

Both directions are proved for every row: the named kind is a bound, and it is below (above)
every other bound. Without the second half a "lattice" is a set of upper bounds with a
distinguished element, which is what an over-approximation looks like from the inside — the
`everyType` answer for `candidates ⊔ subtypesOf` is a bound, and
[`lub_candidates_subtypesOf`] is what says it is not the least one.
-/

namespace CclFormal

/-- `k` is a **least upper bound** of `a` and `b`: above both, and below anything above
both. -/
def IsKindLub (a b k : TypeKind) : Prop :=
  ContainedIn a k ∧ ContainedIn b k ∧
    ∀ K, ContainedIn a K → ContainedIn b K → ContainedIn k K

/-- `m` is a **greatest lower bound**: below both, and above anything below both. -/
def IsKindGlb (a b m : TypeKind) : Prop :=
  ContainedIn m a ∧ ContainedIn m b ∧
    ∀ M, ContainedIn M a → ContainedIn M b → ContainedIn M m

/-- What a bound on a candidate list says: every candidate is admitted. The inversion every
row below starts from, since `ContainedIn` reaches a candidate list two ways. -/
theorem admits_of_containedIn_candidates {ds : List Ty} {K : TypeKind}
    (h : ContainedIn (.candidates ds) K) : ∀ d ∈ ds, Admits K d := by
  cases h with
  | everyType => intro _ _; exact .everyType
  | candidates hall => exact hall

/-- What a bound on a `subtypesOf` says: it is the universe, or a `subtypesOf` whose
parameter is above. -/
theorem containedIn_subtypesOf_cases {k : Ty} {K : TypeKind}
    (h : ContainedIn (.subtypesOf k) K) :
    K = .everyType ∨ ∃ b, K = .subtypesOf b ∧ Subtyping k b := by
  cases h with
  | everyType => exact Or.inl rfl
  | subtypesOf hkb => exact Or.inr ⟨_, rfl, hkb⟩

/-- What a bound on `uintRanges` says: it is the universe or `uintRanges` itself — nothing
lies between them. -/
theorem containedIn_uintRanges_cases {K : TypeKind}
    (h : ContainedIn .uintRanges K) : K = .everyType ∨ K = .uintRanges := by
  cases h with
  | everyType => exact Or.inl rfl
  | uintRanges => exact Or.inr rfl

/-! ## Least upper bounds -/

/-- The universe is the top. -/
theorem lub_everyType (a : TypeKind) : IsKindLub a .everyType .everyType :=
  ⟨.everyType, .everyType, fun _ _ hb => hb⟩

theorem lub_everyType_left (b : TypeKind) : IsKindLub .everyType b .everyType :=
  ⟨.everyType, .everyType, fun _ ha _ => ha⟩

/-- Candidates join by taking both lists: the members of either. -/
theorem lub_candidates_candidates (xs ys : List Ty) :
    IsKindLub (.candidates xs) (.candidates ys) (.candidates (xs ++ ys)) := by
  refine ⟨.candidates fun d hd => .candidates (List.mem_append_left _ hd),
    .candidates fun d hd => .candidates (List.mem_append_right _ hd),
    fun K hx hy => .candidates fun d hd => ?_⟩
  rcases List.mem_append.mp hd with hd | hd
  · exact admits_of_containedIn_candidates hx d hd
  · exact admits_of_containedIn_candidates hy d hd

theorem lub_uintRanges : IsKindLub .uintRanges .uintRanges .uintRanges :=
  ⟨.uintRanges, .uintRanges, fun _ ha _ => ha⟩

/-- Candidates that are all ranges join with `uintRanges` to `uintRanges`. -/
theorem lub_candidates_uintRanges_of_all {xs : List Ty}
    (h : ∀ x ∈ xs, Admits .uintRanges x) :
    IsKindLub (.candidates xs) .uintRanges .uintRanges :=
  ⟨.candidates h, .uintRanges, fun _ _ hb => hb⟩

/-- **A candidate that is no range forces the top, and that is the least answer, not a
fudge.** Anything above `uintRanges` is `uintRanges` or the universe, and the candidate list
is not below `uintRanges`, so the universe is the only upper bound there is. -/
theorem lub_candidates_uintRanges_of_not_all {xs : List Ty} {x : Ty}
    (hx : x ∈ xs) (hnr : ¬ Admits .uintRanges x) :
    IsKindLub (.candidates xs) .uintRanges .everyType := by
  refine ⟨.everyType, .everyType, fun K hc hu => ?_⟩
  rcases containedIn_uintRanges_cases hu with rfl | rfl
  · exact .everyType
  · exact absurd (admits_of_containedIn_candidates hc x hx) hnr

/-- **A bound and `uintRanges` join to the top**, and the universe is the *only* thing above
them. Anything above `uintRanges` is `uintRanges` or the universe, and a bound is never below
`uintRanges` — for a reason that holds of every parameter: the types below it include its
refinements, and a refined range is not a range, which is the distinction `uintRanges` draws.

Not "no kind spells every range below a type": where the parameter is itself a range,
`uintRange` subtyping is equality and the ranges below it look spellable. The refinements are
what rule it out. -/
theorem lub_subtypesOf_uintRanges (k : Ty) :
    IsKindLub (.subtypesOf k) .uintRanges .everyType := by
  refine ⟨.everyType, .everyType, fun K hs hu => ?_⟩
  rcases containedIn_uintRanges_cases hu with rfl | rfl
  · exact .everyType
  · rcases containedIn_subtypesOf_cases hs with h | ⟨b, hb, _⟩ <;> simp_all

/-- Two bounds join by joining their parameters. -/
theorem lub_subtypesOf_subtypesOf {a b j : Ty}
    (haj : Subtyping a j) (hbj : Subtyping b j)
    (hleast : ∀ c, Subtyping a c → Subtyping b c → Subtyping j c) :
    IsKindLub (.subtypesOf a) (.subtypesOf b) (.subtypesOf j) := by
  refine ⟨.subtypesOf haj, .subtypesOf hbj, fun K ha hb => ?_⟩
  rcases containedIn_subtypesOf_cases ha with rfl | ⟨c, rfl, hac⟩
  · exact .everyType
  · rcases containedIn_subtypesOf_cases hb with h | ⟨c', hc', hbc⟩
    · exact absurd h (by simp)
    · cases hc'
      exact .subtypesOf (hleast c hac hbc)

/-- **Candidates and a bound join to a bound, not to the top.** Given a type above `k` and
above every candidate, and least such, `subtypesOf` of it is the least upper bound — so
answering the universe here is a strict over-approximation. What it costs is the *type*: the
least answer is a keyed collection and the universe is a plain one, and since a kind is
covariant with the function it kinds, the second is the supertype. It costs no extent — a
bound names no candidates either.

Note what the hypothesis does *not* ask: nothing decides whether a candidate is below `k`.
The join of the candidates with `k` dominates them all whatever their relation to `k` is, so
this row needs joins only, unlike its meet. -/
theorem lub_candidates_subtypesOf {xs : List Ty} {k j : Ty}
    (hkj : Subtyping k j) (hxj : ∀ x ∈ xs, Subtyping x j)
    (hleast : ∀ c, Subtyping k c → (∀ x ∈ xs, Subtyping x c) → Subtyping j c) :
    IsKindLub (.candidates xs) (.subtypesOf k) (.subtypesOf j) := by
  refine ⟨.candidates fun d hd => .subtypesOf (hxj d hd), .subtypesOf hkj, fun K hc hs => ?_⟩
  rcases containedIn_subtypesOf_cases hs with rfl | ⟨b, rfl, hkb⟩
  · exact .everyType
  · refine .subtypesOf (hleast b hkb fun x hx => ?_)
    cases admits_of_containedIn_candidates hc x hx with
    | subtypesOf hxb => exact hxb

/-! ## Greatest lower bounds

Each row's answer is given as a **set characterisation** rather than a computed list: the
greatest lower bound of a candidate list with anything is the candidates satisfying a
condition, and saying which condition is the content. Two of those conditions are subtyping
questions, which is the asymmetry against the joins — `candidates ⊓ subtypesOf` has to know
which candidates lie below the parameter, where `candidates ⊔ subtypesOf` does not.
-/

/-- What is **below** a candidate list: only another candidate list, whose members are
among its. Nothing else is ever below named candidates. -/
theorem containedIn_candidates_right {ds : List Ty} {M : TypeKind}
    (h : ContainedIn M (.candidates ds)) :
    ∃ es, M = .candidates es ∧ ∀ e ∈ es, e ∈ ds := by
  cases h with
  | candidates hall =>
      refine ⟨_, rfl, fun e he => ?_⟩
      cases hall e he with
      | candidates hm => exact hm

/-- What is **below** a bound: a candidate list all of whose members are below the parameter,
or another bound whose parameter is. -/
theorem containedIn_subtypesOf_right {k : Ty} {M : TypeKind}
    (h : ContainedIn M (.subtypesOf k)) :
    (∃ ds, M = .candidates ds ∧ ∀ d ∈ ds, Subtyping d k) ∨
      (∃ a, M = .subtypesOf a ∧ Subtyping a k) := by
  cases h with
  | candidates hall =>
      refine Or.inl ⟨_, rfl, fun d hd => ?_⟩
      cases hall d hd with
      | subtypesOf hdk => exact hdk
  | subtypesOf hak => exact Or.inr ⟨_, rfl, hak⟩

/-- What is **below** `uintRanges`: a candidate list of ranges, or `uintRanges`. -/
theorem containedIn_uintRanges_right {M : TypeKind}
    (h : ContainedIn M .uintRanges) :
    (∃ ds, M = .candidates ds ∧ ∀ d ∈ ds, Admits .uintRanges d) ∨ M = .uintRanges := by
  cases h with
  | candidates hall => exact Or.inl ⟨_, rfl, hall⟩
  | uintRanges => exact Or.inr rfl

/-- The universe is the meet identity. -/
theorem glb_everyType {a : TypeKind} (hw : a.WellFormed) : IsKindGlb a .everyType a :=
  ⟨ContainedIn.refl a hw, .everyType, fun _ hM _ => hM⟩

theorem glb_uintRanges : IsKindGlb .uintRanges .uintRanges .uintRanges :=
  ⟨.uintRanges, .uintRanges, fun _ hM _ => hM⟩

/-- Candidates meet by intersecting. -/
theorem glb_candidates_candidates {xs ys es : List Ty}
    (hes : ∀ e, e ∈ es ↔ (e ∈ xs ∧ e ∈ ys)) :
    IsKindGlb (.candidates xs) (.candidates ys) (.candidates es) := by
  refine ⟨.candidates fun e he => .candidates ((hes e).mp he).1,
    .candidates fun e he => .candidates ((hes e).mp he).2, fun M hx hy => ?_⟩
  obtain ⟨ds, rfl, hdx⟩ := containedIn_candidates_right hx
  obtain ⟨ds', hds', hdy⟩ := containedIn_candidates_right hy
  cases hds'
  exact .candidates fun d hd => .candidates ((hes d).mpr ⟨hdx d hd, hdy d hd⟩)

/-- Candidates meet `uintRanges` by keeping the ones that are ranges. -/
theorem glb_candidates_uintRanges {xs es : List Ty}
    (hes : ∀ e, e ∈ es ↔ (e ∈ xs ∧ Admits .uintRanges e)) :
    IsKindGlb (.candidates xs) .uintRanges (.candidates es) := by
  refine ⟨.candidates fun e he => .candidates ((hes e).mp he).1,
    .candidates fun e he => ((hes e).mp he).2, fun M hx hu => ?_⟩
  obtain ⟨ds, rfl, hdx⟩ := containedIn_candidates_right hx
  rcases containedIn_uintRanges_right hu with ⟨ds', hds', hdr⟩ | hu'
  · cases hds'
    exact .candidates fun d hd => .candidates ((hes d).mpr ⟨hdx d hd, hdr d hd⟩)
  · exact absurd hu' (by simp)

/-- **Candidates meet a bound by keeping the ones below its parameter**, and knowing which
those are is a subtyping question. The join's counterpart needs no such question, which is
why one row of the merge can be computed where the other must be deferred. -/
theorem glb_candidates_subtypesOf {xs es : List Ty} {k : Ty}
    (hes : ∀ e, e ∈ es ↔ (e ∈ xs ∧ Subtyping e k)) :
    IsKindGlb (.candidates xs) (.subtypesOf k) (.candidates es) := by
  refine ⟨.candidates fun e he => .candidates ((hes e).mp he).1,
    .candidates fun e he => .subtypesOf ((hes e).mp he).2, fun M hx hs => ?_⟩
  obtain ⟨ds, rfl, hdx⟩ := containedIn_candidates_right hx
  rcases containedIn_subtypesOf_right hs with ⟨ds', hds', hdk⟩ | ⟨a, ha, _⟩
  · cases hds'
    exact .candidates fun d hd => .candidates ((hes d).mpr ⟨hdx d hd, hdk d hd⟩)
  · exact absurd ha (by simp)

/-- A bound meets `uintRanges` at the ranges below its parameter — a candidate list, not
either operand, which is the meet's half of "nothing spells every range below a type". -/
theorem glb_subtypesOf_uintRanges {k : Ty} {es : List Ty}
    (hes : ∀ e, e ∈ es ↔ (Admits .uintRanges e ∧ Subtyping e k)) :
    IsKindGlb (.subtypesOf k) .uintRanges (.candidates es) := by
  refine ⟨.candidates fun e he => .subtypesOf ((hes e).mp he).2,
    .candidates fun e he => ((hes e).mp he).1, fun M hs hu => ?_⟩
  rcases containedIn_uintRanges_right hu with ⟨ds, rfl, hdr⟩ | hu'
  · rcases containedIn_subtypesOf_right hs with ⟨ds', hds', hdk⟩ | ⟨a, ha, _⟩
    · cases hds'
      exact .candidates fun d hd => .candidates ((hes d).mpr ⟨hdr d hd, hdk d hd⟩)
    · exact absurd ha (by simp)
  · cases hu'
    rcases containedIn_subtypesOf_right hs with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> exact absurd h (by simp)

/-- Two bounds meet by meeting their parameters. -/
theorem glb_subtypesOf_subtypesOf {a b m : Ty}
    (hma : Subtyping m a) (hmb : Subtyping m b)
    (hgreatest : ∀ c, Subtyping c a → Subtyping c b → Subtyping c m) :
    IsKindGlb (.subtypesOf a) (.subtypesOf b) (.subtypesOf m) := by
  refine ⟨.subtypesOf hma, .subtypesOf hmb, fun M ha hb => ?_⟩
  rcases containedIn_subtypesOf_right ha with ⟨ds, rfl, hda⟩ | ⟨c, rfl, hca⟩
  · rcases containedIn_subtypesOf_right hb with ⟨ds', hds', hdb⟩ | ⟨_, h, _⟩
    · cases hds'
      exact .candidates fun d hd => .subtypesOf (hgreatest d (hda d hd) (hdb d hd))
    · exact absurd h (by simp)
  · rcases containedIn_subtypesOf_right hb with ⟨_, h, _⟩ | ⟨c', hc', hcb⟩
    · exact absurd h (by simp)
    · cases hc'
      exact .subtypesOf (hgreatest c hca hcb)

/-! ## Associativity is free, and that is where the compact merge parts company

Neither bound needs a row for this: two groupings of one triple are each a bound of all
three, so each is below the other by the other's leastness. Every lattice gets associativity
this way, which makes it the wrong thing to measure a merge implementation by — an
implementation can satisfy it and still answer a non-least bound, and it can answer every row
least and still lose it.

`TypeKindMerge.lean` loses it, at the meet, and the two facts together locate the gap: the
kind order is associative, and the compact merge's two membership-deciding rows are not,
because `isBelow` is incomplete where this order's membership is subtyping.
-/

/-- **The greatest lower bound is associative**, from leastness alone. -/
theorem kind_glb_assoc {a b c m₁ m₂ l r : TypeKind}
    (hwa : a.WellFormed) (hwb : b.WellFormed) (hwc : c.WellFormed)
    (hw1 : m₁.WellFormed) (hw2 : m₂.WellFormed) (hwl : l.WellFormed) (hwr : r.WellFormed)
    (h1 : IsKindGlb a b m₁) (hl : IsKindGlb m₁ c l)
    (h2 : IsKindGlb b c m₂) (hr : IsKindGlb a m₂ r) :
    ContainedIn l r ∧ ContainedIn r l :=
  ⟨hr.2.2 l (ContainedIn.trans hwl hw1 hwa hl.1 h1.1)
      (h2.2.2 l (ContainedIn.trans hwl hw1 hwb hl.1 h1.2.1) hl.2.1),
   hl.2.2 r (h1.2.2 r hr.1 (ContainedIn.trans hwr hw2 hwb hr.2.1 h2.1))
      (ContainedIn.trans hwr hw2 hwc hr.2.1 h2.2.1)⟩

/-- **The least upper bound is associative**, by the same argument upward. -/
theorem kind_lub_assoc {a b c j₁ j₂ l r : TypeKind}
    (hwa : a.WellFormed) (hwb : b.WellFormed) (hwc : c.WellFormed)
    (hw1 : j₁.WellFormed) (hw2 : j₂.WellFormed) (hwl : l.WellFormed) (hwr : r.WellFormed)
    (h1 : IsKindLub a b j₁) (hl : IsKindLub j₁ c l)
    (h2 : IsKindLub b c j₂) (hr : IsKindLub a j₂ r) :
    ContainedIn l r ∧ ContainedIn r l :=
  ⟨hl.2.2 r (h1.2.2 r hr.1 (ContainedIn.trans hwb hw2 hwr h2.1 hr.2.1))
      (ContainedIn.trans hwc hw2 hwr h2.2.1 hr.2.1),
   hr.2.2 l (ContainedIn.trans hwa hw1 hwl h1.1 hl.1)
      (h2.2.2 l (ContainedIn.trans hwb hw1 hwl h1.2.1 hl.1) hl.2.1)⟩

end CclFormal
