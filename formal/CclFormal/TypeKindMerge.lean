import CclFormal.Merge

/-!
# What a Σ's witness ranges over when two contributions meet, and the lattice it merges in

`compact.rs :: CompactTypeKind::merge` — the kind order's **⊔** at a positive position and
its **⊓** at a negative one, which is the operation the polar merge performs on a binder's
range. [`TypeKind`](CclFormal/TypeKind.lean) states the *order*; this states the operation
and proves it commutative, idempotent and associative — the join by proof, the meet by an
exhaustive check over a bounded universe.

The polarity is the **enclosing function's**, not the domain's. A Σ is a property of the
function, so the range widens as the function does, and the premise is drawn unswapped where
the domain's is swapped (`TypeKind`'s `sigma_below_iff_elementwise` is why).

Everything is judged up to [`equivTypeKind`], for the same reason `Merge.lean` judges its own
laws up to `equiv`: a candidate list is a *set*, and the operation builds it by appending, so
the two orders of one union are the same kind spelled two ways. That also absorbs the one
place the Rust is finer than the model — it deduplicates candidates by structural
`CompactType` equality while this deduplicates by `equiv`, so where two candidates are
equivalent without being identical the Rust keeps both and the model keeps one. Both spell the
same set, and `equivTypeKind` says so.

## The two rows that decide a membership

The **meet** of candidates with a bound is the candidates below the parameter, and the meet of
a bound with `uintRanges` is the ranges below it. `TypeKindIsALattice` names both
(`glb_candidates_subtypesOf`, `glb_subtypesOf_uintRanges`), and each comes out a candidate
list — an intersection of a named set with a down-set is a named set again — so the merge
answers them rather than owing them to `coalesce`. Membership is decided by [`isBelow`],
absorption in the type merge's own order, which holds of an operand only what a *positive*
reading holds.

So both rows ask [`denotesAType`] first, of the parameter and of each candidate. **A
`subtypesOf` parameter must name exactly one shape**, and neither failure is a type: two or
more name none, which is what the `subtypesOf`/`subtypesOf` row leaves behind when its
parameters are incomparable, and none constrains nothing, which is the merge's identity. Both
answer the empty candidate list, since a lower bound admits only what is certain — the second
before any row dispatches ([`resolveBoundNamingNoShape`]), because the merge would otherwise
erase it. With both answered the meet is a lower bound and associative.

The join's rows ask no membership question, so none of this enters there. Candidates join a bound by folding the type join over them, because the
join dominates the candidates however they relate to the parameter
(`lub_candidates_subtypesOf`); and a bound joins `uintRanges` to the universe, because the
types below any parameter include its refinements and a refined range is not a range, so
nothing below the universe is above both (`lub_subtypesOf_uintRanges`).

-/

namespace CclFormal

/-- Mirror of `compact.rs :: CompactTypeKind`: the kind of a Σ's witness, over the compact
form rather than over `Ty`, because a candidate and a bound's parameter are ordinary
positions the solver resolves. -/
inductive CompactTypeKind where
  /-- Finitely many candidate types. At a Σ's witness one candidate is an ordinary
  collection and two or more is a conditional collection. -/
  | candidates (ds : List CompactTy)
  /-- Every `uintRange`, the kind a `List`'s domain has. Names no candidates and takes no
  parameter, so there is nothing under it to merge. -/
  | uintRanges
  /-- Every type below a given one — a `Map`'s key bound. The parameter is a position, which
  is what lets an unannotated key be determined by the types that reach it. -/
  | subtypesOf (k : CompactTy)
  /-- Every type — the top of the kind order. -/
  | everyType
deriving Repr

namespace CompactTypeKind

/-- Does this position denote a **dense prefix range** and nothing else? The property
`uintRanges` states of its members (`compact.rs :: denotes_a_uint_range`).

A refinement disqualifies it, as it does at the type level: a filtered range has holes, and
admitting it would hand a length witness to a domain that lacks one. An *empty* refinement
slot is no refinement, which is `occupied`'s reading and so is this one.

**One atom, asked as "every atom is this one, and there is one"**, because `occupied` counts
a `BTreeSet` and this counts a `List`. Reading the list's own length would make the predicate
depend on a multiplicity the Rust cannot represent, and then it would not be invariant under
[`CompactTy.equiv`] — which compares atoms by mutual containment — so a merge judged up to
`equiv` could turn a range into a non-range. Spelling the same condition as "all equal, and
non-empty" makes the invariance ([`denotesAUIntRange_congr`]) fall out of containment directly
rather than through a permutation of deduplicated lists. -/
def atomsOneRange : List Atom → Bool
  | [] => false
  | a :: rest =>
    (match a with
     | .uintRange _ => true
     | _ => false)
      && rest.all (· == a)

/-- Does the refinement slot guarantee nothing? `occupied` reads `none` and `some []` alike —
neither carries a refinement — so this does too. Named rather than matched inline because a
proof that two slots agree on it should be an equation between applications, not between two
matches. -/
def refinementSlotEmpty : Option (List Predicate) → Bool
  | none => true
  | some rs => rs.isEmpty

/-- See [`atomsOneRange`] for why the atom condition is spelled the way it is. -/
def denotesAUIntRange : CompactTy → Bool
  | .mk atoms recF varT fn refinements =>
    atomsOneRange atoms
      && recF.isNone && varT.isNone && fn.isNone
      && refinementSlotEmpty refinements

/-- Is some member of `l` equivalent to `x`? Candidate membership, judged the way
`Merge.lean` judges everything: a candidate is a position, and two spellings of one position
are one candidate. -/
def memEquiv (x : CompactTy) (l : List CompactTy) : Bool := l.any (CompactTy.equiv x ·)

/-- Two kinds naming the same set. Candidate lists compare as sets, a bound by its parameter,
and the two that name no members only by themselves. -/
def equivTypeKind : CompactTypeKind → CompactTypeKind → Bool
  | .candidates xs, .candidates ys =>
      xs.all (memEquiv · ys) && ys.all (memEquiv · xs)
  | .uintRanges, .uintRanges => true
  | .subtypesOf a, .subtypesOf b => CompactTy.equiv a b
  | .everyType, .everyType => true
  | _, _ => false

/-- The candidates of `xs` and `ys` together, each kept once. -/
def unionCandidates (xs ys : List CompactTy) : List CompactTy :=
  xs ++ ys.filter (fun y => !memEquiv y xs)

/-- The candidates in both `xs` and `ys`. -/
def interCandidates (xs ys : List CompactTy) : List CompactTy :=
  xs.filter (memEquiv · ys)

/-- The parameter a bound joins to when candidates meet it: the parameter joined with every
candidate. Named so the laws can talk about it. -/
def joinAll (k : CompactTy) (xs : List CompactTy) : CompactTy :=
  xs.foldl (CompactTy.merge true) k

/-- Do a position's atoms name at most one type? The Rust holds them in a `BTreeSet`, where a
duplicate cannot arise; the model's list can carry one, and a duplicate is the same atom rather
than a second. -/
def atomsNameAtMostOne : List Atom → Bool
  | [] => true
  | a :: rest => rest.all (· == a)

/-- How many **shapes** a position names: an atom, a record, a variant, an arrow. Capped at
two, which is all any caller asks.

`coalesce_compact_go` materializes a position from exactly one of them and reports two as
`CoalesceError::IncompatibleBounds` at either polarity, because the merge unions contributions
rather than reconciling them. Refinements are not a shape: they ride the one shape there is, so
`{Int | p}` names one. -/
def shapes : CompactTy → Nat
  | .mk atoms rec var fn _ =>
    let a := if atoms.isEmpty then 0 else if atomsNameAtMostOne atoms then 1 else 2
    min 2 (a + (if rec.isSome then 1 else 0) + (if var.isSome then 1 else 0)
             + (if fn.isSome then 1 else 0))

mutual

/-- Does this position, or any below it, name two shapes where coalesce admits one? -/
def conflicted : CompactTy → Bool
  | .mk atoms rec var fn r =>
    shapes (.mk atoms rec var fn r) > 1
      || (match rec with
          | none => false
          | some m => conflictedKeys m (m.map Prod.fst))
      || (match var with
          | none => false
          | some m => conflictedKeys m (m.map Prod.fst))
      || (match fn with
          | none => false
          | some (_, d, c) => conflicted d || conflicted c)
termination_by t => (sizeOf t, 0)

/-- [`conflicted`] of every payload a key list reaches — the recursion `Merge.lean`'s
`wellFormedKeys` uses, for the same reason: a map's payloads are reached by `lookup`, so the
measure is the map's size paired with the worklist's length. -/
def conflictedKeys (m : List (FieldKey × CompactTy)) : List FieldKey → Bool
  | [] => false
  | k :: ks =>
    (match h : m.lookup k with
     | some v => conflicted v
     | none => false)
      || conflictedKeys m ks
termination_by ks => (sizeOf m, ks.length)
decreasing_by
  · have := CompactTy.lookup_sizeOf h
    apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    simp

end

/-- Does this position name a type? Exactly one shape here, and no conflict below.

**Zero shapes is not a type either.** An unconstrained position imposes nothing, which is the
merge's identity rather than a type — `merge_cempty_left` leaves it untouched at either
polarity — and coalesce materializes it as an unresolved `Type::Infer`.

A *child* may name zero: a record field nothing has constrained materializes as that `Infer`
and the record is a type all the same. Only a conflict below disqualifies one, which is why the
recursion asks [`conflicted`] and not this. -/
def denotesAType (k : CompactTy) : Bool := shapes k == 1 && !conflicted k

/-- Is `x` **below** `k` in the order the type merge induces — `x ⊔ k ≡ k`?

This is `absorbedBy true x k` as a decision, and it holds of `k` only what a **positive**
reading of `k` holds. Absorption implies the two materialize to subtypes
(`MaterializedMergeIsABound`'s `coalesce_monotone_record` and its siblings); at the atom slot
it is set containment, which reads a union. Incomplete there — two positions can materialize
to one type and absorb neither the other — and outright wrong of a `k` whose atom set a
negative position owns, since such a `k` materializes to no type at all. -/
def isBelow (x k : CompactTy) : Bool :=
  denotesAType x && denotesAType k && CompactTy.equiv (CompactTy.merge true x k) k

/-- The kind a candidate list joins with `uintRanges` to: `uintRanges` when every candidate
is a range, and the top when not, since nothing between them holds both
(`TypeKindIsALattice`'s `lub_candidates_uintRanges_of_all` and `…_of_not_all`).

Named because it is what every grouping law meets: the merge's answer at those rows is *this*,
and reasoning about it as a named kind rather than as an `if` inside a `match` is what lets the
rows below reduce by rewriting instead of by case analysis. -/
def rangeJoin (xs : List CompactTy) : CompactTypeKind :=
  if xs.all denotesAUIntRange then .uintRanges else .everyType

/-- `compact.rs :: CompactTypeKind::merge`, arm for arm. `pol` is the enclosing function's
polarity: a join at a positive position, a meet at a negative one.

**Two rows decide a membership**, one and its mirror: the meet of candidates with a bound is
the candidates *below* the parameter, and the meet of a bound with `uintRanges` is the ranges
below it. `TypeKindIsALattice`'s `glb_candidates_subtypesOf` and `glb_subtypesOf_uintRanges`
name both, and each is a candidate list, so the merge answers within the lattice it has
rather than owing an edge. It decides membership with [`isBelow`], which is sound and
incomplete, and that is what costs the meet its associativity. -/
def mergeRows (pol : Bool) : CompactTypeKind → CompactTypeKind → CompactTypeKind
  -- The order's top: it absorbs a join and imposes nothing on a meet.
  | .everyType, other => if pol then .everyType else other
  | other, .everyType => if pol then .everyType else other
  -- Candidates are members, so the two directions are set union and set intersection. An
  -- empty intersection is two collections with no domain in common — a kind admitting
  -- nothing, which is what it is. (A *kind* is a set of types; these candidates are also
  -- domains, because the position they sit at is a Σ's witness.)
  | .candidates xs, .candidates ys =>
      .candidates (if pol then unionCandidates xs ys else interCandidates xs ys)
  -- `uintRanges` names no members, so a join rises to it only when it admits every
  -- candidate — and to the top when it does not, since nothing between them holds both
  -- (`lub_candidates_uintRanges_of_not_all`). A meet keeps the candidates it admits.
  | .candidates xs, .uintRanges =>
      if pol then rangeJoin xs else .candidates (xs.filter denotesAUIntRange)
  | .uintRanges, .candidates xs =>
      if pol then rangeJoin xs else .candidates (xs.filter denotesAUIntRange)
  | .uintRanges, .uintRanges => .uintRanges
  -- Two bounds are ordered by their parameters, so this is the parameter's own merge at this
  -- polarity — the reason the parameter is a position.
  | .subtypesOf x, .subtypesOf y => .subtypesOf (CompactTy.merge pol x y)
  -- **A join with a bound is a bound, not the top** (`lub_candidates_subtypesOf`). Needs
  -- joins only: nothing decides whether a candidate lies below the parameter, because the
  -- join dominates them however they relate to it.
  | .candidates xs, .subtypesOf k =>
      if pol then .subtypesOf (joinAll k xs)
      else .candidates (if denotesAType k then xs.filter (isBelow · k) else [])
  | .subtypesOf k, .candidates xs =>
      if pol then .subtypesOf (joinAll k xs)
      else .candidates (if denotesAType k then xs.filter (isBelow · k) else [])
  -- Nothing spells "every range below a type", so the top is their least upper bound
  -- (`lub_subtypesOf_uintRanges`); the meet is the other row that owes an edge.
  | .subtypesOf k, .uintRanges =>
      if pol then .everyType else .candidates (if denotesAUIntRange k then [k] else [])
  | .uintRanges, .subtypesOf k =>
      if pol then .everyType else .candidates (if denotesAUIntRange k then [k] else [])

/-- A bound whose parameter names **no shape**, read as the kind it is: one naming no members.

Whether a candidate lies below an unresolved parameter is unknown, and a lower bound admits
only what is certain — so the answer is the empty candidate list, the same answer the rows that
read a parameter give a conflicted one, and for the same reason. It is not the universe:
`everyType ⊓ uintRanges` is `uintRanges`, which claims every range lies below the parameter,
and a parameter resolving to `Int` has none below it.

**Not an error.** An unresolved parameter is an ordinary mid-inference state, so rejecting it
would reject programs. A parameter naming *two* shapes is an error and stays reportable: this
leaves it alone, so a lone bound carrying one still materializes as `IncompatibleBounds`, and
the rows that read a parameter answer the empty kind without re-spelling the kind that holds
it. Re-spelling it here instead costs associativity, since the `subtypesOf`/`subtypesOf` row
*produces* such a parameter and only an operand gets normalized. -/
def resolveBoundNamingNoShape : CompactTypeKind → CompactTypeKind
  | .subtypesOf k => if shapes k == 0 then .candidates [] else .subtypesOf k
  | namesAShape => namesAShape

/-- `compact.rs :: CompactTypeKind::merge`: the rows, over operands a meet has read for the
types they name.

Applied at the meet only, since no join row reads a parameter — they merge it or fold
candidates into it, and the universe would lose what those rows still carry. -/
def mergeTypeKind (pol : Bool) (a b : CompactTypeKind) : CompactTypeKind :=
  if pol then mergeRows pol a b
  else mergeRows pol (resolveBoundNamingNoShape a) (resolveBoundNamingNoShape b)

/-! ## `equivTypeKind` is an equivalence -/

/-- A member of a list is equivalent to one, itself. -/
theorem memEquiv_self {x : CompactTy} {l : List CompactTy} (h : x ∈ l) :
    memEquiv x l = true := by
  simp only [memEquiv, List.any_eq_true]
  exact ⟨x, h, CompactTy.equiv_refl x⟩

/-- Every member of a list is `memEquiv` to it — the containment a candidate list has of
itself, which the merge's rows reduce to once a bound resolves to the universe. -/
theorem forall_memEquiv_self (l : List CompactTy) : ∀ x ∈ l, memEquiv x l = true :=
  fun _ hx => memEquiv_self hx

/-- Every member of a list is equivalent to one of its own members. -/
theorem all_memEquiv_self (l : List CompactTy) : l.all (memEquiv · l) = true := by
  simp only [List.all_eq_true]
  intro x hx
  exact memEquiv_self hx

/-- Equivalence to a member of `ys` carries along a containment of `ys` in `zs`. The
candidate half of transitivity, and the one place `CompactTy.equiv_trans` is needed. -/
theorem memEquiv_trans {x : CompactTy} {ys zs : List CompactTy}
    (h1 : memEquiv x ys = true) (h2 : ys.all (memEquiv · zs) = true) :
    memEquiv x zs = true := by
  simp only [memEquiv, List.any_eq_true] at h1 ⊢
  obtain ⟨y, hy, hxy⟩ := h1
  have := (List.all_eq_true.mp h2) y hy
  simp only [memEquiv, List.any_eq_true] at this
  obtain ⟨z, hz, hyz⟩ := this
  exact ⟨z, hz, CompactTy.equiv_trans x y z hxy hyz⟩

theorem equivTypeKind_refl : (k : CompactTypeKind) → equivTypeKind k k = true
  | .candidates xs => by simp only [equivTypeKind, all_memEquiv_self, Bool.and_self]
  | .uintRanges => rfl
  | .subtypesOf a => CompactTy.equiv_refl a
  | .everyType => rfl

theorem equivTypeKind_symm : (a b : CompactTypeKind) →
    equivTypeKind a b = true → equivTypeKind b a = true := by
  intro a b h
  cases a <;> cases b <;> simp only [equivTypeKind, Bool.and_eq_true] at h ⊢ <;>
    first
      | exact h
      | exact ⟨h.2, h.1⟩
      | exact CompactTy.equiv_symm _ _ h
      | simp_all

theorem equivTypeKind_trans : (a b c : CompactTypeKind) →
    equivTypeKind a b = true → equivTypeKind b c = true → equivTypeKind a c = true := by
  intro a b c h1 h2
  cases a <;> cases b <;> cases c <;>
    simp only [equivTypeKind, Bool.and_eq_true] at h1 h2 ⊢ <;>
    first
      | exact h1
      | exact h2
      | exact CompactTy.equiv_trans _ _ _ h1 h2
      | exact ⟨List.all_eq_true.mpr fun x hx =>
            memEquiv_trans ((List.all_eq_true.mp h1.1) x hx) h2.1,
          List.all_eq_true.mpr fun x hx =>
            memEquiv_trans ((List.all_eq_true.mp h2.2) x hx) h1.2⟩
      | simp_all

/-! ## The candidate set, as a set

`unionCandidates` and `interCandidates` build lists, and these say what those lists *mean*:
membership in one is the disjunction of memberships, in the other the conjunction. Every law
below reads the candidate case through them, so no proof reasons about append or filter. -/

/-- Equivalence carries membership: two spellings of one position are one candidate. -/
theorem memEquiv_of_equiv {z x : CompactTy} {l : List CompactTy}
    (hzx : CompactTy.equiv z x = true) (h : memEquiv x l = true) : memEquiv z l = true := by
  simp only [memEquiv, List.any_eq_true] at h ⊢
  obtain ⟨y, hy, hxy⟩ := h
  exact ⟨y, hy, CompactTy.equiv_trans z x y hzx hxy⟩

theorem mem_unionCandidates {xs ys : List CompactTy} {z : CompactTy} :
    memEquiv z (unionCandidates xs ys) = true ↔
      (memEquiv z xs = true ∨ memEquiv z ys = true) := by
  simp only [unionCandidates, memEquiv, List.any_append, Bool.or_eq_true, List.any_eq_true,
    List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro (h | ⟨y, ⟨hy, _⟩, hzy⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y, hy, hzy⟩
  · rintro (h | ⟨y, hy, hzy⟩)
    · exact Or.inl h
    · by_cases hx : (xs.any (CompactTy.equiv y ·)) = true
      · refine Or.inl ?_
        have : memEquiv z xs = true :=
          memEquiv_of_equiv hzy (by simpa [memEquiv] using hx)
        simpa [memEquiv] using this
      · refine Or.inr ⟨y, ⟨hy, by simpa [memEquiv] using hx⟩, hzy⟩

theorem mem_interCandidates {xs ys : List CompactTy} {z : CompactTy} :
    memEquiv z (interCandidates xs ys) = true ↔
      (memEquiv z xs = true ∧ memEquiv z ys = true) := by
  simp only [interCandidates, memEquiv, List.any_eq_true, List.mem_filter]
  constructor
  · rintro ⟨x, ⟨hx, hxy⟩, hzx⟩
    exact ⟨⟨x, hx, hzx⟩, by
      have := memEquiv_of_equiv hzx (l := ys) (by simpa [memEquiv] using hxy)
      simpa [memEquiv] using this⟩
  · rintro ⟨⟨x, hx, hzx⟩, hzy⟩
    refine ⟨x, ⟨hx, ?_⟩, hzx⟩
    have := memEquiv_of_equiv (CompactTy.equiv_symm _ _ hzx) (l := ys)
      (by simpa [memEquiv] using hzy)
    simpa [memEquiv] using this

/-- Two candidate lists with the same members are the same kind. The bridge from the two
membership lemmas above to [`equivTypeKind`]. -/
theorem equivTypeKind_candidates {xs ys : List CompactTy}
    (h : ∀ z, memEquiv z xs = true ↔ memEquiv z ys = true) :
    equivTypeKind (.candidates xs) (.candidates ys) = true := by
  simp only [equivTypeKind, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun x hx => (h x).mp (memEquiv_self hx),
    fun y hy => (h y).mpr (memEquiv_self hy)⟩

/-- A kind is well-formed when the position it carries is. Only a bound carries one; a
candidate list's members are positions too, and asked for the same reason. -/
def wellFormedTypeKind : CompactTypeKind → Bool
  | .candidates ds => ds.all CompactTy.wellFormed
  | .uintRanges => true
  | .subtypesOf k => CompactTy.wellFormed k
  | .everyType => true

/-! ## The range predicate is invariant under `equiv`

Associativity needs this and nothing else does: a join of candidates with `uintRanges` rises
to `uintRanges` only when every candidate is a range, and the union drops candidates
equivalent to ones already present, so the two groupings of that join agree only if dropping
an equivalent candidate cannot change the verdict. -/

/-- **Mutual containment is equality of the atom *sets*.** Extracted once, because it is what
every predicate over the atom slot needs and the only thing any of them may look at.

`CompactType`'s `atoms` is a `BTreeSet`, so a predicate over it is a predicate over a set. The
model's slot is a `List` and its merge appends without deduplicating, so `equiv` compares the
slot by mutual containment — and the two go together: without the coarser reading `merge_idem`
would be false, since `a ++ a` is not `a`. The consequence is that the model admits atom
multiplicities the Rust cannot represent, and a predicate able to see one would be about the
spelling rather than about the position. This says the multiplicity is exactly what `equiv`
hides, so a predicate phrased over membership alone is invariant by construction rather than
by a proof of its own. -/
theorem mem_atoms_congr {a1 a2 : List Atom}
    {r1 r2 v1 v2 : Option (List (FieldKey × CompactTy))}
    {f1 f2 : Option (KindMerge × CompactTy × CompactTy)}
    {c1 c2 : Option (List Predicate)}
    (h : CompactTy.equiv (.mk a1 r1 v1 f1 c1) (.mk a2 r2 v2 f2 c2) = true) :
    ∀ a, a ∈ a1 ↔ a ∈ a2 := by
  rw [CompactTy.equiv.eq_def] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h12, h21⟩, _⟩, _⟩, _⟩, _⟩ := h
  intro a
  constructor
  · intro ha; simpa using (List.all_eq_true.mp h12) a ha
  · intro ha; simpa using (List.all_eq_true.mp h21) a ha

/-- Every atom of a list that names one range is that list's head. -/
theorem eq_head_of_atomsOneRange {a : Atom} {rest : List Atom} {b : Atom}
    (h : atomsOneRange (a :: rest) = true) (hb : b ∈ a :: rest) : b = a := by
  simp only [atomsOneRange, Bool.and_eq_true, List.all_eq_true] at h
  rcases List.mem_cons.mp hb with hb | hb
  · exact hb
  · simpa using h.2 b hb

/-- **Mutual containment of atoms preserves "names one range".** The list that names one
range names it with every atom it has, so a list containing exactly those atoms has them
too — and it has at least one, since the atom itself is contained. -/
theorem atomsOneRange_congr {a1 a2 : List Atom}
    (hmem : ∀ a, a ∈ a1 ↔ a ∈ a2) (h : atomsOneRange a1 = true) :
    atomsOneRange a2 = true := by
  cases a1 with
  | nil => simp [atomsOneRange] at h
  | cons a rest =>
      have ha2 : a ∈ a2 := (hmem a).mp (List.mem_cons_self ..)
      have hall : ∀ b ∈ a2, b = a := fun b hb =>
        eq_head_of_atomsOneRange h ((hmem b).mpr hb)
      cases a2 with
      | nil => simp at ha2
      | cons b rest2 =>
          have hb : b = a := hall b (List.mem_cons_self ..)
          simp only [atomsOneRange, Bool.and_eq_true, List.all_eq_true] at h ⊢
          refine ⟨by rw [hb]; exact h.1, ?_⟩
          intro x hx
          have := hall x (List.mem_cons_of_mem _ hx)
          simp [this, hb]

/-- Two refinement slots naming the same set agree on whether that set is empty. -/
theorem refinementSlotEmpty_congr : (c1 c2 : Option (List Predicate)) →
    refinementsEquiv c1 c2 = true → refinementSlotEmpty c1 = refinementSlotEmpty c2
  | none, none, _ => rfl
  | none, some _, hc => by simp [refinementsEquiv] at hc
  | some _, none, hc => by simp [refinementsEquiv] at hc
  | some p, some q, hc => by
      obtain ⟨hpq, hqp⟩ := refinementsEquiv_iff.mp hc
      cases p with
      | nil =>
          cases q with
          | nil => rfl
          | cons y _ => simpa using hqp y (List.mem_cons_self ..)
      | cons x _ =>
          cases q with
          | nil => simpa using hpq x (List.mem_cons_self ..)
          | cons _ _ => rfl

/-- The predicate is a fact about the position, so two spellings of one position agree on
it. -/
theorem denotesAUIntRange_congr : (x y : CompactTy) → CompactTy.equiv x y = true →
    denotesAUIntRange x = denotesAUIntRange y
  | .mk a1 r1 v1 f1 c1, .mk a2 r2 v2 f2 c2 => by
    intro hEq
    have h := hEq
    rw [CompactTy.equiv.eq_def] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨_h12, _h21⟩, hr⟩, hv⟩, hf⟩, hc⟩ := h
    have hmem := mem_atoms_congr hEq
    have hrange : atomsOneRange a1 = atomsOneRange a2 := by
      by_cases hx : atomsOneRange a1 = true
      · rw [hx, atomsOneRange_congr hmem hx]
      · have : atomsOneRange a2 ≠ true := fun hy =>
          hx (atomsOneRange_congr (fun a => (hmem a).symm) hy)
        simp_all
    have hrs : r1.isNone = r2.isNone := by
      cases r1 <;> cases r2 <;> simp_all
    have hvs : v1.isNone = v2.isNone := by
      cases v1 <;> cases v2 <;> simp_all
    have hfs : f1.isNone = f2.isNone := by
      cases f1 <;> cases f2 <;> simp_all
    simp only [denotesAUIntRange, hrange, hrs, hvs, hfs, refinementSlotEmpty_congr _ _ hc]

/-- Membership in the candidates a `uintRanges` meet keeps: those of `xs` that are ranges.
Reads like the other two membership lemmas, and needs [`denotesAUIntRange_congr`] to move the
predicate between equivalent spellings. -/
theorem mem_filterRange {xs : List CompactTy} {z : CompactTy} :
    memEquiv z (xs.filter denotesAUIntRange) = true ↔
      (memEquiv z xs = true ∧ denotesAUIntRange z = true) := by
  simp only [memEquiv, List.any_eq_true, List.mem_filter]
  constructor
  · rintro ⟨x, ⟨hx, hrx⟩, hzx⟩
    exact ⟨⟨x, hx, hzx⟩, by rw [denotesAUIntRange_congr _ _ hzx]; exact hrx⟩
  · rintro ⟨⟨x, hx, hzx⟩, hrz⟩
    exact ⟨x, ⟨hx, by rw [← denotesAUIntRange_congr _ _ hzx]; exact hrz⟩, hzx⟩

/-- **A union names only ranges exactly when both sides do.** The union drops candidates
equivalent to ones already present, and this is what says dropping them cannot change the
verdict — which is the whole content of associativity's `uintRanges` cases. -/
theorem all_union_range {xs ys : List CompactTy} :
    (unionCandidates xs ys).all denotesAUIntRange = true ↔
      ((xs.all denotesAUIntRange = true) ∧ (ys.all denotesAUIntRange = true)) := by
  simp only [unionCandidates, List.all_append, Bool.and_eq_true, List.all_eq_true,
    List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro ⟨hx, hf⟩
    refine ⟨hx, fun y hy => ?_⟩
    by_cases hm : memEquiv y xs = true
    · simp only [memEquiv, List.any_eq_true] at hm
      obtain ⟨x, hxm, hyx⟩ := hm
      rw [denotesAUIntRange_congr _ _ hyx]
      exact hx x hxm
    · exact hf y ⟨hy, by simpa using hm⟩
  · rintro ⟨hx, hy⟩
    exact ⟨hx, fun z hz => hy z hz.1⟩

/-- Nothing is a member of no candidates. The empty candidate list is the kind a meet with
no common member produces, so every law's `uintRanges`/bound rows reach it. -/
@[simp] theorem memEquiv_nil {z : CompactTy} : memEquiv z [] = false := rfl

/-- [`all_union_range`] with both sides in the shape `simp` normalises `List.all` to. The
join's associativity needs it where a union's range test meets a side's. -/
theorem forall_mem_union_range {xs ys : List CompactTy} :
    (∀ x ∈ unionCandidates xs ys, denotesAUIntRange x = true) ↔
      ((∀ x ∈ xs, denotesAUIntRange x = true) ∧ (∀ x ∈ ys, denotesAUIntRange x = true)) := by
  have := @all_union_range xs ys
  simp only [List.all_eq_true] at this
  exact this

/-! ## What a range test's result merges with

`rangeJoin` is the merge's answer wherever candidates meet `uintRanges`, and every remaining
row of the join's associativity is that answer meeting a third kind. Four rewrites cover them,
so those rows reduce rather than being split — the union one is where
[`all_union_range`] earns its keep. -/

/-- A range test's result joins with candidates to the test over the union. Both sides are
`uintRanges` exactly when every candidate on both sides is a range. -/
@[simp] theorem rangeJoin_join_candidates (xs ys : List CompactTy) :
    mergeRows true (rangeJoin xs) (.candidates ys) = rangeJoin (unionCandidates xs ys) := by
  by_cases hx : xs.all denotesAUIntRange = true
  · by_cases hy : ys.all denotesAUIntRange = true
    · simp [rangeJoin, mergeRows, hx, hy, all_union_range.mpr ⟨hx, hy⟩]
    · have : ¬ ((unionCandidates xs ys).all denotesAUIntRange = true) :=
        fun h => hy (all_union_range.mp h).2
      simp [rangeJoin, mergeRows, hx, hy, this]
  · have : ¬ ((unionCandidates xs ys).all denotesAUIntRange = true) :=
      fun h => hx (all_union_range.mp h).1
    simp [rangeJoin, mergeRows, hx, this]

@[simp] theorem candidates_join_rangeJoin (xs ys : List CompactTy) :
    mergeRows true (.candidates ys) (rangeJoin xs) = rangeJoin (unionCandidates xs ys) := by
  by_cases hx : xs.all denotesAUIntRange = true
  · by_cases hy : ys.all denotesAUIntRange = true
    · simp [rangeJoin, mergeRows, hx, hy, all_union_range.mpr ⟨hx, hy⟩]
    · have : ¬ ((unionCandidates xs ys).all denotesAUIntRange = true) :=
        fun h => hy (all_union_range.mp h).2
      simp [rangeJoin, mergeRows, hx, hy, this]
  · have : ¬ ((unionCandidates xs ys).all denotesAUIntRange = true) :=
      fun h => hx (all_union_range.mp h).1
    simp [rangeJoin, mergeRows, hx, this]

/-- `uintRanges` adds nothing to a test that already ran. -/
@[simp] theorem rangeJoin_join_uintRanges (xs : List CompactTy) :
    mergeRows true (rangeJoin xs) .uintRanges = rangeJoin xs := by
  by_cases hx : xs.all denotesAUIntRange = true <;> simp [rangeJoin, mergeRows, hx]

@[simp] theorem uintRanges_join_rangeJoin (xs : List CompactTy) :
    mergeRows true .uintRanges (rangeJoin xs) = rangeJoin xs := by
  by_cases hx : xs.all denotesAUIntRange = true <;> simp [rangeJoin, mergeRows, hx]

/-- A bound meeting a test's result is the top either way: nothing spells "every range below
a type", and the top absorbs. -/
@[simp] theorem rangeJoin_join_subtypesOf (xs : List CompactTy) (k : CompactTy) :
    mergeRows true (rangeJoin xs) (.subtypesOf k) = .everyType := by
  by_cases hx : xs.all denotesAUIntRange = true <;> simp [rangeJoin, mergeRows, hx]

@[simp] theorem subtypesOf_join_rangeJoin (xs : List CompactTy) (k : CompactTy) :
    mergeRows true (.subtypesOf k) (rangeJoin xs) = .everyType := by
  by_cases hx : xs.all denotesAUIntRange = true <;> simp [rangeJoin, mergeRows, hx]

@[simp] theorem rangeJoin_join_everyType (xs : List CompactTy) :
    mergeRows true (rangeJoin xs) .everyType = .everyType := by
  by_cases hx : xs.all denotesAUIntRange = true <;> simp [rangeJoin, mergeRows, hx]

@[simp] theorem everyType_join_rangeJoin (xs : List CompactTy) :
    mergeRows true .everyType (rangeJoin xs) = .everyType := by
  simp [mergeRows]

/-! ## The lattice laws

Three of the four hold. The fourth, associativity, holds at the join and fails at the meet;
The join's is proved below; the meet's is checked exhaustively, for the reason
"The meet is associative, checked rather than proved" gives.
-/

/-- **Commutative.** Which contribution reached the position first is not a fact about the
position, so the answer may not read it. -/
theorem mergeRows_comm (pol : Bool) : (a b : CompactTypeKind) →
    equivTypeKind (mergeRows pol a b) (mergeRows pol b a) = true := by
  intro a b
  cases pol <;> cases a <;> cases b <;>
    simp only [mergeRows, Bool.false_eq_true, reduceIte] <;>
    first
      | rfl
      | exact equivTypeKind_refl _
      | exact CompactTy.merge_comm _ _ _
      | exact equivTypeKind_candidates fun z => by
          rw [mem_unionCandidates, mem_unionCandidates]; exact Or.comm
      | exact equivTypeKind_candidates fun z => by
          rw [mem_interCandidates, mem_interCandidates]; exact And.comm
      | (repeat' split) <;> simp_all [equivTypeKind, memEquiv_nil]

/-- **Idempotent.** One contribution reaching a position twice says what it said once. No
diagonal row is one of the two deciding rows, so a kind merges with itself without asking
anything of the type order. -/
theorem mergeRows_idem (pol : Bool) : (a : CompactTypeKind) →
    wellFormedTypeKind a = true → equivTypeKind (mergeRows pol a a) a = true := by
  intro a hwf
  cases a <;>
    simp only [mergeRows, wellFormedTypeKind] at hwf ⊢ <;>
    first
      | rfl
      | exact equivTypeKind_refl _
      | (cases pol <;> (try simp only [Bool.false_eq_true, reduceIte]) <;>
          first
            | rfl
            | exact equivTypeKind_refl _
            | exact CompactTy.merge_idem _ _ hwf
            | exact equivTypeKind_candidates fun z => by
                rw [mem_unionCandidates]; exact or_self_iff
            | exact equivTypeKind_candidates fun z => by
                rw [mem_interCandidates]; exact and_self_iff
            | (repeat' split) <;> simp_all [equivTypeKind, memEquiv_nil])

/-! ## What the two readings answer

`TypeKindIsALattice.lean`'s `kind_glb_assoc` derives associativity from leastness alone, so the
kind order has it unconditionally and any failure is this decision procedure's. Two failed, at
the two ends of "the parameter does not name one shape", and the witnesses below are what each
one was. Both are stated as evaluations rather than theorems: `merge`, `equiv` and `wellFormed`
are well-founded recursions the kernel does not reduce, so `decide` cannot see a closed
instance that `#guard` computes outright.
-/

/-- The merge's identity: no shape, so no type and no constraint either. -/
def wEmpty : CompactTy := .mk [] none none none (some [])

/-- Three positions that name a type, no two of them comparable. -/
def wInt : CompactTy := .mk [.prim .int] none none none (some [])
def wBool : CompactTy := .mk [.prim .bool] none none none (some [])
def wR3 : CompactTy := .mk [.uintRange 3] none none none (some [])

#guard [wEmpty, wInt, wBool, wR3].all CompactTy.wellFormed

-- The two ends. A merge of incomparable parameters names two shapes, so it names no type; the
-- identity names none, so it names no type either, and `isBelow` reads it as ⊥ because the
-- order it decides in is the join's.
#guard shapes (CompactTy.merge false wInt wR3) == 2 && !denotesAType (CompactTy.merge false wInt wR3)
#guard shapes wEmpty == 0 && !denotesAType wEmpty
  && CompactTy.equiv (CompactTy.merge false wEmpty wInt) wInt

-- **A conflicted parameter names no members.** Nothing is below both `wInt` and `wR3`, and
-- both bracketings say so. Reading that parameter with `isBelow` kept `wR3`, since the merge
-- unions atoms and a position holding two contains each side's.
#guard equivTypeKind
    (mergeTypeKind false (mergeTypeKind false (.subtypesOf wInt) (.subtypesOf wR3))
      (.candidates [wR3]))
    (.candidates [])
#guard equivTypeKind
    (mergeTypeKind false (.subtypesOf wInt)
      (mergeTypeKind false (mergeTypeKind false (.subtypesOf wR3) (.candidates [wR3]))
        (.candidates [wR3])))
    (.candidates [])

-- **A shapeless parameter names no members either**, and is answered before any row
-- dispatches. Left to a row, the `subtypesOf`/`subtypesOf` row would erase it — the merge's
-- identity — and the range would survive a meet that cannot know the parameter admits it.
#guard equivTypeKind
    (mergeTypeKind false (mergeTypeKind false .uintRanges (.subtypesOf wEmpty))
      (.subtypesOf wR3))
    (mergeTypeKind false .uintRanges
      (mergeTypeKind false (.subtypesOf wEmpty) (.subtypesOf wR3)))
#guard equivTypeKind (mergeTypeKind false .uintRanges (.subtypesOf wEmpty)) (.candidates [])

-- **A shapeless candidate is dropped from a meet**, which is the reading row's own
-- incompleteness: an unresolved candidate's membership is unknown, and a lower bound admits
-- only what is certain.
#guard equivTypeKind
    (mergeTypeKind false (mergeTypeKind false (.subtypesOf wInt) (.subtypesOf wBool))
      (.candidates [wEmpty]))
    (mergeTypeKind false (.subtypesOf wInt)
      (mergeTypeKind false (.subtypesOf wBool) (.candidates [wEmpty])))

/-! ## Folding the type join over the candidates

The join of candidates with a bound folds the type join over the candidate list, so the kind
merge's associativity rests on how that fold behaves: joining in another order, and re-joining
an element already folded in. `Merge.lean` proves the type join commutative, associative,
idempotent and congruent; these lift those four to `List.foldl`.

Only absorption needs well-formedness, and it needs it of a **candidate** rather than of an
accumulator — which is what makes it available, since a merged accumulator can carry a
conflicted kind and is not well-formed in general.
-/

/-- The fold is congruent in its accumulator. -/
theorem joinAll_congr : (xs : List CompactTy) → {k k' : CompactTy} →
    CompactTy.equiv k k' = true → CompactTy.equiv (joinAll k xs) (joinAll k' xs) = true
  | [], _, _, h => h
  | x :: rest, _, _, h => by
      simpa [joinAll, List.foldl] using
        joinAll_congr rest (CompactTy.merge_congr_left true _ _ x h)

/-- Swapping the two outermost joins. -/
theorem merge_swap (k x y : CompactTy) :
    CompactTy.equiv (CompactTy.merge true (CompactTy.merge true k x) y)
      (CompactTy.merge true (CompactTy.merge true k y) x) = true := by
  refine CompactTy.equiv_trans _ _ _ (CompactTy.merge_assoc true k x y) ?_
  refine CompactTy.equiv_trans _ _ _
    (CompactTy.merge_congr_right true k _ _ (CompactTy.merge_comm true x y)) ?_
  exact CompactTy.equiv_symm _ _ (CompactTy.merge_assoc true k y x)

/-- **Joining an element first or last is the same fold.** The step every reordering is built
from. -/
theorem joinAll_merge_comm : (xs : List CompactTy) → (k x : CompactTy) →
    CompactTy.equiv (joinAll (CompactTy.merge true k x) xs)
      (CompactTy.merge true (joinAll k xs) x) = true
  | [], _, _ => CompactTy.equiv_refl _
  | y :: rest, k, x => by
      simpa [joinAll, List.foldl] using
        CompactTy.equiv_trans _ _ _ (joinAll_congr rest (merge_swap k x y))
          (joinAll_merge_comm rest (CompactTy.merge true k y) x)

/-- Two folds commute: what a list contributes does not depend on which went first. -/
theorem joinAll_comm : (ys : List CompactTy) → (k : CompactTy) → (xs : List CompactTy) →
    CompactTy.equiv (joinAll (joinAll k xs) ys) (joinAll (joinAll k ys) xs) = true
  | [], _, _ => CompactTy.equiv_refl _
  | y :: rest, k, xs => by
      have hy : CompactTy.equiv (CompactTy.merge true (joinAll k xs) y)
          (joinAll (CompactTy.merge true k y) xs) = true :=
        CompactTy.equiv_symm _ _ (joinAll_merge_comm xs k y)
      have h1 : CompactTy.equiv (joinAll (joinAll k xs) (y :: rest))
          (joinAll (joinAll (CompactTy.merge true k y) xs) rest) = true := by
        simpa [joinAll, List.foldl] using joinAll_congr rest hy
      exact CompactTy.equiv_trans _ _ _ h1 (joinAll_comm rest (CompactTy.merge true k y) xs)

/-- **A fold absorbs its own members.** Re-joining an element already folded in changes
nothing, which is what lets the union drop the candidates equivalent to ones it kept. -/
theorem joinAll_absorb : (xs : List CompactTy) → (k y : CompactTy) → y ∈ xs →
    CompactTy.wellFormed y = true →
    CompactTy.equiv (CompactTy.merge true (joinAll k xs) y) (joinAll k xs) = true
  | x :: rest, k, y, hy, hwf => by
      rcases List.mem_cons.mp hy with rfl | hy
      · have hout : CompactTy.equiv (joinAll (CompactTy.merge true k y) rest)
            (CompactTy.merge true (joinAll k rest) y) = true := joinAll_merge_comm rest k y
        have hidem : CompactTy.equiv
            (CompactTy.merge true (CompactTy.merge true (joinAll k rest) y) y)
            (CompactTy.merge true (joinAll k rest) y) = true :=
          CompactTy.equiv_trans _ _ _ (CompactTy.merge_assoc true (joinAll k rest) y y)
            (CompactTy.merge_congr_right true _ _ _ (CompactTy.merge_idem true y hwf))
        simpa [joinAll, List.foldl] using
          CompactTy.equiv_trans _ _ _ (CompactTy.merge_congr_left true _ _ y hout)
            (CompactTy.equiv_trans _ _ _ hidem (CompactTy.equiv_symm _ _ hout))
      · simpa [joinAll, List.foldl] using
          joinAll_absorb rest (CompactTy.merge true k x) y hy hwf

/-- **The union folds like the list it came from.** Each candidate the union dropped is
equivalent to one it kept, and an accumulator absorbing the kept ones absorbs the dropped one
too, so re-adding it changes nothing.

Absorption is carried as a hypothesis on the accumulator rather than recomputed: the
accumulator grows through the induction, and only its absorbing the *kept* candidates is ever
needed. -/
theorem joinAll_union (xs : List CompactTy) :
    (ys : List CompactTy) → (acc : CompactTy) →
    (∀ x ∈ xs, CompactTy.equiv (CompactTy.merge true acc x) acc = true) →
    CompactTy.equiv (joinAll acc (ys.filter (fun y => !memEquiv y xs))) (joinAll acc ys) = true
  | [], _, _ => CompactTy.equiv_refl _
  | y :: rest, acc, habs => by
      by_cases hm : memEquiv y xs = true
      · have hAbsY : CompactTy.equiv (CompactTy.merge true acc y) acc = true := by
          simp only [memEquiv, List.any_eq_true] at hm
          obtain ⟨x, hx, hyx⟩ := hm
          exact CompactTy.equiv_trans _ _ _
            (CompactTy.merge_congr_right true acc _ _ hyx) (habs x hx)
        simp only [List.filter_cons, hm, Bool.not_true, Bool.false_eq_true, if_false]
        refine CompactTy.equiv_trans _ _ _ (joinAll_union xs rest acc habs) ?_
        simpa [joinAll, List.foldl] using
          joinAll_congr rest (CompactTy.equiv_symm _ _ hAbsY)
      · have habs' : ∀ x ∈ xs, CompactTy.equiv
            (CompactTy.merge true (CompactTy.merge true acc y) x)
            (CompactTy.merge true acc y) = true := fun x hx =>
          CompactTy.equiv_trans _ _ _ (merge_swap acc y x)
            (CompactTy.merge_congr_left true _ _ y (habs x hx))
        simp only [List.filter_cons, hm, Bool.not_false, if_true]
        simpa [joinAll, List.foldl] using
          joinAll_union xs rest (CompactTy.merge true acc y) habs'

/-- The fold absorbs every member of a well-formed candidate list. -/
theorem joinAll_absorbs_all {xs : List CompactTy} (k : CompactTy)
    (hwf : ∀ x ∈ xs, CompactTy.wellFormed x = true) :
    ∀ x ∈ xs, CompactTy.equiv (CompactTy.merge true (joinAll k xs) x) (joinAll k xs) = true :=
  fun x hx => joinAll_absorb xs k x hx (hwf x hx)

/-- **What the join of candidates with a bound needs to be associative**: folding the union
is folding one list then the other, in either order. -/
theorem joinAll_unionCandidates {xs ys : List CompactTy} (k : CompactTy)
    (hwf : ∀ x ∈ xs, CompactTy.wellFormed x = true) :
    CompactTy.equiv (joinAll k (unionCandidates xs ys)) (joinAll (joinAll k ys) xs) = true := by
  have h1 : joinAll k (unionCandidates xs ys)
      = joinAll (joinAll k xs) (ys.filter (fun y => !memEquiv y xs)) := by
    simp [joinAll, unionCandidates]
  rw [h1]
  exact CompactTy.equiv_trans _ _ _
    (joinAll_union xs ys (joinAll k xs) (joinAll_absorbs_all k hwf))
    (joinAll_comm ys k xs)

/-- **The join is associative.** Three contributions meeting at one positive position give
one answer however they are grouped, which is what lets `coalesce` fold a bound list into a
binder's range in any order.

Well-formedness of the candidates is what the rows carrying a bound need: reconciling their
groupings goes through [`joinAll_unionCandidates`], and absorbing a dropped candidate rests on
the type join being idempotent on it. No row at this polarity decides a membership, which is
why this half survives and the meet's does not. -/
theorem mergeRows_join_assoc (a b c : CompactTypeKind)
    (hwa : wellFormedTypeKind a = true) (hwb : wellFormedTypeKind b = true) :
    equivTypeKind (mergeRows true (mergeRows true a b) c)
      (mergeRows true a (mergeRows true b c)) = true := by
  cases a <;> cases b <;> cases c <;>
    simp only [wellFormedTypeKind, List.all_eq_true] at hwa hwb <;>
    simp only [mergeRows, reduceIte] <;>
    (try simp only [rangeJoin_join_candidates, candidates_join_rangeJoin,
      rangeJoin_join_uintRanges, uintRanges_join_rangeJoin, rangeJoin_join_subtypesOf,
      subtypesOf_join_rangeJoin, rangeJoin_join_everyType, everyType_join_rangeJoin,
      ])
  -- The rows carrying a bound: reconciling the two groupings is a fact about the fold.
  case candidates.candidates.subtypesOf xs ys k =>
    exact joinAll_unionCandidates k hwa
  case subtypesOf.candidates.candidates k xs ys =>
    exact CompactTy.equiv_trans _ _ _ (joinAll_comm ys k xs)
      (CompactTy.equiv_symm _ _ (joinAll_unionCandidates k hwb))
  case candidates.subtypesOf.candidates xs k ys =>
    exact joinAll_comm ys k xs
  case candidates.subtypesOf.subtypesOf xs k j =>
    exact CompactTy.equiv_symm _ _ (joinAll_merge_comm xs k j)
  case subtypesOf.subtypesOf.candidates k j xs =>
    refine CompactTy.equiv_trans _ _ _ (joinAll_congr xs (CompactTy.merge_comm true k j)) ?_
    exact CompactTy.equiv_trans _ _ _ (joinAll_merge_comm xs j k)
      (CompactTy.merge_comm true (joinAll j xs) k)
  case subtypesOf.candidates.subtypesOf k xs j =>
    refine CompactTy.equiv_trans _ _ _ (CompactTy.equiv_symm _ _ (joinAll_merge_comm xs k j)) ?_
    refine CompactTy.equiv_trans _ _ _ (joinAll_congr xs (CompactTy.merge_comm true k j)) ?_
    exact CompactTy.equiv_trans _ _ _ (joinAll_merge_comm xs j k) (CompactTy.merge_comm true _ k)
  -- The one row where both groupings run a range test: over the union on one side, over each
  -- list on the other. `all_union_range` is what says they agree.
  case candidates.candidates.uintRanges xs ys =>
    -- Split on the two tests in the shape the goal states them, so the `if`s resolve by
    -- rewriting. Normalising the negations first turns them into existentials, which cannot.
    simp only [rangeJoin, List.all_eq_true]
    by_cases hy : ∀ y ∈ ys, denotesAUIntRange y = true
    · by_cases hx : ∀ x ∈ xs, denotesAUIntRange x = true
      · rw [if_pos (forall_mem_union_range.mpr ⟨hx, hy⟩), if_pos hy]
        simp only [if_pos hx]
        exact equivTypeKind_refl _
      · rw [if_neg fun h => hx (forall_mem_union_range.mp h).1, if_pos hy]
        simp only [if_neg hx]
        exact equivTypeKind_refl _
    · rw [if_neg fun h => hy (forall_mem_union_range.mp h).2, if_neg hy]
      exact equivTypeKind_refl _
  -- The row where a test runs on each side. Both groupings answer `uintRanges` exactly when
  -- both lists are all ranges, and the top otherwise.
  case candidates.uintRanges.candidates xs ys =>
    simp only [rangeJoin, List.all_eq_true]
    by_cases hx : ∀ x ∈ xs, denotesAUIntRange x = true
    · by_cases hy : ∀ y ∈ ys, denotesAUIntRange y = true
      · rw [if_pos hx, if_pos hy]
        simp only [if_pos hx, if_pos hy]
        exact equivTypeKind_refl _
      · rw [if_pos hx, if_neg hy]
        simp only [if_neg hy]
        exact equivTypeKind_refl _
    · by_cases hy : ∀ y ∈ ys, denotesAUIntRange y = true
      · rw [if_neg hx, if_pos hy]
        simp only [if_neg hx]
        exact equivTypeKind_refl _
      · rw [if_neg hx, if_neg hy]
        exact equivTypeKind_refl _
  -- The mirror of the row above, with `uintRanges` leading.
  case uintRanges.candidates.candidates xs ys =>
    simp only [rangeJoin, List.all_eq_true]
    by_cases hx : ∀ x ∈ xs, denotesAUIntRange x = true
    · by_cases hy : ∀ y ∈ ys, denotesAUIntRange y = true
      · rw [if_pos hx, if_pos (forall_mem_union_range.mpr ⟨hx, hy⟩)]
        simp only [if_pos hy]
        exact equivTypeKind_refl _
      · rw [if_pos hx, if_neg fun h => hy (forall_mem_union_range.mp h).2]
        simp only [if_neg hy]
        exact equivTypeKind_refl _
    · rw [if_neg hx, if_neg fun h => hx (forall_mem_union_range.mp h).1]
      exact equivTypeKind_refl _
  case uintRanges.candidates.uintRanges xs =>
    simp only [rangeJoin, List.all_eq_true]
    by_cases hx : ∀ x ∈ xs, denotesAUIntRange x = true
    · rw [if_pos hx]
      exact equivTypeKind_refl _
    · rw [if_neg hx]
      exact equivTypeKind_refl _
  case uintRanges.candidates.subtypesOf xs k =>
    simp only [rangeJoin, List.all_eq_true]
    by_cases hx : ∀ x ∈ xs, denotesAUIntRange x = true
    · rw [if_pos hx]
      exact equivTypeKind_refl _
    · rw [if_neg hx]
      exact equivTypeKind_refl _
  case uintRanges.candidates.everyType xs =>
    simp only [rangeJoin, List.all_eq_true]
    by_cases hx : ∀ x ∈ xs, denotesAUIntRange x = true
    · rw [if_pos hx]
      exact equivTypeKind_refl _
    · rw [if_neg hx]
      exact equivTypeKind_refl _
  case subtypesOf.candidates.uintRanges k xs =>
    simp only [rangeJoin, List.all_eq_true]
    by_cases hx : ∀ x ∈ xs, denotesAUIntRange x = true
    · rw [if_pos hx]
      exact equivTypeKind_refl _
    · rw [if_neg hx]
      exact equivTypeKind_refl _
  case uintRanges.uintRanges.candidates xs =>
    simp only [rangeJoin, List.all_eq_true]
    by_cases hx : ∀ x ∈ xs, denotesAUIntRange x = true
    · rw [if_pos hx]
      exact equivTypeKind_refl _
    · rw [if_neg hx]
      exact equivTypeKind_refl _
  case subtypesOf.uintRanges.candidates k xs =>
    simp only [rangeJoin, List.all_eq_true]
    by_cases hx : ∀ x ∈ xs, denotesAUIntRange x = true
    · rw [if_pos hx]
      exact equivTypeKind_refl _
    · rw [if_neg hx]
      exact equivTypeKind_refl _
  -- No test here: a bound meeting `uintRanges` is already the top, which absorbs.
  case uintRanges.subtypesOf.candidates k xs => exact equivTypeKind_refl _
  -- The rows where a test's result meets something that is not a candidate list: the top
  -- absorbs it, or `uintRanges` adds nothing to a test that already ran.
  case candidates.uintRanges.uintRanges xs =>
    simp only [rangeJoin, List.all_eq_true]
    by_cases hx : ∀ x ∈ xs, denotesAUIntRange x = true
    · rw [if_pos hx]
      exact equivTypeKind_refl _
    · rw [if_neg hx]
      exact equivTypeKind_refl _
  case candidates.uintRanges.subtypesOf xs k =>
    simp only [rangeJoin, List.all_eq_true]
    by_cases hx : ∀ x ∈ xs, denotesAUIntRange x = true
    · rw [if_pos hx]
      exact equivTypeKind_refl _
    · rw [if_neg hx]
      exact equivTypeKind_refl _
  case candidates.uintRanges.everyType xs =>
    simp only [rangeJoin, List.all_eq_true]
    by_cases hx : ∀ x ∈ xs, denotesAUIntRange x = true
    · rw [if_pos hx]
      exact equivTypeKind_refl _
    · rw [if_neg hx]
      exact equivTypeKind_refl _
  -- Everything else: the top absorbs, candidates union, a bound composes, or a range test
  -- splits and both branches compute.
  all_goals
    first
      | exact equivTypeKind_refl _
      | exact CompactTy.merge_assoc _ _ _ _
      | exact equivTypeKind_candidates fun z => by simp [mem_unionCandidates, or_assoc]
      | (repeat' split) <;>
          simp_all [forall_mem_union_range, equivTypeKind, memEquiv_nil]
      | simp_all [equivTypeKind, memEquiv_nil]


/-! ## The laws over the merge a caller sees

`mergeRows` carries the algebra and `mergeTypeKind` adds the reading, so each law is the row's
plus whatever the reading does to it. Commutativity and associativity are untouched, since the
reading applies to both operands alike. Idempotence is the one place the two differ: the merge
answers the kind a bound *denotes*, so a bound naming no shape comes back as the empty
candidate list rather than as itself.
-/

/-- The reading preserves well-formedness, the empty candidate list being well-formed. -/
theorem wellFormedTypeKind_resolveBoundNamingNoShape {a : CompactTypeKind}
    (h : wellFormedTypeKind a = true) :
    wellFormedTypeKind (resolveBoundNamingNoShape a) = true := by
  cases a <;> simp_all [resolveBoundNamingNoShape] <;> split <;> simp_all [wellFormedTypeKind]

/-- **Commutative.** Which contribution reached the position first is not a fact about the
position, so the answer may not read it. -/
theorem mergeTypeKind_comm (pol : Bool) (a b : CompactTypeKind) :
    equivTypeKind (mergeTypeKind pol a b) (mergeTypeKind pol b a) = true := by
  cases pol <;> simp only [mergeTypeKind, Bool.false_eq_true, reduceIte] <;>
    exact mergeRows_comm _ _ _

/-- **Idempotent**, up to the reading a meet gives a bound naming no shape. One contribution
reaching a position twice says what it said once, and what it said is the kind it denotes. -/
theorem mergeTypeKind_idem (pol : Bool) (a : CompactTypeKind)
    (hwf : wellFormedTypeKind a = true) :
    equivTypeKind (mergeTypeKind pol a a)
      (if pol then a else resolveBoundNamingNoShape a) = true := by
  cases pol <;> simp only [mergeTypeKind, Bool.false_eq_true, reduceIte]
  · exact mergeRows_idem false _ (wellFormedTypeKind_resolveBoundNamingNoShape hwf)
  · exact mergeRows_idem true _ hwf

/-- **Associative at the join**: three contributions meeting at one positive position give one
answer however they are grouped, which is what lets `var_binder_kind` fold a bound list in any
order. No join row reads a parameter, so the reading does not enter. -/
theorem mergeTypeKind_join_assoc (a b c : CompactTypeKind)
    (hwa : wellFormedTypeKind a = true) (hwb : wellFormedTypeKind b = true) :
    equivTypeKind (mergeTypeKind true (mergeTypeKind true a b) c)
      (mergeTypeKind true a (mergeTypeKind true b c)) = true := by
  simpa only [mergeTypeKind, reduceIte] using mergeRows_join_assoc a b c hwa hwb

/-! ## The meet is associative, checked rather than proved

A proof would need the two polar orders to relate: the meet's rows compose `isBelow`, which
absorbs at `pol = true`, with `CompactTy.merge` at `pol = false`, so `x ≤ k ∧ x ≤ j ↔ x ≤ k ⊓ j`
becomes a claim across both. `Merge.lean` proves the merge's laws one polarity at a time and
that biconditional is not among them.

What stands instead is an exhaustive evaluation over the kinds built from six positions — the
identity, three types naming one shape each, a second range, and a position naming two — which
is where both defects lived, since both were about a parameter that names one shape or does
not. The check is a bound on the universe, not on the depth: nothing here nests a bound inside a
record or an arrow.
-/

/-- Six positions: the two degenerate readings and four that name a type. -/
def checkTys : List CompactTy :=
  [wEmpty, wInt, wBool, wR3, .mk [.uintRange 4] none none none (some []),
    .mk [.prim .int, .uintRange 3] none none none (some [])]

/-- Every kind over [`checkTys`] that the grammar spells. -/
def checkKinds : List CompactTypeKind :=
  [.everyType, .uintRanges, .candidates []]
    ++ checkTys.map (fun t => .subtypesOf t)
    ++ checkTys.map (fun t => .candidates [t])
    ++ [.candidates [wInt, wR3], .candidates [wR3, wEmpty]]

/-- The triples the two bracketings disagree on. -/
def assocFailures (pol : Bool) : List (CompactTypeKind × CompactTypeKind × CompactTypeKind) :=
  (checkKinds.flatMap fun a => checkKinds.flatMap fun b => checkKinds.map fun c => (a, b, c)).filter
    fun (a, b, c) =>
      !equivTypeKind (mergeTypeKind pol (mergeTypeKind pol a b) c)
        (mergeTypeKind pol a (mergeTypeKind pol b c))

#guard (assocFailures false).isEmpty
#guard (assocFailures true).isEmpty

end CompactTypeKind
end CclFormal
