import CclFormal.Subtyping
import CclFormal.SubtypingIsReflexive
import CclFormal.SubtypingIsTransitive

/-!
# What a Σ binder ranges over, and the order on it

`ccl::ty::TypeKind` is a **type of types**: it classifies them, and says nothing about what
they are used for. Four constructors, differing only in **how each states which types it
classifies** — candidates name their members one by one, `uintRanges` and `everyType` state a
property of theirs and name none, and `subtypesOf` names them by a type.

A Σ's witness is the one kind-carrying position in the grammar, and a Σ's witness is a data
function's domain, so every type a kind classifies *here* happens to be a domain. That is a
fact about the position, not part of the notion, and reading it into the kind inverts the
Σ rule: the Σ is a property of the function rather than of its domain, which is precisely why
the kind premise is drawn unswapped where the domain's is swapped.

The order is containment (`constrain.rs :: constrain_type_kinds`), and it is the premise of
the Σ rule. Two facts about it are proved here: containment transports membership
([`Admits.mono`]) — the sense in which it really orders the classifiers rather than merely
being reflexive and transitive — and it is transitive ([`ContainedIn.trans`]), which is what
lets a chain of Σ edges compose.

Membership itself is a relation, not a decision. What a caller with no graph to draw into
decides instead is [`refuses`] — certain non-membership — and the one fact relating the two is
that a refusal never lands on a member ([`not_admits_of_refuses`]). That direction is the whole
of what makes a rejection legitimate, and it is what the bound arm's equality test broke.

A kind is **not** a `Ty`, and the direction matters: a kind admits many types and a type is
admitted by many kinds, so there is no "kind of a type" to read off. What a type determines
is the least kind containing it, the singleton candidate list.
-/

namespace CclFormal

/-- Mirror of `ccl::ty::TypeKind`.

`candidates` is `Enumerated` under the name the Rust docs use for its contents, since
"enumerated" says how the set is written and the proofs are about its members. -/
inductive TypeKind where
  /-- Finitely many types, named one by one. -/
  | candidates (ds : List Ty)
  /-- Every `uintRange` — a dense prefix, which is the kind a `List`'s domain has. Not a
  candidate list (there is one range per length) and not the down-set of a large range
  (that would admit sparse subsets). -/
  | uintRanges
  /-- Every type below a given one — what a `Map(K, V)`'s witness is summed over. -/
  | subtypesOf (k : Ty)
  /-- Every type — what a `Collection(V)`'s witness is summed over. The top of the *kind*
  order; it says nothing about values. -/
  | everyType
deriving Repr, DecidableEq

/-- A kind is well-formed when the types it names are. Needed wherever the order appeals to
subtyping, which is reflexive and transitive only over well-formed types. -/
inductive TypeKind.WellFormed : TypeKind → Prop where
  | candidates {ds} : (∀ d ∈ ds, Ty.WellFormed d) → TypeKind.WellFormed (.candidates ds)
  | uintRanges : TypeKind.WellFormed .uintRanges
  | subtypesOf {k} : Ty.WellFormed k → TypeKind.WellFormed (.subtypesOf k)
  | everyType : TypeKind.WellFormed .everyType

/-- Does `k` classify `d`? One constructor per type kind, because how each states which types
it classifies is what the question turns on (`constrain.rs :: candidate_in_kind`).

Membership in a candidate list is **equality**, not subtyping: the list names its members,
so being one of them is identity. At a Σ's witness that reading is also the one the position
requires, since a data domain is invariant and a refined range is therefore a different
candidate from the range it refines. Membership in a `subtypesOf` bound is subtyping, which
is why the Rust draws it as an edge rather than deciding it structurally. -/
inductive Admits : TypeKind → Ty → Prop where
  | everyType {d} : Admits .everyType d
  | uintRanges {n} : Admits .uintRanges (.uintRange n)
  | subtypesOf {k d} : Subtyping d k → Admits (.subtypesOf k) d
  | candidates {ds d} : d ∈ ds → Admits (.candidates ds) d

/-- The **kind premise** of the Σ rule: every type `sub` admits is admitted by `sup`.

One constructor per arm of `constrain_type_kinds`. No variance and no case per kind pair:
containment orders the classifiers, and what differs between the four is only how each states
which types it classifies.

`everyType` and `candidates` overlap on `ContainedIn (.candidates ds) .everyType`, which both
derive. That is two derivations of one fact rather than an ambiguity — unlike `Subtyping`,
whose constructors pin both sides' heads and so are disjoint. -/
inductive ContainedIn : TypeKind → TypeKind → Prop where
  /-- The universe admits every type, so nothing is left to ask. -/
  | everyType {sub} : ContainedIn sub .everyType
  /-- Candidates are members, so containment is membership, once per member. -/
  | candidates {ds sup} : (∀ d ∈ ds, Admits sup d) → ContainedIn (.candidates ds) sup
  /-- **Two bounds are ordered by their bounds.** Every type below `a` is below `b`
  exactly when `a <: b`, which is one ordinary covariant edge. -/
  | subtypesOf {a b} : Subtyping a b → ContainedIn (.subtypesOf a) (.subtypesOf b)
  | uintRanges : ContainedIn .uintRanges .uintRanges

/-- Containment **transports membership**: this is the sense in which the order really orders
the classifiers, rather than being a relation that happens to be reflexive and transitive.

Every naming scheme discharges it differently and none of them structurally: a candidate
list hands over the member it already holds, a bound appeals to subtyping's transitivity,
and a kind naming no members has nothing to hand over but the property it states. -/
theorem Admits.mono {M N : TypeKind} {d : Ty}
    (hM : M.WellFormed) (hN : N.WellFormed) (hd : Ty.WellFormed d)
    (h : ContainedIn M N) (ha : Admits M d) : Admits N d := by
  cases h with
  | everyType => exact .everyType
  | candidates hall =>
      cases ha with
      | candidates hmem => exact hall d hmem
  | subtypesOf hab =>
      cases ha with
      | subtypesOf hda =>
          cases hM with
          | subtypesOf hwa =>
            cases hN with
            | subtypesOf hwb => exact .subtypesOf (subtyping_trans hd hwa hwb hda hab)
  | uintRanges => exact ha

/-! ## The decision a caller with no graph makes

`Admits` is the relation; `ccl::ty::TypeKind::refuses` is what a caller decides when it has no
graph to draw an edge into. The two are related in one direction only, and that direction is
the whole of what makes a rejection legitimate.
-/

mutual

/-- Does a refinement occur anywhere in this type?

The model's image of `Type::holds_an_unresolved_position`. `Ty` carries no `Infer` and no
`Hole`, so those disjuncts have nothing to range over and what is left is the refinement one:
equality compares a predicate, and a predicate's own type slots are not reachable from the slot
walk the Rust uses, so a refinement is treated as still open on both sides. -/
def Ty.holdsARefinement : Ty → Bool
  | .refined _ _ => true
  | .base _ | .uintRange _ | .dataSource _ | .txn => false
  | .fn _ _ d c => Ty.holdsARefinement d || Ty.holdsARefinement c
  | .tuple ts => Ty.holdsARefinementSeq ts
  | .record fs => Ty.holdsARefinementFields fs
  | .variant tags => Ty.holdsARefinementTags tags
termination_by t => sizeOf t
decreasing_by all_goals (try simp_wf) <;> omega

def Ty.holdsARefinementSeq : List Ty → Bool
  | [] => false
  | t :: rest => Ty.holdsARefinement t || Ty.holdsARefinementSeq rest
termination_by ts => sizeOf ts
decreasing_by all_goals (try simp_wf) <;> omega

def Ty.holdsARefinementFields : List (String × Ty) → Bool
  | [] => false
  | (_, t) :: rest => Ty.holdsARefinement t || Ty.holdsARefinementFields rest
termination_by fs => sizeOf fs
decreasing_by all_goals (try simp_wf) <;> omega

def Ty.holdsARefinementTags : List (FieldKey × Ty) → Bool
  | [] => false
  | (_, t) :: rest => Ty.holdsARefinement t || Ty.holdsARefinementTags rest
termination_by ts => sizeOf ts
decreasing_by all_goals (try simp_wf) <;> omega

end

/-- `ccl::ty::TypeKind::refuses`: **certain non-membership**, the only half of the membership
question a caller may act on.

Every caller turns the answer into a rejection — `answer_type_kinds` and `candidate_in_kind`
raise `NotOfKind`, `coalesce_compact_go` raises `KindMismatch` — so a `true` where [`Admits`]
holds refuses a program that type-checks. Two arms decide and two abstain. A bound abstains
because its membership is subtyping, which the solver draws as an edge, so a caller with no
graph has nothing to certify; the universe abstains because it refuses nothing at all.

`Ty` carries no unresolved position, so these are the resolved fragment of the Rust's arms —
its `Infer`/`Hole` abstentions have nothing here to range over. -/
def refuses : TypeKind → Ty → Bool
  | .everyType, _ => false
  | .subtypesOf _, _ => false
  | .uintRanges, .uintRange _ => false
  | .uintRanges, _ => true
  | .candidates ds, d =>
      !d.holdsARefinement && !ds.any Ty.holdsARefinement && !ds.any (Ty.beq d ·)

/-- **A refusal is sound**: nothing `refuses` rejects is a member.

The property every caller rests on, and the one the equality test on a bound broke —
[`a_bound_admits_what_equality_refuses`] carries the pair. Only the two deciding arms have
content: an abstention is vacuous, since nothing reads a `false` here as membership. -/
theorem not_admits_of_refuses : (K : TypeKind) → (d : Ty) → refuses K d = true → ¬ Admits K d
  | .everyType, _, h => by simp [refuses] at h
  | .subtypesOf _, _, h => by simp [refuses] at h
  | .uintRanges, .uintRange _, h => by simp [refuses] at h
  | .uintRanges, .base _, _ | .uintRanges, .dataSource _, _ | .uintRanges, .txn, _
  | .uintRanges, .fn .., _ | .uintRanges, .tuple _, _ | .uintRanges, .record _, _
  | .uintRanges, .variant _, _ | .uintRanges, .refined .., _ => by
      intro ha; cases ha
  | .candidates ds, d, h => by
      intro ha
      cases ha with
      | candidates hmem =>
          simp only [refuses, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at h
          exact absurd ((Ty.beq_iff d d).mpr rfl) (by simpa using h.2 d hmem)

/-- **A bound admits what equality refuses.** `{Int | p} <: Int`, so `subtypesOf Int` admits
it, and the two are not equal — so the arm's old answer reported certain non-membership of a
member, and every caller raised on it.

`Ty` carries no unresolved position, so the arm's *other* old answer — a parameter that is
`Infer` or `Hole`, admitting everything — has nothing here to exhibit. -/
theorem a_bound_admits_what_equality_refuses :
    Admits (.subtypesOf (.base .int)) (.refined (.base .int) [.litBool true])
      ∧ Ty.beq (.refined (.base .int) [.litBool true]) (.base .int) = false := by
  refine ⟨.subtypesOf (.refined rfl rfl (Or.inl (by simp)) ?_ (.base .int)), by simp [Ty.beq]⟩
  simp [deficit]

/-- Containment is **reflexive** over well-formed kinds, so a Σ edge between two spellings
of one kind carries no obligation. -/
theorem ContainedIn.refl : (k : TypeKind) → k.WellFormed → ContainedIn k k
  | .everyType, _ => .everyType
  | .uintRanges, _ => .uintRanges
  | .subtypesOf _, .subtypesOf hw => .subtypesOf (Subtyping.refl _ hw)
  | .candidates _, .candidates _ => .candidates fun _ hm => .candidates hm

/-- Containment is **transitive**, so a chain of Σ edges composes into one. The candidate
case is where the work is, and it is [`Admits.mono`] once per member. -/
theorem ContainedIn.trans {A B C : TypeKind}
    (hA : A.WellFormed) (hB : B.WellFormed) (hC : C.WellFormed)
    (h1 : ContainedIn A B) (h2 : ContainedIn B C) : ContainedIn A C := by
  cases h1 with
  | everyType =>
      cases h2 with
      | everyType => exact .everyType
  | candidates hall =>
      refine .candidates fun d hmem => ?_
      cases hA with
      | candidates hwds => exact Admits.mono hB hC (hwds d hmem) h2 (hall d hmem)
  | subtypesOf hab =>
      cases h2 with
      | everyType => exact .everyType
      | subtypesOf hbc =>
          cases hA with
          | subtypesOf hwa =>
            cases hB with
            | subtypesOf hwb =>
              cases hC with
              | subtypesOf hwc => exact .subtypesOf (subtyping_trans hwa hwb hwc hab hbc)
  | uintRanges =>
      cases h2 with
      | everyType => exact .everyType
      | uintRanges => exact .uintRanges

end CclFormal
