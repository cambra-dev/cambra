import CclFormal.Subtyping
import CclFormal.SubtypingIsReflexive
import CclFormal.SubtypingIsTransitive
import CclFormal.SubtypeCheckDecidesSubtyping

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

Membership is decided where a position materializes, once its type is a type
(`constrain.rs :: admits_resolved`). On a resolved type that check is a decision, and
[`admitsCheck`] is its image here: [`admitsCheck_iff_admits`] proves it decides exactly
[`Admits`].

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
it classifies is what the question turns on (`constrain.rs :: admits`).

Membership in a candidate list is **equality**, not subtyping: the list names its members,
so being one of them is identity. At a Σ's witness that reading is also the one the position
requires, since a data domain is invariant and a refined range is therefore a different
candidate from the range it refines. Membership in a `subtypesOf` bound is subtyping. -/
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

/-! ## The decision at materialization

`ccl::infer::solver::constrain::admits_resolved` decides membership for a materialized position.
It abstains only on an inference variable left in the type, which `Ty` does not carry, so on the
modelled fragment it is a decision. A refinement is decided like any other type: by then its
predicate has been coalesced, so equality and subtyping read it whole.
-/

/-- `admits_resolved` on a resolved type: equality against the candidates, a dense range for
`uintRanges` (a refinement over a range is not one), subtyping for a bound, anything for the
universe. -/
def admitsCheck : TypeKind → Ty → Bool
  | .everyType, _ => true
  | .uintRanges, .uintRange _ => true
  | .uintRanges, _ => false
  | .subtypesOf k, d => subtypeCheck d k
  | .candidates ds, d => ds.any (Ty.beq d ·)

/-- **The check decides membership**: it accepts exactly the members, so a rejection never
refuses a member and an acceptance never admits a non-member. -/
theorem admitsCheck_iff_admits :
    (K : TypeKind) → (d : Ty) → (admitsCheck K d = true ↔ Admits K d)
  | .everyType, _ => by simp [admitsCheck, Admits.everyType]
  | .uintRanges, .uintRange _ => by simp [admitsCheck, Admits.uintRanges]
  | .uintRanges, .base _ | .uintRanges, .dataSource _ | .uintRanges, .txn
  | .uintRanges, .fn .. | .uintRanges, .tuple _ | .uintRanges, .record _
  | .uintRanges, .variant _ | .uintRanges, .refined .. => by
      simp only [admitsCheck, Bool.false_eq_true, false_iff]
      intro ha; cases ha
  | .subtypesOf k, d => by
      rw [admitsCheck, subtypeCheck_iff_subtyping]
      exact ⟨Admits.subtypesOf, fun ha => by cases ha; assumption⟩
  | .candidates ds, d => by
      simp only [admitsCheck, List.any_eq_true]
      constructor
      · rintro ⟨e, hmem, hbeq⟩
        rw [(Ty.beq_iff d e).mp hbeq]
        exact .candidates hmem
      · intro ha
        cases ha with
        | candidates hmem => exact ⟨d, hmem, (Ty.beq_iff d d).mpr rfl⟩

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
