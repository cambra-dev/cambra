import CclFormal.Sub

/-!
# The executable ground subtype checker

`subCheck` is the Bool-valued decision procedure for `Sub` — the mirror of
`constrain_go`'s ground control flow, and the executable half of the M1
differential oracle (`subCheck` vs `constrain_subtype` on ground pairs).
Soundness/completeness against the `Sub` inductive is the next M0 step; it
will need `Ty.beq ↔ Eq` (the derived `BEq` bridged to propositional
equality), which is deliberately not assumed anywhere yet.
-/

namespace CclFormal

/-- Bool form of `kindOk`. -/
def kindOkB : FunKind → FunKind → Bool
  | .compute, .data => false
  | _, _ => true

/-- Bool form of `IndexPartitionTags`. -/
def indexPartitionTagsB (base : Ty) : Nat → List (FieldKey × Ty) → Bool
  | _, [] => true
  | i, (k, payload) :: rest =>
      k == .idx i && payload.stripRefinements == base &&
      indexPartitionTagsB base (i + 1) rest

/-- Bool form of `IsIndexPartitionOf`. -/
def isIndexPartitionOfB (unionDom target : Ty) : Bool :=
  match unionDom with
  | .variant tags =>
      !tags.isEmpty && indexPartitionTagsB target.stripRefinements 0 tags
  | _ => false

mutual

/-- Decide `Sub ρl ρr lhs rhs`, arm for arm with `constrain_go`'s ground
fragment (bridge rule excluded — see `Sub`'s module doc). -/
def subCheck (ρl ρr : Ren) (lhs rhs : Ty) : Bool :=
  match lhs, rhs with
  | .base a, .base b => a == b
  | .uintRange a, .uintRange b => a == b
  | .dataSource a, .dataSource b => a == b
  | .txn, .txn => true
  | .fn n0 k0 d0 c0, .fn n1 k1 d1 c1 =>
      if k0 == .data && isIndexPartitionOfB d0 d1 then
        -- Bridge branch: legs covariant into the rhs domain, codomain
        -- *without* the Pi correspondence (faithful to `constrain_go`).
        (match d0 with
          | .variant tags => subBridge ρl ρr d1 tags
          | _ => false) &&
        subCheck ρl ρr c0 c1
      else
        kindOkB k0 k1 &&
        (if k0 == .data && k1 == .data then
          subCheck ρr ρl d1 d0 && subCheck ρl ρr d0 d1
        else
          subCheck ρr ρl d1 d0) &&
        subCheck (codRen n0 n1 ρl) ρr c0 c1
  | .tuple a, .tuple b => subSeq ρl ρr a b
  | .record a, .record b => subFields ρl ρr a b
  | .variant a, .variant b => subTags ρl ρr b a
  | lhs, rhs =>
      -- The refinement arm doubles as the mismatch catch-all: with no
      -- refinement layer on either side this is `constrain_go`'s final
      -- `Mismatch`.
      if _h : lhs.peel.2 = [] ∧ rhs.peel.2 = [] then false
      else
        (deficit ρl ρr lhs.peel.2 rhs.peel.2).isEmpty &&
        subCheck ρl ρr lhs.peel.1 rhs.peel.1
termination_by sizeOf lhs + sizeOf rhs
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact Ty.peel_sum_lt _ _ _h

/-- Tuple positions, in demand (rhs) order. -/
def subSeq (ρl ρr : Ren) (a b : List Ty) : Bool :=
  match a, b with
  | _, [] => true
  | [], _ :: _ => false
  | t0 :: a', t1 :: b' => subCheck ρl ρr t0 t1 && subSeq ρl ρr a' b'
termination_by sizeOf a + sizeOf b
decreasing_by all_goals (simp_wf; omega)

/-- Record fields the rhs demands, looked up find-first in the lhs. -/
def subFields (ρl ρr : Ren) (a b : List (String × Ty)) : Bool :=
  match b with
  | [] => true
  | (n, t1) :: rest =>
      (match _h : lookupBy a n with
        | some t0 => subCheck ρl ρr t0 t1
        | none => false) &&
      subFields ρl ρr a rest
termination_by sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  · have := lookupBy_sizeOf _h
    omega
  · omega

/-- Bridge legs: every payload of the partitioned lhs domain flows
covariantly into the rhs domain. -/
def subBridge (ρl ρr : Ren) (d1 : Ty) (tags : List (FieldKey × Ty)) : Bool :=
  match tags with
  | [] => true
  | (_, payload) :: rest => subCheck ρl ρr payload d1 && subBridge ρl ρr d1 rest
termination_by sizeOf d1 + sizeOf tags
decreasing_by all_goals (simp_wf; omega)

/-- Variant tags the lhs may produce, looked up find-first in the rhs. -/
def subTags (ρl ρr : Ren) (b a : List (FieldKey × Ty)) : Bool :=
  match a with
  | [] => true
  | (k, t0) :: rest =>
      (match _h : lookupBy b k with
        | some t1 => subCheck ρl ρr t0 t1
        | none => false) &&
      subTags ρl ρr b rest
termination_by sizeOf b + sizeOf a
decreasing_by
  all_goals simp_wf
  · have := lookupBy_sizeOf _h
    omega
  · omega

end

/-!
## Executable spec examples

One `#guard` per adjudicated behavior (see `formal/design.md`, "M0 status
and adjudicated decisions") — the checker refusing to build is the cheapest
regression net for the rules' shape.
-/

/- `{Int | p} <: Int` — dropping a refinement is subsumption. -/
#guard subCheck .id .id (.refined (.base .int) .elem) (.base .int) = true

/- `Int ⊀ {Int | p}` — a refinement cannot be conjured (that is `Restrict`). -/
#guard subCheck .id .id (.base .int) (.refined (.base .int) .elem) = false

/- `{T | p} <: {U | p}` iff `T <: U` — the refined base is covariant:
`{{a, b} | p} <: {{a} | p}` by record width under the shared predicate. -/
#guard subCheck .id .id
  (.refined (.record [("a", .base .int), ("b", .base .bool)]) .elem)
  (.refined (.record [("a", .base .int)]) .elem) = true

/- `UIntRange` is equality-only: `[0,3) ⊀ [0,4)` despite the inclusion. -/
#guard subCheck .id .id (.uintRange 3) (.uintRange 4) = false
#guard subCheck .id .id (.uintRange 3) (.uintRange 3) = true

/- Record width: more fields flow to fewer, never the reverse. -/
#guard subCheck .id .id
  (.record [("a", .base .int), ("b", .base .bool)])
  (.record [("a", .base .int)]) = true
#guard subCheck .id .id
  (.record [("a", .base .int)])
  (.record [("a", .base .int), ("b", .base .bool)]) = false

/- Variant width is the dual: fewer tags flow to more. -/
#guard subCheck .id .id
  (.variant [(.name "some", .base .int)])
  (.variant [(.name "some", .base .int), (.name "none", .base .unit)]) = true

/- The kind lattice `data ⊑ compute`: a collection satisfies a capability
demand, a capability never satisfies a collection demand. -/
#guard subCheck .id .id
  (.fn none .data (.uintRange 2) (.base .int))
  (.fn none .compute (.uintRange 2) (.base .int)) = true
#guard subCheck .id .id
  (.fn none .compute (.uintRange 2) (.base .int))
  (.fn none .data (.uintRange 2) (.base .int)) = false

/- Compute domains are contravariant; **data-data domains are invariant**
(the domain *is* the data), so the same domain widening data-to-data fails. -/
#guard subCheck .id .id
  (.fn none .compute (.record [("a", .base .int)]) (.base .int))
  (.fn none .compute (.record [("a", .base .int), ("b", .base .bool)])
    (.base .int)) = true
#guard subCheck .id .id
  (.fn none .data (.record [("a", .base .int)]) (.base .int))
  (.fn none .data (.record [("a", .base .int), ("b", .base .bool)])
    (.base .int)) = false

/- The Pi-binder correspondence: a dependent codomain refinement matches its
α-renamed twin (`(x: [0,3)) ⤇ {Int | __elem == x}` vs the same under `y`). -/
#guard subCheck .id .id
  (.fn (some "x") .data (.uintRange 3)
    (.refined (.base .int) (.binop "eq" .elem (.var "x"))))
  (.fn (some "y") .data (.uintRange 3)
    (.refined (.base .int) (.binop "eq" .elem (.var "y")))) = true

/- ...and a genuinely different binder reference does not match. -/
#guard subCheck .id .id
  (.fn (some "x") .data (.uintRange 3)
    (.refined (.base .int) (.binop "eq" .elem (.var "x"))))
  (.fn (some "y") .data (.uintRange 3)
    (.refined (.base .int) (.binop "eq" .elem (.var "z")))) = false

/- The bridge rule: `⧺ᵢ ({D | πᵢ} ⤇ W) <: D ⤇ W` — a gated partition of `D`
is the plain data function over `D`, legs covariant. -/
#guard subCheck .id .id
  (.fn none .data
    (.variant [(.idx 0, .refined (.uintRange 3) (.litInt 0)),
               (.idx 1, .refined (.uintRange 3) (.litInt 1))])
    (.base .int))
  (.fn none .data (.uintRange 3) (.base .int)) = true

/- Bridge boundary: non-contiguous indices are not a partition; the general
arm's contravariant domain edge (`[0,3) ⊀ Variant`) then rejects. -/
#guard subCheck .id .id
  (.fn none .data
    (.variant [(.idx 1, .refined (.uintRange 3) (.litInt 0))])
    (.base .int))
  (.fn none .data (.uintRange 3) (.base .int)) = false

/- Bridge boundary: a leg whose *stripped* payload differs from the target
is not a partition either. -/
#guard subCheck .id .id
  (.fn none .data
    (.variant [(.idx 0, .refined (.uintRange 4) (.litInt 0))])
    (.base .int))
  (.fn none .data (.uintRange 3) (.base .int)) = false

/- **Flagged quirk, modeled faithfully**: the bridge arm's codomain edge
carries no Pi-binder correspondence, so α-equivalent dependent codomains —
which the general arm accepts (see the Pi-correspondence `#guard` above) —
do NOT match when the domain shape routes the pair through the bridge. -/
#guard subCheck .id .id
  (.fn (some "x") .data
    (.variant [(.idx 0, .refined (.uintRange 3) (.litInt 0))])
    (.refined (.base .int) (.binop "eq" .elem (.var "x"))))
  (.fn (some "y") .data (.uintRange 3)
    (.refined (.base .int) (.binop "eq" .elem (.var "y")))) = false

end CclFormal
