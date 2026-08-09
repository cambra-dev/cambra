import CclFormal.Sub

/-!
# The executable ground subtype checker

`subCheck` is the Bool-valued decision procedure for `Sub` — the mirror of
`constrain_go`'s ground control flow, and the executable half of the M1
differential oracle (`subCheck` vs `constrain_subtype` on ground pairs).
Soundness and completeness against `Sub` are proved in
`CclFormal/Equiv.lean`, so the relation is decidable and every `#guard`
below is a fact about `Sub` itself.
-/

namespace CclFormal

/-- Bool form of `kindOk`. -/
def kindOkB : FunKind → FunKind → Bool
  | .compute, .data => false
  | _, _ => true

mutual

/-- Decide `Sub ρl ρr lhs rhs`, arm for arm with `constrain_go`'s ground
fragment (partition collapse as normalization — see `Sub`'s module doc). -/
def subCheck (ρl ρr : Ren) (lhs rhs : Ty) : Bool :=
  match lhs, rhs with
  | .base a, .base b => a == b
  | .uintRange a, .uintRange b => a == b
  | .dataSource a, .dataSource b => a == b
  | .txn, .txn => true
  | .fn n0 k0 d0 c0, .fn n1 k1 d1 c1 =>
      if _h : (normFun (.fn n0 k0 d0 c0)).isSome ∨
          (normFun (.fn n1 k1 d1 c1)).isSome then
        -- Partition normalization: rewrite to the plain form(s), re-enter.
        subCheck ρl ρr ((normFun (.fn n0 k0 d0 c0)).getD (.fn n0 k0 d0 c0))
          ((normFun (.fn n1 k1 d1 c1)).getD (.fn n1 k1 d1 c1))
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
    | (have := normPair_sizeOf _ _ _h; simp at this ⊢; omega)

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

/- Partition normalization: `⧺ᵢ ({D | πᵢ} ⤇ W) <: D ⤇ W` — a gated
partition of `D` *is* the plain data function over `D`. -/
#guard subCheck .id .id
  (.fn none .data
    (.variant [(.idx 0, .refined (.uintRange 3) (.litInt 0)),
               (.idx 1, .refined (.uintRange 3) (.litInt 1))])
    (.base .int))
  (.fn none .data (.uintRange 3) (.base .int)) = true

/- Normalization boundary: non-contiguous indices are not a partition; the
general arm's domain edge (`[0,3) ⊀ Variant`) then rejects. -/
#guard subCheck .id .id
  (.fn none .data
    (.variant [(.idx 1, .refined (.uintRange 3) (.litInt 0))])
    (.base .int))
  (.fn none .data (.uintRange 3) (.base .int)) = false

/- A partition of a *different* domain normalizes to that domain and then
fails data-data invariance against the demand. -/
#guard subCheck .id .id
  (.fn none .data
    (.variant [(.idx 0, .refined (.uintRange 4) (.litInt 0))])
    (.base .int))
  (.fn none .data (.uintRange 3) (.base .int)) = false

/- **Repaired quirk**: normalization re-enters the general arm, so
α-equivalent dependent codomains reconcile regardless of whether the
supplier's domain is partition-shaped (the retired bridge arm rejected this
pair by skipping the Pi correspondence). -/
#guard subCheck .id .id
  (.fn (some "x") .data
    (.variant [(.idx 0, .refined (.uintRange 3) (.litInt 0))])
    (.refined (.base .int) (.binop "eq" .elem (.var "x"))))
  (.fn (some "y") .data (.uintRange 3)
    (.refined (.base .int) (.binop "eq" .elem (.var "y")))) = true

/- **Repaired composition**: the counterexample chain that refuted
transitivity under the bridge arm now composes — see
`CclFormal/Trans.lean` for the machine-checked derivations. -/
#guard subCheck .id .id
  (.fn none .data
    (.variant [(.idx 0, .refined (.record [("a", .base .int)]) (.litBool true))])
    (.base .int))
  (.fn none .compute (.record [("a", .base .int), ("b", .base .bool)])
    (.base .int)) = true

end CclFormal
