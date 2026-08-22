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
  | .compute, .compute => true
  | .data, .data => true
  | _, _ => false

mutual

/-- Decide `Sub lhs rhs`, arm for arm with `constrain_go`'s ground
fragment. Ground types are closed, so there are no morphisms to thread —
codomains (and their index-spelled refinements) compare directly. -/
def subCheck (lhs rhs : Ty) : Bool :=
  match lhs, rhs with
  | .base a, .base b => a == b
  | .uintRange a, .uintRange b => a == b
  | .dataSource a, .dataSource b => a == b
  | .txn, .txn => true
  | .fn _ k0 d0 c0, .fn _ k1 d1 c1 =>
      kindOkB k0 k1 &&
      (if k0 == .data && k1 == .data then
        subCheck d1 d0 && subCheck d0 d1
      else
        subCheck d1 d0) &&
      subCheck c0 c1
  | .tuple a, .tuple b => subSeq a b
  | .record a, .record b => subFields a b
  | .variant a, .variant b => subTags b a
  | lhs, rhs =>
      -- The refinement arm doubles as the mismatch catch-all: with no
      -- refinement layer on either side this is `constrain_go`'s final
      -- `Mismatch`.
      if _h : lhs.peel.2 = [] ∧ rhs.peel.2 = [] then false
      else
        (deficit lhs.peel.2 rhs.peel.2).isEmpty &&
        subCheck lhs.peel.1 rhs.peel.1
termination_by sizeOf lhs + sizeOf rhs
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact Ty.peel_sum_lt _ _ _h

/-- Tuple positions, in demand (rhs) order. -/
def subSeq (a b : List Ty) : Bool :=
  match a, b with
  | _, [] => true
  | [], _ :: _ => false
  | t0 :: a', t1 :: b' => subCheck t0 t1 && subSeq a' b'
termination_by sizeOf a + sizeOf b
decreasing_by all_goals (simp_wf; omega)

/-- Record fields the rhs demands, looked up find-first in the lhs. -/
def subFields (a : List (String × Ty)) (b : List (String × Ty)) : Bool :=
  match b with
  | [] => true
  | (n, t1) :: rest =>
      (match _h : lookupBy a n with
        | some t0 => subCheck t0 t1
        | none => false) &&
      subFields a rest
termination_by sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  · have := lookupBy_sizeOf _h
    omega
  · omega


/-- Variant tags the lhs may produce, looked up find-first in the rhs. -/
def subTags (b a : List (FieldKey × Ty)) : Bool :=
  match a with
  | [] => true
  | (k, t0) :: rest =>
      (match _h : lookupBy b k with
        | some t1 => subCheck t0 t1
        | none => false) &&
      subTags b rest
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
#guard subCheck (.refined (.base .int) [.elem]) (.base .int) = true

/- `Int ⊀ {Int | p}` — a refinement cannot be conjured (that is `Restrict`). -/
#guard subCheck (.base .int) (.refined (.base .int) [.elem]) = false

/- `{T | p} <: {U | p}` iff `T <: U` — the refined base is covariant:
`{{a, b} | p} <: {{a} | p}` by record width under the shared predicate. -/
#guard subCheck
  (.refined (.record [("a", .base .int), ("b", .base .bool)]) [.elem])
  (.refined (.record [("a", .base .int)]) [.elem]) = true

/- `UIntRange` is equality-only: `[0,3) ⊀ [0,4)` despite the inclusion. -/
#guard subCheck (.uintRange 3) (.uintRange 4) = false
#guard subCheck (.uintRange 3) (.uintRange 3) = true

/- Record width: more fields flow to fewer, never the reverse. -/
#guard subCheck
  (.record [("a", .base .int), ("b", .base .bool)])
  (.record [("a", .base .int)]) = true
#guard subCheck
  (.record [("a", .base .int)])
  (.record [("a", .base .int), ("b", .base .bool)]) = false

/- Variant width is the dual: fewer tags flow to more. -/
#guard subCheck
  (.variant [(.name "some", .base .int)])
  (.variant [(.name "some", .base .int), (.name "none", .base .unit)]) = true

/- The kinds relate by equality: neither a collection where a capability is
demanded nor a capability where a collection is demanded. -/
#guard subCheck
  (.fn none .data (.uintRange 2) (.base .int))
  (.fn none .compute (.uintRange 2) (.base .int)) = false
#guard subCheck
  (.fn none .compute (.uintRange 2) (.base .int))
  (.fn none .data (.uintRange 2) (.base .int)) = false
#guard subCheck
  (.fn none .data (.uintRange 2) (.base .int))
  (.fn none .data (.uintRange 2) (.base .int)) = true

/- Compute domains are contravariant; **data-data domains are invariant**
(the domain *is* the data), so the same domain widening data-to-data fails. -/
#guard subCheck
  (.fn none .compute (.record [("a", .base .int)]) (.base .int))
  (.fn none .compute (.record [("a", .base .int), ("b", .base .bool)])
    (.base .int)) = true
#guard subCheck
  (.fn none .data (.record [("a", .base .int)]) (.base .int))
  (.fn none .data (.record [("a", .base .int), ("b", .base .bool)])
    (.base .int)) = false

/- Indices make α-canonicity structural: two α-variant
dependent function types are the *same* term — `(x: [0,3)) ⤇ {Int | __elem == #0}`
and its `y`-spelt twin both close to `piBound 0`, whatever the display
binder says. -/
#guard subCheck
  (.fn (some "x") .data (.uintRange 3)
    (.refined (.base .int) [(.binop "eq" .elem (.piBound 0))]))
  (.fn (some "y") .data (.uintRange 3)
    (.refined (.base .int) [(.binop "eq" .elem (.piBound 0))])) = true

/- Injectivity: a reference to a *different* frame is a different index and
does not match — the silent specialization sharing indices exist to rule
out. -/
#guard subCheck
  (.fn (some "x") .data (.uintRange 3)
    (.refined (.base .int) [(.binop "eq" .elem (.piBound 0))]))
  (.fn (some "y") .data (.uintRange 3)
    (.refined (.base .int) [(.binop "eq" .elem (.piBound 1))])) = false

/- A *free* reference (a `let`-bound name a refinement may keep) is a globally
unique name and compares structurally: same name matches, distinct names do
not. -/
#guard subCheck
  (.fn (some "x") .data (.uintRange 3)
    (.refined (.base .int) [(.binop "eq" .elem (.var "n"))]))
  (.fn (some "y") .data (.uintRange 3)
    (.refined (.base .int) [(.binop "eq" .elem (.var "n"))])) = true
#guard subCheck
  (.fn (some "x") .data (.uintRange 3)
    (.refined (.base .int) [(.binop "eq" .elem (.var "n"))]))
  (.fn (some "y") .data (.uintRange 3)
    (.refined (.base .int) [(.binop "eq" .elem (.var "m"))])) = false

/- No partition collapse: a `Variant` domain is below only a `Variant`
domain, so a fan-out-shaped supplier does not satisfy a plain-domain demand.
The fan-out never presents this pair — it is a `DisjointJoin` over the one
domain its arms share — so the relation needs no arm for it. -/
#guard subCheck
  (.fn none .data
    (.variant [(.idx 0, .refined (.uintRange 3) [(.litInt 0)]),
               (.idx 1, .refined (.uintRange 3) [(.litInt 1)])])
    (.base .int))
  (.fn none .data (.uintRange 3) (.base .int)) = false

/- A chain whose two hops use different rules — contravariant record width at
each — composes: the executable face of `sub_trans_id`. The kind cannot be one
of the hops any more; it is fixed across the whole chain. -/
#guard subCheck
  (.fn none .compute (.record [("a", .base .int)]) (.base .int))
  (.fn none .compute (.record [("a", .base .int), ("b", .base .bool)])
    (.base .int)) = true
#guard subCheck
  (.fn none .compute (.record [("a", .base .int), ("b", .base .bool)])
    (.base .int))
  (.fn none .compute
    (.record [("a", .base .int), ("b", .base .bool), ("c", .base .unit)])
    (.base .int)) = true
#guard subCheck
  (.fn none .compute (.record [("a", .base .int)]) (.base .int))
  (.fn none .compute
    (.record [("a", .base .int), ("b", .base .bool), ("c", .base .unit)])
    (.base .int)) = true

end CclFormal
