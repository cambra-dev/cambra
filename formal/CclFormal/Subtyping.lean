import CclFormal.Ty

/-!
# The declarative concrete subtype relation

`Subtyping lhs rhs` is the Lean statement of the relation `src/ccl/infer/solver/constrain.rs ::
constrain_go` *implements* on concrete types (no `Infer` on either side) — stated declaratively; the
Rust operationalizes subsumption inside `constrain` and never writes the relation down.

Concrete types are **closed** (`src/ccl/design/type-inference.md`, "A binder reference is stored in
one of two forms"): a constructed function never carries a free name for its own binder —
construction converts the reference to a de Bruijn index (`Predicate.piBound`, mirroring
`Name::PiBound`), so two α-variant function types are structurally identical and refinements compare
structurally with no transport. The relation therefore carries **no rename environments**: the `Ren`
machinery that mirrored `Subst::extended_rename` modeled the solver's name-spelled mid-solve form,
which closure keeps out of concrete types. The `fn` binder slot survives in the grammar as the
opening address (the solver's descent and application open at it), but the relation never reads it.

## Deliberate departures from `constrain_go` (each is a tracked decision)

- **No trivial-equality short-circuit.** `constrain_go` starts with
  `lhs == rhs → Ok` (under identity morphisms). Here reflexivity is a *theorem* (`Subtyping.refl`),
  not a rule — provable only for well-formed (uniquely-keyed) types, which surfaces that the
  short-circuit and the find-first record/variant arms disagree on duplicate-keyed products. See
  `Ty.WellFormed`.

- **No binder-correspondence edge.** `constrain_go`'s Fun/Fun codomain edge
  opens each closed codomain at its own binder and carries the correspondence onward for the
  solver's name-spelled fragments; on closed concrete inputs the open-then-rename round trip is the
  identity on the indices, so the model compares codomains directly. A verdict divergence here is a
  finding about the opening sites, which is what the differential oracle is pointed at.

- **No partition-collapse arm.** A value-`Case` fan-out is a
  `DisjointJoin` over the arms' one shared domain, so no comparison ever meets a `Variant` of
  refined legs in domain position against a plain-domain demand (`src/ccl/design/ir.md`, "`Copair`
  and `DisjointJoin` — two collection-combining operations, not one"). The relation therefore
  relates a `Variant` domain only to a `Variant` domain.
-/

namespace CclFormal

/-- Peel all outer refinement layers: mirror of
`constrain.rs :: peel_refinements` (outermost predicate first). -/
def Ty.peel : Ty → Ty × List Predicate
  | .refined b ps => (b.peel.1, ps ++ b.peel.2)
  | t => (t, [])

/-- Peeling an unrefined type is the identity. -/
theorem Ty.peel_of_not_refined {t : Ty} (h : t.isRefined = false) :
    t.peel = (t, []) := by
  cases t <;> simp_all [Ty.peel, Ty.isRefined]

/-- Peeling never grows a type. -/
theorem Ty.peel_fst_sizeOf_le : (t : Ty) → sizeOf t.peel.1 ≤ sizeOf t
  | .base _ | .uintRange _ | .dataSource _ | .txn
  | .fn .. | .tuple _ | .record _ | .variant _ => by simp [Ty.peel]
  | .refined b p => by
      have ih := peel_fst_sizeOf_le b
      simp [Ty.peel]
      omega

/-- Peeling a genuinely refined type strictly shrinks it. -/
theorem Ty.peel_fst_sizeOf_lt : (t : Ty) → t.peel.2 ≠ [] → sizeOf t.peel.1 < sizeOf t
  | .base _, h | .uintRange _, h | .dataSource _, h | .txn, h
  | .fn .., h | .tuple _, h | .record _, h | .variant _, h => by
      simp [Ty.peel] at h
  | .refined b p, _ => by
      have ih := Ty.peel_fst_sizeOf_le b
      simp [Ty.peel]
      omega

/-- Combined form of the two peel lemmas: if either side is genuinely
refined, peeling both shrinks the pair — the decrease of the checker's
refinement arm. -/
theorem Ty.peel_sum_lt (lhs rhs : Ty)
    (h : ¬(lhs.peel.2 = [] ∧ rhs.peel.2 = [])) :
    sizeOf lhs.peel.1 + sizeOf rhs.peel.1 < sizeOf lhs + sizeOf rhs := by
  cases hl : lhs.peel.2 with
  | nil =>
      cases hr : rhs.peel.2 with
      | nil => exact absurd ⟨hl, hr⟩ h
      | cons _ _ =>
          have h1 := Ty.peel_fst_sizeOf_le lhs
          have h2 := Ty.peel_fst_sizeOf_lt rhs (by simp [hr])
          omega
  | cons _ _ =>
      have h1 := Ty.peel_fst_sizeOf_lt lhs (by simp [hl])
      have h2 := Ty.peel_fst_sizeOf_le rhs
      omega

/-- Peeling preserves well-formedness. -/
theorem Ty.WellFormed.peel_fst : {t : Ty} → t.WellFormed → t.peel.1.WellFormed
  | .base _, h | .uintRange _, h | .dataSource _, h | .txn, h
  | .fn .., h | .tuple _, h | .record _, h | .variant _, h => by
      simpa [Ty.peel] using h
  | .refined _ _, .refined _ _ hb => by
      simpa [Ty.peel] using hb.peel_fst

/-- A type with no top-level refinement layer is its own peel — for
well-formed types, whose refinement sets are non-empty (`Type::refined` never builds a `refined b
[]`, which would peel to its base while remaining a
distinct term). -/
theorem Ty.peel_nil_self : {t : Ty} → t.WellFormed → t.peel.2 = [] → t.peel.1 = t
  | .base _, _, _ | .uintRange _, _, _ | .dataSource _, _, _ | .txn, _, _
  | .fn .., _, _ | .tuple _, _, _ | .record _, _, _ | .variant _, _, _ => rfl
  | .refined _ _, .refined hne _ _, h => by
      simp [Ty.peel] at h
      exact absurd h.1 hne

/-- A peel is complete: the base it returns carries no refinement layer, so
peeling is idempotent. -/
theorem Ty.peel_fst_not_refined : (t : Ty) → t.peel.1.isRefined = false
  | .base _ | .uintRange _ | .dataSource _ | .txn
  | .fn .. | .tuple _ | .record _ | .variant _ => by simp [Ty.peel, Ty.isRefined]
  | .refined b _ => by simpa [Ty.peel] using Ty.peel_fst_not_refined b

theorem Ty.peel_fst_peel (t : Ty) : t.peel.1.peel = (t.peel.1, []) :=
  Ty.peel_of_not_refined (Ty.peel_fst_not_refined t)

/-- The refined case's termination shape: peeling the base stays under the
refined node's size, whatever the predicate contributes. -/
theorem Ty.peel_fst_lt_one_add (b : Ty) (n : Nat) :
    sizeOf b.peel.1 < 1 + sizeOf b + n := by
  have := Ty.peel_fst_sizeOf_le b
  omega

/-- Find-first keyed lookup, shared by the record and variant arms (the
Rust arms use `iter().find(..)`). -/
def lookupBy [BEq α] (l : List (α × Ty)) (k : α) : Option Ty :=
  (l.find? (fun e => e.1 == k)).map (·.2)

/-- A found value is smaller than the list it was found in. (The `SizeOf α`
binder matters: without it the statement elaborates with the default
trivial instance and stops matching use sites' real one.) -/
theorem lookupBy_sizeOf [BEq α] [SizeOf α] {l : List (α × Ty)} {k : α} {t : Ty}
    (h : lookupBy l k = some t) : sizeOf t < sizeOf l := by
  unfold lookupBy at h
  cases hf : l.find? (fun e => e.1 == k) with
  | none => simp [hf] at h
  | some e =>
      have hm := List.sizeOf_lt_of_mem (List.mem_of_find?_eq_some hf)
      obtain ⟨a, u⟩ := e
      simp [hf] at h
      subst h
      simp at hm
      omega

/-- A successful lookup found a real binding. -/
theorem lookupBy_mem [BEq α] [LawfulBEq α] {l : List (α × Ty)} {k : α} {t : Ty}
    (h : lookupBy l k = some t) : (k, t) ∈ l := by
  unfold lookupBy at h
  cases hf : l.find? (fun e => e.1 == k) with
  | none => simp [hf] at h
  | some e =>
      have hm := List.mem_of_find?_eq_some hf
      have hk := List.find?_some hf
      obtain ⟨a, b⟩ := e
      simp [hf] at h
      simp at hk
      subst hk h
      exact hm

/-- The converse under unique keys: lookup returns the member itself. -/
theorem lookupBy_of_mem_nodup [BEq α] [LawfulBEq α] {l : List (α × Ty)}
    {k : α} {t : Ty} (hnd : (l.map (·.1)).Nodup) (hm : (k, t) ∈ l) :
    lookupBy l k = some t := by
  induction l with
  | nil => cases hm
  | cons e rest ih =>
      obtain ⟨a, u⟩ := e
      have hnd' : (∀ (x : Ty), (a, x) ∉ rest) ∧
          (List.map (fun x => x.fst) rest).Nodup := by simpa using hnd
      rcases List.mem_cons.mp hm with heq | hmem
      · injection heq with h1 h2
        subst h1; subst h2
        simp [lookupBy]
      · have hak : (a == k) = false := by
          cases hab : a == k with
          | false => rfl
          | true =>
              have ha : a = k := eq_of_beq hab
              subst ha
              exact absurd hmem (hnd'.1 t)
        have hfind : ((a, u) :: rest).find? (fun e => e.1 == k) =
            rest.find? (fun e => e.1 == k) := by
          rw [List.find?_cons_of_neg]
          simpa using hak
        have := ih hnd'.2 hmem
        unfold lookupBy at this ⊢
        rw [hfind]
        exact this

/-- `lookupBy` is `List.lookup`. The typing rules use one and the relation's
arms use the other, both find-first by key, and the proofs cross between them. -/
theorem lookupBy_eq_lookup {α} [BEq α] [LawfulBEq α]
    (l : List (α × Ty)) (k : α) : lookupBy l k = l.lookup k := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      obtain ⟨x, y⟩ := a
      by_cases hx : x = k
      · subst hx; simp [lookupBy, List.lookup, List.find?]
      · have h1 : (x == k) = false := by simpa using hx
        have h2 : (k == x) = false := by simpa using (Ne.symm hx)
        simp [lookupBy, List.lookup, List.find?, h1, h2] at ih ⊢
        exact ih

/-- The kind edge (`constrain.rs :: constrain_kind`): the two kinds relate by
**equality**, so either mismatch is a rejection — a capability supplied where a collection is
demanded, and a collection supplied where a capability is. The kinds denote different things (a
collection carries data, a capability carries
none), so neither direction is a safe weakening. -/
def kindOk : FunKind → FunKind → Prop
  | .compute, .compute => True
  | .data, .data => True
  | _, _ => False

/-- Equality of kinds is transitive, so a chain fixes one kind throughout. -/
theorem kindOk_trans {k0 km k1 : FunKind}
    (h1 : kindOk k0 km) (h2 : kindOk km k1) : kindOk k0 k1 := by
  cases k0 <;> cases km <;> cases k1 <;> simp_all [kindOk]

/-- The refinements `rrefs` demands that no layer of `lrefs` supplies —
matched by structural predicate equality (never implication), exactly the deficit of
`constrain_go`'s refinement arm. Refinements are closed, so no
transport precedes the comparison. -/
def deficit (lrefs rrefs : List Predicate) : List Predicate :=
  rrefs.filter (fun r => !(lrefs.contains r))

/-- Identical refinement sets have no deficit. -/
theorem deficit_self (S : List Predicate) : deficit S S = [] := by
  unfold deficit
  apply List.filter_eq_nil_iff.mpr
  intro r hm
  simpa using hm

/-- An empty deficit **is** refinement containment: the demanded set is a
subset of the supplied one. Both directions, since the relation's arms produce
the deficit and its consumers want the containment. -/
theorem deficit_eq_nil_iff {l r : List Predicate} :
    deficit l r = [] ↔ ∀ p ∈ r, p ∈ l := by
  unfold deficit
  rw [List.filter_eq_nil_iff]
  constructor
  · intro h p hp
    have := h p hp
    simp only [Bool.not_eq_true', Bool.not_eq_false] at this
    exact List.mem_of_elem_eq_true this
  · intro h p hp
    simp only [Bool.not_eq_true', Bool.not_eq_false]
    exact List.elem_eq_true_of_mem (h p hp)

/-- The declarative concrete subtype relation. One constructor per
`constrain_go` arm (concrete fragment); rule order in the Rust `match` is irrelevant here because
the conclusions are syntactically disjoint — every constructor pins both sides' head constructors,
and `refined`
requires a refinement layer on at least one side. -/
inductive Subtyping : Ty → Ty → Prop where
  /-- Leaves match by equality — `(Base(a), Base(b)) if a == b`. -/
  | base (b : BaseTy) : Subtyping (.base b) (.base b)
  /-- `UIntRange` is **equality-only**: it is a data domain (a loop bound),
  and range inclusion is deliberately not subsumption. -/
  | uintRange (n : Nat) : Subtyping (.uintRange n) (.uintRange n)
  | dataSource (s : String) : Subtyping (.dataSource s) (.dataSource s)
  | txn : Subtyping .txn .txn
  /-- Function edge, non-`data`-`data` kinds: the two kinds are equal (so both
  are `compute`), the domain is contravariant, and the codomains compare directly — a refinement's
  binding is its index, so the edge needs no binder
  correspondence. -/
  | fnCompute {n0 n1 k0 k1 d0 c0 d1 c1} :
      kindOk k0 k1 →
      ¬(k0 = .data ∧ k1 = .data) →
      Subtyping d1 d0 →
      Subtyping c0 c1 →
      Subtyping (.fn n0 k0 d0 c0) (.fn n1 k1 d1 c1)
  /-- Function edge, `data`-`data`: the domain *is* the data, so it is
  **invariant** — both directions, spelled the only order-independent way
  (`constrain_go`: "Data domains are invariant"). -/
  | fnData {n0 n1 d0 c0 d1 c1} :
      Subtyping d1 d0 →
      Subtyping d0 d1 →
      Subtyping c0 c1 →
      Subtyping (.fn n0 .data d0 c0) (.fn n1 .data d1 c1)
  /-- Positional width: every position the rhs demands exists in the lhs
  and is covariantly below it. -/
  | tuple {a b} :
      b.length ≤ a.length →
      (∀ (i : Nat) t0 t1, a[i]? = some t0 → b[i]? = some t1 → Subtyping t0 t1) →
      Subtyping (.tuple a) (.tuple b)
  /-- Named width: every field the rhs demands is present (find-first) in
  the lhs and covariantly below it. -/
  | record {a b} :
      (∀ n t1, (n, t1) ∈ b → (lookupBy a n).isSome) →
      (∀ n t0 t1, (n, t1) ∈ b → lookupBy a n = some t0 → Subtyping t0 t1) →
      Subtyping (.record a) (.record b)
  /-- Variant width is the dual: every tag the lhs may produce is accepted
  (find-first) by the rhs, payloads covariant. -/
  | variant {a b} :
      (∀ k t0, (k, t0) ∈ a → (lookupBy b k).isSome) →
      (∀ k t0 t1, (k, t0) ∈ a → lookupBy b k = some t1 → Subtyping t0 t1) →
      Subtyping (.variant a) (.variant b)
  /-- Refinement arm: peel both sides fully; the lhs must supply every
  refinement the rhs demands — set containment by structural equality, never implication — and the
  bases compare directly. Covers refinement dropping (`{T | p} <: T`), forbids refinement conjuring
  (`T ⊀ {T | p}`), and makes the base **covariant** (`{T | p} <: {U | p}` iff `T <: U`).

  The guard (a refinement layer on at least one side) keeps the rule disjoint from the
  head-constructor rules, exactly as the Rust arm's position after them does. The concrete fragment
  has no variable-base
  deficit-flow sub-case (that is an `Infer` arm). -/
  | refined {lhs rhs lb lrefs rb rrefs} :
      lhs.peel = (lb, lrefs) →
      rhs.peel = (rb, rrefs) →
      (lrefs ≠ [] ∨ rrefs ≠ []) →
      deficit lrefs rrefs = [] →
      Subtyping lb rb →
      Subtyping lhs rhs

/-! ## Peeling both sides of an edge -/

/-- Universal peel inversion: **every** rule leaves the peeled bases related
and the peeled refinement sets contained. For the head-constructor rules both peels are `(t, [])`,
so this is the derivation itself; for the
refinement rule it is exactly its premises. -/
theorem subtyping_peel_inv {x y : Ty} (h : Subtyping x y) :
    deficit x.peel.2 y.peel.2 = [] ∧ Subtyping x.peel.1 y.peel.1 := by
  cases h with
  | base b => exact ⟨rfl, .base b⟩
  | uintRange n => exact ⟨rfl, .uintRange n⟩
  | dataSource s => exact ⟨rfl, .dataSource s⟩
  | txn => exact ⟨rfl, .txn⟩
  | fnCompute h1 h2 h3 h4 => exact ⟨rfl, .fnCompute h1 h2 h3 h4⟩
  | fnData h1 h2 h3 => exact ⟨rfl, .fnData h1 h2 h3⟩
  | tuple h1 h2 => exact ⟨rfl, .tuple h1 h2⟩
  | record h1 h2 => exact ⟨rfl, .record h1 h2⟩
  | variant h1 h2 => exact ⟨rfl, .variant h1 h2⟩
  | refined hpl hpr _ hdef hbase =>
      rw [hpl, hpr]
      exact ⟨hdef, hbase⟩

end CclFormal
