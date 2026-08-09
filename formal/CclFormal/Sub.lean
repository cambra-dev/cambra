import CclFormal.Ty

/-!
# The declarative ground subtype relation

`Sub ρl ρr lhs rhs` is the Lean statement of the relation
`src/ccl/infer/solver/constrain.rs :: constrain_go` *implements* on ground
types (no `Infer` on either side) — stated declaratively for the first time;
the Rust operationalizes subsumption inside `constrain` and never writes the
relation down.

The two `Ren` arguments are the ground shadow of the solver's side morphisms
`sl`/`sr`: on ground types the only morphisms in flight are the Pi-binder
renames the `Fun`-vs-`Fun` codomain edge mints (`sl.extended_rename(k, x)`),
so each side carries a rename environment, they swap at every contravariant
edge, and refinement predicates are transported through them before
comparison (the ground residue of `Subst::force_refinement`).

## Deliberate departures from `constrain_go` (each is a tracked decision)

- **No trivial-equality short-circuit.** `constrain_go` starts with
  `lhs == rhs → Ok` (under identity morphisms). Here reflexivity is a
  *theorem* (`Sub.refl`), not a rule — provable only for well-formed
  (uniquely-keyed) types, which surfaces that the short-circuit and the
  find-first record/variant arms disagree on duplicate-keyed products. See
  `Ty.WF`.

Partition collapse (`⧺ᵢ({𝐷|π̂ᵢ}) ≡ 𝐷` as a domain) is modeled exactly as
the Rust now implements it: a **normalization** applied before comparison
(`Sub.fnNorm` mirroring `constrain_go`'s normalize-then-recurse arm). Its
predecessor — the target-relative `is_index_partition_of` bridge arm — was
found by this model to break transitivity of subsumption and to drop the
Pi-binder correspondence on its codomain edge; both defects are repaired
by the rewrite (see `formal/design.md` and
`src/ccl/infer/solver/differential.rs` for the pinned history).
-/

namespace CclFormal

/-- The ground shadow of the solver's `Subst`: a Pi-binder rename
environment. `extend` prepends, so a re-bound name shadows — matching one
`extended_rename` on top of an existing morphism. (The exact shadowing
semantics of `Subst::extended_rename` is an M1 differential-fuzz target;
see `formal/design.md`.) -/
abbrev Ren := List (String × String)

namespace Ren

/-- The identity morphism (`Subst::id()`). -/
def id : Ren := []

/-- Apply to one name: first matching entry wins, absent names are fixed. -/
def apply (ρ : Ren) (x : String) : String :=
  match ρ.find? (fun e => e.1 == x) with
  | some e => e.2
  | none => x

/-- `Subst::extended_rename(k, x)`: the codomain edge's binder
correspondence `k ↦ x`. -/
def extend (ρ : Ren) (k x : String) : Ren := (k, x) :: ρ

/-- Acting as the identity — the property `Sub.refl` needs of the ambient
morphisms (satisfied by `Ren.id`, preserved by diagonal extension). -/
def IsId (ρ : Ren) : Prop := ∀ x, ρ.apply x = x

end Ren

/-- Transport a predicate through a rename: Pi-binder references move, the
reserved `elem` binder never does (`REFINEMENT_BINDER` is disjoint from
user identifiers by construction). Ground residue of
`Subst::force_refinement`. -/
def Pred.rename (ρ : Ren) : Pred → Pred
  | .elem => .elem
  | .var x => .var (ρ.apply x)
  | .litInt n => .litInt n
  | .litBool b => .litBool b
  | .litStr s => .litStr s
  | .litUnit => .litUnit
  | .unop op a => .unop op (a.rename ρ)
  | .binop op a b => .binop op (a.rename ρ) (b.rename ρ)
  | .proj a k => .proj (a.rename ρ) k
  | .app f a => .app (f.rename ρ) (a.rename ρ)

/-- Peel all outer refinement layers: mirror of
`constrain.rs :: peel_refinements` (outermost predicate first). -/
def Ty.peel : Ty → Ty × List Pred
  | .refined b p => (b.peel.1, p :: b.peel.2)
  | t => (t, [])

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

/-- A leg's contribution to the partition's common domain: what sits under
its gate, or the leg itself when the gate lives in the term (a
`filter_values` restrict) and the leg type is bare. At most one layer is
peeled — mirror of the leg handling in `constrain.rs :: partition_domain`. -/
def legUnder : Ty → Ty
  | .refined u _ => u
  | t => t

/-- Contiguous `Index` keys from `i`, every leg's `legUnder` equal to
`common`. -/
def partitionTagsGo (common : Ty) : Nat → List (FieldKey × Ty) → Bool
  | _, [] => true
  | i, (k, p) :: rest =>
      k == .idx i && legUnder p == common && partitionTagsGo common (i + 1) rest

/-- The domain a gated **partition** normalizes to — mirror of
`constrain.rs :: partition_domain`: a `Variant` with contiguous
`Index(0..n)` tags (n ≥ 1) whose legs share one domain under (at most) one
gate layer each. `none` for anything shaped differently. -/
def partitionDomain : Ty → Option Ty
  | .variant ((k0, p0) :: rest) =>
      if k0 == .idx 0 && partitionTagsGo (legUnder p0) 1 rest then
        some (legUnder p0)
      else none
  | _ => none

/-- The plain form of a partition-domained function — mirror of
`constrain.rs :: normalized_partition_fun`. Kind, binder, and codomain ride
along untouched. -/
def normFun : Ty → Option Ty
  | .fn n k d c => (partitionDomain d).map fun d' => .fn n k d' c
  | _ => none

theorem legUnder_sizeOf_le (t : Ty) : sizeOf (legUnder t) ≤ sizeOf t := by
  cases t <;> simp [legUnder] <;> omega

/-- Normalizing a domain strictly shrinks it (the common domain sits inside
the variant's first leg). -/
theorem partitionDomain_sizeOf {d u : Ty} (h : partitionDomain d = some u) :
    sizeOf u < sizeOf d := by
  match d, h with
  | .variant ((k0, p0) :: rest), h =>
      simp only [partitionDomain] at h
      split at h
      · injection h with h
        subst h
        have := legUnder_sizeOf_le p0
        simp
        omega
      · exact absurd h (by simp)

/-- Normalizing a function strictly shrinks it. -/
theorem normFun_sizeOf {t t' : Ty} (h : normFun t = some t') :
    sizeOf t' < sizeOf t := by
  match t, h with
  | .fn n k d c, h =>
      simp only [normFun, Option.map_eq_some_iff] at h
      obtain ⟨d', hd, rfl⟩ := h
      have := partitionDomain_sizeOf hd
      simp
      omega

/-- The combined decrease for the checker's normalization branch: at least
one side strictly shrinks, the other never grows. -/
theorem normPair_sizeOf (l r : Ty)
    (h : (normFun l).isSome ∨ (normFun r).isSome) :
    sizeOf ((normFun l).getD l) + sizeOf ((normFun r).getD r) <
      sizeOf l + sizeOf r := by
  have hl : sizeOf ((normFun l).getD l) ≤ sizeOf l := by
    cases hn : normFun l with
    | none => simp
    | some t => simpa using Nat.le_of_lt (normFun_sizeOf hn)
  have hr : sizeOf ((normFun r).getD r) ≤ sizeOf r := by
    cases hn : normFun r with
    | none => simp
    | some t => simpa using Nat.le_of_lt (normFun_sizeOf hn)
  rcases h with h | h
  · cases hn : normFun l with
    | none => exact absurd h (by simp [hn])
    | some t =>
        have := normFun_sizeOf hn
        simp only [Option.getD_some]
        omega
  · cases hn : normFun r with
    | none => exact absurd h (by simp [hn])
    | some t =>
        have := normFun_sizeOf hn
        simp only [Option.getD_some]
        omega

/-- The kind edge over the ground two-point lattice `data ⊑ compute`
(`constrain.rs :: constrain_kind`): the sole rejection is a capability
supplied where a collection is demanded. -/
def kindOk : FunKind → FunKind → Prop
  | .compute, .data => False
  | _, _ => True

/-- The codomain edge's morphism: Pi-vs-Pi extends the **lhs** side with the
binder correspondence; any other binder shape leaves it unchanged
(`constrain_go`'s `cod_sl`). -/
def codRen (n0 n1 : Option String) (ρl : Ren) : Ren :=
  match n0, n1 with
  | some k, some x => ρl.extend k x
  | _, _ => ρl

/-- The refinements `rrefs` demands that no transported layer of `lrefs`
supplies — each side forced through its own morphism first, matched by
structural predicate equality (never implication), exactly the deficit of
`constrain_go`'s refinement arm. -/
def deficit (ρl ρr : Ren) (lrefs rrefs : List Pred) : List Pred :=
  let lifted := lrefs.map (Pred.rename ρl)
  rrefs.filter (fun r => !(lifted.contains (r.rename ρr)))

/-- The declarative ground subtype relation. One constructor per
`constrain_go` arm (ground fragment); rule order in the Rust `match` is
irrelevant here because the conclusions are syntactically disjoint —
every constructor pins both sides' head constructors, and `refined`
requires a refinement layer on at least one side. -/
inductive Sub : Ren → Ren → Ty → Ty → Prop where
  /-- Leaves match by equality — `(Base(a), Base(b)) if a == b`. -/
  | base {ρl ρr} (b : BaseTy) : Sub ρl ρr (.base b) (.base b)
  /-- `UIntRange` is **equality-only**: it is a data domain (a loop bound),
  and range inclusion is deliberately not subsumption. -/
  | uintRange {ρl ρr} (n : Nat) : Sub ρl ρr (.uintRange n) (.uintRange n)
  | dataSource {ρl ρr} (s : String) : Sub ρl ρr (.dataSource s) (.dataSource s)
  | txn {ρl ρr} : Sub ρl ρr .txn .txn
  /-- Partition normalization (`constrain_go`'s normalize-then-recurse arm):
  a gated partition of `𝐷` *is* the plain function over `𝐷`, so the
  partitioned side(s) rewrite to their plain forms and the pair re-enters
  the relation — the general rules then supply the kind edge, domain
  variance, and Pi correspondence. (The Rust arm also excludes `Infer`
  domains on either side; the ground fragment has none, so the exclusion is
  vacuous here.) -/
  | fnNorm {ρl ρr n0 k0 d0 c0 n1 k1 d1 c1} :
      ((normFun (.fn n0 k0 d0 c0)).isSome ∨ (normFun (.fn n1 k1 d1 c1)).isSome) →
      Sub ρl ρr ((normFun (.fn n0 k0 d0 c0)).getD (.fn n0 k0 d0 c0))
        ((normFun (.fn n1 k1 d1 c1)).getD (.fn n1 k1 d1 c1)) →
      Sub ρl ρr (.fn n0 k0 d0 c0) (.fn n1 k1 d1 c1)
  /-- Function edge, non-`data`-`data` kinds: the kind lattice admits the
  pair, the domain is contravariant (sides — and their morphisms — swap),
  and the codomain edge carries the Pi correspondence on the lhs morphism. -/
  | fnCompute {ρl ρr n0 n1 k0 k1 d0 c0 d1 c1} :
      normFun (.fn n0 k0 d0 c0) = none →
      normFun (.fn n1 k1 d1 c1) = none →
      kindOk k0 k1 →
      ¬(k0 = .data ∧ k1 = .data) →
      Sub ρr ρl d1 d0 →
      Sub (codRen n0 n1 ρl) ρr c0 c1 →
      Sub ρl ρr (.fn n0 k0 d0 c0) (.fn n1 k1 d1 c1)
  /-- Function edge, `data`-`data`: the domain *is* the data, so it is
  **invariant** — both directions, spelled the only order-independent way
  (`constrain_go`: "Data domains are invariant"). -/
  | fnData {ρl ρr n0 n1 d0 c0 d1 c1} :
      normFun (.fn n0 .data d0 c0) = none →
      normFun (.fn n1 .data d1 c1) = none →
      Sub ρr ρl d1 d0 →
      Sub ρl ρr d0 d1 →
      Sub (codRen n0 n1 ρl) ρr c0 c1 →
      Sub ρl ρr (.fn n0 .data d0 c0) (.fn n1 .data d1 c1)
  /-- Positional width: every position the rhs demands exists in the lhs
  and is covariantly below it. -/
  | tuple {ρl ρr a b} :
      b.length ≤ a.length →
      (∀ (i : Nat) t0 t1, a[i]? = some t0 → b[i]? = some t1 → Sub ρl ρr t0 t1) →
      Sub ρl ρr (.tuple a) (.tuple b)
  /-- Named width: every field the rhs demands is present (find-first) in
  the lhs and covariantly below it. -/
  | record {ρl ρr a b} :
      (∀ n t1, (n, t1) ∈ b → (lookupBy a n).isSome) →
      (∀ n t0 t1, (n, t1) ∈ b → lookupBy a n = some t0 → Sub ρl ρr t0 t1) →
      Sub ρl ρr (.record a) (.record b)
  /-- Variant width is the dual: every tag the lhs may produce is accepted
  (find-first) by the rhs, payloads covariant. -/
  | variant {ρl ρr a b} :
      (∀ k t0, (k, t0) ∈ a → (lookupBy b k).isSome) →
      (∀ k t0 t1, (k, t0) ∈ a → lookupBy b k = some t1 → Sub ρl ρr t0 t1) →
      Sub ρl ρr (.variant a) (.variant b)
  /-- Refinement arm: peel both sides fully; the lhs must supply (after
  transport through the side morphisms) every refinement the rhs demands —
  set containment by structural equality, never implication — and the bases
  compare under the same morphisms. Covers refinement dropping
  (`{T | p} <: T`), forbids refinement conjuring (`T ⊀ {T | p}`), and makes
  the base **covariant** (`{T | p} <: {U | p}` iff `T <: U`).

  The guard (a refinement layer on at least one side) keeps the rule
  disjoint from the head-constructor rules, exactly as the Rust arm's
  position after them does. The ground fragment has no variable-base
  deficit-flow sub-case (that is an `Infer` arm). -/
  | refined {ρl ρr lhs rhs lb lrefs rb rrefs} :
      lhs.peel = (lb, lrefs) →
      rhs.peel = (rb, rrefs) →
      (lrefs ≠ [] ∨ rrefs ≠ []) →
      deficit ρl ρr lrefs rrefs = [] →
      Sub ρl ρr lb rb →
      Sub ρl ρr lhs rhs

end CclFormal
