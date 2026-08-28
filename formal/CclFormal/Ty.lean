/-!
# The concrete `Type` grammar

The Lean mirror of the **concrete fragment** of `src/ccl/ty.rs :: Type` — every variant a
fully-inferred type can contain. Excluded, deliberately:

- `Infer` and `SharedHole` — inference unknowns; the concrete relation has no
  variable arms (they enter at the solver-model milestone).
- `History` and `ChanDom` — transients erased before the strict wall; they are
  pipeline artifacts, not types a checked program exhibits.
- `App` and `Below` — type-function applications reduce during inference and
  `Below` lives only in annotation position; both are transient in the same sense as `Infer`.
- `FunKind::Var` — kind unknowns resolve at coalesce; a concrete kind is one of
  the two points, related only to itself.
-/

namespace CclFormal

/-- Mirror of `ccl::ops::BaseType`. -/
inductive BaseTy where
  | int | uint | string | bool | unit
deriving Repr, DecidableEq

/-- Mirror of `ccl::ty::FieldKey`: a record/tuple field or variant tag. -/
inductive FieldKey where
  | idx (n : Nat)
  | name (s : String)
deriving Repr, DecidableEq

/-- Mirror of the concrete part of `ccl::ty::FunKind` (`Var` excluded): two
points, related by equality — a collection and a capability denote different
things, so neither stands in for the other. -/
inductive FunKind where
  | compute | data
deriving Repr, DecidableEq

/-- A refinement predicate term.

Mirrors the fragment of `TypedExpr` that refinement predicates use, and only up to what subtyping
observes: `Refinement`'s `PartialEq` is **type-blind structural equality** of the predicate term
(`src/ccl/ty.rs`), so the model carries no type slots and `op` names are opaque strings. `elem` is
the single reserved refinement binder (`REFINEMENT_BINDER`, `__elem`); `piBound` references an
enclosing `Fun` Pi binder as a de Bruijn index — the number of `fn` codomains crossed between the
reference and the function that binds it, mirroring `Name::PiBound`
(`src/ccl/design/type-inference.md`, "A binder reference is stored in one of two forms"). A concrete
type is closed: construction converts a binder reference to its index (`close_pi_binder`), so two
α-variant function types are structurally identical and the relation needs no rename environments.
`var` remains for the *free* references a refinement may keep — a `let`-bound name a user-written
refinement mentions, or a source — which are globally unique and compare structurally. The Rust→JSON
emitter must map `TypedExpr` predicates into exactly this fragment and refuse anything outside
it, so a vocabulary gap fails loudly instead of comparing wrongly. -/
inductive Predicate where
  | elem
  | var (x : String)
  | piBound (k : Nat)
  | litInt (n : Int)
  | litBool (b : Bool)
  | litStr (s : String)
  | litUnit
  | unop (op : String) (a : Predicate)
  | binop (op : String) (a b : Predicate)
  | proj (a : Predicate) (k : FieldKey)
  | app (f a : Predicate)
  /-- A binder the predicate itself introduces — a filter's lambda. Carries no
  parameter type: `eq_refinement_predicate`'s `Lambda` arm pairs the binders and
  compares the bodies, and reads no type slot. -/
  | lam (body : Predicate)
  /-- A reference to one of this predicate's own `lam` binders, as the number of
  `lam`s crossed to reach it. The Rust compares such a reference **by position**
  (`eq_refinement_predicate` pairs the two sides' binders), so spelling it as an index is what makes
  structural equality here mean α-invariance there. A reference to a binder *outside* the predicate
  stays a `var`, compared by
  identity, which is the other half of that rule. -/
  | boundVar (k : Nat)
  /-- A cast embedded in a predicate, carrying its value and the refinement
  predicates of its target's domain — and nothing else. `eq_refinement_predicate` compares a cast's
  target because that target is a semantic filter: two predicates whose embedded comprehensions
  filter `> 0` and `< 0` denote different refinements, and conflating them would let a deficit
  accept an unsatisfied demand. It reads only what `cast_target_refinement` returns, the domain's
  refinement set, so the target's *base* types are absent
  here for the same reason every other type slot is. -/
  | cast (value : Predicate) (targetRefs : List Predicate)
deriving Repr

mutual

/-- Structural equality, hand-written for the same reason [`Ty.beq`] is: `cast`
carries a `List Predicate`, so `Predicate` is a *nested* inductive and no `DecidableEq` handler
applies. `beq_iff` below proves it equivalent to propositional equality, which is what makes the
derived `DecidableEq` lawful and every proof that compares
predicates sound. -/
def Predicate.beq : Predicate → Predicate → Bool
  | .elem, .elem => true
  | .var a, .var b => a == b
  | .piBound a, .piBound b => a == b
  | .litInt a, .litInt b => a == b
  | .litBool a, .litBool b => a == b
  | .litStr a, .litStr b => a == b
  | .litUnit, .litUnit => true
  | .unop o0 a0, .unop o1 a1 => o0 == o1 && Predicate.beq a0 a1
  | .binop o0 a0 b0, .binop o1 a1 b1 => o0 == o1 && Predicate.beq a0 a1 && Predicate.beq b0 b1
  | .proj a0 k0, .proj a1 k1 => Predicate.beq a0 a1 && k0 == k1
  | .app f0 a0, .app f1 a1 => Predicate.beq f0 f1 && Predicate.beq a0 a1
  | .lam b0, .lam b1 => Predicate.beq b0 b1
  | .boundVar a, .boundVar b => a == b
  | .cast v0 r0, .cast v1 r1 => Predicate.beq v0 v1 && Predicate.beqSeq r0 r1
  | _, _ => false
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp_wf; omega)

def Predicate.beqSeq : List Predicate → List Predicate → Bool
  | [], [] => true
  | p0 :: a, p1 :: b => Predicate.beq p0 p1 && Predicate.beqSeq a b
  | _, _ => false
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp_wf; omega)

end

instance : BEq Predicate := ⟨Predicate.beq⟩

mutual

theorem Predicate.beq_iff : (a b : Predicate) → (Predicate.beq a b = true ↔ a = b)
  | .elem, b => by cases b <;> simp [Predicate.beq]
  | .var _, b => by cases b <;> simp [Predicate.beq]
  | .piBound _, b => by cases b <;> simp [Predicate.beq]
  | .litInt _, b => by cases b <;> simp [Predicate.beq]
  | .litBool _, b => by cases b <;> simp [Predicate.beq]
  | .litStr _, b => by cases b <;> simp [Predicate.beq]
  | .litUnit, b => by cases b <;> simp [Predicate.beq]
  | .unop _ a0, b => by
      cases b <;> simp [Predicate.beq]
      case unop _ a1 => simp [Predicate.beq_iff a0 a1]
  | .binop _ a0 b0, b => by
      cases b <;> simp [Predicate.beq]
      case binop _ a1 b1 => simp [Predicate.beq_iff a0 a1, Predicate.beq_iff b0 b1, and_assoc]
  | .proj a0 _, b => by
      cases b <;> simp [Predicate.beq]
      case proj a1 _ => simp [Predicate.beq_iff a0 a1]
  | .app f0 a0, b => by
      cases b <;> simp [Predicate.beq]
      case app f1 a1 => simp [Predicate.beq_iff f0 f1, Predicate.beq_iff a0 a1]
  | .lam b0, b => by
      cases b <;> simp [Predicate.beq]
      case lam b1 => simp [Predicate.beq_iff b0 b1]
  | .boundVar _, b => by cases b <;> simp [Predicate.beq]
  | .cast v0 r0, b => by
      cases b <;> simp [Predicate.beq]
      case cast v1 r1 => simp [Predicate.beq_iff v0 v1, Predicate.beqSeq_iff r0 r1]
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp_wf; omega)

theorem Predicate.beqSeq_iff : (a b : List Predicate) → (Predicate.beqSeq a b = true ↔ a = b)
  | [], [] => by simp [Predicate.beqSeq]
  | [], _ :: _ => by simp [Predicate.beqSeq]
  | _ :: _, [] => by simp [Predicate.beqSeq]
  | p0 :: a, p1 :: b => by
      simp [Predicate.beqSeq, Predicate.beq_iff p0 p1, Predicate.beqSeq_iff a b]
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp_wf; omega)

end

instance : LawfulBEq Predicate where
  eq_of_beq h := (Predicate.beq_iff _ _).mp h
  rfl := (Predicate.beq_iff _ _).mpr rfl

instance : DecidableEq Predicate := fun a b =>
  decidable_of_iff (Predicate.beq a b = true) (Predicate.beq_iff a b)

/-- Mirror of the concrete fragment of `ccl::ty::Type`.

`refined` carries a **refinement set**, exactly like `Type::Refinement(base, RefinementSet)`: a base
narrowed by the conjunction of its refinements, with `Ty.WellFormed` requiring the same two
invariants `Type::refined` establishes — the refinements are non-empty, and the base is not itself
refined, so layers never nest.

The refinements are *represented* as a `List Predicate` and `Ty.beq` compares them positionally,
which keeps `beq` propositional equality (`Ty.beq_iff`) and so keeps `DecidableEq`. The **relation**
is what treats them as a set: `deficit` is containment, never list equality, so `Subtyping` cannot
observe refinement order — stated and proved as `subtyping_refinements_perm` rather than left as a
reading of the rules.

Equality is hand-written (`Ty.beq` — the `BEq`/`DecidableEq` deriving handlers do not support this
nested inductive) and proved equivalent to propositional equality by `Ty.beq_iff`, yielding lawful
`BEq` and `DecidableEq`
instances. -/
inductive Ty where
  | base (b : BaseTy)
  | uintRange (n : Nat)
  | dataSource (name : String)
  | txn
  | fn (binder : Option String) (kind : FunKind) (dom cod : Ty)
  | tuple (ts : List Ty)
  | record (fields : List (String × Ty))
  | variant (tags : List (FieldKey × Ty))
  | refined (base : Ty) (refinements : List Predicate)
deriving Repr

mutual

/-- Structural equality. -/
def Ty.beq : Ty → Ty → Bool
  | .base a, .base b => a == b
  | .uintRange a, .uintRange b => a == b
  | .dataSource a, .dataSource b => a == b
  | .txn, .txn => true
  | .fn n0 k0 d0 c0, .fn n1 k1 d1 c1 =>
      n0 == n1 && k0 == k1 && Ty.beq d0 d1 && Ty.beq c0 c1
  | .tuple a, .tuple b => Ty.beqSeq a b
  | .record a, .record b => Ty.beqFields a b
  | .variant a, .variant b => Ty.beqTags a b
  | .refined b0 p0, .refined b1 p1 => Ty.beq b0 b1 && p0 == p1
  | _, _ => false
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp_wf; omega)

def Ty.beqSeq : List Ty → List Ty → Bool
  | [], [] => true
  | t0 :: a, t1 :: b => Ty.beq t0 t1 && Ty.beqSeq a b
  | _, _ => false
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp_wf; omega)

def Ty.beqFields : List (String × Ty) → List (String × Ty) → Bool
  | [], [] => true
  | (n0, t0) :: a, (n1, t1) :: b => n0 == n1 && Ty.beq t0 t1 && Ty.beqFields a b
  | _, _ => false
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp_wf; omega)

def Ty.beqTags : List (FieldKey × Ty) → List (FieldKey × Ty) → Bool
  | [], [] => true
  | (k0, t0) :: a, (k1, t1) :: b => k0 == k1 && Ty.beq t0 t1 && Ty.beqTags a b
  | _, _ => false
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp_wf; omega)

end

instance : BEq Ty := ⟨Ty.beq⟩

mutual

theorem Ty.beq_iff : (a b : Ty) → (Ty.beq a b = true ↔ a = b)
  | .base _, b => by cases b <;> simp [Ty.beq]
  | .uintRange _, b => by cases b <;> simp [Ty.beq]
  | .dataSource _, b => by cases b <;> simp [Ty.beq]
  | .txn, b => by cases b <;> simp [Ty.beq]
  | .fn n0 k0 d0 c0, b => by
      cases b <;> simp [Ty.beq]
      case fn n1 k1 d1 c1 =>
        simp [Ty.beq_iff d0 d1, Ty.beq_iff c0 c1, and_assoc]
  | .tuple ts, b => by
      cases b <;> simp [Ty.beq]
      case tuple bs => exact Ty.beqSeq_iff ts bs
  | .record fs, b => by
      cases b <;> simp [Ty.beq]
      case record bs => exact Ty.beqFields_iff fs bs
  | .variant tags, b => by
      cases b <;> simp [Ty.beq]
      case variant bs => exact Ty.beqTags_iff tags bs
  | .refined b0 p0, b => by
      cases b <;> simp [Ty.beq]
      case refined b1 p1 => simp [Ty.beq_iff b0 b1]
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp_wf; omega)

theorem Ty.beqSeq_iff : (a b : List Ty) → (Ty.beqSeq a b = true ↔ a = b)
  | [], [] => by simp [Ty.beqSeq]
  | [], _ :: _ => by simp [Ty.beqSeq]
  | _ :: _, [] => by simp [Ty.beqSeq]
  | t0 :: a, t1 :: b => by
      simp [Ty.beqSeq, Ty.beq_iff t0 t1, Ty.beqSeq_iff a b]
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp_wf; omega)

theorem Ty.beqFields_iff :
    (a b : List (String × Ty)) → (Ty.beqFields a b = true ↔ a = b)
  | [], [] => by simp [Ty.beqFields]
  | [], _ :: _ => by simp [Ty.beqFields]
  | _ :: _, [] => by simp [Ty.beqFields]
  | (n0, t0) :: a, (n1, t1) :: b => by
      simp [Ty.beqFields, Ty.beq_iff t0 t1, Ty.beqFields_iff a b]
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp_wf; omega)

theorem Ty.beqTags_iff :
    (a b : List (FieldKey × Ty)) → (Ty.beqTags a b = true ↔ a = b)
  | [], [] => by simp [Ty.beqTags]
  | [], _ :: _ => by simp [Ty.beqTags]
  | _ :: _, [] => by simp [Ty.beqTags]
  | (k0, t0) :: a, (k1, t1) :: b => by
      simp [Ty.beqTags, Ty.beq_iff t0 t1, Ty.beqTags_iff a b]
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp_wf; omega)

end

instance : LawfulBEq Ty where
  eq_of_beq h := (Ty.beq_iff _ _).mp h
  rfl := (Ty.beq_iff _ _).mpr rfl

/-- Propositional equality of concrete types is decidable. -/
instance : DecidableEq Ty := fun a b => decidable_of_iff _ (Ty.beq_iff a b)

/-- Whether `t` is a refinement node. The flattening invariant forbids one
directly under another, so this is what `Ty.WellFormed` checks of a base. -/
def Ty.isRefined : Ty → Bool
  | .refined _ _ => true
  | _ => false

/-- Mirror of `Type::refined`: `base` narrowed by `refinements`, establishing both
invariants. No refinements is no refinement, and a base that is already refined has
`refinements` merged into its set rather than stacked on top. -/
def Ty.mkRefined (base : Ty) (refinements : List Predicate) : Ty :=
  match refinements with
  | [] => base
  | _ =>
    match base with
    | .refined b ps => .refined b (ps ++ refinements.filter (· ∉ ps))
    | bare => .refined bare refinements

/-- Well-formedness the Rust builders maintain but the `Type` representation
does not enforce: record fields and variant tags are keyed **uniquely**.

The solver's find-first lookup makes this load-bearing: on a duplicate-keyed record, `constrain`'s
trivial-equality short-circuit would accept `t <: t` while the record arm's find-first lookup would
demand cross-subtyping between the duplicates — reflexivity-as-a-theorem (`Subtyping.refl`) is
provable exactly under this invariant, which is the model naming an invariant the Rust leaves
implicit. -/
inductive Ty.WellFormed : Ty → Prop where
  | base (b) : Ty.WellFormed (.base b)
  | uintRange (n) : Ty.WellFormed (.uintRange n)
  | dataSource (s) : Ty.WellFormed (.dataSource s)
  | txn : Ty.WellFormed .txn
  | fn {n k d c} : Ty.WellFormed d → Ty.WellFormed c → Ty.WellFormed (.fn n k d c)
  | tuple {ts} : (∀ t ∈ ts, Ty.WellFormed t) → Ty.WellFormed (.tuple ts)
  | record {fs} : (fs.map (·.1)).Nodup → (∀ f ∈ fs, Ty.WellFormed f.2) →
      Ty.WellFormed (.record fs)
  | variant {tags} : (tags.map (·.1)).Nodup → (∀ t ∈ tags, Ty.WellFormed t.2) →
      Ty.WellFormed (.variant tags)
  | refined {b ps} : ps ≠ [] → b.isRefined = false → Ty.WellFormed b →
      Ty.WellFormed (.refined b ps)

/-! ### Member extractors

Every recursion over a well-formed type needs its children's well-formedness, so the projections
live with the invariant rather than with
whichever theorem reached for one first. -/

theorem Ty.WellFormed.fn_domain {n k d c} (h : Ty.WellFormed (.fn n k d c)) : d.WellFormed := by
  cases h with | fn hd _ => exact hd

theorem Ty.WellFormed.fn_codomain {n k d c} (h : Ty.WellFormed (.fn n k d c)) : c.WellFormed := by
  cases h with | fn _ hc => exact hc

theorem Ty.WellFormed.tuple_mem {ts t} (h : Ty.WellFormed (.tuple ts)) (hm : t ∈ ts) : t.WellFormed
    := by
  cases h with | tuple hts => exact hts t hm

theorem Ty.WellFormed.record_mem {fs : List (String × Ty)} {n t}
    (h : Ty.WellFormed (.record fs)) (hm : (n, t) ∈ fs) : t.WellFormed := by
  cases h with | record _ hf => exact hf (n, t) hm

theorem Ty.WellFormed.variant_mem {tags : List (FieldKey × Ty)} {k t}
    (h : Ty.WellFormed (.variant tags)) (hm : (k, t) ∈ tags) : t.WellFormed := by
  cases h with | variant _ ht => exact ht (k, t) hm

end CclFormal
