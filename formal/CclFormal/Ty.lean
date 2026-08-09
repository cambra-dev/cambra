/-!
# The ground `Type` grammar

The Lean mirror of the **ground fragment** of `src/ccl/ty.rs :: Type` — every
variant a fully-inferred type can contain. Excluded, deliberately:

- `Infer` and `SharedHole` — inference unknowns; the ground relation has no
  variable arms (they enter at the solver-model milestone).
- `History` and `ChanDom` — transients erased before the strict wall; they are
  pipeline artifacts, not types a checked program exhibits.
- `App` and `Below` — type-function applications reduce during inference and
  `Below` lives only in annotation position; both are transient in the same
  sense as `Infer`.
- `FunKind::Var` — kind unknowns resolve at coalesce; ground kinds are the
  two-point lattice.
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

/-- Mirror of the ground part of `ccl::ty::FunKind` (`Var` excluded): the
two-point kind lattice with `data ⊑ compute`. -/
inductive FunKind where
  | compute | data
deriving Repr, DecidableEq

/-- A refinement predicate term.

Mirrors the fragment of `TypedExpr` that refinement predicates use, and only
up to what subtyping observes: `Refinement`'s `PartialEq` is **type-blind
structural equality** of the predicate term (`src/ccl/ty.rs`), so the model
carries no type slots and `op` names are opaque strings. `elem` is the single
reserved refinement binder (`REFINEMENT_BINDER`, `__elem`); `var` references
an enclosing `Fun` Pi binder by name. The Rust→JSON emitter (M1) must map
`TypedExpr` predicates into exactly this fragment and refuse anything outside
it, so a vocabulary gap fails loudly instead of comparing wrongly. -/
inductive Pred where
  | elem
  | var (x : String)
  | litInt (n : Int)
  | litBool (b : Bool)
  | litStr (s : String)
  | litUnit
  | unop (op : String) (a : Pred)
  | binop (op : String) (a b : Pred)
  | proj (a : Pred) (k : FieldKey)
  | app (f a : Pred)
deriving Repr, DecidableEq

/-- Mirror of the ground fragment of `ccl::ty::Type`.

`refined` carries a **claim set**, exactly like
`Type::Refinement(base, RefinementSet)`: a base narrowed by the conjunction of
its claims, with `Ty.WF` requiring the same two invariants `Type::refined`
establishes — the claims are non-empty, and the base is not itself refined, so
layers never nest.

The claims are *represented* as a `List Pred` and `Ty.beq` compares them
positionally, which keeps `beq` propositional equality (`Ty.beq_iff`) and so
keeps `DecidableEq`. The **relation** is what treats them as a set: `deficit`
is containment, never list equality, so `Sub` cannot observe claim order —
stated and proved as `sub_claims_perm` rather than left as a reading of the
rules.

Equality is hand-written (`Ty.beq` — the `BEq`/`DecidableEq` deriving
handlers do not support this nested inductive) and bridged to propositional
equality by `Ty.beq_iff`, yielding lawful `BEq` and `DecidableEq`
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
  | refined (base : Ty) (claims : List Pred)
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

/-- Propositional equality of ground types is decidable. -/
instance : DecidableEq Ty := fun a b => decidable_of_iff _ (Ty.beq_iff a b)

/-- Whether `t` is a refinement node. The flattening invariant forbids one
directly under another, so this is what `Ty.WF` checks of a base. -/
def Ty.isRefined : Ty → Bool
  | .refined _ _ => true
  | _ => false

/-- Mirror of `Type::refined`: `base` narrowed by `claims`, establishing both
invariants. No claims is no refinement, and a base that is already refined has
`claims` merged into its set rather than stacked on top. -/
def Ty.mkRefined (base : Ty) (claims : List Pred) : Ty :=
  match claims with
  | [] => base
  | _ =>
    match base with
    | .refined b ps => .refined b (ps ++ claims.filter (· ∉ ps))
    | bare => .refined bare claims

/-- Well-formedness the Rust builders maintain but the `Type` representation
does not enforce: record fields and variant tags are keyed **uniquely**.

The solver's find-first lookup makes this load-bearing: on a duplicate-keyed
record, `constrain`'s trivial-equality short-circuit would accept `t <: t`
while the record arm's find-first lookup would demand cross-subtyping between
the duplicates — reflexivity-as-a-theorem (`Sub.refl`) is provable exactly
under this invariant, which is the model naming an invariant the Rust leaves
implicit. -/
inductive Ty.WF : Ty → Prop where
  | base (b) : Ty.WF (.base b)
  | uintRange (n) : Ty.WF (.uintRange n)
  | dataSource (s) : Ty.WF (.dataSource s)
  | txn : Ty.WF .txn
  | fn {n k d c} : Ty.WF d → Ty.WF c → Ty.WF (.fn n k d c)
  | tuple {ts} : (∀ t ∈ ts, Ty.WF t) → Ty.WF (.tuple ts)
  | record {fs} : (fs.map (·.1)).Nodup → (∀ f ∈ fs, Ty.WF f.2) →
      Ty.WF (.record fs)
  | variant {tags} : (tags.map (·.1)).Nodup → (∀ t ∈ tags, Ty.WF t.2) →
      Ty.WF (.variant tags)
  | refined {b ps} : ps ≠ [] → b.isRefined = false → Ty.WF b →
      Ty.WF (.refined b ps)

end CclFormal
