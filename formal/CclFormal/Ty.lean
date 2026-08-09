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

`refined` carries **one** refinement layer, exactly like
`Type::Refinement(base, r)` — a multiply-refined type is nested `refined`
layers, and the subtype relation peels them all at once.

`BEq` is derived (the `DecidableEq` deriving handler does not support this
nested inductive); the executable checker compares with it, the declarative
relation uses propositional equality, and `beq ↔ eq` is part of the
checker-equivalence milestone step. -/
inductive Ty where
  | base (b : BaseTy)
  | uintRange (n : Nat)
  | dataSource (name : String)
  | txn
  | fn (binder : Option String) (kind : FunKind) (dom cod : Ty)
  | tuple (ts : List Ty)
  | record (fields : List (String × Ty))
  | variant (tags : List (FieldKey × Ty))
  | refined (base : Ty) (p : Pred)
deriving Repr, BEq

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
  | refined {b p} : Ty.WF b → Ty.WF (.refined b p)

end CclFormal
