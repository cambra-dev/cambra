import CclFormal.Ty
import CclFormal.Subtyping

/-!
# Terms, typing, and the small-step semantics (definitional core)

The pure-core term language, its values, capture-free substitution, the call-by-value small-step
relation, and the declarative typing judgment `HasTy Γ e T`. Progress/preservation and the two
corollaries (refinement soundness, case-binder preservation) live in `WellTypedTermsAreSafe.lean`.

## Adjudications (deviations-on-contact)

- **Terms are de Bruijn; types keep their named Pi binders.** The subtype
  relation never moves a binder, so names-with-renames mirrored the Rust one-to-one there. Reduction
  *duplicates and re-scopes* binders, where named representations buy α-conversion obligations and
  nothing else — and the Rust's term binders are uniquified (`uniquify`), so they are α-irrelevant
  identifiers, not semantic content. The typing oracle maps uniquified names to indices
  mechanically.
- **The non-dependent fragment first**: every refinement predicate is over
  the reserved `__elem` only (`Predicate.elemOnly`) — no predicate references an enclosing term
  binder. Types are therefore **closed under term substitution**, exactly the fragment the
  transitivity proof covers (`NoPi`); the dependent extension rides with the Pi-binder thread.
- **`cast` checks its refinements at runtime, and progress is stated modulo
  filtering.** In CCL a cast is the refinement introduction (lowering's filter); at runtime the
  corresponding `Restrict` *drops* elements. A scalar small-step mirrors that as: `cast` steps
  through when every refinement evaluates to `true` on the value and is **blocked** otherwise.
  "Well-typed terms don't get stuck" becomes "a well-typed term is a value, steps, or is
  filter-blocked at a cast" — and refinement soundness (`⊢ e : {T | p}` and `e ⇓ v` implies `p(v) =
  true`) holds because the cast is the only door.
- **The fragment is enforced *in the judgment*** (`Ty.TermFragment` premises on
  the rules that choose types freely: `lam`'s domain, `variant`'s tags, `sub`'s target), not assumed
  of the theorem statements. Hypothesizing it only at the boundary would not confine a derivation's
  *internal* types — `sub` can detour through arbitrary types — and two preservation counterexamples
  live on such detours; see `Ty.TermFragment`.
- **`refineV` — checked values inhabit the refinement.** `cast` is the only
  refinement *door* a program can write, but preservation forces a second, value-level introduction:
  `cast p v` (refinements holding) steps to `v`, and `v`'s refined typing must come from somewhere —
  `Subtyping` deliberately forbids refinement conjuring. `refineV` says a refinement that *evaluates
  true on a value* types that value: the term-model face of literal-singleton typing (a refinement
  is a fact about a value). Runtime-checked (`refinementsHold`), value-only, so it is exactly the
  knowledge the `castV` step validates.

Left for later increments, recorded not dropped: `compose` (the point-free core — the source-shaped
lambda fragment is what the typing oracle checks first), records (keyed tuples; nothing new
algebraically), the dependent fragment, and wildcard `case` arms (needed before the case-binder
calibration lemma — the Rust's `case _:` payload-binder defect — can be *stated*).
-/

namespace CclFormal

/-- Term-level literals (the concrete fragment of `ccl::Lit`). -/
inductive Lit where
  | int (n : Int)
  | bool (b : Bool)
  | str (s : String)
  | unit
deriving Repr, DecidableEq

/-- The type of a literal. -/
def Lit.ty : Lit → Ty
  | .int _ => .base .int
  | .bool _ => .base .bool
  | .str _ => .base .string
  | .unit => .base .unit

/-- The pure-core term language (de Bruijn indices; see the module docs).

`case` arms pair a variant tag with a body whose index 0 is the payload binder — the
scrutinee-derived bound the calibration lemma is about. `cast` carries the refinement set it
asserts; it is the only refinement introduction,
mirroring CCL (a filter's lowering). -/
inductive Term where
  | lit (l : Lit)
  | var (n : Nat)
  | lam (dom : Ty) (body : Term)
  | app (f a : Term)
  | letE (bound body : Term)
  | tuple (es : List Term)
  | proj (e : Term) (i : Nat)
  | variant (tag : FieldKey) (e : Term)
  | caseE (scrut : Term) (arms : List (FieldKey × Term))
  | cast (refinements : List Predicate) (e : Term)
deriving Repr

namespace Term

/-- Values: literals, lambdas, tuples of values, variants of values. -/
inductive IsVal : Term → Prop
  | lit (l : Lit) : IsVal (.lit l)
  | lam (dom : Ty) (body : Term) : IsVal (.lam dom body)
  | tuple {es : List Term} : (∀ e ∈ es, IsVal e) → IsVal (.tuple es)
  | variant {e : Term} (tag : FieldKey) : IsVal e → IsVal (.variant tag e)

/-- Shift free indices `≥ c` by one (the standard de Bruijn lift). -/
def shift (c : Nat) : Term → Term
  | .lit l => .lit l
  | .var n => if n < c then .var n else .var (n + 1)
  | .lam dom body => .lam dom (shift (c + 1) body)
  | .app f a => .app (shift c f) (shift c a)
  | .letE bound body => .letE (shift c bound) (shift (c + 1) body)
  | .tuple es => .tuple (es.attach.map fun ⟨e, _⟩ => shift c e)
  | .proj e i => .proj (shift c e) i
  | .variant tag e => .variant tag (shift c e)
  | .caseE scrut arms =>
      .caseE (shift c scrut) (arms.attach.map fun ⟨(tag, body), _⟩ => (tag, shift (c + 1) body))
  | .cast refinements e => .cast refinements (shift c e)
termination_by e => sizeOf e
decreasing_by all_goals
  first
  | (simp; omega)
  | (rename_i h _; have := List.sizeOf_lt_of_mem h; simp at this ⊢; omega)
  | (rename_i h; have := List.sizeOf_lt_of_mem h; simp at this ⊢; omega)

/-- Substitute `v` for index `k` (types are closed in this fragment, so no
type substitution exists to perform). -/
def subst (k : Nat) (v : Term) : Term → Term
  | .lit l => .lit l
  | .var n => if n = k then v else if n < k then .var n else .var (n - 1)
  | .lam dom body => .lam dom (subst (k + 1) (shift 0 v) body)
  | .app f a => .app (subst k v f) (subst k v a)
  | .letE bound body => .letE (subst k v bound) (subst (k + 1) (shift 0 v) body)
  | .tuple es => .tuple (es.attach.map fun ⟨e, _⟩ => subst k v e)
  | .proj e i => .proj (subst k v e) i
  | .variant tag e => .variant tag (subst k v e)
  | .caseE scrut arms =>
      .caseE (subst k v scrut)
        (arms.attach.map fun ⟨(tag, body), _⟩ => (tag, subst (k + 1) (shift 0 v) body))
  | .cast refinements e => .cast refinements (subst k v e)
termination_by e => sizeOf e
decreasing_by all_goals
  first
  | (simp; omega)
  | (rename_i h _; have := List.sizeOf_lt_of_mem h; simp at this ⊢; omega)
  | (rename_i h; have := List.sizeOf_lt_of_mem h; simp at this ⊢; omega)

end Term

/-! ## Predicate evaluation

A refinement predicate is a `Predicate` over the reserved element binder; its truth on a value is
what `cast` checks and what refinement soundness is about. Evaluation is partial — an op outside the
interpreted vocabulary, or a shape mismatch, yields `none` — mirroring that the wire emitter maps
only
a fixed `BinOpKind` vocabulary. -/

/-- Evaluate a predicate against the value bound to `__elem`. Returns the
literal result, or `none` where the fragment does not interpret. -/
def Predicate.eval (v : Term) : Predicate → Option Lit
  | .elem =>
      match v with
      | .lit l => some l
      | _ => none
  -- A reference to an enclosing binder — free name or index — denotes the
  -- frame's parameter, which element-wise evaluation does not hold: the
  -- discharge that supplies it happens before a predicate is evaluated.
  | .var _ => none
  | .piBound _ => none
  | .litInt n => some (.int n)
  | .litBool b => some (.bool b)
  | .litStr s => some (.str s)
  | .litUnit => some .unit
  | .unop op a =>
      match op, Predicate.eval v a with
      | "not", some (.bool b) => some (.bool !b)
      | "neg", some (.int n) => some (.int (-n))
      | _, _ => none
  | .binop op a b =>
      match op, Predicate.eval v a, Predicate.eval v b with
      | "eq", some x, some y => some (.bool (x = y))
      | "ne", some x, some y => some (.bool (x ≠ y))
      | "lt", some (.int x), some (.int y) => some (.bool (x < y))
      | "le", some (.int x), some (.int y) => some (.bool (x ≤ y))
      | "gt", some (.int x), some (.int y) => some (.bool (x > y))
      | "ge", some (.int x), some (.int y) => some (.bool (x ≥ y))
      | "add", some (.int x), some (.int y) => some (.int (x + y))
      | "sub", some (.int x), some (.int y) => some (.int (x - y))
      | "mul", some (.int x), some (.int y) => some (.int (x * y))
      | "and", some (.bool x), some (.bool y) => some (.bool (x && y))
      | "or", some (.bool x), some (.bool y) => some (.bool (x || y))
      | _, _, _ => none
  | .proj a _k =>
      match Predicate.eval v a with
      | _ => none  -- literal results carry no fields; projection needs the
                   -- structured-value extension
  | .app _ _ => none
  -- A predicate's own binder and a reference to it: element-wise evaluation
  -- supplies `__elem` and nothing else, so there is no value to bind here.
  | .lam _ => none
  | .boundVar _ => none
  -- A cast is the refinement *introduction* the term calculus models as `Term.cast`;
  -- inside a predicate it stands for an embedded collection, which element-wise
  -- evaluation has no value for.
  | .cast _ _ => none

/-- Every refinement of a set holds on `v`. -/
def Term.refinementsHold (refinements : List Predicate) (v : Term) : Bool :=
  refinements.all fun p => Predicate.eval v p == some (.bool true)

/-! ## The call-by-value small-step relation -/

namespace Term

/-- One step. `cast` is the door refinements guard: it steps through exactly
when every refinement holds on the value (a blocked cast is a *filtered* element,
not a stuck term — see the module docs). -/
inductive Step : Term → Term → Prop
  | appL {f f' a} : Step f f' → Step (.app f a) (.app f' a)
  | appR {f a a'} : IsVal f → Step a a' → Step (.app f a) (.app f a')
  | beta {dom body a} : IsVal a → Step (.app (.lam dom body) a) (subst 0 a body)
  | letL {bound bound' body} : Step bound bound' → Step (.letE bound body) (.letE bound' body)
  | letV {bound body} : IsVal bound → Step (.letE bound body) (subst 0 bound body)
  | tupleAt {pre : List Term} {e e' : Term} {post : List Term} :
      (∀ x ∈ pre, IsVal x) → Step e e' →
      Step (.tuple (pre ++ e :: post)) (.tuple (pre ++ e' :: post))
  | projE {e e' i} : Step e e' → Step (.proj e i) (.proj e' i)
  | projV {es : List Term} {i : Nat} {e : Term} :
      (∀ x ∈ es, IsVal x) → es[i]? = some e → Step (.proj (.tuple es) i) e
  | variantE {tag e e'} : Step e e' → Step (.variant tag e) (.variant tag e')
  | caseS {scrut scrut' arms} : Step scrut scrut' → Step (.caseE scrut arms) (.caseE scrut' arms)
  | caseV {tag v arms body} :
      IsVal v → arms.lookup tag = some body →
      Step (.caseE (.variant tag v) arms) (subst 0 v body)
  | castE {refinements e e'} : Step e e' → Step (.cast refinements e) (.cast refinements e')
  | castV {refinements v} :
      IsVal v → refinementsHold refinements v = true → Step (.cast refinements v) v

/-- A term is *filter-blocked* when its next redex is a cast whose refinements do
not all hold on the value — the scalar face of a `Restrict` dropping a row.
Progress is stated modulo this outcome. -/
inductive Blocked : Term → Prop
  | castV {refinements v} : IsVal v → refinementsHold refinements v = false → Blocked
    (.cast refinements v)
  | appL {f a} : Blocked f → Blocked (.app f a)
  | appR {f a} : IsVal f → Blocked a → Blocked (.app f a)
  | letL {bound body} : Blocked bound → Blocked (.letE bound body)
  | tupleAt {pre : List Term} {e : Term} {post : List Term} :
      (∀ x ∈ pre, IsVal x) → Blocked e → Blocked (.tuple (pre ++ e :: post))
  | projE {e i} : Blocked e → Blocked (.proj e i)
  | variantE {tag e} : Blocked e → Blocked (.variant tag e)
  | caseS {scrut arms} : Blocked scrut → Blocked (.caseE scrut arms)
  | castE {refinements e} : Blocked e → Blocked (.cast refinements e)

end Term

/-! ## The declarative typing judgment -/

/-- Predicates of the non-dependent fragment: over `__elem` only, no
references to enclosing binders — neither a free name nor an index. -/
def Predicate.elemOnly : Predicate → Bool
  | .elem | .litInt _ | .litBool _ | .litStr _ | .litUnit => true
  | .var _ => false
  | .piBound _ => false
  | .unop _ a => a.elemOnly
  | .binop _ a b => a.elemOnly && b.elemOnly
  | .proj a _ => a.elemOnly
  | .app f a => f.elemOnly && a.elemOnly
  -- Outside the element-only fragment for the same reason `var` is: the term
  -- judgment scopes no frame for a binder the predicate introduces.
  | .lam _ => false
  | .boundVar _ => false
  | .cast _ _ => false

/-- The types the term fragment covers, hereditarily: **every refinement
predicate is `Predicate.elemOnly`**, the non-dependent fragment. Off it, a refinement references an
enclosing binder the term judgment does not scope — the element-wise checks (`refinementsHold`,
`Predicate.eval`) hold no frame parameter to supply for a `piBound` index or a free name, so a
dependent refinement's truth on a value is not even stated here. The dependent fragment enters when
the judgment scopes its types' frames, not before.

The shape follows `Ty.WellFormed`: an inductive with one constructor per head, so
`cases` is the inversion. -/
inductive Ty.TermFragment : Ty → Prop
  | base (b) : Ty.TermFragment (.base b)
  | uintRange (n) : Ty.TermFragment (.uintRange n)
  | dataSource (s) : Ty.TermFragment (.dataSource s)
  | txn : Ty.TermFragment .txn
  | fn {n k d c} : Ty.TermFragment d → Ty.TermFragment c →
      Ty.TermFragment (.fn n k d c)
  | tuple {ts} : (∀ t ∈ ts, Ty.TermFragment t) → Ty.TermFragment (.tuple ts)
  | record {fs} : (∀ f ∈ fs, Ty.TermFragment f.2) → Ty.TermFragment (.record fs)
  | variant {tags} : (∀ t ∈ tags, Ty.TermFragment t.2) → Ty.TermFragment (.variant tags)
  | refined {b ps} : (∀ p ∈ ps, p.elemOnly = true) → Ty.TermFragment b →
      Ty.TermFragment (.refined b ps)

/-- `Γ ⊢ e : T` for the pure core. Contexts are de Bruijn (index 0 is the
innermost binder). Subsumption is the concrete relation directly — with refinements closed at
construction it carries no environments to instantiate.

`cast` is the refinement introduction a *program* writes: it asserts its refinements on top of the
value's type, and the small-step checks them — the pairing refinement soundness rests on. `refineV`
is the value-level introduction preservation forces (see the module docs): refinements that evaluate
true on a value type that value. `caseE` types every arm's body under the payload type the
scrutinee's variant assigns to its tag: the scrutinee-derived bound of the calibration lemma.

The rules that choose a type freely — `lam`'s domain annotation, `variant`'s tag table, `sub`'s
target, and `caseE`'s result (free only in the degenerate empty-tags elimination, where every arm
premise is vacuous and `U` is otherwise unconstrained) — require it in the term fragment
(`Ty.TermFragment`); everything else inherits fragment membership from its
premises (`hasTy_fragment` in `WellTypedTermsAreSafe.lean` is that invariant, stated). -/
inductive HasTy : List Ty → Term → Ty → Prop
  | lit {Γ} (l : Lit) : HasTy Γ (.lit l) l.ty
  | var {Γ n T} : Γ[n]? = some T → HasTy Γ (.var n) T
  | lam {Γ dom body cod} :
      dom.TermFragment →
      HasTy (dom :: Γ) body cod →
      HasTy Γ (.lam dom body) (.fn none .compute dom cod)
  | app {Γ f a name kind dom cod} :
      HasTy Γ f (.fn name kind dom cod) → HasTy Γ a dom →
      HasTy Γ (.app f a) cod
  | letE {Γ bound body T U} :
      HasTy Γ bound T → HasTy (T :: Γ) body U →
      HasTy Γ (.letE bound body) U
  | tuple {Γ} {es : List Term} {Ts : List Ty} :
      es.length = Ts.length →
      (∀ (i : Nat) e T, es[i]? = some e → Ts[i]? = some T → HasTy Γ e T) →
      HasTy Γ (.tuple es) (.tuple Ts)
  | proj {Γ e i} {Ts : List Ty} {T : Ty} :
      HasTy Γ e (.tuple Ts) → Ts[i]? = some T →
      HasTy Γ (.proj e i) T
  | variant {Γ e tag T} {tags : List (FieldKey × Ty)} :
      Ty.TermFragment (.variant tags) →
      HasTy Γ e T → tags.lookup tag = some T →
      HasTy Γ (.variant tag e) (.variant tags)
  | caseE {Γ scrut arms U} {tags : List (FieldKey × Ty)} :
      U.TermFragment →
      HasTy Γ scrut (.variant tags) →
      (∀ tag T, tags.lookup tag = some T → (arms.lookup tag).isSome) →
      (∀ tag T body, tags.lookup tag = some T → arms.lookup tag = some body →
        HasTy (T :: Γ) body U) →
      HasTy Γ (.caseE scrut arms) U
  | cast {Γ e T} {refinements : List Predicate} :
      HasTy Γ e T →
      refinements ≠ [] → (∀ p ∈ refinements, p.elemOnly = true) →
      T.isRefined = false →
      HasTy Γ (.cast refinements e) (.refined T refinements)
  | refineV {Γ v T} {refinements : List Predicate} :
      HasTy Γ v T → v.IsVal →
      Term.refinementsHold refinements v = true →
      refinements ≠ [] → (∀ p ∈ refinements, p.elemOnly = true) →
      T.isRefined = false →
      HasTy Γ v (.refined T refinements)
  | sub {Γ e T U} :
      HasTy Γ e T → Subtyping T U → U.TermFragment →
      HasTy Γ e U

/-! ## First sanity facts -/

/-- Values do not step. -/
theorem Term.IsVal.not_step {v v' : Term} (hv : v.IsVal) : ¬ Term.Step v v' := by
  intro hs
  induction hs with
  | tupleAt hpre _ ih =>
    cases hv with
    | tuple hall =>
      exact ih (hall _ (by simp))
  | variantE _ ih =>
    cases hv with
    | variant _ he => exact ih he
  | _ => cases hv <;> simp_all

/-- Values are not blocked. -/
theorem Term.IsVal.not_blocked {v : Term} (hv : v.IsVal) : ¬ Term.Blocked v := by
  intro hb
  induction hb with
  | tupleAt hpre _ ih =>
    cases hv with
    | tuple hall => exact ih (hall _ (by simp))
  | variantE _ ih =>
    cases hv with
    | variant _ he => exact ih he
  | _ => cases hv <;> simp_all

end CclFormal
