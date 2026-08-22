import CclFormal.Merge

/-!
# Materialization: the compact type back out as a `Ty`

The Lean mirror of `src/ccl/infer/solver/coalesce.rs`'s `coalesce_compact_go` — the
partial function from a merged bound to the type the solver reports. `merge` says
how bounds combine; this says what the combination *is*, and it is the half that
decides whether a join has an answer at all.

`coalesce` is partial in two different ways, and they are distinct outcomes:

- **Refused** (`CoErr`): the position has no type. Two or more concrete
  contributions at once, a `Data` slot whose alternatives do not reconcile, a
  conflicted slot, or a record with mixed key kinds.
- **Unresolved** (`ok none`): nothing concrete reached the position, so
  `coalesce_compact_go` emits a fresh `Type::Infer`. The model has no `Infer` node
  — the same exclusion `Ty` makes for the subtype relation — so it reports the
  fact and not the variable. A position that materializes to an inference variable
  is therefore compared only as "unresolved", refinements included: the Rust attaches
  the position's refinements to the variable and the model cannot carry them.

## What it drops, beyond `CTy`'s own adjudications

- **The Pi binder.** `coalesce_compact_go` keeps `cf.name` when the codomain
  references it (`kept_name`). `CTy` has no binder slot, so the model always emits
  `none` and the differential compares modulo the binder.
- **`Openness`.** `CTy`'s variant slot is a bare tag map, so a materialized
  variant carries no arm-set completeness. Every generated arm set is closed.
- **Which error.** A conflicted `fn` slot is `KindConflict` or
  `DomainJoinConflict` in the Rust depending on how many alternatives survive, and
  the model drops a conflicted slot's alternatives (see `Merge.lean`), so it
  reports one `conflictedSlot` for both.

## Why it terminates

By `depth`, not by any subterm ordering. One recursive call is the reason: a
`Compute` slot's alternatives are folded with `merge` (`meetAll`) and the *result*
is materialized, and that result is not a subterm of the position. The bound is
`merge_depth_le` — **`merge` does not deepen a position**, since it unions atoms,
merges map payloads pointwise, and recurses into a function slot's domain and
codomain — so the folded domain is no deeper than the alternatives it came from,
which are children of the position. `compact.rs` makes no such argument anywhere,
and its own recursion rests on it.

Everything else recurses on a child, and each call's bound is named beside it
(`depth_cod_lt`, `depth_dom_lt`, `depth_recPayload_lt`, `depth_varPayload_lt`,
`depth_fold_lt`). The keyed maps are walked with `List.attach`, so each payload's
recursive call carries the membership proof its bound needs.
-/

namespace CclFormal
namespace CTy

/-- Why a position has no type. -/
inductive CoErr where
  /-- Bounds with no common shape at one position (`IncompatibleBounds`). Two or
  more concrete contributions is one way; a product with no fields is the same
  thing read one level down, since a positive merge intersects field sets and
  there is no zero-field product for the empty map to be. -/
  | incompatible
  /-- A `Data` slot whose alternatives do not reconcile (`DomainJoinConflict`). -/
  | domainJoin
  /-- A conflicted `fn` slot (`KindConflict` or `DomainJoinConflict`). -/
  | conflictedSlot
  /-- A record with mixed `Index`/`Name` keys (`UnresolvedPartial`). -/
  | partialRecord
deriving Repr, DecidableEq

/-- The type an atom contributes (`AtomKey::to_type`). -/
def atomTy : Atom → Ty
  | .prim b => .base b
  | .uintRange n => .uintRange n
  | .source s => .dataSource s
  | .txn => .txn

/-- Re-attach the position's refinements, flattening as `Type::refined` does: an empty
refinement set is the bare type. -/
def attachRefinements (t : Ty) : Option (List Pred) → Ty
  | none => t
  | some [] => t
  | some ps => match t with
    | .refined b qs => .refined b (qs ++ ps)
    | _ => .refined t ps

/-- A dense index-keyed map's payloads in *index* order, as a tuple.

`Ty.tuple` is positional and the map's list order carries no information — `eqv`
compares maps as sets, mirroring the `BTreeMap` the Rust holds, whose iteration
order is the key order. So the payloads are read by index rather than by
position. -/
def byIndex (n : Nat) (kvs : List (Nat × Ty)) : Option Ty :=
  ((List.range n).mapM (fun i => List.lookup i kvs)).map Ty.tuple

/-- The index keys of a map, if every key is one. -/
def indexKeys : List (FieldKey × CTy) → Option (List Nat)
  | [] => some []
  | (.idx n, _) :: rest => (indexKeys rest).map (n :: ·)
  | (.name _, _) :: _ => none

/-- The name keys of a map, if every key is one. -/
def nameKeys : List (FieldKey × CTy) → Option (List String)
  | [] => some []
  | (.name s, _) :: rest => (nameKeys rest).map (s :: ·)
  | (.idx _, _) :: _ => none

/-! ### The depth bounds `coalesce`'s recursion decreases by

Every recursive call is on something strictly shallower than the position, which is
what makes one measure — `depth` — enough. The folded `Compute` domain is the call
that needs `merge_depth_le`; the rest are children. -/

theorem depth_cod_lt {a : List Atom} {r v : Option (List (FieldKey × CTy))}
    {c : Option (List Pred)} {k : KindM} {ds : List CTy} {cod : CTy} :
    depth cod < depth (CTy.mk a r v (some (k, ds, cod)) c) := by
  have h1 : depth cod ≤ optFnDepth (some (k, ds, cod)) := by
    simp only [optFnDepth]
    exact Nat.le_max_right _ _
  have h2 : optFnDepth (some (k, ds, cod))
      ≤ Nat.max (optMapDepth r) (Nat.max (optMapDepth v) (optFnDepth (some (k, ds, cod)))) :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  rw [depth]
  omega

theorem depth_dom_lt {a : List Atom} {r v : Option (List (FieldKey × CTy))}
    {c : Option (List Pred)} {k : KindM} {ds : List CTy} {cod d : CTy} (h : d ∈ ds) :
    depth d < depth (CTy.mk a r v (some (k, ds, cod)) c) := by
  have h1 : depth d ≤ optFnDepth (some (k, ds, cod)) := by
    simp only [optFnDepth]
    exact Nat.le_trans (le_listDepth h) (Nat.le_max_left _ _)
  have h2 : optFnDepth (some (k, ds, cod))
      ≤ Nat.max (optMapDepth r) (Nat.max (optMapDepth v) (optFnDepth (some (k, ds, cod)))) :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  rw [depth]
  omega

/-- The folded `Compute` domain: bounded because `merge` does not deepen. -/
theorem depth_fold_lt {a : List Atom} {r v : Option (List (FieldKey × CTy))}
    {c : Option (List Pred)} {k : KindM} {cod d : CTy} {rest : List CTy} {q : Bool} :
    depth (meetAll q d rest) < depth (CTy.mk a r v (some (k, d :: rest, cod)) c) := by
  have h0 : depth (meetAll q d rest) ≤ listDepth (d :: rest) := by
    refine Nat.le_trans (meetAll_depth_le q d rest) ?_
    rw [listDepth]
    exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  have h1 : listDepth (d :: rest) ≤ optFnDepth (some (k, d :: rest, cod)) := by
    simp only [optFnDepth]
    exact Nat.le_max_left _ _
  have h2 : optFnDepth (some (k, d :: rest, cod))
      ≤ Nat.max (optMapDepth r)
        (Nat.max (optMapDepth v) (optFnDepth (some (k, d :: rest, cod)))) :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  rw [depth]
  omega

theorem depth_recPayload_lt {a : List Atom} {m : List (FieldKey × CTy)}
    {v : Option (List (FieldKey × CTy))} {f : Option (KindM × List CTy × CTy)}
    {c : Option (List Pred)} {p : FieldKey × CTy} (h : p ∈ m) :
    depth p.2 < depth (CTy.mk a (some m) v f c) := by
  have h1 : depth p.2 ≤ optMapDepth (some m) := by
    simp only [optMapDepth]
    exact le_mapDepth h
  have h2 : optMapDepth (some m)
      ≤ Nat.max (optMapDepth (some m)) (Nat.max (optMapDepth v) (optFnDepth f)) :=
    Nat.le_max_left _ _
  rw [depth]
  omega

theorem depth_varPayload_lt {a : List Atom} {m : List (FieldKey × CTy)}
    {r : Option (List (FieldKey × CTy))} {f : Option (KindM × List CTy × CTy)}
    {c : Option (List Pred)} {p : FieldKey × CTy} (h : p ∈ m) :
    depth p.2 < depth (CTy.mk a r (some m) f c) := by
  have h1 : depth p.2 ≤ optMapDepth (some m) := by
    simp only [optMapDepth]
    exact le_mapDepth h
  have h2 : optMapDepth (some m)
      ≤ Nat.max (optMapDepth r) (Nat.max (optMapDepth (some m)) (optFnDepth f)) :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  rw [depth]
  omega

/-! The same three bounds phrased over an `attach` element, so `decreasing_by` can
find them without naming the lambda's binder. -/

theorem depth_recAttach_lt {a : List Atom} {m : List (FieldKey × CTy)}
    {v : Option (List (FieldKey × CTy))} {f : Option (KindM × List CTy × CTy)}
    {c : Option (List Pred)} (rp : {x : FieldKey × CTy // x ∈ m}) :
    depth rp.1.2 < depth (CTy.mk a (some m) v f c) :=
  depth_recPayload_lt rp.2

theorem depth_varAttach_lt {a : List Atom} {m : List (FieldKey × CTy)}
    {r : Option (List (FieldKey × CTy))} {f : Option (KindM × List CTy × CTy)}
    {c : Option (List Pred)} (vp : {x : FieldKey × CTy // x ∈ m}) :
    depth vp.1.2 < depth (CTy.mk a r (some m) f c) :=
  depth_varPayload_lt vp.2

theorem depth_domAttach_lt {a : List Atom} {r v : Option (List (FieldKey × CTy))}
    {c : Option (List Pred)} {k : KindM} {ds : List CTy} {cod : CTy}
    (alt : {x : CTy // x ∈ ds}) :
    depth alt.1 < depth (CTy.mk a r v (some (k, ds, cod)) c) :=
  depth_dom_lt alt.2

/-- Build a function type from two materialized halves, unresolved if either is. -/
def funTy (kind : FunKind) : Option Ty → Option Ty → Option Ty
  | some d, some c => some (.fn none kind d c)
  | _, _ => none

/-- The shapes a position contributed, combined: none is unresolved, one is the
type with the position's refinements re-attached, and two or more is a position with
no type at all.

Named, and not a `match` inside [`coalesce`], because it is what every shape
argument reads: materializing at all means exactly one contribution is non-empty.
-/
def combine (shapes : List (Option Ty)) (refinements : Option (List Pred)) :
    Except CoErr (Option Ty) :=
  match shapes with
  | [] => .ok none
  | [t] => .ok (t.map (attachRefinements · refinements))
  | _ => .error .incompatible

mutual

/-- Mirror of `coalesce_compact_go`. `ok none` is an unresolved position.

The four contributions are *named* functions rather than sub-expressions of one
`do` block, because a proof has to speak about one of them on its own: the shape
argument every case of the monotonicity lemma rests on is that materializing
means exactly one contribution is non-empty, and that is unstatable about an
inline expression. Each takes the whole position, which is also what the `depth`
lemmas below are stated against. -/
def coalesce (pol : Bool) : CTy → Except CoErr (Option Ty)
  | t => do
    -- The position is passed whole to each contribution and destructured only
    -- afterwards: the measure below is stated on `t`, and matching on the
    -- constructor first would specialize it out from under the recursive calls.
    let recShape ← recShapes pol t
    let varShape ← varShapes pol t
    let funShape ← funShapes pol t
    match t with
    | .mk atoms recF varT fn refinements =>
      -- Whether a contribution is read is the *slot's* question, so the list's
      -- length is manifest here rather than something a lemma has to recover
      -- from the helper's branches. An absent slot's helper answers `none` and
      -- is not read.
      combine ((atoms.map atomTy).eraseDups.map some
        ++ (if recF.isSome then [recShape] else [])
        ++ (if varT.isSome then [varShape] else [])
        ++ (if fn.isSome then [funShape] else [])) refinements
termination_by t => (depth t, 1)
decreasing_by all_goals (apply Prod.Lex.right; omega)

/-- The record slot's contribution: the empty product is unit, dense index keys
are a tuple, sparse ones are unresolved, name keys are a record, and a mix has no
type. The payloads materialize either way, so a nested refusal wins over a
discarded shape — what the `?` in `materialize_record` does. The key kinds are
checked *before* any payload is materialized: a mixed-key map has no type and
`materialize_record` returns without touching the payloads. -/
def recShapes (pol : Bool) : CTy → Except CoErr (Option Ty)
  | .mk _ none _ _ _ => pure none
  | .mk _ (some m) _ _ _ =>
    if m.isEmpty then .error .incompatible
    else
      match indexKeys m with
      | some idxs => do
        let payloads ← m.attach.mapM fun rp => coalesce pol rp.1.2
        if idxs.length == m.length && (List.range m.length).all (idxs.contains ·) then
          pure ((payloads.mapM id).bind (fun ts => byIndex m.length (idxs.zip ts)))
        else
          pure none
      | none =>
        match nameKeys m with
        | some names => do
          let payloads ← m.attach.mapM fun rp => coalesce pol rp.1.2
          pure ((payloads.mapM id).map (fun ts => Ty.record (names.zip ts)))
        | none => .error .partialRecord
termination_by t => (depth t, 0)
decreasing_by all_goals (apply Prod.Lex.left; exact depth_recAttach_lt _)

/-- The variant slot's contribution: its arms, materialized in the map's order. -/
def varShapes (pol : Bool) : CTy → Except CoErr (Option Ty)
  | .mk _ _ none _ _ => pure none
  | .mk _ _ (some m) _ _ => do
    let payloads ← m.attach.mapM fun vp => coalesce pol vp.1.2
    pure ((payloads.mapM id).map (fun ts => Ty.variant ((m.map Prod.fst).zip ts)))
termination_by t => (depth t, 0)
decreasing_by all_goals (apply Prod.Lex.left; exact depth_varAttach_lt _)

/-- The function slot's contribution. The resolved kind decides what the domain
alternatives mean: a `Compute` reading — and an unpinned kind variable, which
defaults to it — meets them, while a `Data` reading needs exactly one to survive
materialization. -/
def funShapes (pol : Bool) : CTy → Except CoErr (Option Ty)
  | .mk _ _ _ none _ => pure none
  | .mk _ _ _ (some (k, ds, cod)) _ => do
    let c ← coalesce pol cod
    match k with
    | .conflict => .error .conflictedSlot
    | .data => do
      let mats ← ds.attach.mapM fun alt => coalesce (!pol) alt.1
      match mats.eraseDups with
      | [one] => pure (funTy .data one c)
      | _ => .error .domainJoin
    | _ =>
      match ds with
      | [] => .error .conflictedSlot
      | d :: rest => do
        let dt ← coalesce (!pol) (meetAll (!pol) d rest)
        pure (funTy .compute dt c)
termination_by t => (depth t, 0)
decreasing_by
  all_goals
    apply Prod.Lex.left
    first
    | exact depth_cod_lt
    | exact depth_fold_lt
    | exact depth_domAttach_lt _

end

/-! ## Reading a contribution back

Each slot contributes an empty list when it is absent and a one-element list when
it is present, and `combine` accepts the concatenation only when it is a
singleton. Together those are the shape argument: materializing means exactly one
slot carries the position. -/

theorem combine_ok : ∀ {shapes : List (Option Ty)} {refinements : Option (List Pred)} {ty : Ty},
    combine shapes refinements = .ok (some ty) → ∃ t, shapes = [some t] ∧ ty = attachRefinements t refinements
  | [], _, _, h => by simp [combine] at h
  | [x], refinements, ty, h => by
    rcases x with _ | t
    · simp [combine] at h
    · refine ⟨t, rfl, ?_⟩
      simp only [combine, Option.map_some, Except.ok.injEq, Option.some.injEq] at h
      exact h.symm
  | _ :: _ :: _, _, _, h => by simp [combine] at h

theorem recShapes_none (pol : Bool) {as v f c} : recShapes pol (.mk as none v f c) = .ok none := by
  rw [recShapes]
  rfl

theorem varShapes_none (pol : Bool) {as r f c} : varShapes pol (.mk as r none f c) = .ok none := by
  rw [varShapes]
  rfl

theorem funShapes_none (pol : Bool) {as r v c} : funShapes pol (.mk as r v none c) = .ok none := by
  rw [funShapes]
  rfl

/-! ## Reading a `mapM` back

`coalesce` materializes a keyed slot's payloads with `mapM` over `attach`, and
every proof about a keyed slot has to invert that. Two cases are enough: a proof
inducts on the map and peels one entry at a time. -/

theorem mapM_ok_nil {α β ε} {f : α → Except ε β} {l' : List β}
    (h : ([] : List α).mapM f = .ok l') : l' = [] := by
  simp only [List.mapM_nil] at h
  cases h
  rfl

theorem mapM_ok_cons {α β ε} {f : α → Except ε β} {a : α} {as : List α} {l' : List β}
    (h : (a :: as).mapM f = .ok l') :
    ∃ b bs, f a = .ok b ∧ as.mapM f = .ok bs ∧ l' = b :: bs := by
  rw [List.mapM_cons] at h
  rcases hfa : f a with e | b <;> rw [hfa] at h
  · cases h
  · rcases hbs : as.mapM f with e | bs <;> rw [hbs] at h
    · cases h
    · cases h
      exact ⟨b, bs, rfl, rfl, rfl⟩

theorem mapM_some_nil {α β} {f : α → Option β} {l' : List β}
    (h : ([] : List α).mapM f = some l') : l' = [] := by
  simp only [List.mapM_nil] at h
  cases h
  rfl

theorem mapM_some_cons {α β} {f : α → Option β} {a : α} {as : List α} {l' : List β}
    (h : (a :: as).mapM f = some l') :
    ∃ b bs, f a = some b ∧ as.mapM f = some bs ∧ l' = b :: bs := by
  rw [List.mapM_cons] at h
  rcases hfa : f a with _ | b <;> rw [hfa] at h
  · cases h
  · rcases hbs : as.mapM f with _ | bs <;> rw [hbs] at h
    · cases h
    · cases h
      exact ⟨b, bs, rfl, rfl, rfl⟩

theorem mapM_some_get {α β} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
      l'.length = l.length ∧
        ∀ (i : Nat) (x : α) (y : β), l[i]? = some x → l'[i]? = some y → f x = some y
  | [], l', h => by
    cases mapM_some_nil h
    exact ⟨rfl, fun i x y hx _ => absurd hx (by simp)⟩
  | a :: as, l', h => by
    obtain ⟨b, bs, hfa, hbs, rfl⟩ := mapM_some_cons h
    obtain ⟨hlen, hget⟩ := mapM_some_get hbs
    refine ⟨by simp [hlen], fun i x y hx hy => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
      subst hx
      subst hy
      exact hfa
    | succ n =>
      simp only [List.getElem?_cons_succ] at hx hy
      exact hget n x y hx hy

/-! ## Keys of a materialized map

`indexKeys`/`nameKeys` succeed exactly when every key is of one kind, so the map's
key list is the returned list re-tagged. -/

theorem indexKeys_keys : ∀ {m : List (FieldKey × CTy)} {idxs : List Nat},
    indexKeys m = some idxs → m.map Prod.fst = idxs.map FieldKey.idx
  | [], idxs, h => by simp [indexKeys] at h; simp [← h]
  | (.idx n, v) :: m, idxs, h => by
    simp only [indexKeys, Option.map_eq_some_iff] at h
    obtain ⟨rest, hrest, rfl⟩ := h
    simpa using indexKeys_keys hrest
  | (.name s, v) :: m, idxs, h => by simp [indexKeys] at h

theorem nameKeys_keys : ∀ {m : List (FieldKey × CTy)} {names : List String},
    nameKeys m = some names → m.map Prod.fst = names.map FieldKey.name
  | [], names, h => by simp [nameKeys] at h; simp [← h]
  | (.name s, v) :: m, names, h => by
    simp only [nameKeys, Option.map_eq_some_iff] at h
    obtain ⟨rest, hrest, rfl⟩ := h
    simpa using nameKeys_keys hrest
  | (.idx n, v) :: m, names, h => by simp [nameKeys] at h

/-! ## The comparison the differential uses

Refinements compare as a **set**, mirroring `RefinementSet`: the Rust's refinement set is
deduplicated and insertion-ordered, and the model appends, so a positional
comparison would report an order difference as a divergence. Binders compare
normally — the harness erases them on its side, because `CTy` has no binder slot
and the model can only ever emit `none`. -/

mutual

def tyEqv : Ty → Ty → Bool
  | .base a, .base b => a == b
  | .uintRange a, .uintRange b => a == b
  | .dataSource a, .dataSource b => a == b
  | .txn, .txn => true
  | .fn n0 k0 d0 c0, .fn n1 k1 d1 c1 => n0 == n1 && k0 == k1 && tyEqv d0 d1 && tyEqv c0 c1
  | .tuple a, .tuple b => tyEqvSeq a b
  | .record a, .record b => tyEqvRec a b
  | .variant a, .variant b => tyEqvVar a b
  | .refined b1 p1, .refined b2 p2 =>
      tyEqv b1 b2 && p1.all (p2.contains ·) && p2.all (p1.contains ·)
  | _, _ => false
termination_by a b => sizeOf a + sizeOf b

def tyEqvSeq : List Ty → List Ty → Bool
  | [], [] => true
  | x :: xs, y :: ys => tyEqv x y && tyEqvSeq xs ys
  | _, _ => false
termination_by a b => sizeOf a + sizeOf b

def tyEqvRec : List (String × Ty) → List (String × Ty) → Bool
  | [], [] => true
  | (n1, t1) :: xs, (n2, t2) :: ys => n1 == n2 && tyEqv t1 t2 && tyEqvRec xs ys
  | _, _ => false
termination_by a b => sizeOf a + sizeOf b

def tyEqvVar : List (FieldKey × Ty) → List (FieldKey × Ty) → Bool
  | [], [] => true
  | (k1, t1) :: xs, (k2, t2) :: ys => k1 == k2 && tyEqv t1 t2 && tyEqvVar xs ys
  | _, _ => false
termination_by a b => sizeOf a + sizeOf b

end

/-- The outcome the harness reports, and whether the model agrees with it. -/
inductive CoGot where
  | ok (t : Ty)
  | unresolved
  | err (kind : String)

def coalesceAgrees (want : Except CoErr (Option Ty)) (got : CoGot) : Bool :=
  match want, got with
  | .ok (some t), .ok u => tyEqv t u
  | .ok none, .unresolved => true
  | .error e, .err kind =>
      match e with
      | .incompatible => kind == "IncompatibleBounds"
      | .domainJoin => kind == "DomainJoinConflict"
      -- A conflicted slot is one error here and two there: which one the Rust
      -- reports reads the alternatives the model drops.
      | .conflictedSlot => kind == "KindConflict" || kind == "DomainJoinConflict"
      | .partialRecord => kind == "UnresolvedPartial"
  | _, _ => false

end CTy
end CclFormal
