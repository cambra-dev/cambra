import CclFormal.Ty

/-!
# The solver's polar merge and its algebra

The Lean mirror of `src/ccl/infer/solver/compact.rs`'s bound-merging — the
operation `coalesce` folds over a variable's bounds (`CompactType::merge`,
`CompactFun::merge`, `merge_refinements`, `merge_records`, `merge_variants`) —
and the theorems that make the solver's order-independence refinement a proof
obligation instead of a fuzz observation:

- `eqv` is an equivalence relation (`eqv_refl`, `eqv_symm`, `eqv_trans`);
- `merge` is commutative (`merge_comm`), idempotent (`merge_idem`, under `wf`),
  and a congruence for `eqv` (`merge_congr_left`/`_right`);
- `merge` is associative (`merge_assoc`), at either polarity and with no side
  condition — the kinds join in a semilattice (`joinKind`) and the domains are
  combined by polarity alone, so no step reads a value a later step can change;
- the fold `coalesce` performs is therefore invariant under permutation
  (`foldMerge_perm`) and duplication (`foldMerge_dup`) of the bound list;
- `merge pol` is the least upper bound of the order it induces, and the *only*
  one up to `eqv` (`merge_isLub`, `join_unique`), with the empty position as the
  order's least element (`merge_cempty_left`, `le_cempty`).

`differential.rs`'s `differential_bound_merge_vs_lean_model` is what keeps this
a statement about the solver: it folds generated bound lists through
`CompactType::merge` exactly as `compact_go` does and checks every step against
`merge` here, judged by `eqv`.

## What the model is a mirror of, and what it drops

`CTy` is the ground fragment of `CompactType`: atoms, the optional
record/variant maps, the optional function slot, and the refinement slot with its
`none` sentinel. Deliberately dropped, with the reasoning:

- **Inference variables** (`vars`) — the ground algebra doesn't read them;
  they union like atoms and would only pad every proof.
- **History slots** — transients erased before the strict wall, exactly as
  `Ty` excludes `History` (same-polarity componentwise merge; nothing new).
- **The Pi binder** (`CompactFun::name`, merged `a.name.or(b.name)`) —
  first-wins is order-dependent as written, but the slot carries no refinement
  identity: a refinement's binding is its index (`Name::PiBound`), so the merged
  refinements agree whatever spelling survives, and the slot is display plus the
  frame's opening address; the asymmetry is unobservable.
- **A conflicted slot's domain payload** — `compact.rs` keeps `widest`, which
  picks between two equal-length lists by arrival order. Coalesce prints those
  alternatives and reads nothing from them, so the model drops the payload rather
  than mirror an order-dependent choice, and the differential's encoder drops it
  too. Every other slot's alternatives are mirrored in full: `fn`'s domain slot is
  a `List CTy` matching `DomainSet`, because `coalesce_compact_go` folds the
  contravariant meet over it and two slots differing in the tail materialize
  differently.

## The equivalence is the code's own equality

`eqv` mirrors `CompactType`'s `PartialEq`: set-semantic on atoms and refinements
(mirroring `BTreeSet` and `RefinementSet`), key-set + payload on the maps
(mirroring `BTreeMap`), componentwise on the function slot. The merge's one
internal comparison — `union_domains` deduplicating two `Data` domains — uses
that same equality, which is what makes every theorem quotient-compatible:
the gate cannot distinguish two `eqv`-equal inputs.

The empty position **is** an identity (`merge_cempty_left`), because every slot
including the refinement slot has a `none` that merges as one. `compact_go` still
folds a variable's bounds from the *first bound* rather than from
`CompactType::default()`, so the fold theorems are stated over nonempty lists,
but that is now the code's habit rather than an algebraic requirement.
-/

namespace CclFormal

/-- Mirror of `compact.rs :: AtomKey` (ground fragment — `ChanDom` excluded,
the same adjudication as `Ty`'s exclusion of pipeline transients). -/
inductive Atom where
  | prim (b : BaseTy)
  | uintRange (n : Nat)
  | source (s : String)
  | txn
deriving Repr, DecidableEq

/-- Mirror of `compact.rs :: KindMerge`: the flat semilattice
`unknown < {data, compute} < conflict`. `unknown` is a kind variable nothing
pinned — the identity, since nothing *required* a kind there — and `conflict` is
the absorbing state a bad kind meeting leaves behind (coalesce turns it into an
error; it never materializes). -/
inductive KindM where
  | data | compute | conflict | unknown
deriving Repr, DecidableEq

/-! ## The refinement slot

`compact.rs`'s `refinements` is an `Option<RefinementSet>`, and the two states
are distinct. `none` is "no refinement contribution here" and merges as the identity
— a hole, or a bare variable whose content is its identity alone — while
`some []` is a *value* that guarantees nothing, which is absorbing under the
positive intersect. Collapsing them makes a bare variable erase the refinements a
sibling bound established, which is why the slot carries the same sentinel the
shape slots do. -/

/-- The refinement slot's merge: `none` is the identity, and two present sets
intersect at a positive position and unite at a negative one
(`merge_refinements`). -/
def mergeRefinements (pol : Bool) : Option (List Pred) → Option (List Pred) → Option (List Pred)
  | none, c => c
  | c, none => c
  | some p1, some p2 => some (if pol then p1.filter (p2.contains ·) else p1 ++ p2)

/-- Set-semantic equality on the refinement slot, mirroring `RefinementSet`. -/
def refinementsEqv : Option (List Pred) → Option (List Pred) → Bool
  | none, none => true
  | some p1, some p2 => p1.all (p2.contains ·) && p2.all (p1.contains ·)
  | _, _ => false

/-- `refinementsEqv`, read as mutual membership. -/
theorem refinementsEqv_iff {p q : List Pred} :
    refinementsEqv (some p) (some q) = true ↔ (∀ x ∈ p, x ∈ q) ∧ ∀ x ∈ q, x ∈ p := by
  simp only [refinementsEqv, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]

theorem refinementsEqv_refl (c : Option (List Pred)) : refinementsEqv c c = true := by
  rcases c with _ | p
  · rfl
  · exact refinementsEqv_iff.mpr ⟨fun _ h => h, fun _ h => h⟩

theorem refinementsEqv_symm {a b : Option (List Pred)} (h : refinementsEqv a b = true) :
    refinementsEqv b a = true := by
  rcases a with _ | p <;> rcases b with _ | q
  · rfl
  · exact absurd h (by simp [refinementsEqv])
  · exact absurd h (by simp [refinementsEqv])
  · exact refinementsEqv_iff.mpr (refinementsEqv_iff.mp h).symm

theorem refinementsEqv_trans {a b c : Option (List Pred)} (hab : refinementsEqv a b = true)
    (hbc : refinementsEqv b c = true) : refinementsEqv a c = true := by
  rcases a with _ | p <;> rcases b with _ | q <;> rcases c with _ | r
  case none.none.none => rfl
  case some.some.some =>
    obtain ⟨hpq, hqp⟩ := refinementsEqv_iff.mp hab
    obtain ⟨hqr, hrq⟩ := refinementsEqv_iff.mp hbc
    exact refinementsEqv_iff.mpr ⟨fun x hx => hqr x (hpq x hx), fun x hx => hqp x (hrq x hx)⟩
  -- Every remaining case has one side `none` and the other `some`, which
  -- `refinementsEqv` refuses.
  all_goals simp_all [refinementsEqv]

/-- The two present-set cases, read as membership: what every law below reduces
to once the `none` identity arms are out of the way. -/
private theorem mergeRefinements_mem (pol : Bool) (p q : List Pred) (x : Pred) :
    (x ∈ (mergeRefinements pol (some p) (some q)).getD [] ↔
      if pol then x ∈ p ∧ x ∈ q else x ∈ p ∨ x ∈ q) := by
  cases pol <;>
    simp only [mergeRefinements, Bool.false_eq_true, reduceIte, Option.getD_some, List.mem_append,
      List.mem_filter, List.contains_iff_mem]

theorem mergeRefinements_comm (pol : Bool) (a b : Option (List Pred)) :
    refinementsEqv (mergeRefinements pol a b) (mergeRefinements pol b a) = true := by
  rcases a with _ | p <;> rcases b with _ | q <;>
    first
    | exact refinementsEqv_refl _
    | skip
  cases pol <;>
    simp only [mergeRefinements, Bool.false_eq_true, reduceIte] <;>
    refine refinementsEqv_iff.mpr ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
    simp only [List.mem_append, List.mem_filter, List.contains_iff_mem] at hx ⊢ <;>
    first
    | exact hx.symm
    | exact ⟨hx.2, hx.1⟩

theorem mergeRefinements_idem (pol : Bool) (a : Option (List Pred)) :
    refinementsEqv (mergeRefinements pol a a) a = true := by
  rcases a with _ | p
  · rfl
  cases pol <;>
    simp only [mergeRefinements, Bool.false_eq_true, reduceIte] <;>
    refine refinementsEqv_iff.mpr ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
    simp only [List.mem_append, List.mem_filter, List.contains_iff_mem] at hx ⊢ <;>
    first
    | exact hx.elim id id
    | exact Or.inl hx
    | exact hx.1
    | exact ⟨hx, hx⟩

theorem mergeRefinements_assoc (pol : Bool) (a b c : Option (List Pred)) :
    refinementsEqv (mergeRefinements pol (mergeRefinements pol a b) c)
      (mergeRefinements pol a (mergeRefinements pol b c)) = true := by
  rcases a with _ | p <;> rcases b with _ | q <;> rcases c with _ | r <;>
    first
    | exact refinementsEqv_refl _
    | skip
  cases pol <;>
    simp only [mergeRefinements, Bool.false_eq_true, reduceIte] <;>
    refine refinementsEqv_iff.mpr ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
    simp only [List.mem_append, List.mem_filter, List.contains_iff_mem] at hx ⊢ <;>
    first
    | exact or_assoc.mp hx
    | exact or_assoc.mpr hx
    | exact and_assoc.mp hx
    | exact and_assoc.mpr hx

theorem mergeRefinements_congr_left (pol : Bool) {a a' : Option (List Pred)}
    (b : Option (List Pred)) (h : refinementsEqv a a' = true) :
    refinementsEqv (mergeRefinements pol a b) (mergeRefinements pol a' b) = true := by
  rcases a with _ | p <;> rcases a' with _ | p'
  · exact refinementsEqv_refl _
  · exact absurd h (by simp [refinementsEqv])
  · exact absurd h (by simp [refinementsEqv])
  rcases b with _ | q
  · exact h
  obtain ⟨hpp, hpp'⟩ := refinementsEqv_iff.mp h
  cases pol <;>
    simp only [mergeRefinements, Bool.false_eq_true, reduceIte] <;>
    refine refinementsEqv_iff.mpr ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
    simp only [List.mem_append, List.mem_filter, List.contains_iff_mem] at hx ⊢
  · exact hx.imp (hpp x) id
  · exact hx.imp (hpp' x) id
  · exact ⟨hpp x hx.1, hx.2⟩
  · exact ⟨hpp' x hx.1, hx.2⟩

/-- The kind join at the head of `CompactFun::merge`: `unknown` is the identity
(nothing *required* a kind on that side, so the other side's answer stands),
`conflict` is absorbing, a kind meeting itself is itself, and the two concrete
kinds are incomparable — neither reading stands in for the other. One operation
for both polarities. -/
def joinKind : KindM → KindM → KindM
  | .conflict, _ => .conflict
  | _, .conflict => .conflict
  | .unknown, k => k
  | k, .unknown => k
  | k1, k2 => if k1 == k2 then k1 else .conflict

theorem joinKind_comm (a b : KindM) : joinKind a b = joinKind b a := by
  cases a <;> cases b <;> rfl

theorem joinKind_assoc (a b c : KindM) :
    joinKind (joinKind a b) c = joinKind a (joinKind b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem joinKind_idem (a : KindM) : joinKind a a = a := by
  cases a <;> rfl

/-- Mirror of the ground fragment of `compact.rs :: CompactType`.

The function slot is `(kind, domain, codomain)` with `domain : Option CTy` —
`some d` is a single domain alternative, `none` is "two or more distinct
alternatives" (see the module docs for why the tail of `union_domains`' list
is diagnostic-only). `recF`/`varT` mirror the `Option<BTreeMap<..>>` fields:
`none` is the merge identity ("no component here"), `some []` the absorbing
empty shape — the distinction `compact.rs` documents as load-bearing. -/
inductive CTy where
  | mk (atoms : List Atom)
       (recF : Option (List (FieldKey × CTy)))
       (varT : Option (List (FieldKey × CTy)))
       (fn : Option (KindM × List CTy × CTy))
       (refinements : Option (List Pred))
deriving Repr

namespace CTy

/-- `sizeOf` of a looked-up payload is below the map's. -/
theorem lookup_sizeOf {m : List (FieldKey × CTy)} {k : FieldKey} {w : CTy}
    (h : m.lookup k = some w) : sizeOf w < sizeOf m := by
  induction m with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    rw [List.lookup] at h
    split at h
    · cases h
      cases hd
      simp
      omega
    · have := ih h
      cases hd
      simp
      omega

/-! ## The equivalence (`CompactType`'s `PartialEq`) -/

mutual

/-- Set-semantic equality, mirroring `CompactType`'s `PartialEq` (see module
docs). Defined *before* `merge` because the merge's domain-dedup gate uses it,
exactly as `union_domains` uses `PartialEq`. -/
def eqv : CTy → CTy → Bool
  | .mk a1 r1 v1 f1 c1, .mk a2 r2 v2 f2 c2 =>
    a1.all (a2.contains ·) && a2.all (a1.contains ·)
      && (match r1, r2 with
          | none, none => true
          | some m1, some m2 =>
            subKeys m1 m2 (m1.map Prod.fst) && subKeys m2 m1 (m2.map Prod.fst)
          | _, _ => false)
      && (match v1, v2 with
          | none, none => true
          | some m1, some m2 =>
            subKeys m1 m2 (m1.map Prod.fst) && subKeys m2 m1 (m2.map Prod.fst)
          | _, _ => false)
      && (match f1, f2 with
          | none, none => true
          | some (k1, d1, c1), some (k2, d2, c2) =>
            k1 == k2
              && (subDoms d2 d1 && subDoms d1 d2)
              && eqv c1 c2
          | _, _ => false)
      && refinementsEqv c1 c2
termination_by a b => (sizeOf a + sizeOf b, 0)

/-- Whether `m` holds an `eqv` partner for `d`. Structural in `m` so the
termination measure can see each element. -/
def anyEqv (d : CTy) : List CTy → Bool
  | [] => false
  | y :: ys => eqv d y || anyEqv d ys
termination_by m => (sizeOf d + sizeOf m, 0)
decreasing_by all_goals (apply Prod.Lex.left; simp; omega)

/-- Containment of one alternative list in another, over a worklist. The domain
alternatives compare as a **set**: `union_domains` deduplicates them, and their
only readers are a `Data` slot's refusal to have more than one and a `Compute`
slot's commutative meet-fold at coalesce, so their order carries no information.
This is the one place `eqv` is deliberately coarser than `CompactFun`'s derived
`PartialEq`, which compares the `Vec` positionally. -/
def subDoms (m2 : List CTy) : List CTy → Bool
  | [] => true
  | d :: ds => anyEqv d m2 && subDoms m2 ds
termination_by ds => (sizeOf m2 + sizeOf ds, ds.length)
decreasing_by all_goals (apply Prod.Lex.left; simp; omega)

/-- Keyed containment over a key worklist: every key in `ks` resolves in both
maps to `eqv` payloads. Driven by `lookup` on **both** sides (not the peeled
entry), so a shadowed duplicate binding is unobservable — mirroring
`BTreeMap`, which cannot hold one. `eqv` calls it with `ks = m1.map Prod.fst`
in both directions. -/
def subKeys (m1 m2 : List (FieldKey × CTy)) : List FieldKey → Bool
  | [] => true
  | k :: ks =>
    (match h1 : m1.lookup k, h2 : m2.lookup k with
     | some v, some w => eqv v w
     | _, _ => false)
      && subKeys m1 m2 ks
termination_by ks => (sizeOf m1 + sizeOf m2, ks.length)
decreasing_by
  · have hv := lookup_sizeOf h1
    have hw := lookup_sizeOf h2
    apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    simp

end

/-! ## The domain alternatives, read as a set

`eqv`'s fn clause compares them with `subDoms`, and every law below reasons
through `anyEqv_iff`/`subDoms_iff`, so the representation is never touched again.
This is the one place `eqv` is deliberately coarser than `CompactFun`'s derived
`PartialEq`, which compares the `Vec` positionally: `union_domains` deduplicates
the alternatives and their only readers are a `Data` slot's refusal to hold more
than one and a `Compute` slot's commutative meet-fold at coalesce, so their order
carries no information. That the order is unobservable downstream is what
`tests/type_merge_fuzz.rs` checks, by comparing coalesced outcomes across arrival
orders. -/

/-- Set equality on the alternatives, the shape `eqv`'s fn clause checks. -/
def domsEqv (a b : List CTy) : Bool := subDoms b a && subDoms a b

theorem anyEqv_iff {d : CTy} {m : List CTy} :
    anyEqv d m = true ↔ ∃ y ∈ m, eqv d y = true := by
  induction m with
  | nil => simp [anyEqv]
  | cons y ys ih =>
    rw [anyEqv, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨z, hz, hzy⟩)
      · exact ⟨y, by simp, h⟩
      · exact ⟨z, by simp [hz], hzy⟩
    · rintro ⟨z, hz, hzy⟩
      rcases List.mem_cons.mp hz with h | h
      · exact Or.inl (h ▸ hzy)
      · exact Or.inr ⟨z, h, hzy⟩

theorem subDoms_iff {m2 ds : List CTy} :
    subDoms m2 ds = true ↔ ∀ x ∈ ds, ∃ y ∈ m2, eqv x y = true := by
  induction ds with
  | nil => simp [subDoms]
  | cons d ds ih =>
    rw [subDoms, Bool.and_eq_true, ih, anyEqv_iff]
    constructor
    · rintro ⟨hd, htl⟩ x hx
      rcases List.mem_cons.mp hx with h | h
      · exact h ▸ hd
      · exact htl x h
    · intro h
      exact ⟨h d (by simp), fun x hx => h x (by simp [hx])⟩

/-- `domsEqv` and the pair of containments its `Bool` unfolds to — the shape a
proof gets after `simp only [Bool.and_eq_true]` splits `eqv`'s clause. -/
theorem domsEqv_iff_and {a b : List CTy} :
    domsEqv a b = true ↔ subDoms b a = true ∧ subDoms a b = true := by
  rw [domsEqv, Bool.and_eq_true]

theorem domsEqv_iff {a b : List CTy} :
    domsEqv a b = true ↔
      (∀ x ∈ a, ∃ y ∈ b, eqv x y = true) ∧ ∀ y ∈ b, ∃ x ∈ a, eqv y x = true := by
  rw [domsEqv, Bool.and_eq_true, subDoms_iff, subDoms_iff]

theorem domsEqv_symm {a b : List CTy} (h : domsEqv a b = true) : domsEqv b a = true :=
  domsEqv_iff.mpr (domsEqv_iff.mp h).symm

/-! ## The merge -/

mutual

/-- Mirror of `CompactType::merge` (ground fragment). `pol` is the polarity:
positive merges are joins (types union, refinements/record-keys intersect, variant
tags union), negative merges are meets (the duals). -/
def merge (pol : Bool) : CTy → CTy → CTy
  | .mk a1 r1 v1 f1 c1, .mk a2 r2 v2 f2 c2 =>
    .mk (a1 ++ a2)
        (match r1, r2 with
         | none, r | r, none => r
         | some m1, some m2 =>
           some
             (if pol then interMap pol m1 m2
              else unionMapGo pol m1 m2 ++ m2.filter (fun kw => (m1.lookup kw.1).isNone)))
        (match v1, v2 with
         | none, v | v, none => v
         | some m1, some m2 =>
           some
             (if pol then unionMapGo pol m1 m2 ++ m2.filter (fun kw => (m1.lookup kw.1).isNone)
              else interMap pol m1 m2))
        (match f1, f2 with
         | none, f | f, none => f
         | some s1, some s2 => some (mergeFun pol s1 s2))
        (mergeRefinements pol c1 c2)
termination_by a b => sizeOf a + sizeOf b

/-- Keyed merge, intersecting keys (records at positive polarity, variants at
negative): keep only keys present on both sides, payloads merged at the outer
polarity (covariant depth — `merge_keyed` with `intersect_keys = true`). -/
def interMap (pol : Bool) :
    List (FieldKey × CTy) → List (FieldKey × CTy) → List (FieldKey × CTy)
  | [], _ => []
  | (k, v) :: rest, m2 =>
    match h : m2.lookup k with
    | some w => (k, merge pol v w) :: interMap pol rest m2
    | none => interMap pol rest m2
termination_by a b => sizeOf a + sizeOf b
decreasing_by
  · have := lookup_sizeOf h
    simp
    omega
  · simp
    omega
  · simp
    omega

/-- The `m1`-side of the key-uniting merge (records at negative polarity,
variants at positive — `merge_keyed` with `intersect_keys = false`): every key
of `m1`, merged with `m2`'s payload when present. The full union appends
`m2`'s leftover keys: `unionMapGo pol m1 m2 ++ m2.filter (·.1 ∉ keys m1)` —
see [`unionMap`]. -/
def unionMapGo (pol : Bool) :
    List (FieldKey × CTy) → List (FieldKey × CTy) → List (FieldKey × CTy)
  | [], _ => []
  | (k, v) :: rest, m2 =>
    (k,
      match h : m2.lookup k with
      | some w => merge pol v w
      | none => v)
      :: unionMapGo pol rest m2
termination_by a b => sizeOf a + sizeOf b
decreasing_by
  · have := lookup_sizeOf h
    simp
    omega
  · simp
    omega

/-- The contravariant domain meet: defined when each side has **one distinct
alternative**, and undefined otherwise — `compact.rs` flags the latter at
coalesce. Only ever used at a negative position, where `merge`'s polarity flip
makes the inner merge positive.

"One distinct alternative" rather than "one alternative" because `DomainSet`
deduplicates, so on the lists it produces the two conditions agree — and only the
first is invisible to `domsEqv`, which cannot tell `[x]` from `[x, x]`. Testing
the length instead would make the merge fail to be a congruence. -/
def meetDoms : List CTy → List CTy → Option (List CTy)
  | x :: xs, y :: ys =>
    if subDoms [x] xs && subDoms [y] ys then some [merge true x y] else none
  | _, _ => none
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp; omega)

/-- Mirror of `union_domains`: the alternatives of both sides, deduplicated by
`eqv` — the same equality `contains` uses. Never a meet: a `Data` domain *is* the
data, and whether the slot reads as data is not known here. -/
def unionDoms (a b : List CTy) : List CTy :=
  a ++ b.filter (fun d => !anyEqv d a)

/-- Mirror of `CompactFun::merge` (see module docs for the `Option CTy`
domain encoding and the dropped binder/diagnostic payloads).

The kinds join in the [`KindM`] semilattice, the same operation at both
polarities. The domains are then combined by *polarity alone*: a positive join
accumulates the alternatives and a negative merge takes the contravariant meet.
Neither reads the kind, which is what makes the operation associative — the kind
a slot ends at is not known until the last bound has merged, so a domain rule
selected from it would let association decide the outcome. `compact.rs` defers
the kind's own rule to `coalesce_compact_go`.

The dedup gate on the accumulated alternatives is `eqv` — the same equality
`union_domains`' `contains` uses — which is what keeps the whole algebra
quotient-compatible. -/
def mergeFun (pol : Bool) :
    KindM × List CTy × CTy → KindM × List CTy × CTy → KindM × List CTy × CTy
  | (k1, d1, c1), (k2, d2, c2) =>
    let cod := merge pol c1 c2
    let k := joinKind k1 k2
    if k == .conflict then
      -- A conflicted slot's payload is diagnostic; coalesce reports rather than
      -- reads it, so the model drops it.
      (.conflict, [], cod)
    else if pol then
      -- The alternatives accumulate. What several of them *mean* is the resolved
      -- kind's question, answered at coalesce.
      (k, unionDoms d1 d2, cod)
    else
      -- Negative: the contravariant meet.
      match meetDoms d1 d2 with
      | some ds => (k, ds, cod)
      | none => (.conflict, [], cod)
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp; omega)



end

/-- Keyed merge, uniting keys: keys of either side, payloads merged where both
are present. (Defined outside the mutual block — it makes no recursive call of
its own, and the well-founded measure cannot see through a same-size wrapper;
`merge` inlines this same expression.) -/
def unionMap (pol : Bool) (m1 m2 : List (FieldKey × CTy)) :
    List (FieldKey × CTy) :=
  unionMapGo pol m1 m2 ++ m2.filter (fun kw => (m1.lookup kw.1).isNone)

/-! ## Pointwise readings

Everything below reasons about maps through `lookup` — the merged maps are
characterized pointwise (`interMap_lookup`, `unionMap_lookup`), and `subKeys`
unfolds to a per-key statement (`subKeys_iff`), so the set-level proofs never
touch the association-list representation again. -/

/-- A `lookup` hit means the key occurs in the key list. -/
theorem mem_keys_of_lookup {m : List (FieldKey × CTy)} {k : FieldKey} {v : CTy}
    (h : m.lookup k = some v) : k ∈ m.map Prod.fst := by
  induction m with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    rw [List.lookup] at h
    split at h
    · rename_i heq
      simp at heq
      simp [heq]
    · simp only [List.map_cons, List.mem_cons]
      exact Or.inr (ih h)

/-- A key in the key list has a `lookup` hit. -/
theorem lookup_of_mem_keys {m : List (FieldKey × CTy)} {k : FieldKey}
    (h : k ∈ m.map Prod.fst) : (m.lookup k).isSome := by
  induction m with
  | nil => simp at h
  | cons hd tl ih =>
    rw [List.lookup]
    split
    · simp
    · rename_i hne
      simp at hne
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h hne
      · exact ih h

/-- `subKeys`, read per key. -/
theorem subKeys_iff {m1 m2 : List (FieldKey × CTy)} {ks : List FieldKey} :
    subKeys m1 m2 ks = true ↔
      ∀ k ∈ ks, ∃ v w, m1.lookup k = some v ∧ m2.lookup k = some w ∧ eqv v w = true := by
  induction ks with
  | nil => simp [subKeys]
  | cons k ks ih =>
    rw [subKeys, Bool.and_eq_true, ih]
    constructor
    · intro ⟨hhead, htail⟩ k' hk'
      rcases List.mem_cons.mp hk' with h | h
      · subst h
        split at hhead
        · rename_i v w h1 h2
          exact ⟨v, w, h1, h2, hhead⟩
        · exact absurd hhead (by simp)
      · exact htail k' h
    · intro h
      obtain ⟨v, w, h1, h2, hvw⟩ := h k (by simp)
      refine ⟨?_, fun k' hk' => h k' (by simp [hk'])⟩
      split
      · rename_i v' w' h1' h2'
        rw [h1] at h1'
        rw [h2] at h2'
        cases h1'
        cases h2'
        exact hvw
      · rename_i hno
        exact (hno v w (by rw [h1]) (by rw [h2])).elim

/-! ## `eqv` is an equivalence relation -/

theorem eqv_refl : (t : CTy) → eqv t t = true
  | .mk a r v f c => by
    have hmap : ∀ (m : List (FieldKey × CTy)), sizeOf m < sizeOf (CTy.mk a r v f c) →
        subKeys m m (m.map Prod.fst) = true := by
      intro m hm
      rw [subKeys_iff]
      intro k hk
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (lookup_of_mem_keys hk)
      have hsz : sizeOf w < sizeOf (CTy.mk a r v f c) :=
        Nat.lt_trans (lookup_sizeOf hw) hm
      exact ⟨w, w, hw, hw, eqv_refl w⟩
    rw [eqv.eq_def]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp [List.all_eq_true]
    · simp [List.all_eq_true]
    · rcases r with _ | m
      · rfl
      · have hm : sizeOf m < sizeOf (CTy.mk a (some m) v f c) := by
          simp
          omega
        simp [hmap m hm]
    · rcases v with _ | m
      · rfl
      · have hm : sizeOf m < sizeOf (CTy.mk a r (some m) f c) := by
          simp
          omega
        simp [hmap m hm]
    · rcases f with _ | ⟨k, d, cod⟩
      · rfl
      · have hszc : sizeOf cod < sizeOf (CTy.mk a r v (some (k, d, cod)) c) := by
          simp
          omega
        have hd : subDoms d d = true := by
          refine subDoms_iff.mpr fun x hx => ⟨x, hx, ?_⟩
          have hszx : sizeOf x < sizeOf (CTy.mk a r v (some (k, d, cod)) c) := by
            have := List.sizeOf_lt_of_mem hx
            simp
            omega
          exact eqv_refl x
        simp [hd, eqv_refl cod]
    · exact refinementsEqv_refl c
termination_by t => sizeOf t
decreasing_by all_goals omega

/-- Unfolded, pointwise reading of the map clause both `eqv` map slots use. -/
theorem mapClause_iff {m1 m2 : List (FieldKey × CTy)} :
    (subKeys m1 m2 (m1.map Prod.fst) && subKeys m2 m1 (m2.map Prod.fst)) = true ↔
      (∀ k, (m1.lookup k).isSome ↔ (m2.lookup k).isSome) ∧
        (∀ k v w, m1.lookup k = some v → m2.lookup k = some w → eqv v w = true)
          ∧ ∀ k v w, m1.lookup k = some v → m2.lookup k = some w → eqv w v = true := by
  rw [Bool.and_eq_true, subKeys_iff, subKeys_iff]
  constructor
  · intro ⟨h12, h21⟩
    refine ⟨fun k => ?_, fun k v w hv hw => ?_, fun k v w hv hw => ?_⟩
    · constructor
      · intro h1
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h1
        obtain ⟨_, w, _, hw, _⟩ := h12 k (mem_keys_of_lookup hv)
        simp [hw]
      · intro h2
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h2
        obtain ⟨_, v, _, hv, _⟩ := h21 k (mem_keys_of_lookup hw)
        simp [hv]
    · obtain ⟨v', w', hv', hw', hvw⟩ := h12 k (mem_keys_of_lookup hv)
      rw [hv] at hv'
      rw [hw] at hw'
      cases hv'
      cases hw'
      exact hvw
    · obtain ⟨w', v', hw', hv', hwv⟩ := h21 k (mem_keys_of_lookup hw)
      rw [hv] at hv'
      rw [hw] at hw'
      cases hv'
      cases hw'
      exact hwv
  · intro ⟨hdom, hfwd, hbwd⟩
    constructor
    · intro k hk
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (lookup_of_mem_keys hk)
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((hdom k).mp (by simp [hv]))
      exact ⟨v, w, hv, hw, hfwd k v w hv hw⟩
    · intro k hk
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (lookup_of_mem_keys hk)
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((hdom k).mpr (by simp [hw]))
      exact ⟨w, v, hw, hv, hbwd k v w hv hw⟩

theorem eqv_symm : (a b : CTy) → eqv a b = true → eqv b a = true
  | .mk a1 r1 v1 f1 c1, .mk a2 r2 v2 f2 c2 => by
    intro h
    rw [eqv.eq_def] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, hr⟩, hv⟩, hf⟩, hc⟩ := h
    rw [eqv.eq_def]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨h2, h1⟩, ?_⟩, ?_⟩, ?_⟩, refinementsEqv_symm hc⟩
    · rcases r1 with _ | m1 <;> rcases r2 with _ | m2 <;> simp_all
    · rcases v1 with _ | m1 <;> rcases v2 with _ | m2 <;> simp_all
    · rcases f1 with _ | ⟨k1, d1, cod1⟩ <;> rcases f2 with _ | ⟨k2, d2, cod2⟩
      · rfl
      · simp at hf
      · simp at hf
      · simp only [Bool.and_eq_true] at hf
        obtain ⟨⟨hk, hd⟩, hcod⟩ := hf
        simp only [Bool.and_eq_true]
        have hszc : sizeOf cod2 + sizeOf cod1 <
            sizeOf (CTy.mk a2 r2 v2 (some (k2, d2, cod2)) c2) +
              sizeOf (CTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1) := by
          simp
          omega
        refine ⟨⟨?_, ?_⟩, eqv_symm cod1 cod2 hcod⟩
        · simp at hk
          simp [hk]
        · exact domsEqv_iff_and.mp (domsEqv_symm (domsEqv_iff_and.mpr hd))
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals omega

theorem eqv_trans : (a b c : CTy) → eqv a b = true → eqv b c = true → eqv a c = true
  | .mk a1 r1 v1 f1 c1, .mk a2 r2 v2 f2 c2, .mk a3 r3 v3 f3 c3 => by
    intro hab hbc
    rw [eqv.eq_def] at hab hbc
    simp only [Bool.and_eq_true] at hab hbc
    obtain ⟨⟨⟨⟨⟨hab1, hab2⟩, habr⟩, habv⟩, habf⟩, habc⟩ := hab
    obtain ⟨⟨⟨⟨⟨hbc1, hbc2⟩, hbcr⟩, hbcv⟩, hbcf⟩, hbcc⟩ := hbc
    rw [eqv.eq_def]
    simp only [Bool.and_eq_true]
    have hsub : ∀ {α : Type} [inst : DecidableEq α] (x y z : List α),
        (x.all (y.contains ·)) = true → (y.all (z.contains ·)) = true →
          (x.all (z.contains ·)) = true := by
      intro α _ x y z hxy hyz
      simp only [List.all_eq_true] at *
      intro p hp
      have h1 := hxy p hp
      simp only [List.contains_iff_mem] at h1 ⊢
      have h2 := hyz _ h1
      simpa using h2
    have hmapTrans : ∀ (m1 m2 m3 : List (FieldKey × CTy)),
        sizeOf m1 < sizeOf (CTy.mk a1 r1 v1 f1 c1) →
        sizeOf m3 < sizeOf (CTy.mk a3 r3 v3 f3 c3) →
        (subKeys m1 m2 (m1.map Prod.fst) && subKeys m2 m1 (m2.map Prod.fst)) = true →
        (subKeys m2 m3 (m2.map Prod.fst) && subKeys m3 m2 (m3.map Prod.fst)) = true →
        (subKeys m1 m3 (m1.map Prod.fst) && subKeys m3 m1 (m3.map Prod.fst)) = true := by
      intro m1 m2 m3 hs1 hs3 h12 h23
      rw [mapClause_iff] at h12 h23 ⊢
      obtain ⟨hdom12, hfwd12, hbwd12⟩ := h12
      obtain ⟨hdom23, hfwd23, hbwd23⟩ := h23
      refine ⟨fun k => (hdom12 k).trans (hdom23 k), fun k x z hx hz => ?_, fun k x z hx hz => ?_⟩
      · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ((hdom12 k).mp (by simp [hx]))
        have hxy := hfwd12 k x y hx hy
        have hyz := hfwd23 k y z hy hz
        have hszx : sizeOf x < sizeOf (CTy.mk a1 r1 v1 f1 c1) :=
          Nat.lt_trans (lookup_sizeOf hx) hs1
        have hszz : sizeOf z < sizeOf (CTy.mk a3 r3 v3 f3 c3) :=
          Nat.lt_trans (lookup_sizeOf hz) hs3
        exact eqv_trans x y z hxy hyz
      · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ((hdom12 k).mp (by simp [hx]))
        have hzy := hbwd23 k y z hy hz
        have hyx := hbwd12 k x y hx hy
        have hszx : sizeOf x < sizeOf (CTy.mk a1 r1 v1 f1 c1) :=
          Nat.lt_trans (lookup_sizeOf hx) hs1
        have hszz : sizeOf z < sizeOf (CTy.mk a3 r3 v3 f3 c3) :=
          Nat.lt_trans (lookup_sizeOf hz) hs3
        exact eqv_trans z y x hzy hyx
    refine ⟨⟨⟨⟨⟨hsub a1 a2 a3 hab1 hbc1, hsub a3 a2 a1 hbc2 hab2⟩, ?_⟩, ?_⟩, ?_⟩,
      refinementsEqv_trans habc hbcc⟩
    · rcases r1 with _ | m1 <;> rcases r2 with _ | m2 <;> rcases r3 with _ | m3 <;>
        first
        | rfl
        | (simp at habr; done)
        | (simp at hbcr; done)
        | (exact hmapTrans m1 m2 m3 (by simp; omega) (by simp; omega) habr hbcr)
    · rcases v1 with _ | m1 <;> rcases v2 with _ | m2 <;> rcases v3 with _ | m3 <;>
        first
        | rfl
        | (simp at habv; done)
        | (simp at hbcv; done)
        | (exact hmapTrans m1 m2 m3 (by simp; omega) (by simp; omega) habv hbcv)
    · rcases f1 with _ | ⟨k1, d1, cod1⟩ <;> rcases f2 with _ | ⟨k2, d2, cod2⟩ <;>
        rcases f3 with _ | ⟨k3, d3, cod3⟩ <;>
        first
        | rfl
        | (simp at habf; done)
        | (simp at hbcf; done)
        | skip
      simp only [Bool.and_eq_true] at habf hbcf
      obtain ⟨⟨habk, habd⟩, habcod⟩ := habf
      obtain ⟨⟨hbck, hbcd⟩, hbccod⟩ := hbcf
      simp only [Bool.and_eq_true]
      have hszc : sizeOf cod1 + sizeOf cod3 <
          sizeOf (CTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1) +
            sizeOf (CTy.mk a3 r3 v3 (some (k3, d3, cod3)) c3) := by
        simp
        omega
      refine ⟨⟨?_, ?_⟩, eqv_trans cod1 cod2 cod3 habcod hbccod⟩
      · simp at habk hbck
        simp [habk, hbck]
      · obtain ⟨hab1, hab2⟩ := domsEqv_iff.mp (domsEqv_iff_and.mpr habd)
        obtain ⟨hbc1, hbc2⟩ := domsEqv_iff.mp (domsEqv_iff_and.mpr hbcd)
        refine domsEqv_iff_and.mp (domsEqv_iff.mpr ⟨fun x hx => ?_, fun z hz => ?_⟩)
        · obtain ⟨y, hy, hxy⟩ := hab1 x hx
          obtain ⟨w, hw, hyw⟩ := hbc1 y hy
          have hszd : sizeOf x + sizeOf w <
              sizeOf (CTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1) +
                sizeOf (CTy.mk a3 r3 v3 (some (k3, d3, cod3)) c3) := by
            have h1 := List.sizeOf_lt_of_mem hx
            have h2 := List.sizeOf_lt_of_mem hw
            simp
            omega
          exact ⟨w, hw, eqv_trans x y w hxy hyw⟩
        · obtain ⟨y, hy, hzy⟩ := hbc2 z hz
          obtain ⟨x, hx, hyx⟩ := hab2 y hy
          have hszd : sizeOf z + sizeOf x <
              sizeOf (CTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1) +
                sizeOf (CTy.mk a3 r3 v3 (some (k3, d3, cod3)) c3) := by
            have h1 := List.sizeOf_lt_of_mem hx
            have h2 := List.sizeOf_lt_of_mem hz
            simp
            omega
          exact ⟨x, hx, eqv_trans z y x hzy hyx⟩
termination_by a _ c => sizeOf a + sizeOf c
decreasing_by all_goals omega

/-! ## The domain alternatives: the algebra -/

/-! ### The negative arm, characterized

`meetDoms` is defined on a singleton pair and nowhere else, so every proof about
a negative merge splits on that once, here, rather than over nine list shapes. -/

/-- One distinct alternative: non-empty, with everything `eqv` to a member. The
property `meetDoms` is defined on, and `domsEqv`-invariant (`oneDistinct_congr`). -/
def OneDistinct (l : List CTy) : Prop := ∃ x, x ∈ l ∧ ∀ z ∈ l, eqv z x = true

/-- `meetDoms`, read off its definition: the payload is built from the two lists'
*heads*, so the swapped call and a congruent call name the same representatives. -/
theorem meetDoms_eq_some {a b ds : List CTy} (h : meetDoms a b = some ds) :
    ∃ x xs y ys, a = x :: xs ∧ b = y :: ys
      ∧ (subDoms [x] xs && subDoms [y] ys) = true ∧ ds = [merge true x y] := by
  rcases a with _ | ⟨x, xs⟩
  · exact absurd h (by simp [meetDoms])
  · rcases b with _ | ⟨y, ys⟩
    · exact absurd h (by simp [meetDoms])
    · rw [meetDoms] at h
      split at h
      · rename_i hgate
        cases h
        exact ⟨x, xs, y, ys, rfl, rfl, hgate, rfl⟩
      · exact absurd h (by simp)

theorem meetDoms_of_gate {x y : CTy} {xs ys : List CTy}
    (h : (subDoms [x] xs && subDoms [y] ys) = true) :
    meetDoms (x :: xs) (y :: ys) = some [merge true x y] := by
  rw [meetDoms, if_pos h]

/-- A single alternative on each side: what `wf` gives an input bound. -/
theorem meetDoms_single (x y : CTy) : meetDoms [x] [y] = some [merge true x y] :=
  meetDoms_of_gate (by simp [subDoms])

/-- Under the gate, the head is a representative of the whole list. -/
theorem all_eqv_head {x : CTy} {xs : List CTy} (h : subDoms [x] xs = true) :
    ∀ z ∈ x :: xs, eqv z x = true := by
  intro z hz
  rcases List.mem_cons.mp hz with h' | h'
  · exact h' ▸ eqv_refl x
  · obtain ⟨w, hw, hzw⟩ := (subDoms_iff.mp h) z h'
    exact (List.mem_singleton.mp hw) ▸ hzw

theorem oneDistinct_cons {x : CTy} {xs : List CTy} (h : subDoms [x] xs = true) :
    OneDistinct (x :: xs) := ⟨x, by simp, all_eqv_head h⟩

theorem gate_of_oneDistinct {x : CTy} {xs : List CTy} (h : OneDistinct (x :: xs)) :
    subDoms [x] xs = true := by
  obtain ⟨u, _, hall⟩ := h
  refine subDoms_iff.mpr fun z hz => ⟨x, by simp, ?_⟩
  exact eqv_trans _ _ _ (hall z (by simp [hz])) (eqv_symm _ _ (hall x (by simp)))

theorem oneDistinct_of_meetDoms {a b ds : List CTy} (h : meetDoms a b = some ds) :
    OneDistinct a ∧ OneDistinct b := by
  obtain ⟨x, xs, y, ys, ha, hb, hgate, _⟩ := meetDoms_eq_some h
  rw [Bool.and_eq_true] at hgate
  exact ⟨ha ▸ oneDistinct_cons hgate.1, hb ▸ oneDistinct_cons hgate.2⟩

theorem meetDoms_isSome_of {a b : List CTy} (ha : OneDistinct a) (hb : OneDistinct b) :
    ∃ ds, meetDoms a b = some ds := by
  rcases a with _ | ⟨x, xs⟩
  · exact absurd ha (by simp [OneDistinct])
  · rcases b with _ | ⟨y, ys⟩
    · exact absurd hb (by simp [OneDistinct])
    · exact ⟨_, meetDoms_of_gate (by
        rw [Bool.and_eq_true]
        exact ⟨gate_of_oneDistinct ha, gate_of_oneDistinct hb⟩)⟩

/-- The property is `domsEqv`-invariant, which is what keeps the negative arm a
congruence: `domsEqv` cannot tell `[x]` from `[x, x]`, and neither can this. -/
theorem oneDistinct_congr {a a' : List CTy} (h : domsEqv a a' = true) (ha : OneDistinct a) :
    OneDistinct a' := by
  obtain ⟨x, hx, hax⟩ := ha
  obtain ⟨h1, h2⟩ := domsEqv_iff.mp h
  obtain ⟨x', hx', hxx'⟩ := h1 x hx
  refine ⟨x', hx', fun z hz => ?_⟩
  obtain ⟨w, hw, hzw⟩ := h2 z hz
  exact eqv_trans _ _ _ hzw (eqv_trans _ _ _ (hax w hw) hxx')

theorem meetDoms_none_of_left {a b : List CTy} (h : ¬OneDistinct a) : meetDoms a b = none := by
  rcases hm : meetDoms a b with _ | ds
  · rfl
  · exact absurd (oneDistinct_of_meetDoms hm).1 h

theorem meetDoms_none_of_right {a b : List CTy} (h : ¬OneDistinct b) : meetDoms a b = none := by
  rcases hm : meetDoms a b with _ | ds
  · rfl
  · exact absurd (oneDistinct_of_meetDoms hm).2 h

/-- A singleton always has one distinct alternative — the shape the inner meet
leaves for the outer one. -/
theorem oneDistinct_single (x : CTy) : OneDistinct [x] := ⟨x, by simp, by simp [eqv_refl]⟩

theorem meetDoms_none_comm {a b : List CTy} (h : meetDoms a b = none) :
    meetDoms b a = none := by
  rcases hm : meetDoms b a with _ | ds
  · rfl
  · obtain ⟨hb, ha⟩ := oneDistinct_of_meetDoms hm
    obtain ⟨ds', hds'⟩ := meetDoms_isSome_of ha hb
    rw [hds'] at h
    exact absurd h (by simp)

theorem domsEqv_singleton {x y : CTy} (h : eqv x y = true) : domsEqv [x] [y] = true :=
  domsEqv_iff.mpr
    ⟨fun _ hx => ⟨y, by simp, by simpa [List.mem_singleton.mp hx] using h⟩,
     fun _ hy => ⟨x, by simp, by simpa [List.mem_singleton.mp hy] using eqv_symm _ _ h⟩⟩

theorem domsEqv_refl (a : List CTy) : domsEqv a a = true :=
  domsEqv_iff.mpr ⟨fun x hx => ⟨x, hx, eqv_refl x⟩, fun y hy => ⟨y, hy, eqv_refl y⟩⟩

theorem domsEqv_trans {a b c : List CTy} (hab : domsEqv a b = true)
    (hbc : domsEqv b c = true) : domsEqv a c = true := by
  obtain ⟨hab1, hab2⟩ := domsEqv_iff.mp hab
  obtain ⟨hbc1, hbc2⟩ := domsEqv_iff.mp hbc
  refine domsEqv_iff.mpr ⟨fun x hx => ?_, fun z hz => ?_⟩
  · obtain ⟨y, hy, hxy⟩ := hab1 x hx
    obtain ⟨w, hw, hyw⟩ := hbc1 y hy
    exact ⟨w, hw, eqv_trans _ _ _ hxy hyw⟩
  · obtain ⟨y, hy, hzy⟩ := hbc2 z hz
    obtain ⟨x, hx, hyx⟩ := hab2 y hy
    exact ⟨x, hx, eqv_trans _ _ _ hzy hyx⟩

/-- The union holds nothing new. -/
theorem mem_unionDoms {a b : List CTy} {x : CTy} (h : x ∈ unionDoms a b) :
    x ∈ a ∨ x ∈ b := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_filter.mp h).1

/-- …and loses nothing: the dedup only drops an alternative that already has a
partner. -/
theorem unionDoms_covers {a b : List CTy} {x : CTy} (h : x ∈ a ∨ x ∈ b) :
    ∃ y ∈ unionDoms a b, eqv x y = true := by
  rcases h with h | h
  · exact ⟨x, List.mem_append.mpr (Or.inl h), eqv_refl x⟩
  · rcases hk : anyEqv x a with _ | _
    · exact ⟨x, List.mem_append.mpr (Or.inr (List.mem_filter.mpr ⟨h, by simp [hk]⟩)),
        eqv_refl x⟩
    · obtain ⟨y, hy, hxy⟩ := anyEqv_iff.mp hk
      exact ⟨y, List.mem_append.mpr (Or.inl hy), hxy⟩

/-- Cover a member of any of three lists, through either nesting. -/
theorem unionDoms_coversR {a b c : List CTy} {x : CTy} (h : x ∈ a ∨ x ∈ b ∨ x ∈ c) :
    ∃ y ∈ unionDoms a (unionDoms b c), eqv x y = true := by
  rcases h with h | h
  · exact unionDoms_covers (Or.inl h)
  · obtain ⟨z, hz, hxz⟩ := unionDoms_covers (a := b) (b := c) h
    obtain ⟨w, hw, hzw⟩ := unionDoms_covers (a := a) (b := unionDoms b c) (Or.inr hz)
    exact ⟨w, hw, eqv_trans _ _ _ hxz hzw⟩

theorem unionDoms_coversL {a b c : List CTy} {x : CTy} (h : x ∈ a ∨ x ∈ b ∨ x ∈ c) :
    ∃ y ∈ unionDoms (unionDoms a b) c, eqv x y = true := by
  rcases h with h | h
  · obtain ⟨z, hz, hxz⟩ := unionDoms_covers (a := a) (b := b) (Or.inl h)
    obtain ⟨w, hw, hzw⟩ := unionDoms_covers (a := unionDoms a b) (b := c) (Or.inl hz)
    exact ⟨w, hw, eqv_trans _ _ _ hxz hzw⟩
  · rcases h with h | h
    · obtain ⟨z, hz, hxz⟩ := unionDoms_covers (a := a) (b := b) (Or.inr h)
      obtain ⟨w, hw, hzw⟩ := unionDoms_covers (a := unionDoms a b) (b := c) (Or.inl hz)
      exact ⟨w, hw, eqv_trans _ _ _ hxz hzw⟩
    · exact unionDoms_covers (Or.inr h)

theorem mem_unionDomsL {a b c : List CTy} {x : CTy} (h : x ∈ unionDoms (unionDoms a b) c) :
    x ∈ a ∨ x ∈ b ∨ x ∈ c := by
  rcases mem_unionDoms h with h | h
  · exact (mem_unionDoms h).imp id Or.inl
  · exact Or.inr (Or.inr h)

theorem mem_unionDomsR {a b c : List CTy} {x : CTy} (h : x ∈ unionDoms a (unionDoms b c)) :
    x ∈ a ∨ x ∈ b ∨ x ∈ c := by
  rcases mem_unionDoms h with h | h
  · exact Or.inl h
  · exact Or.inr (mem_unionDoms h)

theorem unionDoms_comm (a b : List CTy) : domsEqv (unionDoms a b) (unionDoms b a) = true :=
  domsEqv_iff.mpr
    ⟨fun _ hx => unionDoms_covers (mem_unionDoms hx).symm,
     fun _ hy => unionDoms_covers (mem_unionDoms hy).symm⟩

theorem unionDoms_idem (a : List CTy) : domsEqv (unionDoms a a) a = true :=
  domsEqv_iff.mpr
    ⟨fun x hx => ⟨x, (mem_unionDoms hx).elim id id, eqv_refl x⟩,
     fun _ hy => unionDoms_covers (Or.inl hy)⟩

theorem unionDoms_assoc (a b c : List CTy) :
    domsEqv (unionDoms (unionDoms a b) c) (unionDoms a (unionDoms b c)) = true :=
  domsEqv_iff.mpr
    ⟨fun _ hx => unionDoms_coversR (mem_unionDomsL hx),
     fun _ hy => unionDoms_coversL (mem_unionDomsR hy)⟩

theorem unionDoms_congr_left {a a' : List CTy} (b : List CTy) (h : domsEqv a a' = true) :
    domsEqv (unionDoms a b) (unionDoms a' b) = true := by
  obtain ⟨h1, h2⟩ := domsEqv_iff.mp h
  refine domsEqv_iff.mpr ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rcases mem_unionDoms hx with hm | hm
    · obtain ⟨x', hx', hxx'⟩ := h1 x hm
      obtain ⟨z, hz, hx'z⟩ := unionDoms_covers (a := a') (b := b) (Or.inl hx')
      exact ⟨z, hz, eqv_trans _ _ _ hxx' hx'z⟩
    · exact unionDoms_covers (Or.inr hm)
  · rcases mem_unionDoms hy with hm | hm
    · obtain ⟨y', hy', hyy'⟩ := h2 y hm
      obtain ⟨z, hz, hy'z⟩ := unionDoms_covers (a := a) (b := b) (Or.inl hy')
      exact ⟨z, hz, eqv_trans _ _ _ hyy' hy'z⟩
    · exact unionDoms_covers (Or.inr hm)


/-! ## Pointwise readings of the merged maps -/

/-- `interMap`, read through `lookup`: defined exactly when both sides have
the key, payload the merge of the two firsts. -/
theorem interMap_lookup {pol : Bool} {m1 m2 : List (FieldKey × CTy)} {k : FieldKey} :
    (interMap pol m1 m2).lookup k =
      match m1.lookup k, m2.lookup k with
      | some v, some w => some (merge pol v w)
      | _, _ => none := by
  induction m1 with
  | nil => simp [interMap, List.lookup]
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    rw [interMap]
    rcases h2 : m2.lookup k' with _ | w'
    · rcases hk : k == k' with _ | _
      · rw [List.lookup_cons]
        simp only [hk, ih]
      · have : k = k' := by simpa using hk
        subst this
        rw [ih, List.lookup_cons]
        simp [h2]
    · rcases hk : k == k' with _ | _
      · rw [List.lookup_cons, List.lookup_cons]
        simp only [hk, ih]
      · have : k = k' := by simpa using hk
        subst this
        rw [List.lookup_cons, List.lookup_cons]
        simp [h2]

/-- `unionMapGo`, read through `lookup`: defined exactly on `m1`'s keys,
payload merged with `m2`'s when present. -/
theorem unionMapGo_lookup {pol : Bool} {m1 m2 : List (FieldKey × CTy)} {k : FieldKey} :
    (unionMapGo pol m1 m2).lookup k =
      match m1.lookup k, m2.lookup k with
      | some v, some w => some (merge pol v w)
      | some v, none => some v
      | none, _ => none := by
  induction m1 with
  | nil => simp [unionMapGo, List.lookup]
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    rw [unionMapGo, List.lookup_cons, List.lookup_cons]
    rcases hk : k == k' with _ | _
    · simp only [hk, ih]
    · have : k = k' := by simpa using hk
      subst this
      rcases h2 : m2.lookup k with _ | w' <;> simp [h2]

/-- Looking up in the `m2` leftovers (keys absent from `m1`): the filter
predicate depends only on the key, so the first `k`-entry survives exactly
when `m1` lacks `k`. -/
theorem lookup_filter_leftover {m1 m2 : List (FieldKey × CTy)} {k : FieldKey} :
    (m2.filter (fun kw => (m1.lookup kw.1).isNone)).lookup k =
      if (m1.lookup k).isNone then m2.lookup k else none := by
  induction m2 with
  | nil => simp [List.lookup]
  | cons hd tl ih =>
    obtain ⟨k', w'⟩ := hd
    rw [List.filter_cons]
    rcases h1 : (m1.lookup k').isNone with _ | _
    · simp only [h1, Bool.false_eq_true, if_false, ih]
      rcases hk : k == k' with _ | _
      · rw [List.lookup_cons]
        simp [hk]
      · have : k = k' := by simpa using hk
        subst this
        rw [List.lookup_cons]
        simp [h1]
    · simp only [h1, if_true]
      rw [List.lookup_cons, List.lookup_cons]
      rcases hk : k == k' with _ | _
      · simp only [hk, ih]
      · have : k = k' := by simpa using hk
        subst this
        simp [h1, ih]

/-- `unionMap`, read through `lookup`. -/
theorem unionMap_lookup {pol : Bool} {m1 m2 : List (FieldKey × CTy)} {k : FieldKey} :
    (unionMap pol m1 m2).lookup k =
      match m1.lookup k, m2.lookup k with
      | some v, some w => some (merge pol v w)
      | some v, none => some v
      | none, some w => some w
      | none, none => none := by
  rw [unionMap, List.lookup_append, unionMapGo_lookup, lookup_filter_leftover]
  rcases h1 : m1.lookup k with _ | v <;> rcases h2 : m2.lookup k with _ | w <;> simp [h1, h2]

/-! ## The merge algebra: commutativity -/

/-- The dedup gate is symmetric as a *Bool*: `eqv x y = eqv y x`. -/
theorem eqv_comm_bool (x y : CTy) : eqv x y = eqv y x := by
  rcases h : eqv y x with _ | _
  · rcases h' : eqv x y with _ | _
    · rfl
    · rw [eqv_symm x y h'] at h
      exact h
  · exact eqv_symm y x h

/-- `subKeys` is reflexive on any map (shadowed duplicates are unobservable). -/
theorem subKeys_self (m : List (FieldKey × CTy)) : subKeys m m (m.map Prod.fst) = true := by
  rw [subKeys_iff]
  intro k hk
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (lookup_of_mem_keys hk)
  exact ⟨v, v, hv, hv, eqv_refl v⟩

/-- The function-slot equivalence, as a `Prop` (the shape `eqv`'s fn clause
checks, lifted off the Bool so case analyses stay readable). -/
def FunEqv : KindM × List CTy × CTy → KindM × List CTy × CTy → Prop
  | (k1, d1, c1), (k2, d2, c2) =>
    k1 = k2
      ∧ domsEqv d1 d2 = true
      ∧ eqv c1 c2 = true

/-- `FunEqv` is exactly `eqv`'s fn clause. -/
theorem funClause_of_funEqv {s1 s2 : KindM × List CTy × CTy} (h : FunEqv s1 s2) :
    (s1.1 == s2.1
      && domsEqv s1.2.1 s2.2.1
      && eqv s1.2.2 s2.2.2) = true := by
  obtain ⟨k1, d1, c1⟩ := s1
  obtain ⟨k2, d2, c2⟩ := s2
  obtain ⟨hk, hd, hc⟩ := h
  subst hk
  simp only [Bool.and_eq_true]
  refine ⟨⟨by simp, ?_⟩, hc⟩
  rcases d1 with _ | x <;> rcases d2 with _ | y <;> simp_all

mutual

theorem merge_comm (pol : Bool) : (a b : CTy) → eqv (merge pol a b) (merge pol b a) = true
  | .mk a1 r1 v1 f1 c1, .mk a2 r2 v2 f2 c2 => by
    -- Pointwise commutativity of the two keyed merges, packaged with the size
    -- bounds the recursive calls need.
    have hinter : ∀ (p : Bool) (m1 m2 : List (FieldKey × CTy)),
        (∀ x y k, m1.lookup k = some x → m2.lookup k = some y →
          eqv (merge p x y) (merge p y x) = true) →
        (subKeys (interMap p m1 m2) (interMap p m2 m1)
            ((interMap p m1 m2).map Prod.fst) &&
          subKeys (interMap p m2 m1) (interMap p m1 m2)
            ((interMap p m2 m1).map Prod.fst)) = true := by
      intro p m1 m2 hcomm
      rw [mapClause_iff]
      refine ⟨fun k => ?_, fun k x y hx hy => ?_, fun k x y hx hy => ?_⟩
      · rw [interMap_lookup, interMap_lookup]
        rcases m1.lookup k with _ | v <;> rcases m2.lookup k with _ | w <;> simp
      · rw [interMap_lookup] at hx hy
        rcases h1 : m1.lookup k with _ | v <;> rcases h2 : m2.lookup k with _ | w <;>
            rw [h1, h2] at hx hy <;> dsimp only at hx hy
        · exact absurd hx (by simp)
        · exact absurd hx (by simp)
        · exact absurd hx (by simp)
        · cases hx
          cases hy
          exact hcomm v w k h1 h2
      · rw [interMap_lookup] at hx hy
        rcases h1 : m1.lookup k with _ | v <;> rcases h2 : m2.lookup k with _ | w <;>
            rw [h1, h2] at hx hy <;> dsimp only at hx hy
        · exact absurd hx (by simp)
        · exact absurd hx (by simp)
        · exact absurd hx (by simp)
        · cases hx
          cases hy
          exact eqv_symm _ _ (hcomm v w k h1 h2)
    have hunion : ∀ (p : Bool) (m1 m2 : List (FieldKey × CTy)),
        (∀ x y k, m1.lookup k = some x → m2.lookup k = some y →
          eqv (merge p x y) (merge p y x) = true) →
        (subKeys (unionMap p m1 m2) (unionMap p m2 m1)
            ((unionMap p m1 m2).map Prod.fst) &&
          subKeys (unionMap p m2 m1) (unionMap p m1 m2)
            ((unionMap p m2 m1).map Prod.fst)) = true := by
      intro p m1 m2 hcomm
      rw [mapClause_iff]
      refine ⟨fun k => ?_, fun k x y hx hy => ?_, fun k x y hx hy => ?_⟩
      · rw [unionMap_lookup, unionMap_lookup]
        rcases m1.lookup k with _ | v <;> rcases m2.lookup k with _ | w <;> simp
      · rw [unionMap_lookup] at hx hy
        rcases h1 : m1.lookup k with _ | v <;> rcases h2 : m2.lookup k with _ | w <;>
            rw [h1, h2] at hx hy <;> dsimp only at hx hy
        · exact absurd hx (by simp)
        · cases hx
          cases hy
          exact eqv_refl _
        · cases hx
          cases hy
          exact eqv_refl _
        · cases hx
          cases hy
          exact hcomm v w k h1 h2
      · rw [unionMap_lookup] at hx hy
        rcases h1 : m1.lookup k with _ | v <;> rcases h2 : m2.lookup k with _ | w <;>
            rw [h1, h2] at hx hy <;> dsimp only at hx hy
        · exact absurd hx (by simp)
        · cases hx
          cases hy
          exact eqv_refl _
        · cases hx
          cases hy
          exact eqv_refl _
        · cases hx
          cases hy
          exact eqv_symm _ _ (hcomm v w k h1 h2)
    rw [merge.eq_def, merge.eq_def, eqv.eq_def]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp only [List.all_eq_true, List.contains_iff_mem, List.mem_append]
      intro x hx
      exact hx.symm
    · simp only [List.all_eq_true, List.contains_iff_mem, List.mem_append]
      intro x hx
      exact hx.symm
    · rcases r1 with _ | m1 <;> rcases r2 with _ | m2
      · rfl
      · simp [subKeys_self]
      · simp [subKeys_self]
      · have hpay : ∀ x y k, m1.lookup k = some x → m2.lookup k = some y →
            eqv (merge pol x y) (merge pol y x) = true := by
          intro x y k hx hy
          have hszx := lookup_sizeOf hx
          have hszy := lookup_sizeOf hy
          exact merge_comm pol x y
        cases pol
        · simpa [unionMap] using hunion false m1 m2 hpay
        · simpa [unionMap] using hinter true m1 m2 hpay
    · rcases v1 with _ | m1 <;> rcases v2 with _ | m2
      · rfl
      · simp [subKeys_self]
      · simp [subKeys_self]
      · have hpay : ∀ x y k, m1.lookup k = some x → m2.lookup k = some y →
            eqv (merge pol x y) (merge pol y x) = true := by
          intro x y k hx hy
          have hszx := lookup_sizeOf hx
          have hszy := lookup_sizeOf hy
          exact merge_comm pol x y
        cases pol
        · simpa [unionMap] using hinter false m1 m2 hpay
        · simpa [unionMap] using hunion true m1 m2 hpay
    · rcases f1 with _ | ⟨k1, d1, cod1⟩ <;> rcases f2 with _ | ⟨k2, d2, cod2⟩
      · rfl
      · simpa [domsEqv] using funClause_of_funEqv (s1 := (k2, d2, cod2)) (s2 := (k2, d2, cod2))
          ⟨rfl, domsEqv_refl d2, eqv_refl cod2⟩
      · simpa [domsEqv] using funClause_of_funEqv (s1 := (k1, d1, cod1)) (s2 := (k1, d1, cod1))
          ⟨rfl, domsEqv_refl d1, eqv_refl cod1⟩
      · have hsz : sizeOf (k1, d1, cod1) + sizeOf (k2, d2, cod2) <
            sizeOf (CTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1) +
              sizeOf (CTy.mk a2 r2 v2 (some (k2, d2, cod2)) c2) := by
          simp
          omega
        simpa [domsEqv] using funClause_of_funEqv (mergeFun_comm pol (k1, d1, cod1) (k2, d2, cod2))
    · exact mergeRefinements_comm pol c1 c2
termination_by a b => (sizeOf a + sizeOf b, 1)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

theorem mergeFun_comm (pol : Bool) : (s1 s2 : KindM × List CTy × CTy) →
    FunEqv (mergeFun pol s1 s2) (mergeFun pol s2 s1)
  | (k1, d1, c1), (k2, d2, c2) => by
    have hszc : sizeOf c1 + sizeOf c2 < sizeOf (k1, d1, c1) + sizeOf (k2, d2, c2) := by
      simp
      omega
    have hcod : eqv (merge pol c1 c2) (merge pol c2 c1) = true := merge_comm pol c1 c2
    rw [mergeFun.eq_def, mergeFun.eq_def]
    simp only [joinKind_comm k2 k1]
    rcases hk : joinKind k1 k2 == KindM.conflict with _ | _ <;>
      simp only [hk, Bool.false_eq_true, reduceIte]
    case true => exact ⟨rfl, domsEqv_refl [], hcod⟩
    cases pol
    · -- Negative: the contravariant meet, defined only on singletons; every other
      -- shape conflicts on both sides.
      simp only [Bool.false_eq_true, reduceIte]
      rcases hm : meetDoms d1 d2 with _ | ds
      · rw [meetDoms_none_comm hm]
        exact ⟨rfl, domsEqv_refl [], hcod⟩
      · obtain ⟨x, xs, y, ys, ha, hb, hgate, hds⟩ := meetDoms_eq_some hm
        rw [Bool.and_eq_true] at hgate
        -- The swapped call meets the same two heads, with the gate mirrored.
        have hswap : meetDoms d2 d1 = some [merge true y x] := by
          rw [ha, hb]
          exact meetDoms_of_gate (by rw [Bool.and_eq_true]; exact ⟨hgate.2, hgate.1⟩)
        -- The bound stays in terms of the parameters, which is the form the
        -- termination measure is stated over; only the goal is rewritten.
        have hszd : sizeOf x + sizeOf y < sizeOf (k1, d1, c1) + sizeOf (k2, d2, c2) := by
          rw [ha, hb]
          simp
          omega
        rw [hswap, hds]
        exact ⟨rfl, domsEqv_singleton (merge_comm true x y), hcod⟩
    · -- Positive: the alternatives are a set, and the union of two sets is
      -- symmetric up to `eqv`.
      simp only [reduceIte]
      exact ⟨rfl, unionDoms_comm d1 d2, hcod⟩
termination_by s1 s2 => (sizeOf s1 + sizeOf s2, 0)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; omega)
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

end

/-! ## Depth

The measure materialization terminates on. `merge` combines contributions
pointwise and never nests one inside another, so a merged position is no deeper
than the deeper of its inputs (`merge_depth_le`) — which is what bounds
`coalesce`'s recursion through a `Compute` slot's folded alternatives, a call no
`sizeOf` measure reaches. -/

mutual

/-- Nesting depth: one for the position, plus the deepest child. Atoms and refinements
do not nest, so they do not count. -/
def depth : CTy → Nat
  | .mk _ recF varT fn _ =>
    1 + Nat.max (optMapDepth recF) (Nat.max (optMapDepth varT) (optFnDepth fn))

def optMapDepth : Option (List (FieldKey × CTy)) → Nat
  | none => 0
  | some m => mapDepth m

def mapDepth : List (FieldKey × CTy) → Nat
  | [] => 0
  | (_, w) :: rest => Nat.max (depth w) (mapDepth rest)

def optFnDepth : Option (KindM × List CTy × CTy) → Nat
  | none => 0
  | some (_, ds, cod) => Nat.max (listDepth ds) (depth cod)

def listDepth : List CTy → Nat
  | [] => 0
  | d :: ds => Nat.max (depth d) (listDepth ds)

end

/-! ### Reading `depth` -/

theorem depth_pos (t : CTy) : 1 ≤ depth t := by
  rcases t with ⟨a, r, v, f, c⟩
  rw [depth]
  omega

theorem le_mapDepth {m : List (FieldKey × CTy)} {p : FieldKey × CTy} (h : p ∈ m) :
    depth p.2 ≤ mapDepth m := by
  induction m with
  | nil => exact absurd h (by simp)
  | cons hd tl ih =>
    rw [mapDepth]
    rcases List.mem_cons.mp h with h' | h'
    · rcases hd with ⟨k, w⟩
      rw [h']
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h') (by rcases hd with ⟨k, w⟩; exact Nat.le_max_right _ _)

theorem mapDepth_le {m : List (FieldKey × CTy)} {b : Nat}
    (h : ∀ p ∈ m, depth p.2 ≤ b) : mapDepth m ≤ b := by
  induction m with
  | nil => simp [mapDepth]
  | cons hd tl ih =>
    rcases hd with ⟨k, w⟩
    rw [mapDepth]
    exact Nat.max_le.mpr ⟨h (k, w) (by simp), ih fun p hp => h p (by simp [hp])⟩

theorem le_listDepth {l : List CTy} {x : CTy} (h : x ∈ l) : depth x ≤ listDepth l := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons hd tl ih =>
    rw [listDepth]
    rcases List.mem_cons.mp h with h' | h'
    · rw [h']
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

theorem listDepth_le {l : List CTy} {b : Nat} (h : ∀ x ∈ l, depth x ≤ b) :
    listDepth l ≤ b := by
  induction l with
  | nil => simp [listDepth]
  | cons hd tl ih =>
    rw [listDepth]
    exact Nat.max_le.mpr ⟨h hd (by simp), ih fun x hx => h x (by simp [hx])⟩

theorem mem_of_lookup {m : List (FieldKey × CTy)} {k : FieldKey} {w : CTy}
    (h : m.lookup k = some w) : (k, w) ∈ m := by
  induction m with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    rw [List.lookup] at h
    split at h
    · rename_i heq
      cases h
      rcases hd with ⟨k', w'⟩
      simp only [beq_iff_eq] at heq
      rw [heq]
      simp
    · exact List.mem_cons.mpr (Or.inr (ih h))

/-- Every entry of `interMap` is a merge of one from each side. -/
theorem mem_interMap {pol : Bool} {m1 m2 : List (FieldKey × CTy)} {p : FieldKey × CTy}
    (hp : p ∈ interMap pol m1 m2) :
    ∃ v w, (p.1, v) ∈ m1 ∧ (p.1, w) ∈ m2 ∧ p.2 = merge pol v w := by
  induction m1 with
  | nil => exact absurd hp (by simp [interMap])
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    rw [interMap] at hp
    split at hp
    · rename_i w hw
      rcases List.mem_cons.mp hp with h' | h'
      · subst h'
        exact ⟨v, w, by simp, mem_of_lookup hw, rfl⟩
      · obtain ⟨v', w', hv', hw', he⟩ := ih h'
        exact ⟨v', w', List.mem_cons.mpr (Or.inr hv'), hw', he⟩
    · obtain ⟨v', w', hv', hw', he⟩ := ih hp
      exact ⟨v', w', List.mem_cons.mpr (Or.inr hv'), hw', he⟩

/-- Every entry of `unionMapGo` is one of `m1`'s, merged with `m2`'s when present. -/
theorem mem_unionMapGo {pol : Bool} {m1 m2 : List (FieldKey × CTy)} {p : FieldKey × CTy}
    (hp : p ∈ unionMapGo pol m1 m2) :
    ∃ v, (p.1, v) ∈ m1 ∧
      (p.2 = v ∨ ∃ w, (p.1, w) ∈ m2 ∧ p.2 = merge pol v w) := by
  induction m1 with
  | nil => exact absurd hp (by simp [unionMapGo])
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    rw [unionMapGo] at hp
    rcases List.mem_cons.mp hp with h' | h'
    · subst h'
      rcases hw : m2.lookup k with _ | w
      · exact ⟨v, by simp, Or.inl (by simp [hw])⟩
      · exact ⟨v, by simp, Or.inr ⟨w, mem_of_lookup hw, by simp [hw]⟩⟩
    · obtain ⟨v', hv', hrest⟩ := ih h'
      exact ⟨v', List.mem_cons.mpr (Or.inr hv'), hrest⟩

/-- The codomain is merged whatever else the slots do. -/
theorem mergeFun_cod (pol : Bool) (s1 s2 : KindM × List CTy × CTy) :
    (mergeFun pol s1 s2).2.2 = merge pol s1.2.2 s2.2.2 := by
  obtain ⟨k1, d1, c1⟩ := s1
  obtain ⟨k2, d2, c2⟩ := s2
  rw [mergeFun.eq_def]
  dsimp only
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- A slot whose kinds join to a conflict merges to the conflicted slot, at
either polarity and whatever the domains hold. -/
theorem mergeFun_of_conflict (pol : Bool) (s1 s2 : KindM × List CTy × CTy)
    (h : joinKind s1.1 s2.1 = .conflict) :
    mergeFun pol s1 s2 = (.conflict, [], merge pol s1.2.2 s2.2.2) := by
  obtain ⟨k1, d1, c1⟩ := s1
  obtain ⟨k2, d2, c2⟩ := s2
  rw [mergeFun.eq_def]
  simp only [h]
  rfl

/-! ### `merge` does not deepen a position

Each component of the merged position is built from components of the inputs, so
the whole is no deeper than the deeper input. The three lemmas below take the
recursion as a hypothesis, which keeps them out of any mutual block; `merge_depth_le`
supplies it by induction on a depth bound. -/

theorem interMap_depth_le {pol : Bool} {m1 m2 : List (FieldKey × CTy)} {bnd : Nat}
    (h1 : mapDepth m1 ≤ bnd) (h2 : mapDepth m2 ≤ bnd)
    (hrec : ∀ v w, depth v ≤ mapDepth m1 → depth w ≤ mapDepth m2 →
      depth (merge pol v w) ≤ Nat.max (depth v) (depth w)) :
    mapDepth (interMap pol m1 m2) ≤ bnd := by
  refine mapDepth_le fun p hp => ?_
  obtain ⟨v, w, hv, hw, he⟩ := mem_interMap hp
  rw [he]
  exact Nat.le_trans (hrec v w (le_mapDepth (p := (p.1, v)) hv) (le_mapDepth (p := (p.1, w)) hw))
    (Nat.max_le.mpr ⟨Nat.le_trans (le_mapDepth (p := (p.1, v)) hv) h1,
      Nat.le_trans (le_mapDepth (p := (p.1, w)) hw) h2⟩)

theorem unionMap_depth_le {pol : Bool} {m1 m2 : List (FieldKey × CTy)} {bnd : Nat}
    (h1 : mapDepth m1 ≤ bnd) (h2 : mapDepth m2 ≤ bnd)
    (hrec : ∀ v w, depth v ≤ mapDepth m1 → depth w ≤ mapDepth m2 →
      depth (merge pol v w) ≤ Nat.max (depth v) (depth w)) :
    mapDepth (unionMapGo pol m1 m2 ++ m2.filter (fun kw => (m1.lookup kw.1).isNone))
      ≤ bnd := by
  refine mapDepth_le fun p hp => ?_
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨v, hv, hcase⟩ := mem_unionMapGo hp
    rcases hcase with he | ⟨w, hw, he⟩
    · rw [he]
      exact Nat.le_trans (le_mapDepth (p := (p.1, v)) hv) h1
    · rw [he]
      exact Nat.le_trans
        (hrec v w (le_mapDepth (p := (p.1, v)) hv) (le_mapDepth (p := (p.1, w)) hw))
        (Nat.max_le.mpr ⟨Nat.le_trans (le_mapDepth (p := (p.1, v)) hv) h1,
          Nat.le_trans (le_mapDepth (p := (p.1, w)) hw) h2⟩)
  · exact Nat.le_trans (le_mapDepth (List.mem_filter.mp hp).1) h2

theorem mergeFun_depth_le {pol : Bool} {k1 k2 : KindM} {d1 d2 : List CTy} {c1 c2 : CTy}
    (hdom : ∀ x y, depth x ≤ listDepth d1 → depth y ≤ listDepth d2 →
      depth (merge true x y) ≤ Nat.max (depth x) (depth y))
    (hcod : depth (merge pol c1 c2) ≤ Nat.max (depth c1) (depth c2)) :
    optFnDepth (some (mergeFun pol (k1, d1, c1) (k2, d2, c2)))
      ≤ Nat.max (optFnDepth (some (k1, d1, c1))) (optFnDepth (some (k2, d2, c2))) := by
  have hb1 : listDepth d1 ≤ Nat.max (optFnDepth (some (k1, d1, c1)))
      (optFnDepth (some (k2, d2, c2))) := by
    rw [optFnDepth]
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hb2 : listDepth d2 ≤ Nat.max (optFnDepth (some (k1, d1, c1)))
      (optFnDepth (some (k2, d2, c2))) := by
    show listDepth d2 ≤ _
    exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ (depth c2)) (Nat.le_max_right _ _))
      (Nat.le_refl _)
  have hcb : depth (merge pol c1 c2) ≤ Nat.max (optFnDepth (some (k1, d1, c1)))
      (optFnDepth (some (k2, d2, c2))) := by
    refine Nat.le_trans hcod (Nat.max_le.mpr ⟨?_, ?_⟩)
    · rw [optFnDepth]
      exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    · exact Nat.le_trans (Nat.le_max_right (listDepth d2) _) (Nat.le_max_right _ _)
  -- Every alternative the merge keeps comes from one side, or is a meet of one
  -- from each; the codomain is a merge of the two codomains.
  have hds : listDepth (mergeFun pol (k1, d1, c1) (k2, d2, c2)).2.1
      ≤ Nat.max (optFnDepth (some (k1, d1, c1))) (optFnDepth (some (k2, d2, c2))) := by
    rw [mergeFun.eq_def]
    dsimp only
    split
    · simpa [listDepth] using Nat.zero_le _
    · split
      · refine listDepth_le fun x hx => ?_
        rcases mem_unionDoms hx with h | h
        · exact Nat.le_trans (le_listDepth h) hb1
        · exact Nat.le_trans (le_listDepth h) hb2
      · rcases hm : meetDoms d1 d2 with _ | ds
        · simpa [listDepth] using Nat.zero_le _
        · obtain ⟨x, xs, y, ys, ha1, ha2, _, hds⟩ := meetDoms_eq_some hm
          rw [hds]
          refine listDepth_le fun z hz => ?_
          rw [List.mem_singleton.mp hz]
          exact Nat.le_trans
            (hdom x y (le_listDepth (ha1 ▸ by simp)) (le_listDepth (ha2 ▸ by simp)))
            (Nat.max_le.mpr
              ⟨Nat.le_trans (le_listDepth (ha1 ▸ by simp)) hb1,
               Nat.le_trans (le_listDepth (ha2 ▸ by simp)) hb2⟩)
  have hc : depth (mergeFun pol (k1, d1, c1) (k2, d2, c2)).2.2
      ≤ Nat.max (optFnDepth (some (k1, d1, c1))) (optFnDepth (some (k2, d2, c2))) := by
    rw [mergeFun_cod]
    exact hcb
  rcases hs : mergeFun pol (k1, d1, c1) (k2, d2, c2) with ⟨k, ds, cod⟩
  rw [optFnDepth]
  rw [hs] at hds hc
  exact Nat.max_le.mpr ⟨hds, hc⟩

theorem succ_max_le (A B : Nat) : 1 + Nat.max A B ≤ Nat.max (1 + A) (1 + B) := by
  simp only [Nat.max_def]
  split <;> split <;> omega

/-- A position is one deeper than its deepest component. -/
theorem depth_mk_le {a1 : List Atom} {r v : Option (List (FieldKey × CTy))}
    {f : Option (KindM × List CTy × CTy)} {c : Option (List Pred)} {bnd : Nat}
    (hr : optMapDepth r ≤ bnd) (hv : optMapDepth v ≤ bnd) (hf : optFnDepth f ≤ bnd) :
    depth (CTy.mk a1 r v f c) ≤ 1 + bnd := by
  rw [depth]
  exact Nat.add_le_add_left (Nat.max_le.mpr ⟨hr, Nat.max_le.mpr ⟨hv, hf⟩⟩) 1

/-- **`merge` does not deepen a position.** Every component of the merged position
is built from components of the inputs — atoms and refinements union, map payloads
merge pointwise, a function slot's alternatives come from one side or are a meet of
one from each, and its codomain is a merge of the two — so the whole is no deeper
than the deeper input.

By induction on a depth bound rather than on the term, because the statement is
needed exactly where no structural measure works: `coalesce`'s recursion through a
`Compute` slot's folded alternatives materializes a `merge` result, not a subterm.
`compact.rs` relies on this and states it nowhere. -/
theorem merge_depth_le_bounded : ∀ (n : Nat) (pol : Bool) (a b : CTy),
    depth a ≤ n → depth b ≤ n →
      depth (merge pol a b) ≤ Nat.max (depth a) (depth b) := by
  intro n
  induction n with
  | zero =>
    intro _ a _ ha _
    exact absurd (Nat.le_trans (depth_pos a) ha) (by omega)
  | succ n ih =>
    intro pol a b ha hb
    rcases a with ⟨a1, r1, v1, f1, c1⟩
    rcases b with ⟨a2, r2, v2, f2, c2⟩
    -- Children are shallower than their position, so the bound drops by one and the
    -- induction hypothesis applies to any pair of them.
    have hchild : ∀ x y : CTy,
        depth x ≤ Nat.max (optMapDepth r1) (Nat.max (optMapDepth v1) (optFnDepth f1)) →
        depth y ≤ Nat.max (optMapDepth r2) (Nat.max (optMapDepth v2) (optFnDepth f2)) →
        depth (merge pol x y) ≤ Nat.max (depth x) (depth y) := by
      intro x y hx hy
      have hA : Nat.max (optMapDepth r1) (Nat.max (optMapDepth v1) (optFnDepth f1)) ≤ n := by
        rw [depth] at ha
        omega
      have hB : Nat.max (optMapDepth r2) (Nat.max (optMapDepth v2) (optFnDepth f2)) ≤ n := by
        rw [depth] at hb
        omega
      exact ih pol x y (Nat.le_trans hx hA) (Nat.le_trans hy hB)
    have hchild' : ∀ x y : CTy,
        depth x ≤ Nat.max (optMapDepth r1) (Nat.max (optMapDepth v1) (optFnDepth f1)) →
        depth y ≤ Nat.max (optMapDepth r2) (Nat.max (optMapDepth v2) (optFnDepth f2)) →
        depth (merge true x y) ≤ Nat.max (depth x) (depth y) := by
      intro x y hx hy
      have hA : Nat.max (optMapDepth r1) (Nat.max (optMapDepth v1) (optFnDepth f1)) ≤ n := by
        rw [depth] at ha
        omega
      have hB : Nat.max (optMapDepth r2) (Nat.max (optMapDepth v2) (optFnDepth f2)) ≤ n := by
        rw [depth] at hb
        omega
      exact ih true x y (Nat.le_trans hx hA) (Nat.le_trans hy hB)
    -- The three components, each bounded by the deeper input's deepest component.
    have hB1 := Nat.le_max_left
      (Nat.max (optMapDepth r1) (Nat.max (optMapDepth v1) (optFnDepth f1)))
      (Nat.max (optMapDepth r2) (Nat.max (optMapDepth v2) (optFnDepth f2)))
    have hB2 := Nat.le_max_right
      (Nat.max (optMapDepth r1) (Nat.max (optMapDepth v1) (optFnDepth f1)))
      (Nat.max (optMapDepth r2) (Nat.max (optMapDepth v2) (optFnDepth f2)))
    rw [merge.eq_def]
    dsimp only
    refine Nat.le_trans
      (depth_mk_le
        (bnd := Nat.max (Nat.max (optMapDepth r1) (Nat.max (optMapDepth v1) (optFnDepth f1)))
          (Nat.max (optMapDepth r2) (Nat.max (optMapDepth v2) (optFnDepth f2))))
        ?_ ?_ ?_) ?_
    · -- Records: intersected at a positive position, united at a negative one.
      rcases r1 with _ | m1
      · rcases r2 with _ | m2
        · simp [optMapDepth]
        · exact Nat.le_trans (Nat.le_max_left _ _) hB2
      · rcases r2 with _ | m2
        · exact Nat.le_trans (Nat.le_max_left _ _) hB1
        · have h1 : mapDepth m1 ≤ _ := Nat.le_trans (Nat.le_max_left _ _) hB1
          have h2 : mapDepth m2 ≤ _ := Nat.le_trans (Nat.le_max_left _ _) hB2
          have hr : ∀ v w, depth v ≤ mapDepth m1 → depth w ≤ mapDepth m2 →
              depth (merge pol v w) ≤ Nat.max (depth v) (depth w) := fun v w hv hw =>
            hchild v w (Nat.le_trans hv (Nat.le_max_left _ _))
              (Nat.le_trans hw (Nat.le_max_left _ _))
          cases pol
          · simpa [optMapDepth] using unionMap_depth_le h1 h2 hr
          · simpa [optMapDepth] using interMap_depth_le h1 h2 hr
    · -- Variants: the dual.
      rcases v1 with _ | m1
      · rcases v2 with _ | m2
        · simp [optMapDepth]
        · exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hB2
      · rcases v2 with _ | m2
        · exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hB1
        · have h1 : mapDepth m1 ≤ _ :=
            Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hB1
          have h2 : mapDepth m2 ≤ _ :=
            Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hB2
          have hr : ∀ v w, depth v ≤ mapDepth m1 → depth w ≤ mapDepth m2 →
              depth (merge pol v w) ≤ Nat.max (depth v) (depth w) := fun v w hv hw =>
            hchild v w
              (Nat.le_trans hv (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
              (Nat.le_trans hw (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
          cases pol
          · simpa [optMapDepth] using interMap_depth_le h1 h2 hr
          · simpa [optMapDepth] using unionMap_depth_le h1 h2 hr
    · -- The function slot.
      rcases f1 with _ | ⟨k1, d1, cod1⟩
      · rcases f2 with _ | s2
        · simp [optFnDepth]
        · exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hB2
      · rcases f2 with _ | ⟨k2, d2, cod2⟩
        · exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hB1
        · have hin1 : optFnDepth (some (k1, d1, cod1)) ≤ _ :=
            Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hB1
          have hin2 : optFnDepth (some (k2, d2, cod2)) ≤ _ :=
            Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hB2
          have hdom : ∀ x y, depth x ≤ listDepth d1 → depth y ≤ listDepth d2 →
              depth (merge true x y) ≤ Nat.max (depth x) (depth y) := fun x y hx hy =>
            hchild' x y
              (Nat.le_trans hx (Nat.le_trans (Nat.le_max_left _ _)
                (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))))
              (Nat.le_trans hy (Nat.le_trans (Nat.le_max_left _ _)
                (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))))
          have hcodb : depth (merge pol cod1 cod2) ≤ Nat.max (depth cod1) (depth cod2) :=
            hchild cod1 cod2
              (Nat.le_trans (Nat.le_max_right _ _)
                (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
              (Nat.le_trans (Nat.le_max_right _ _)
                (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
          exact Nat.le_trans (mergeFun_depth_le hdom hcodb)
            (Nat.max_le.mpr ⟨hin1, hin2⟩)
    · rw [depth, depth]
      exact succ_max_le _ _

/-- `merge` does not deepen a position, with no bound to supply. -/
theorem merge_depth_le (pol : Bool) (a b : CTy) :
    depth (merge pol a b) ≤ Nat.max (depth a) (depth b) :=
  merge_depth_le_bounded (Nat.max (depth a) (depth b)) pol a b
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- The meet of a slot's alternatives, folded left as `coalesce_compact_go` folds
them. Named rather than written as `List.foldl` so the depth bound below states a
term the termination checker sees unchanged. -/
def meetAll (pol : Bool) : CTy → List CTy → CTy
  | acc, [] => acc
  | acc, x :: xs => meetAll pol (merge pol acc x) xs

/-- Folding the meet over a slot's alternatives stays within their depth — the
bound `coalesce` needs for the one recursive call no subterm ordering reaches. -/
theorem meetAll_depth_le (pol : Bool) : (d : CTy) → (rest : List CTy) →
    depth (meetAll pol d rest) ≤ Nat.max (depth d) (listDepth rest)
  | d, [] => by
    rw [meetAll, listDepth]
    exact Nat.le_max_left _ _
  | d, x :: xs => by
    rw [meetAll]
    refine Nat.le_trans (meetAll_depth_le pol (merge pol d x) xs) ?_
    refine Nat.max_le.mpr ⟨Nat.le_trans (merge_depth_le pol d x) ?_, ?_⟩
    · rw [listDepth]
      exact Nat.max_le.mpr
        ⟨Nat.le_max_left _ _,
         Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)⟩
    · rw [listDepth]
      exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-! ## Well-formedness of input bounds

`compact_go` builds every bound's `CTy` from a `Type`: a function contributes
exactly one domain and a ground kind (`AtomKey::from_type` / the `Type::Fun`
arm), so an *input* bound never carries a `conflict` kind or a multi-domain
slot — those states are only ever *produced* by merging. Idempotence (and the
fold's duplicate-invariance) is stated under this invariant: a conflicted or
domain-less slot is an error state the solver never feeds back in, and
`eqv`-idempotence genuinely fails there (the model's conflict arm canonicalizes
the diagnostic payload away). -/

mutual

/-- Keys are duplicate-free, mirroring the `BTreeMap` the map stands for, which
cannot hold two bindings for one key. `eqv` is blind to a shadowed duplicate
because it compares by `lookup`, but `coalesce` materializes every entry and
`subTags` checks every one, so a duplicate is observable in the type. -/
def nodupKeys : List FieldKey → Bool
  | [] => true
  | k :: ks => !ks.contains k && nodupKeys ks

/-- The input-bound invariant (see the section header). -/
def wf : CTy → Bool
  | .mk atoms r v f c =>
    (match r with
     | none => true
     | some m => wfKeys m (m.map Prod.fst) && nodupKeys (m.map Prod.fst))
      && (match v with
          | none => true
          | some m => wfKeys m (m.map Prod.fst) && nodupKeys (m.map Prod.fst))
      && (match f with
          | none => true
          | some (k, d, cod) =>
            (k != .conflict)
              && (match d with
                  | [x] => wf x
                  | _ => false)
              && wf cod)
      -- The refinement slot's `none` is the merge identity, and `compact_go` gives it
      -- only to the two contributions that are not values: a hole and a bare
      -- variable, neither of which carries content. A position with content and
      -- no refinement slot would absorb a sibling bound's refinements instead of
      -- intersecting with none of its own, so `Int` joined with `{Int | p}` would
      -- keep `p`.
      && (match c with
          | none => atoms.isEmpty && r.isNone && v.isNone && f.isNone
          | some _ => true)
termination_by t => (sizeOf t, 0)

/-- All payloads of a map are `wf` (worklist form, like `subKeys`). -/
def wfKeys (m : List (FieldKey × CTy)) : List FieldKey → Bool
  | [] => true
  | k :: ks =>
    (match h : m.lookup k with
     | some v => wf v
     | none => true)
      && wfKeys m ks
termination_by ks => (sizeOf m, ks.length)
decreasing_by
  · have := lookup_sizeOf h
    apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    simp

end

/-- Pointwise reading of `wfKeys`. -/
theorem wfKeys_iff {m : List (FieldKey × CTy)} {ks : List FieldKey} :
    wfKeys m ks = true ↔ ∀ k ∈ ks, ∀ v, m.lookup k = some v → wf v = true := by
  induction ks with
  | nil => simp [wfKeys]
  | cons k ks ih =>
    rw [wfKeys, Bool.and_eq_true, ih]
    constructor
    · intro ⟨hhead, htail⟩ k' hk'
      rcases List.mem_cons.mp hk' with h | h
      · subst h
        intro v hv
        rw [hv] at hhead
        exact hhead
      · exact htail k' h
    · intro h
      refine ⟨?_, fun k' hk' => h k' (by simp [hk'])⟩
      rcases hv : m.lookup k with _ | v
      · rfl
      · exact h k (by simp) v hv

/-! ## Idempotence -/

theorem merge_idem (pol : Bool) : (a : CTy) → wf a = true → eqv (merge pol a a) a = true
  | .mk a1 r1 v1 f1 c1 => by
    intro hwf
    rw [wf.eq_def] at hwf
    simp only [Bool.and_eq_true] at hwf
    obtain ⟨⟨⟨hwr, hwv⟩, hwfn⟩, _hwc⟩ := hwf
    -- Both keyed self-merges are pointwise `merge pol v v`, closed by the
    -- recursive call on the (wf) payload.
    have hmap : ∀ (p : Bool) (m : List (FieldKey × CTy)),
        (∀ x k, m.lookup k = some x → eqv (merge p x x) x = true) →
        ∀ (mm : List (FieldKey × CTy)),
          (∀ k, mm.lookup k =
            match m.lookup k, m.lookup k with
            | some v, some w => some (merge p v w)
            | some v, none => some v
            | none, some _ => none
            | none, none => none) →
        (subKeys mm m (mm.map Prod.fst) && subKeys m mm (m.map Prod.fst)) = true := by
      intro p m hidem mm hmm
      rw [mapClause_iff]
      refine ⟨fun k => ?_, fun k x y hx hy => ?_, fun k x y hx hy => ?_⟩
      · rw [hmm k]
        rcases m.lookup k with _ | v <;> simp
      · rw [hmm k] at hx
        cases h1 : m.lookup k with
        | none =>
          rw [h1] at hx
          exact absurd hx (by simp)
        | some v =>
          rw [h1] at hx
          dsimp only at hx
          cases hx
          rw [h1] at hy
          cases hy
          exact hidem _ k h1
      · rw [hmm k] at hx
        cases h1 : m.lookup k with
        | none =>
          rw [h1] at hx
          exact absurd hx (by simp)
        | some v =>
          rw [h1] at hx
          dsimp only at hx
          cases hx
          rw [h1] at hy
          cases hy
          exact eqv_symm _ _ (hidem _ k h1)
    rw [merge.eq_def, eqv.eq_def]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp only [List.all_eq_true, List.contains_iff_mem, List.mem_append]
      exact fun x hx => hx.elim id id
    · simp only [List.all_eq_true, List.contains_iff_mem, List.mem_append]
      exact fun x hx => Or.inl hx
    · rcases r1 with _ | m
      · rfl
      · have hpay : ∀ x k, m.lookup k = some x → eqv (merge pol x x) x = true := by
          intro x k hx
          have hszx := lookup_sizeOf hx
          have hwx : wf x = true := (wfKeys_iff.mp (by simp only [Bool.and_eq_true] at hwr; simpa using hwr.1)) k
            (mem_keys_of_lookup hx) x hx
          exact merge_idem pol x hwx
        cases pol
        · simpa [unionMap] using hmap false m hpay (unionMap false m m)
            (fun k => by
              rw [unionMap_lookup]
              rcases m.lookup k with _ | v <;> rfl)
        · simpa using hmap true m hpay (interMap true m m)
            (fun k => by
              rw [interMap_lookup]
              rcases m.lookup k with _ | v <;> rfl)
    · rcases v1 with _ | m
      · rfl
      · have hpay : ∀ x k, m.lookup k = some x → eqv (merge pol x x) x = true := by
          intro x k hx
          have hszx := lookup_sizeOf hx
          have hwx : wf x = true := (wfKeys_iff.mp (by simp only [Bool.and_eq_true] at hwv; simpa using hwv.1)) k
            (mem_keys_of_lookup hx) x hx
          exact merge_idem pol x hwx
        cases pol
        · simpa using hmap false m hpay (interMap false m m)
            (fun k => by
              rw [interMap_lookup]
              rcases m.lookup k with _ | v <;> rfl)
        · simpa [unionMap] using hmap true m hpay (unionMap true m m)
            (fun k => by
              rw [unionMap_lookup]
              rcases m.lookup k with _ | v <;> rfl)
    · rcases f1 with _ | ⟨k1, d1, cod1⟩
      · rfl
      · rcases d1 with _ | ⟨x, xs⟩
        · simp [wf] at hwfn
        · rcases xs with _ | ⟨x2, xs2⟩
          case cons => simp [wf] at hwfn
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hwfn
          obtain ⟨⟨hk1, hwx⟩, hwcod⟩ := hwfn
          have hszx : sizeOf x < sizeOf (CTy.mk a1 r1 v1 (some (k1, [x], cod1)) c1) := by
            simp
            omega
          have hszc : sizeOf cod1 <
              sizeOf (CTy.mk a1 r1 v1 (some (k1, [x], cod1)) c1) := by
            simp
            omega
          have hx : eqv (merge (!pol) x x) x = true := merge_idem (!pol) x hwx
          have hcod : eqv (merge pol cod1 cod1) cod1 = true := merge_idem pol cod1 hwcod
          dsimp only
          rw [mergeFun.eq_def]
          -- The kind is idempotent and `wf` rules out a conflict, so the slot's
          -- kind survives untouched and only the domain and codomain recurse.
          simp only [joinKind_idem k1, beq_iff_eq, if_neg hk1]
          cases pol
          · simp only [Bool.false_eq_true, reduceIte, meetDoms_single]
            simpa [domsEqv] using funClause_of_funEqv
              (s1 := (k1, [merge true x x], merge false cod1 cod1))
              (s2 := (k1, [x], cod1))
              ⟨rfl, domsEqv_singleton (by simpa using hx), hcod⟩
          · simp only [reduceIte]
            simpa [domsEqv] using funClause_of_funEqv
              (s1 := (k1, unionDoms [x] [x], merge true cod1 cod1))
              (s2 := (k1, [x], cod1)) ⟨rfl, unionDoms_idem [x], hcod⟩
    · exact mergeRefinements_idem pol c1
termination_by a => sizeOf a
decreasing_by all_goals (simp; omega)

/-! ## Congruence: `merge` respects `eqv`

The one gate inside `merge` — the positive `data ⊔ data` domain dedup — is
`eqv` itself, so it cannot distinguish `eqv`-equal inputs (`eqv_congr_bool`).
That is the whole reason congruence holds; a gate keyed on anything finer
(e.g. structural equality, with `eqv` coarser than it) would break it. -/

/-- Replacing one side of the gate by an `eqv`-equal value leaves the gate's
verdict unchanged. -/
theorem eqv_congr_bool {x x' : CTy} (h : eqv x x' = true) (y : CTy) :
    eqv x y = eqv x' y := by
  rcases hg : eqv x' y with _ | _
  · rcases hg' : eqv x y with _ | _
    · rfl
    · rw [eqv_trans x' x y (eqv_symm x x' h) hg'] at hg
      exact hg
  · exact eqv_trans x x' y h hg

/-- `FunEqv` is reflexive. -/
theorem funEqv_refl (s : KindM × List CTy × CTy) : FunEqv s s := by
  obtain ⟨k, d, c⟩ := s
  exact ⟨rfl, domsEqv_refl d, eqv_refl c⟩

mutual

theorem merge_congr_left (pol : Bool) :
    (a a' b : CTy) → eqv a a' = true → eqv (merge pol a b) (merge pol a' b) = true
  | .mk a1 r1 v1 f1 c1, .mk a1' r1' v1' f1' c1', .mk b1 rb vb fb cb => by
    intro h
    rw [eqv.eq_def] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, hr⟩, hv⟩, hf⟩, hcl⟩ := h
    -- Pointwise congruence for the two keyed merges.
    have hinterC : ∀ (p : Bool) (m1 m1' m2 : List (FieldKey × CTy)),
        (subKeys m1 m1' (m1.map Prod.fst) && subKeys m1' m1 (m1'.map Prod.fst)) = true →
        (∀ x x' y k, m1.lookup k = some x → m1'.lookup k = some x' → m2.lookup k = some y →
          eqv (merge p x y) (merge p x' y) = true) →
        (subKeys (interMap p m1 m2) (interMap p m1' m2)
            ((interMap p m1 m2).map Prod.fst) &&
          subKeys (interMap p m1' m2) (interMap p m1 m2)
            ((interMap p m1' m2).map Prod.fst)) = true := by
      intro p m1 m1' m2 hcl hcong
      rw [mapClause_iff] at hcl ⊢
      obtain ⟨hdom, hfwd, hbwd⟩ := hcl
      refine ⟨fun k => ?_, fun k x y hx hy => ?_, fun k x y hx hy => ?_⟩
      · rw [interMap_lookup, interMap_lookup]
        rcases hl1 : m1.lookup k with _ | v <;> rcases hl2 : m2.lookup k with _ | w <;>
          rcases hl1' : m1'.lookup k with _ | v' <;>
          first
          | (simp; done)
          | (have hcontra := hdom k; simp [hl1, hl1'] at hcontra)
      · rw [interMap_lookup] at hx hy
        cases hl1 : m1.lookup k with
        | none =>
          rw [hl1] at hx
          exact absurd hx (by simp)
        | some v =>
          rw [hl1] at hx
          cases hl2 : m2.lookup k with
          | none =>
            rw [hl2] at hx
            exact absurd hx (by simp)
          | some w =>
            rw [hl2] at hx
            dsimp only at hx
            obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp ((hdom k).mp (by simp [hl1]))
            rw [hv', hl2] at hy
            dsimp only at hy
            cases hx
            cases hy
            exact hcong _ _ _ k hl1 hv' hl2
      · rw [interMap_lookup] at hx hy
        cases hl1' : m1'.lookup k with
        | none =>
          rw [hl1'] at hy
          exact absurd hy (by simp)
        | some v' =>
          rw [hl1'] at hy
          cases hl2 : m2.lookup k with
          | none =>
            rw [hl2] at hy
            exact absurd hy (by simp)
          | some w =>
            rw [hl2] at hy
            dsimp only at hy
            obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((hdom k).mpr (by simp [hl1']))
            rw [hv, hl2] at hx
            dsimp only at hx
            cases hx
            cases hy
            exact eqv_symm _ _ (hcong _ _ _ k hv hl1' hl2)
    have hunionC : ∀ (p : Bool) (m1 m1' m2 : List (FieldKey × CTy)),
        (subKeys m1 m1' (m1.map Prod.fst) && subKeys m1' m1 (m1'.map Prod.fst)) = true →
        (∀ x x' y k, m1.lookup k = some x → m1'.lookup k = some x' → m2.lookup k = some y →
          eqv (merge p x y) (merge p x' y) = true) →
        (subKeys (unionMap p m1 m2) (unionMap p m1' m2)
            ((unionMap p m1 m2).map Prod.fst) &&
          subKeys (unionMap p m1' m2) (unionMap p m1 m2)
            ((unionMap p m1' m2).map Prod.fst)) = true := by
      intro p m1 m1' m2 hcl hcong
      have hpay : ∀ x x' k, m1.lookup k = some x → m1'.lookup k = some x' →
          eqv x x' = true := (mapClause_iff.mp hcl).2.1 |> fun hh => fun x x' k hx hx' =>
            hh k x x' hx hx'
      rw [mapClause_iff] at hcl ⊢
      obtain ⟨hdom, hfwd, hbwd⟩ := hcl
      refine ⟨fun k => ?_, fun k x y hx hy => ?_, fun k x y hx hy => ?_⟩
      · rw [unionMap_lookup, unionMap_lookup]
        rcases hl1 : m1.lookup k with _ | v <;> rcases hl2 : m2.lookup k with _ | w <;>
          rcases hl1' : m1'.lookup k with _ | v' <;>
          first
          | (simp; done)
          | (have hcontra := hdom k; simp [hl1, hl1'] at hcontra)
      · rw [unionMap_lookup] at hx hy
        cases hl1 : m1.lookup k with
        | none =>
          rw [hl1] at hx
          cases hl2 : m2.lookup k with
          | none =>
            rw [hl2] at hx
            exact absurd hx (by simp)
          | some w =>
            rw [hl2] at hx
            dsimp only at hx
            have hno : m1'.lookup k = none := by
              rcases hl1' : m1'.lookup k with _ | v'
              · rfl
              · exact absurd ((hdom k).mpr (by simp [hl1'])) (by simp [hl1])
            rw [hno, hl2] at hy
            dsimp only at hy
            cases hx
            cases hy
            exact eqv_refl _
        | some v =>
          rw [hl1] at hx
          obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp ((hdom k).mp (by simp [hl1]))
          rw [hv'] at hy
          cases hl2 : m2.lookup k with
          | none =>
            rw [hl2] at hx hy
            dsimp only at hx hy
            cases hx
            cases hy
            exact hpay _ _ k hl1 hv'
          | some w =>
            rw [hl2] at hx hy
            dsimp only at hx hy
            cases hx
            cases hy
            exact hcong _ _ _ k hl1 hv' hl2
      · rw [unionMap_lookup] at hx hy
        cases hl1' : m1'.lookup k with
        | none =>
          rw [hl1'] at hy
          cases hl2 : m2.lookup k with
          | none =>
            rw [hl2] at hy
            exact absurd hy (by simp)
          | some w =>
            rw [hl2] at hy
            dsimp only at hy
            have hno : m1.lookup k = none := by
              rcases hl1 : m1.lookup k with _ | v
              · rfl
              · exact absurd ((hdom k).mp (by simp [hl1])) (by simp [hl1'])
            rw [hno, hl2] at hx
            dsimp only at hx
            cases hx
            cases hy
            exact eqv_refl _
        | some v' =>
          rw [hl1'] at hy
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((hdom k).mpr (by simp [hl1']))
          rw [hv] at hx
          cases hl2 : m2.lookup k with
          | none =>
            rw [hl2] at hx hy
            dsimp only at hx hy
            cases hx
            cases hy
            exact eqv_symm _ _ (hpay _ _ k hv hl1')
          | some w =>
            rw [hl2] at hx hy
            dsimp only at hx hy
            cases hx
            cases hy
            exact eqv_symm _ _ (hcong _ _ _ k hv hl1' hl2)
    rw [merge.eq_def, merge.eq_def, eqv.eq_def]
    simp only [Bool.and_eq_true]
    simp only [List.all_eq_true, List.contains_iff_mem] at h1 h2
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp only [List.all_eq_true, List.contains_iff_mem, List.mem_append]
      exact fun x hx => hx.imp (fun hm => by simpa using h1 x hm) id
    · simp only [List.all_eq_true, List.contains_iff_mem, List.mem_append]
      exact fun x hx => hx.imp (fun hm => by simpa using h2 x hm) id
    · rcases r1 with _ | m1 <;> rcases r1' with _ | m1' <;>
        first
        | (simp at hr; done)
        | skip
      · rcases rb with _ | mb
        · rfl
        · simp [subKeys_self]
      · rcases rb with _ | mb
        · simpa using hr
        · have hcong : ∀ x x' y k, m1.lookup k = some x → m1'.lookup k = some x' →
              mb.lookup k = some y → eqv (merge pol x y) (merge pol x' y) = true := by
            intro x x' y k hx hx' hy
            have hszx := lookup_sizeOf hx
            have hszx' := lookup_sizeOf hx'
            have hszy := lookup_sizeOf hy
            have hxx' : eqv x x' = true :=
              (mapClause_iff.mp (by simpa using hr)).2.1 k x x' hx hx'
            exact merge_congr_left pol x x' y hxx'
          cases pol
          · simpa [unionMap] using hunionC false m1 m1' mb (by simpa using hr) hcong
          · simpa using hinterC true m1 m1' mb (by simpa using hr) hcong
    · rcases v1 with _ | m1 <;> rcases v1' with _ | m1' <;>
        first
        | (simp at hv; done)
        | skip
      · rcases vb with _ | mb
        · rfl
        · simp [subKeys_self]
      · rcases vb with _ | mb
        · simpa using hv
        · have hcong : ∀ x x' y k, m1.lookup k = some x → m1'.lookup k = some x' →
              mb.lookup k = some y → eqv (merge pol x y) (merge pol x' y) = true := by
            intro x x' y k hx hx' hy
            have hszx := lookup_sizeOf hx
            have hszx' := lookup_sizeOf hx'
            have hszy := lookup_sizeOf hy
            have hxx' : eqv x x' = true :=
              (mapClause_iff.mp (by simpa using hv)).2.1 k x x' hx hx'
            exact merge_congr_left pol x x' y hxx'
          cases pol
          · simpa using hinterC false m1 m1' mb (by simpa using hv) hcong
          · simpa [unionMap] using hunionC true m1 m1' mb (by simpa using hv) hcong
    · rcases f1 with _ | s1 <;> rcases f1' with _ | s1' <;>
        first
        | (simp at hf; done)
        | skip
      · rcases fb with _ | sb
        · rfl
        · simpa [domsEqv] using funClause_of_funEqv (funEqv_refl sb)
      · rcases fb with _ | sb
        · simpa using hf
        · obtain ⟨k1, d1, cod1⟩ := s1
          obtain ⟨k1', d1', cod1'⟩ := s1'
          simp only [Bool.and_eq_true] at hf
          obtain ⟨⟨hk, hd⟩, hcod⟩ := hf
          have hk' : k1 = k1' := by simpa using hk
          have hsz : sizeOf (k1, d1, cod1) + sizeOf (k1', d1', cod1') + sizeOf sb <
              sizeOf (CTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1) +
                sizeOf (CTy.mk a1' r1' v1' (some (k1', d1', cod1')) c1') +
                sizeOf (CTy.mk b1 rb vb (some sb) cb) := by
            simp
            omega
          have hde : FunEqv (k1, d1, cod1) (k1', d1', cod1') :=
            ⟨hk', domsEqv_iff_and.mpr hd, hcod⟩
          simpa [domsEqv] using funClause_of_funEqv
            (mergeFun_congr_left pol (k1, d1, cod1) (k1', d1', cod1') sb hde)
    · exact mergeRefinements_congr_left pol cb hcl
termination_by a a' b => (sizeOf a + sizeOf a' + sizeOf b, 1)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; omega)
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

theorem mergeFun_congr_left (pol : Bool) :
    (s1 s1' sb : KindM × List CTy × CTy) → FunEqv s1 s1' →
      FunEqv (mergeFun pol s1 sb) (mergeFun pol s1' sb)
  | (k1, d1, c1), (k1', d1', c1'), (kb, db, cb) => by
    intro ⟨hk, hd, hc⟩
    subst hk
    have hszc : sizeOf c1 + sizeOf c1' + sizeOf cb <
        sizeOf (k1, d1, c1) + sizeOf (k1, d1', c1') + sizeOf (kb, db, cb) := by
      simp
      omega
    have hcod : eqv (merge pol c1 cb) (merge pol c1' cb) = true :=
      merge_congr_left pol c1 c1' cb hc
    -- The domain recursion, hoisted so its size bound sits beside its call: the
    -- alternatives are members of the slots, which is what bounds them.
    have hdom : ∀ x x' y, x ∈ d1 → x' ∈ d1' → y ∈ db → eqv x x' = true →
        eqv (merge true x y) (merge true x' y) = true := by
      intro x x' y hx hx' hy hxx'
      have h1 := List.sizeOf_lt_of_mem hx
      have h2 := List.sizeOf_lt_of_mem hx'
      have h3 := List.sizeOf_lt_of_mem hy
      have hszd : sizeOf x + sizeOf x' + sizeOf y <
          sizeOf (k1, d1, c1) + sizeOf (k1, d1', c1') + sizeOf (kb, db, cb) := by
        simp
        omega
      exact merge_congr_left true x x' y hxx'
    rw [mergeFun.eq_def, mergeFun.eq_def]
    simp only
    -- The kinds are equal, so both sides join to the same kind and only the
    -- domain and codomain are left to compare.
    rcases hkc : joinKind k1 kb == KindM.conflict with _ | _ <;>
      simp only [hkc, Bool.false_eq_true, reduceIte]
    case true => exact ⟨rfl, domsEqv_refl [], hcod⟩
    cases pol
    · -- Negative: the meet. `OneDistinct` is `domsEqv`-invariant, so the two sides
      -- are defined together, and their heads are `eqv`-related.
      simp only [Bool.false_eq_true, reduceIte]
      rcases hm : meetDoms d1 db with _ | ds
      · have hm' : meetDoms d1' db = none := by
          rcases hm' : meetDoms d1' db with _ | ds'
          · rfl
          · obtain ⟨ha', hb⟩ := oneDistinct_of_meetDoms hm'
            obtain ⟨ds'', hds''⟩ :=
              meetDoms_isSome_of (oneDistinct_congr (domsEqv_symm hd) ha') hb
            rw [hds''] at hm
            exact absurd hm (by simp)
        rw [hm']
        exact ⟨rfl, domsEqv_refl [], hcod⟩
      · obtain ⟨x, xs, y, ys, ha, hb, hgate, hds⟩ := meetDoms_eq_some hm
        rw [Bool.and_eq_true] at hgate
        obtain ⟨hoa, hob⟩ := oneDistinct_of_meetDoms hm
        obtain ⟨ds', hds'⟩ := meetDoms_isSome_of (oneDistinct_congr hd hoa) hob
        obtain ⟨x', xs', y', ys', ha', hb', hgate', hds2⟩ := meetDoms_eq_some hds'
        rw [Bool.and_eq_true] at hgate'
        -- The two heads are `eqv`: each is the sole distinct alternative of its
        -- side, and the sides are `domsEqv`.
        have hxx' : eqv x x' = true := by
          obtain ⟨h1, _⟩ := domsEqv_iff.mp hd
          obtain ⟨w, hw, hxw⟩ := h1 x (by rw [ha]; simp)
          exact eqv_trans _ _ _ hxw (all_eqv_head hgate'.1 w (ha' ▸ hw))
        -- The base's head is literally the same on both sides.
        have hyy' : y = y' := by
          rw [hb] at hb'
          exact (List.cons.injEq .. ▸ hb').1
        rw [hds', hds, hds2, hyy']
        exact ⟨rfl,
          domsEqv_singleton
            (hdom x x' y' (ha ▸ by simp) (ha' ▸ by simp) (hb' ▸ by simp) hxx'),
          hcod⟩
    · -- Positive: the union is a congruence because its dedup gate is `eqv`.
      simp only [reduceIte]
      exact ⟨rfl, unionDoms_congr_left db hd, hcod⟩
termination_by s1 s1' sb => (sizeOf s1 + sizeOf s1' + sizeOf sb, 0)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; assumption)
  | (apply Prod.Lex.left; omega)
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

end

/-- Congruence in the right argument (via commutativity). -/
theorem merge_congr_right (pol : Bool) (a b b' : CTy) (h : eqv b b' = true) :
    eqv (merge pol a b) (merge pol a b') = true :=
  eqv_trans _ _ _ (merge_comm pol a b)
    (eqv_trans _ _ _ (merge_congr_left pol b b' a h) (merge_comm pol b' a))

/-- Full congruence. -/
theorem merge_congr (pol : Bool) {a a' b b' : CTy}
    (ha : eqv a a' = true) (hb : eqv b b' = true) :
    eqv (merge pol a b) (merge pol a' b') = true :=
  eqv_trans _ _ _ (merge_congr_left pol a a' b ha) (merge_congr_right pol a' b b' hb)

/-! ## Associativity

The kinds join in a semilattice and the domains are combined by polarity alone
([`mergeFun`]), so no step of the fold reads a value that a later step can
change, and the merge is associative with no side condition. That is what makes
the fold below a function of the bound *set*.

An earlier rule selected the domain combination from the slot's kind, and that
was **not** associative: three bounds at one position — a `data` function over
one domain and two whose kind variable nothing had pinned, over two others —
merged to a conflict in one association and to an accepted `data` function in
another, whose domain was the meet of two of the three. `compact.rs` now defers
that choice to `coalesce_compact_go`, where the kind is resolved
(`undetermined_kinds_join_without_deciding_the_domain_rule` pins the exhibit). -/

/-- A negative merge whose domain meet is undefined is the conflicted slot — the
same shape a conflicted kind produces. -/
theorem mergeFun_neg_none (s1 s2 : KindM × List CTy × CTy)
    (h : meetDoms s1.2.1 s2.2.1 = none) :
    mergeFun false s1 s2 = (.conflict, [], merge false s1.2.2 s2.2.2) := by
  obtain ⟨k1, d1, c1⟩ := s1
  obtain ⟨k2, d2, c2⟩ := s2
  rw [mergeFun.eq_def]
  dsimp only
  split
  · rfl
  · simp only [Bool.false_eq_true, reduceIte]
    rw [h]

/-- A merged slot's kind is the kinds' join, or a conflict the domains forced
(the negative meet has no single domain to take). -/
theorem mergeFun_kind (pol : Bool) (s1 s2 : KindM × List CTy × CTy) :
    (mergeFun pol s1 s2).1 = joinKind s1.1 s2.1 ∨ (mergeFun pol s1 s2).1 = .conflict := by
  obtain ⟨k1, d1, c1⟩ := s1
  obtain ⟨k2, d2, c2⟩ := s2
  rw [mergeFun.eq_def]
  dsimp only
  split
  · rename_i hc
    exact Or.inr rfl
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl

/-- `joinKind` is absorbed by a conflict on either side. -/
theorem joinKind_conflict_left (k : KindM) : joinKind .conflict k = .conflict := by
  cases k <;> rfl

theorem joinKind_conflict_right (k : KindM) : joinKind k .conflict = .conflict := by
  cases k <;> rfl

mutual

theorem merge_assoc (pol : Bool) :
    (a b c : CTy) →
      eqv (merge pol (merge pol a b) c) (merge pol a (merge pol b c)) = true
  | .mk a1 r1 v1 f1 c1, .mk a2 r2 v2 f2 c2, .mk a3 r3 v3 f3 c3 => by
    -- Pointwise associativity for the two keyed merges.
    have hinterA : ∀ (p : Bool) (m1 m2 m3 : List (FieldKey × CTy)),
        (∀ x y z k, m1.lookup k = some x → m2.lookup k = some y → m3.lookup k = some z →
          eqv (merge p (merge p x y) z) (merge p x (merge p y z)) = true) →
        (subKeys (interMap p (interMap p m1 m2) m3) (interMap p m1 (interMap p m2 m3))
            ((interMap p (interMap p m1 m2) m3).map Prod.fst) &&
          subKeys (interMap p m1 (interMap p m2 m3)) (interMap p (interMap p m1 m2) m3)
            ((interMap p m1 (interMap p m2 m3)).map Prod.fst)) = true := by
      intro p m1 m2 m3 hassoc
      rw [mapClause_iff]
      refine ⟨fun k => ?_, fun k x y hx hy => ?_, fun k x y hx hy => ?_⟩
      · rw [interMap_lookup, interMap_lookup, interMap_lookup, interMap_lookup]
        rcases m1.lookup k with _ | v <;> rcases m2.lookup k with _ | w <;>
          rcases m3.lookup k with _ | u <;> simp
      · rw [interMap_lookup, interMap_lookup] at hx
        rw [interMap_lookup, interMap_lookup] at hy
        rcases h1 : m1.lookup k with _ | v <;> rw [h1] at hx hy <;>
          rcases h2 : m2.lookup k with _ | w <;> rw [h2] at hx hy <;>
          rcases h3 : m3.lookup k with _ | u <;> rw [h3] at hx hy <;>
          dsimp only at hx hy <;>
          first
          | (simp only [reduceCtorEq] at hx)
          | (cases hx; cases hy; exact hassoc _ _ _ k h1 h2 h3)
      · rw [interMap_lookup, interMap_lookup] at hx
        rw [interMap_lookup, interMap_lookup] at hy
        rcases h1 : m1.lookup k with _ | v <;> rw [h1] at hx hy <;>
          rcases h2 : m2.lookup k with _ | w <;> rw [h2] at hx hy <;>
          rcases h3 : m3.lookup k with _ | u <;> rw [h3] at hx hy <;>
          dsimp only at hx hy <;>
          first
          | (simp only [reduceCtorEq] at hx)
          | (cases hx; cases hy; exact eqv_symm _ _ (hassoc _ _ _ k h1 h2 h3))
    have hunionA : ∀ (p : Bool) (m1 m2 m3 : List (FieldKey × CTy)),
        (∀ x y z k, m1.lookup k = some x → m2.lookup k = some y → m3.lookup k = some z →
          eqv (merge p (merge p x y) z) (merge p x (merge p y z)) = true) →
        (subKeys (unionMap p (unionMap p m1 m2) m3) (unionMap p m1 (unionMap p m2 m3))
            ((unionMap p (unionMap p m1 m2) m3).map Prod.fst) &&
          subKeys (unionMap p m1 (unionMap p m2 m3)) (unionMap p (unionMap p m1 m2) m3)
            ((unionMap p m1 (unionMap p m2 m3)).map Prod.fst)) = true := by
      intro p m1 m2 m3 hassoc
      rw [mapClause_iff]
      refine ⟨fun k => ?_, fun k x y hx hy => ?_, fun k x y hx hy => ?_⟩
      · rw [unionMap_lookup, unionMap_lookup, unionMap_lookup, unionMap_lookup]
        rcases m1.lookup k with _ | v <;> rcases m2.lookup k with _ | w <;>
          rcases m3.lookup k with _ | u <;> simp
      · rw [unionMap_lookup, unionMap_lookup] at hx
        rw [unionMap_lookup, unionMap_lookup] at hy
        rcases h1 : m1.lookup k with _ | v <;> rw [h1] at hx hy <;>
          rcases h2 : m2.lookup k with _ | w <;> rw [h2] at hx hy <;>
          rcases h3 : m3.lookup k with _ | u <;> rw [h3] at hx hy <;>
          dsimp only at hx hy <;>
          first
          | (simp only [reduceCtorEq] at hx)
          | (cases hx; cases hy;
             first
             | exact eqv_refl _
             | exact hassoc _ _ _ k h1 h2 h3)
      · rw [unionMap_lookup, unionMap_lookup] at hx
        rw [unionMap_lookup, unionMap_lookup] at hy
        rcases h1 : m1.lookup k with _ | v <;> rw [h1] at hx hy <;>
          rcases h2 : m2.lookup k with _ | w <;> rw [h2] at hx hy <;>
          rcases h3 : m3.lookup k with _ | u <;> rw [h3] at hx hy <;>
          dsimp only at hx hy <;>
          first
          | (simp only [reduceCtorEq] at hx)
          | (cases hx; cases hy;
             first
             | exact eqv_refl _
             | exact eqv_symm _ _ (hassoc _ _ _ k h1 h2 h3))
    rw [merge.eq_def, merge.eq_def, merge.eq_def, merge.eq_def, eqv.eq_def]
    dsimp only
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp only [List.all_eq_true, List.contains_iff_mem, List.mem_append]
      exact fun x hx => by simpa [or_assoc] using hx
    · simp only [List.all_eq_true, List.contains_iff_mem, List.mem_append]
      exact fun x hx => by simpa [or_assoc] using hx
    · rcases r1 with _ | m1 <;> rcases r2 with _ | m2 <;> rcases r3 with _ | m3 <;>
        first
        | rfl
        | (simp [subKeys_self]; done)
        | skip
      have hassoc : ∀ x y z k, m1.lookup k = some x → m2.lookup k = some y →
          m3.lookup k = some z →
          eqv (merge pol (merge pol x y) z) (merge pol x (merge pol y z)) = true := by
        intro x y z k hx hy hz
        have hszx := lookup_sizeOf hx
        have hszy := lookup_sizeOf hy
        have hszz := lookup_sizeOf hz
        exact merge_assoc pol x y z
      cases pol
      · simpa [unionMap] using hunionA false m1 m2 m3 hassoc
      · simpa using hinterA true m1 m2 m3 hassoc
    · rcases v1 with _ | m1 <;> rcases v2 with _ | m2 <;> rcases v3 with _ | m3 <;>
        first
        | rfl
        | (simp [subKeys_self]; done)
        | skip
      have hassoc : ∀ x y z k, m1.lookup k = some x → m2.lookup k = some y →
          m3.lookup k = some z →
          eqv (merge pol (merge pol x y) z) (merge pol x (merge pol y z)) = true := by
        intro x y z k hx hy hz
        have hszx := lookup_sizeOf hx
        have hszy := lookup_sizeOf hy
        have hszz := lookup_sizeOf hz
        exact merge_assoc pol x y z
      cases pol
      · simpa using hinterA false m1 m2 m3 hassoc
      · simpa [unionMap] using hunionA true m1 m2 m3 hassoc
    · rcases f1 with _ | s1 <;> rcases f2 with _ | s2 <;> rcases f3 with _ | s3 <;>
        first
        | rfl
        | (simpa [domsEqv] using funClause_of_funEqv (funEqv_refl _))
        | skip
      obtain ⟨k1, d1, cod1⟩ := s1
      obtain ⟨k2, d2, cod2⟩ := s2
      obtain ⟨k3, d3, cod3⟩ := s3
      have hsz : sizeOf (k1, d1, cod1) + sizeOf (k2, d2, cod2) + sizeOf (k3, d3, cod3) <
          sizeOf (CTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1) +
            sizeOf (CTy.mk a2 r2 v2 (some (k2, d2, cod2)) c2) +
            sizeOf (CTy.mk a3 r3 v3 (some (k3, d3, cod3)) c3) := by
        simp
        omega
      simpa [domsEqv] using funClause_of_funEqv
        (mergeFun_assoc pol (k1, d1, cod1) (k2, d2, cod2) (k3, d3, cod3))
    · exact mergeRefinements_assoc pol c1 c2 c3
termination_by a b c => (sizeOf a + sizeOf b + sizeOf c, 1)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; omega)
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

theorem mergeFun_assoc (pol : Bool) :
    (s1 s2 s3 : KindM × List CTy × CTy) →
      FunEqv (mergeFun pol (mergeFun pol s1 s2) s3) (mergeFun pol s1 (mergeFun pol s2 s3))
  | (k1, d1, c1), (k2, d2, c2), (k3, d3, c3) => by
    have hszc : sizeOf c1 + sizeOf c2 + sizeOf c3 <
        sizeOf (k1, d1, c1) + sizeOf (k2, d2, c2) + sizeOf (k3, d3, c3) := by
      simp
      omega
    have hcod : eqv (merge pol (merge pol c1 c2) c3) (merge pol c1 (merge pol c2 c3)) = true :=
      merge_assoc pol c1 c2 c3
    -- The domain recursion, hoisted so its size bound sits beside its call.
    have hassoc : ∀ x y z, x ∈ d1 → y ∈ d2 → z ∈ d3 →
        eqv (merge true (merge true x y) z) (merge true x (merge true y z)) = true := by
      intro x y z hx hy hz
      have h1 := List.sizeOf_lt_of_mem hx
      have h2 := List.sizeOf_lt_of_mem hy
      have h3 := List.sizeOf_lt_of_mem hz
      have hszd : sizeOf x + sizeOf y + sizeOf z <
          sizeOf (k1, d1, c1) + sizeOf (k2, d2, c2) + sizeOf (k3, d3, c3) := by
        simp
        omega
      exact merge_assoc true x y z
    have hK : joinKind (joinKind k1 k2) k3 = joinKind k1 (joinKind k2 k3) :=
      joinKind_assoc k1 k2 k3
    rcases hk : joinKind (joinKind k1 k2) k3 with _ | _ | _ | _
    -- The three kinds join to a conflict: absorbing, so whichever pairwise join
    -- the association takes first, both outer slots are the conflicted one.
    case conflict =>
      have hl : mergeFun pol (mergeFun pol (k1, d1, c1) (k2, d2, c2)) (k3, d3, c3) =
          (.conflict, [], merge pol (merge pol c1 c2) c3) := by
        have := mergeFun_of_conflict pol (mergeFun pol (k1, d1, c1) (k2, d2, c2)) (k3, d3, c3)
          (by
            rcases mergeFun_kind pol (k1, d1, c1) (k2, d2, c2) with h | h
            · simpa only [h] using hk
            · simpa only [h] using joinKind_conflict_left k3)
        rw [this, mergeFun_cod]
      have hr : mergeFun pol (k1, d1, c1) (mergeFun pol (k2, d2, c2) (k3, d3, c3)) =
          (.conflict, [], merge pol c1 (merge pol c2 c3)) := by
        have := mergeFun_of_conflict pol (k1, d1, c1) (mergeFun pol (k2, d2, c2) (k3, d3, c3))
          (by
            rcases mergeFun_kind pol (k2, d2, c2) (k3, d3, c3) with h | h
            · simpa only [h] using hK.symm.trans hk
            · simpa only [h] using joinKind_conflict_right k1)
        rw [this, mergeFun_cod]
      rw [hl, hr]
      exact ⟨rfl, domsEqv_refl [], hcod⟩
    all_goals
      -- No conflict anywhere: a conflicted pairwise join would absorb into `hk`,
      -- so both inner merges carry the joined kind and both sides reduce.
      have h12 : (joinKind k1 k2 == KindM.conflict) = false := by
        rcases h : joinKind k1 k2 with _ | _ | _ | _
        case conflict =>
          rw [h, joinKind_conflict_left] at hk
          simp at hk
        all_goals rfl
      have h23 : (joinKind k2 k3 == KindM.conflict) = false := by
        rcases h : joinKind k2 k3 with _ | _ | _ | _
        case conflict =>
          rw [hK, h, joinKind_conflict_right] at hk
          simp at hk
        all_goals rfl
      have hkl : (joinKind (joinKind k1 k2) k3 == KindM.conflict) = false := by
        rw [hk]; rfl
      have hkr : (joinKind k1 (joinKind k2 k3) == KindM.conflict) = false := by
        rw [← hK, hk]; rfl
      cases pol
      · -- Negative: nested contravariant meets. Both nestings are defined exactly
        -- when all three slots have one distinct alternative, and otherwise both
        -- conflict — whichever slot is the culprit.
        by_cases hd1 : OneDistinct d1
        · by_cases hd2 : OneDistinct d2
          · by_cases hd3 : OneDistinct d3
            · obtain ⟨_, h12s⟩ := meetDoms_isSome_of hd1 hd2
              obtain ⟨x, xs, y, ys, ha1, ha2, _, hds12⟩ := meetDoms_eq_some h12s
              obtain ⟨_, h23s⟩ := meetDoms_isSome_of hd2 hd3
              obtain ⟨y', ys', z, zs, ha2', ha3, _, hds23⟩ := meetDoms_eq_some h23s
              -- Both decompositions of `d2` are the same cons, so they name one head.
              have hy : y = y' := by
                rw [ha2] at ha2'
                exact (List.cons.injEq .. ▸ ha2').1
              -- Reduce each inner slot first, so the outer kind test is a `joinKind`
              -- the kind facts decide.
              have hil : mergeFun false (k1, d1, c1) (k2, d2, c2)
                  = (joinKind k1 k2, [merge true x y], merge false c1 c2) := by
                rw [mergeFun.eq_def]
                simp only [h12, Bool.false_eq_true, reduceIte, h12s, hds12]
              have hir : mergeFun false (k2, d2, c2) (k3, d3, c3)
                  = (joinKind k2 k3, [merge true y z], merge false c2 c3) := by
                rw [mergeFun.eq_def]
                simp only [h23, Bool.false_eq_true, reduceIte, h23s, hds23, ← hy]
              rw [hil, hir, mergeFun.eq_def, mergeFun.eq_def]
              simp only [hkl, hkr, Bool.false_eq_true, reduceIte]
              rw [show meetDoms [merge true x y] d3
                    = some [merge true (merge true x y) z] from by
                  rw [ha3]
                  exact meetDoms_of_gate (by
                    rw [Bool.and_eq_true]
                    exact ⟨by simp [subDoms], gate_of_oneDistinct (ha3 ▸ hd3)⟩),
                show meetDoms d1 [merge true y z]
                    = some [merge true x (merge true y z)] from by
                  rw [ha1]
                  exact meetDoms_of_gate (by
                    rw [Bool.and_eq_true]
                    exact ⟨gate_of_oneDistinct (ha1 ▸ hd1), by simp [subDoms]⟩)]
              exact ⟨by rw [hK],
                domsEqv_singleton
                  (hassoc x y z (ha1 ▸ by simp) (ha2 ▸ by simp) (ha3 ▸ by simp)),
                hcod⟩
            · -- `d3` has no single alternative: the left's outer meet is undefined,
              -- and the right's inner one is.
              rw [mergeFun_neg_none (k2, d2, c2) (k3, d3, c3) (meetDoms_none_of_right hd3),
                mergeFun_of_conflict false (k1, d1, c1)
                  (KindM.conflict, [], merge false c2 c3)
                  (by simpa using joinKind_conflict_right k1),
                mergeFun_neg_none _ (k3, d3, c3) (meetDoms_none_of_right hd3)]
              refine ⟨rfl, domsEqv_refl [], ?_⟩
              simpa [mergeFun_cod] using hcod
          · -- `d2` fails on both sides: as the right argument of one inner meet and
            -- the left argument of the other.
            rw [mergeFun_neg_none (k1, d1, c1) (k2, d2, c2) (meetDoms_none_of_right hd2),
              mergeFun_neg_none (k2, d2, c2) (k3, d3, c3) (meetDoms_none_of_left hd2),
              mergeFun_of_conflict false (KindM.conflict, [], merge false c1 c2) (k3, d3, c3)
                (by simpa using joinKind_conflict_left k3),
              mergeFun_of_conflict false (k1, d1, c1)
                (KindM.conflict, [], merge false c2 c3)
                (by simpa using joinKind_conflict_right k1)]
            refine ⟨rfl, domsEqv_refl [], ?_⟩
            simpa [mergeFun_cod] using hcod
        · -- `d1` fails: the left's inner meet is undefined, the right's outer one is.
          rw [mergeFun_neg_none (k1, d1, c1) (k2, d2, c2) (meetDoms_none_of_left hd1),
            mergeFun_of_conflict false (KindM.conflict, [], merge false c1 c2) (k3, d3, c3)
              (by simpa using joinKind_conflict_left k3),
            mergeFun_neg_none (k1, d1, c1) _ (meetDoms_none_of_left hd1)]
          refine ⟨rfl, domsEqv_refl [], ?_⟩
          simpa [mergeFun_cod] using hcod
      · -- Positive: the alternatives are a set, and set union is associative.
        simp only [mergeFun.eq_def, h12, h23, hkl, hkr, joinKind_conflict_left,
          joinKind_conflict_right, Bool.false_eq_true, reduceIte, beq_self_eq_true, if_true]
        exact ⟨by rw [hK], unionDoms_assoc d1 d2 d3, hcod⟩
termination_by s1 s2 s3 => (sizeOf s1 + sizeOf s2 + sizeOf s3, 0)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; omega)
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

end

/-! ## The fold: coalescing a bound list is order- and duplicate-invariant

`compact_go` folds a variable's bounds through `merge` from the first bound
(no identity element exists — see the module docs). The outcome is a function of
the bound *set*: permutations (`foldMerge_perm`) cannot change it, and neither
can duplicates (`foldMerge_dup`, which needs `wf` on the repeated bound because
idempotence does). This is the algebraic statement behind the type-merge fuzz's
\"outcomes agree under permuted constraint orders\". -/

/-- The fold `compact_go` performs over a variable's bound list, seeded at the
first bound. -/
def foldMerge (pol : Bool) (t : CTy) (ts : List CTy) : CTy :=
  ts.foldl (merge pol) t

/-- The fold respects `eqv` in its seed (any polarity). -/
theorem foldMerge_congr (pol : Bool) {t t' : CTy} (ts : List CTy) (h : eqv t t' = true) :
    eqv (foldMerge pol t ts) (foldMerge pol t' ts) = true := by
  induction ts generalizing t t' with
  | nil => exact h
  | cons x ts ih => exact ih (merge_congr_left pol t t' x h)

/-- **Order-invariance**: permuting the bound list cannot change the coalesced
outcome (up to `eqv`), at either polarity and with no side condition. -/
theorem foldMerge_perm (pol : Bool) {l1 l2 : List CTy} (h : l1.Perm l2) :
    ∀ (t : CTy), eqv (foldMerge pol t l1) (foldMerge pol t l2) = true := by
  induction h with
  | nil => exact fun t => eqv_refl _
  | @cons x l1 l2 hp ih => exact fun t => ih (merge pol t x)
  | @swap x y l =>
    intro t
    -- merge (merge t y) x ~ merge t (merge y x) ~ merge t (merge x y)
    --   ~ merge (merge t x) y
    have hseed : eqv (merge pol (merge pol t y) x) (merge pol (merge pol t x) y) = true :=
      eqv_trans _ _ _ (merge_assoc pol t y x)
        (eqv_trans _ _ _ (merge_congr_right pol t _ _ (merge_comm pol y x))
          (eqv_symm _ _ (merge_assoc pol t x y)))
    simpa [foldMerge, List.foldl_cons] using foldMerge_congr pol l hseed
  | @trans l1 l2 l3 h12 h23 ih1 ih2 => exact fun t => eqv_trans _ _ _ (ih1 t) (ih2 t)

/-- **Duplicate-invariance**: a bound occurring twice contributes once — the
other half of \"the outcome is a function of the bound set\". Needs `wf` for
the duplicated bound (idempotence does). -/
theorem foldMerge_dup (pol : Bool) {t x : CTy} (l : List CTy) (hwx : wf x = true) :
    eqv (foldMerge pol t (x :: x :: l)) (foldMerge pol t (x :: l)) = true := by
  -- merge (merge t x) x ~ merge t (merge x x) ~ merge t x
  have hseed : eqv (merge pol (merge pol t x) x) (merge pol t x) = true :=
    eqv_trans _ _ _ (merge_assoc pol t x x)
      (merge_congr_right pol t _ _ (merge_idem pol x hwx))
  simpa [foldMerge, List.foldl_cons] using foldMerge_congr pol l hseed

/-! ## The order the merge induces, and uniqueness

`merge pol` is commutative, associative and idempotent, so it comes with an
order: `le pol a b` reads "merging `a` into `b` adds nothing". `merge pol` is that
order's least upper bound, and any least upper bound is `eqv`-equal to it
(`join_unique`).

The scope is narrow and worth stating. These proofs use only commutativity,
associativity, idempotence and congruence, so they are the semilattice-to-poset
correspondence and carry exactly that content — `merge` is a join *of the order it
defines*. That it is the join with respect to **subtyping** is a different
statement, needing a denotation into a lattice of types, and it is not made here
(`formal/design.md`, "M4c — the lattice, and what a merge means *(planned)*").

Absorption and distributivity hold of the types and are not stated here, because
`CTy` is the wrong carrier for them. There is one type lattice, and `merge true`
computes its join while `merge false` computes its meet; what is polarity-indexed
is the *denotation*. One `CTy` denotes two types — a contribution set is the union
of its contributions read positively and their intersection read negatively — so
`CTy` is one syntax carrying two representations rather than a lattice carrier.

Writing `a ⊓ (a ⊔ b) = a` over `CTy` needs one syntactic `a` in both a join
argument (read positively) and a meet argument (read negatively), which needs
`⟦a⟧⁺ = ⟦a⟧⁻`. That holds for a single contribution (`{Int}` is `Int` either way)
and fails once a set holds two, which is the case the law is about. So the laws
proved here are the ones a single polarity's operation has, and the cross-polarity
laws wait on a carrier where both operations act on the same object
(`formal/design.md`, "M4c — the lattice, and what a merge means *(planned)*").

Reflexivity needs `wf` because idempotence does; nothing else here has a side
condition. -/

/-- The empty position: no contribution at any slot, which is what a `Hole`
compacts to (`CompactType::empty`). -/
def cempty : CTy := .mk [] none none none none

/-- The empty position is the merge identity, at either polarity. Every slot's
`none` is its own identity, the atom list unions, and the refinement slot's sentinel
supplies the one the refinement *set* cannot (an empty set is absorbing under the
positive intersect, not neutral) — so the merged position is the other side
itself, not merely `eqv` to it. `compact_go` still folds from the first bound,
but nothing in the algebra requires that any more. -/
theorem merge_cempty_left (pol : Bool) (a : CTy) : merge pol cempty a = a := by
  rcases a with ⟨a1, r1, v1, f1, c1⟩
  rw [merge.eq_def]
  rfl

theorem merge_cempty_right (pol : Bool) (a : CTy) : eqv (merge pol a cempty) a = true := by
  exact eqv_trans _ _ _ (merge_comm pol a cempty)
    (by rw [merge_cempty_left]; exact eqv_refl a)

/-- The order `merge pol` induces: `a ≤ b` when merging `a` into `b` adds
nothing. -/
def le (pol : Bool) (a b : CTy) : Prop := eqv (merge pol a b) b = true

theorem le_refl (pol : Bool) {a : CTy} (h : wf a = true) : le pol a a :=
  merge_idem pol a h

theorem le_trans (pol : Bool) {a b c : CTy} (hab : le pol a b) (hbc : le pol b c) :
    le pol a c := by
  -- a ⊔ c ~ a ⊔ (b ⊔ c) ~ (a ⊔ b) ⊔ c ~ b ⊔ c ~ c
  have h1 : eqv (merge pol a c) (merge pol a (merge pol b c)) = true :=
    merge_congr_right pol a c (merge pol b c) (eqv_symm _ _ hbc)
  have h2 : eqv (merge pol a (merge pol b c)) (merge pol (merge pol a b) c) = true :=
    eqv_symm _ _ (merge_assoc pol a b c)
  have h3 : eqv (merge pol (merge pol a b) c) c = true :=
    eqv_trans _ _ _ (merge_congr_left pol (merge pol a b) b c hab) hbc
  exact eqv_trans _ _ _ h1 (eqv_trans _ _ _ h2 h3)

/-- Antisymmetry up to `eqv`: the order is a partial order on the quotient. -/
theorem le_antisymm (pol : Bool) {a b : CTy} (hab : le pol a b) (hba : le pol b a) :
    eqv a b = true :=
  eqv_trans _ _ _ (eqv_symm _ _ hba) (eqv_trans _ _ _ (merge_comm pol b a) hab)

/-- `merge pol a b` is an upper bound of `a`. -/
theorem le_merge_left (pol : Bool) (a b : CTy) (ha : wf a = true) :
    le pol a (merge pol a b) := by
  -- a ⊔ (a ⊔ b) ~ (a ⊔ a) ⊔ b ~ a ⊔ b
  exact eqv_trans _ _ _ (eqv_symm _ _ (merge_assoc pol a a b))
    (merge_congr_left pol (merge pol a a) a b (merge_idem pol a ha))

/-- …and of `b`. -/
theorem le_merge_right (pol : Bool) (a b : CTy) (hb : wf b = true) :
    le pol b (merge pol a b) :=
  eqv_trans _ _ _ (merge_congr_right pol b (merge pol a b) (merge pol b a)
      (merge_comm pol a b))
    (eqv_trans _ _ _ (le_merge_left pol b a hb) (merge_comm pol b a))

/-- …and it is the *least* one: anything above both is above it. No side
condition — this is associativity and congruence alone. -/
theorem merge_le (pol : Bool) {a b c : CTy} (ha : le pol a c) (hb : le pol b c) :
    le pol (merge pol a b) c :=
  eqv_trans _ _ _ (merge_assoc pol a b c)
    (eqv_trans _ _ _ (merge_congr_right pol a (merge pol b c) c hb) ha)

/-- Least upper bound, spelled out. -/
def IsLub (pol : Bool) (a b m : CTy) : Prop :=
  le pol a m ∧ le pol b m ∧ ∀ u : CTy, le pol a u → le pol b u → le pol m u

/-- `cempty` is the order's least element: it is below everything, with no side
condition (`le_refl` needs `wf`; this does not). -/
theorem le_cempty (pol : Bool) (a : CTy) : le pol cempty a := by
  rw [le, merge_cempty_left]
  exact eqv_refl a

theorem merge_isLub (pol : Bool) (a b : CTy) (ha : wf a = true) (hb : wf b = true) :
    IsLub pol a b (merge pol a b) :=
  ⟨le_merge_left pol a b ha, le_merge_right pol a b hb, fun _ hau hbu => merge_le pol hau hbu⟩

/-- **Uniqueness**: a least upper bound of two positions is the merge, up to
`eqv`. The merge is not *a* way to combine two bounds; it is the only one the
order admits. -/
theorem join_unique (pol : Bool) {a b m : CTy} (ha : wf a = true) (hb : wf b = true)
    (h : IsLub pol a b m) : eqv m (merge pol a b) = true :=
  le_antisymm pol
    (h.2.2 (merge pol a b) (le_merge_left pol a b ha) (le_merge_right pol a b hb))
    (merge_le pol h.1 h.2.1)

end CTy

end CclFormal
