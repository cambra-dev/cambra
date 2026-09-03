import CclFormal.Ty

/-!
# The solver's polar merge and its algebra

The Lean mirror of `src/ccl/infer/solver/compact.rs`'s bound-merging — the operation `coalesce`
folds over a variable's bounds (`CompactType::merge`, `CompactFun::merge`, `merge_refinements`,
`merge_records`, `merge_variants`) — and the theorems that make the solver's order-independence
refinement a proof obligation instead of a fuzz observation:

- `equiv` is an equivalence relation (`equiv_refl`, `equiv_symm`, `equiv_trans`);
- `merge` is commutative (`merge_comm`), idempotent (`merge_idem`, under `wellFormed`),
  and a congruence for `equiv` (`merge_congr_left`/`_right`);
- `merge` is associative (`merge_assoc`), at either polarity and with no side
  condition — the kinds join in a semilattice (`joinKind`) and the domains are combined by polarity
  alone, so no step reads a value a later step can change;
- the fold `coalesce` performs is therefore invariant under permutation
  (`foldMerge_perm`) and duplication (`foldMerge_dup`) of the bound list;
- `merge pol` is the least upper bound of the order it induces, and the *only*
  one up to `equiv` (`merge_is_least_absorber`, `least_absorber_unique`), with the empty position as
  the order's least element (`merge_cempty_left`, `absorbedBy_cempty`).

`differential_polar_merge_vs_lean_model` (`tests/differential_oracle.rs`) is what keeps this a
statement about the solver: it folds generated bound lists through `CompactType::merge` exactly as
`compact_go` does and checks every step against `merge` here, judged by `equiv`.

## What the model is a mirror of, and what it drops

`CompactTy` is the concrete fragment of `CompactType`: atoms, the optional record/variant maps, the
optional function slot, and the refinement slot with its `none` sentinel. Deliberately dropped, with
the reasoning:

- **Inference variables** (`vars`) — the concrete algebra doesn't read them;
  they union like atoms and would only pad every proof.
- **History slots** — transients erased before the strict wall, exactly as
  `Ty` excludes `History` (same-polarity componentwise merge; nothing new).
- **The Pi binder** (`CompactFun::name`, merged `a.name.or(b.name)`) —
  first-wins is order-dependent as written, but the slot carries no refinement identity: a
  refinement's binding is its index (`Name::PiBound`), so the merged refinements agree whatever
  spelling survives, and the slot is display plus the frame's opening address; the asymmetry is
  unobservable.
- **A conflicted slot's domain payload** — `compact.rs` keeps `widest`, which
  picks between two equal-length lists by arrival order. Coalesce prints those alternatives and
  reads nothing from them, so the model drops the payload rather than mirror an order-dependent
  choice, and the differential's encoder drops it too. Every other slot's alternatives are mirrored
  in full: `fn`'s domain slot is a `List CompactTy` matching `DomainSet`, because
  `coalesce_compact_go` folds the contravariant meet over it and two slots differing in the tail
  materialize differently.

## The equivalence is the code's own equality

`equiv` mirrors `CompactType`'s `PartialEq`: set-semantic on atoms and refinements (mirroring
`BTreeSet` and `RefinementSet`), key-set + payload on the maps (mirroring `BTreeMap`), componentwise
on the function slot. The merge's one internal comparison — `union_domains` deduplicating two `Data`
domains — uses that same equality, which is what makes every theorem quotient-compatible: the gate
cannot distinguish two `equiv`-equal inputs.

The empty position **is** an identity (`merge_cempty_left`), because every slot including the
refinement slot has a `none` that merges as one. `compact_go` still folds a variable's bounds from
the *first bound* rather than from `CompactType::default()`, so the fold theorems are stated over
nonempty lists, but that is now the code's habit rather than an algebraic requirement.
-/

namespace CclFormal

/-- Mirror of `compact.rs :: AtomKey` (concrete fragment — `ChanDom` excluded,
the same adjudication as `Ty`'s exclusion of pipeline transients). -/
inductive Atom where
  | prim (b : BaseTy)
  | uintRange (n : Nat)
  | source (s : String)
  | txn
deriving Repr, DecidableEq

/-- Mirror of `compact.rs :: KindMerge`: the flat semilattice
`unknown < {data, compute} < conflict`. `unknown` is a kind variable nothing pinned — the identity,
since nothing *required* a kind there — and `conflict` is the absorbing state a bad kind meeting
leaves behind (coalesce turns it into an
error; it never materializes). -/
inductive KindMerge where
  | data | compute | conflict | unknown
deriving Repr, DecidableEq

/-! ## The refinement slot

`compact.rs`'s `refinements` is an `Option<RefinementSet>`, and the two states are distinct. `none`
is "no refinement contribution here" and merges as the identity — a hole, or a bare variable whose
content is its identity alone — while `some []` is a *value* that guarantees nothing, which is
absorbing under the positive intersect. Collapsing them makes a bare variable erase the refinements
a sibling bound established, which is why the slot carries the same sentinel the
shape slots do. -/

/-- The refinement slot's merge: `none` is the identity, and two present sets
intersect at a positive position and unite at a negative one
(`merge_refinements`). -/
def mergeRefinements (pol : Bool) : Option (List Predicate) → Option (List Predicate) → Option
    (List Predicate)
  | none, c => c
  | c, none => c
  | some p1, some p2 => some (if pol then p1.filter (p2.contains ·) else p1 ++ p2)

/-- Set-semantic equality on the refinement slot, mirroring `RefinementSet`. -/
def refinementsEquiv : Option (List Predicate) → Option (List Predicate) → Bool
  | none, none => true
  | some p1, some p2 => p1.all (p2.contains ·) && p2.all (p1.contains ·)
  | _, _ => false

/-- `refinementsEquiv`, read as mutual membership. -/
theorem refinementsEquiv_iff {p q : List Predicate} :
    refinementsEquiv (some p) (some q) = true ↔ (∀ x ∈ p, x ∈ q) ∧ ∀ x ∈ q, x ∈ p := by
  simp only [refinementsEquiv, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]

theorem refinementsEquiv_refl (c : Option (List Predicate)) : refinementsEquiv c c = true := by
  rcases c with _ | p
  · rfl
  · exact refinementsEquiv_iff.mpr ⟨fun _ h => h, fun _ h => h⟩

theorem refinementsEquiv_symm {a b : Option (List Predicate)} (h : refinementsEquiv a b = true) :
    refinementsEquiv b a = true := by
  rcases a with _ | p <;> rcases b with _ | q
  · rfl
  · exact absurd h (by simp [refinementsEquiv])
  · exact absurd h (by simp [refinementsEquiv])
  · exact refinementsEquiv_iff.mpr (refinementsEquiv_iff.mp h).symm

theorem refinementsEquiv_trans {a b c : Option (List Predicate)} (hab : refinementsEquiv a b = true)
    (hbc : refinementsEquiv b c = true) : refinementsEquiv a c = true := by
  rcases a with _ | p <;> rcases b with _ | q <;> rcases c with _ | r
  case none.none.none => rfl
  case some.some.some =>
    obtain ⟨hpq, hqp⟩ := refinementsEquiv_iff.mp hab
    obtain ⟨hqr, hrq⟩ := refinementsEquiv_iff.mp hbc
    exact refinementsEquiv_iff.mpr ⟨fun x hx => hqr x (hpq x hx), fun x hx => hqp x (hrq x hx)⟩
  -- Every remaining case has one side `none` and the other `some`, which
  -- `refinementsEquiv` refuses.
  all_goals simp_all [refinementsEquiv]

/-- The two present-set cases, read as membership: what every law below reduces
to once the `none` identity arms are out of the way. -/
private theorem mergeRefinements_mem (pol : Bool) (p q : List Predicate) (x : Predicate) :
    (x ∈ (mergeRefinements pol (some p) (some q)).getD [] ↔
      if pol then x ∈ p ∧ x ∈ q else x ∈ p ∨ x ∈ q) := by
  cases pol <;>
    simp only [mergeRefinements, Bool.false_eq_true, reduceIte, Option.getD_some, List.mem_append,
      List.mem_filter, List.contains_iff_mem]

theorem mergeRefinements_comm (pol : Bool) (a b : Option (List Predicate)) :
    refinementsEquiv (mergeRefinements pol a b) (mergeRefinements pol b a) = true := by
  rcases a with _ | p <;> rcases b with _ | q <;>
    first
    | exact refinementsEquiv_refl _
    | skip
  cases pol <;>
    simp only [mergeRefinements, Bool.false_eq_true, reduceIte] <;>
    refine refinementsEquiv_iff.mpr ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
    simp only [List.mem_append, List.mem_filter, List.contains_iff_mem] at hx ⊢ <;>
    first
    | exact hx.symm
    | exact ⟨hx.2, hx.1⟩

theorem mergeRefinements_idem (pol : Bool) (a : Option (List Predicate)) :
    refinementsEquiv (mergeRefinements pol a a) a = true := by
  rcases a with _ | p
  · rfl
  cases pol <;>
    simp only [mergeRefinements, Bool.false_eq_true, reduceIte] <;>
    refine refinementsEquiv_iff.mpr ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
    simp only [List.mem_append, List.mem_filter, List.contains_iff_mem] at hx ⊢ <;>
    first
    | exact hx.elim id id
    | exact Or.inl hx
    | exact hx.1
    | exact ⟨hx, hx⟩

theorem mergeRefinements_assoc (pol : Bool) (a b c : Option (List Predicate)) :
    refinementsEquiv (mergeRefinements pol (mergeRefinements pol a b) c)
      (mergeRefinements pol a (mergeRefinements pol b c)) = true := by
  rcases a with _ | p <;> rcases b with _ | q <;> rcases c with _ | r <;>
    first
    | exact refinementsEquiv_refl _
    | skip
  cases pol <;>
    simp only [mergeRefinements, Bool.false_eq_true, reduceIte] <;>
    refine refinementsEquiv_iff.mpr ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
    simp only [List.mem_append, List.mem_filter, List.contains_iff_mem] at hx ⊢ <;>
    first
    | exact or_assoc.mp hx
    | exact or_assoc.mpr hx
    | exact and_assoc.mp hx
    | exact and_assoc.mpr hx

theorem mergeRefinements_congr_left (pol : Bool) {a a' : Option (List Predicate)}
    (b : Option (List Predicate)) (h : refinementsEquiv a a' = true) :
    refinementsEquiv (mergeRefinements pol a b) (mergeRefinements pol a' b) = true := by
  rcases a with _ | p <;> rcases a' with _ | p'
  · exact refinementsEquiv_refl _
  · exact absurd h (by simp [refinementsEquiv])
  · exact absurd h (by simp [refinementsEquiv])
  rcases b with _ | q
  · exact h
  obtain ⟨hpp, hpp'⟩ := refinementsEquiv_iff.mp h
  cases pol <;>
    simp only [mergeRefinements, Bool.false_eq_true, reduceIte] <;>
    refine refinementsEquiv_iff.mpr ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
    simp only [List.mem_append, List.mem_filter, List.contains_iff_mem] at hx ⊢
  · exact hx.imp (hpp x) id
  · exact hx.imp (hpp' x) id
  · exact ⟨hpp x hx.1, hx.2⟩
  · exact ⟨hpp' x hx.1, hx.2⟩

/-- The kind join at the head of `CompactFun::merge`: `unknown` is the identity
(nothing *required* a kind on that side, so the other side's answer stands), `conflict` is
absorbing, a kind meeting itself is itself, and the two concrete kinds are incomparable — neither
reading stands in for the other. One operation
for both polarities. -/
def joinKind : KindMerge → KindMerge → KindMerge
  | .conflict, _ => .conflict
  | _, .conflict => .conflict
  | .unknown, k => k
  | k, .unknown => k
  | k1, k2 => if k1 == k2 then k1 else .conflict

theorem joinKind_comm (a b : KindMerge) : joinKind a b = joinKind b a := by
  cases a <;> cases b <;> rfl

theorem joinKind_assoc (a b c : KindMerge) :
    joinKind (joinKind a b) c = joinKind a (joinKind b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem joinKind_idem (a : KindMerge) : joinKind a a = a := by
  cases a <;> rfl

/-- Mirror of the concrete fragment of `compact.rs :: CompactType`.

The function slot is `(kind, domain, codomain)` with `domain : Option CompactTy` — `some d` is a
single domain alternative, `none` is "two or more distinct alternatives" (see the module docs for
why the tail of `union_domains`' list is diagnostic-only). `recF`/`varT` mirror the
`Option<BTreeMap<..>>` fields: `none` is the merge identity ("no component here"), `some []` the
absorbing
empty shape — the distinction `compact.rs` documents as load-bearing. -/
inductive CompactTy where
  | mk (atoms : List Atom)
       (recF : Option (List (FieldKey × CompactTy)))
       (varT : Option (List (FieldKey × CompactTy)))
       (fn : Option (KindMerge × CompactTy × CompactTy))
       (refinements : Option (List Predicate))
deriving Repr

namespace CompactTy

/-- `sizeOf` of a looked-up payload is below the map's. -/
theorem lookup_sizeOf {m : List (FieldKey × CompactTy)} {k : FieldKey} {w : CompactTy}
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
def equiv : CompactTy → CompactTy → Bool
  | .mk a1 r1 v1 f1 c1, .mk a2 r2 v2 f2 c2 =>
    a1.all (a2.contains ·) && a2.all (a1.contains ·)
      && (match r1, r2 with
          | none, none => true
          | some m1, some m2 =>
            subtypeKeys m1 m2 (m1.map Prod.fst) && subtypeKeys m2 m1 (m2.map Prod.fst)
          | _, _ => false)
      && (match v1, v2 with
          | none, none => true
          | some m1, some m2 =>
            subtypeKeys m1 m2 (m1.map Prod.fst) && subtypeKeys m2 m1 (m2.map Prod.fst)
          | _, _ => false)
      && (match f1, f2 with
          | none, none => true
          | some (k1, d1, c1), some (k2, d2, c2) =>
            k1 == k2 && equiv d1 d2 && equiv c1 c2
          | _, _ => false)
      && refinementsEquiv c1 c2
termination_by a b => (sizeOf a + sizeOf b, 0)

/-- Keyed containment over a key worklist: every key in `ks` resolves in both
maps to `equiv` payloads. Driven by `lookup` on **both** sides (not the peeled entry), so a shadowed
duplicate binding is unobservable — mirroring `BTreeMap`, which cannot hold one. `equiv` calls it
with `ks = m1.map Prod.fst`
in both directions. -/
def subtypeKeys (m1 m2 : List (FieldKey × CompactTy)) : List FieldKey → Bool
  | [] => true
  | k :: ks =>
    (match h1 : m1.lookup k, h2 : m2.lookup k with
     | some v, some w => equiv v w
     | _, _ => false)
      && subtypeKeys m1 m2 ks
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

`equiv`'s fn clause compares them with `subtypeDomains`, and every law below reasons through
`anyEquiv_iff`/`subtypeDomains_iff`, so the representation is never touched again. This is the one
place `equiv` is deliberately coarser than `CompactFun`'s derived `PartialEq`, which compares the
`Vec` positionally: `union_domains` deduplicates the alternatives and their only readers are a
`Data` slot's refusal to hold more than one and a `Compute` slot's commutative meet-fold at
coalesce, so their order carries no information. That the order is unobservable downstream is what
`tests/constraint_order_fuzz.rs` checks, by comparing coalesced outcomes across arrival
orders. -/

/-! ## The merge -/

mutual

/-- Mirror of `CompactType::merge` (concrete fragment). `pol` is the polarity:
positive merges are joins (types union, refinements/record-keys intersect, variant
tags union), negative merges are meets (the duals). -/
def merge (pol : Bool) : CompactTy → CompactTy → CompactTy
  | .mk a1 r1 v1 f1 c1, .mk a2 r2 v2 f2 c2 =>
    .mk (a1 ++ a2)
        (match r1, r2 with
         | none, r | r, none => r
         | some m1, some m2 =>
           some
             (if pol then intersectMap pol m1 m2
              else unionMapGo pol m1 m2 ++ m2.filter (fun kw => (m1.lookup kw.1).isNone)))
        (match v1, v2 with
         | none, v | v, none => v
         | some m1, some m2 =>
           some
             (if pol then unionMapGo pol m1 m2 ++ m2.filter (fun kw => (m1.lookup kw.1).isNone)
              else intersectMap pol m1 m2))
        (match f1, f2 with
         | none, f | f, none => f
         | some s1, some s2 => some (mergeFun pol s1 s2))
        (mergeRefinements pol c1 c2)
termination_by a b => sizeOf a + sizeOf b

/-- Keyed merge, intersecting keys (records at positive polarity, variants at
negative): keep only keys present on both sides, payloads merged at the outer
polarity (covariant depth — `merge_keyed` with `intersect_keys = true`). -/
def intersectMap (pol : Bool) :
    List (FieldKey × CompactTy) → List (FieldKey × CompactTy) → List (FieldKey × CompactTy)
  | [], _ => []
  | (k, v) :: rest, m2 =>
    match h : m2.lookup k with
    | some w => (k, merge pol v w) :: intersectMap pol rest m2
    | none => intersectMap pol rest m2
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
variants at positive — `merge_keyed` with `intersect_keys = false`): every key of `m1`, merged with
`m2`'s payload when present. The full union appends `m2`'s leftover keys: `unionMapGo pol m1 m2 ++
m2.filter (·.1 ∉ keys m1)` —
see [`unionMap`]. -/
def unionMapGo (pol : Bool) :
    List (FieldKey × CompactTy) → List (FieldKey × CompactTy) → List (FieldKey × CompactTy)
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

/-- Mirror of `CompactFun::merge` (see module docs for the `Option CompactTy`
domain encoding and the dropped binder/diagnostic payloads).

The kinds join in the [`KindMerge`] semilattice and the domain merges **contravariantly**, as one
ordinary position: there is no domain lattice to consult, because a `fun` slot holds one domain.
What was a join or meet of candidate sets is the same `merge` every other position gets, and a
candidate set lives one level up, on the witness a Σ binds (`compact.rs`, `CompactFun::domain`).

Nothing reads the kind, which is what makes the operation associative — the kind a slot ends at is
not known until the last bound has merged, so a domain rule selected from it would let association
decide the outcome. `compact.rs` defers the kind's own rule to `coalesce_compact_go`.

A conflicted kind keeps its domain rather than dropping it: `CompactFun::merge` computes the domain
before the kinds join and stores it either way, so there is no payload for the model to drop. -/
def mergeFun (pol : Bool) :
    KindMerge × CompactTy × CompactTy → KindMerge × CompactTy × CompactTy → KindMerge ×
      CompactTy × CompactTy
  | (k1, d1, c1), (k2, d2, c2) =>
    (joinKind k1 k2, merge (!pol) d1 d2, merge pol c1 c2)
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp; omega)



end

/-- Keyed merge, uniting keys: keys of either side, payloads merged where both
are present. (Defined outside the mutual block — it makes no recursive call of its own, and the
well-founded measure cannot see through a same-size wrapper;
`merge` inlines this same expression.) -/
def unionMap (pol : Bool) (m1 m2 : List (FieldKey × CompactTy)) :
    List (FieldKey × CompactTy) :=
  unionMapGo pol m1 m2 ++ m2.filter (fun kw => (m1.lookup kw.1).isNone)

/-! ## Pointwise readings

Everything below reasons about maps through `lookup` — the merged maps are characterized pointwise
(`intersectMap_lookup`, `unionMap_lookup`), and `subtypeKeys` unfolds to a per-key statement
(`subtypeKeys_iff`), so the set-level proofs never
touch the association-list representation again. -/

/-- A `lookup` hit means the key occurs in the key list. -/
theorem mem_keys_of_lookup {m : List (FieldKey × CompactTy)} {k : FieldKey} {v : CompactTy}
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
theorem lookup_of_mem_keys {m : List (FieldKey × CompactTy)} {k : FieldKey}
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

/-- `subtypeKeys`, read per key. -/
theorem subtypeKeys_iff {m1 m2 : List (FieldKey × CompactTy)} {ks : List FieldKey} :
    subtypeKeys m1 m2 ks = true ↔
      ∀ k ∈ ks, ∃ v w, m1.lookup k = some v ∧ m2.lookup k = some w ∧ equiv v w = true := by
  induction ks with
  | nil => simp [subtypeKeys]
  | cons k ks ih =>
    rw [subtypeKeys, Bool.and_eq_true, ih]
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

/-! ## `equiv` is an equivalence relation -/

theorem equiv_refl : (t : CompactTy) → equiv t t = true
  | .mk a r v f c => by
    have hmap : ∀ (m : List (FieldKey × CompactTy)), sizeOf m < sizeOf (CompactTy.mk a r v f c) →
        subtypeKeys m m (m.map Prod.fst) = true := by
      intro m hm
      rw [subtypeKeys_iff]
      intro k hk
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (lookup_of_mem_keys hk)
      have hsz : sizeOf w < sizeOf (CompactTy.mk a r v f c) :=
        Nat.lt_trans (lookup_sizeOf hw) hm
      exact ⟨w, w, hw, hw, equiv_refl w⟩
    rw [equiv.eq_def]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp [List.all_eq_true]
    · simp [List.all_eq_true]
    · rcases r with _ | m
      · rfl
      · have hm : sizeOf m < sizeOf (CompactTy.mk a (some m) v f c) := by
          simp
          omega
        simp [hmap m hm]
    · rcases v with _ | m
      · rfl
      · have hm : sizeOf m < sizeOf (CompactTy.mk a r (some m) f c) := by
          simp
          omega
        simp [hmap m hm]
    · rcases f with _ | ⟨k, d, cod⟩
      · rfl
      · have hszd : sizeOf d < sizeOf (CompactTy.mk a r v (some (k, d, cod)) c) := by
          simp
          omega
        have hszc : sizeOf cod < sizeOf (CompactTy.mk a r v (some (k, d, cod)) c) := by
          simp
          omega
        simp [equiv_refl d, equiv_refl cod]
    · exact refinementsEquiv_refl c
termination_by t => sizeOf t
decreasing_by all_goals omega

/-- Unfolded, pointwise reading of the map clause both `equiv` map slots use. -/
theorem mapClause_iff {m1 m2 : List (FieldKey × CompactTy)} :
    (subtypeKeys m1 m2 (m1.map Prod.fst) && subtypeKeys m2 m1 (m2.map Prod.fst)) = true ↔
      (∀ k, (m1.lookup k).isSome ↔ (m2.lookup k).isSome) ∧
        (∀ k v w, m1.lookup k = some v → m2.lookup k = some w → equiv v w = true)
          ∧ ∀ k v w, m1.lookup k = some v → m2.lookup k = some w → equiv w v = true := by
  rw [Bool.and_eq_true, subtypeKeys_iff, subtypeKeys_iff]
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

theorem equiv_symm : (a b : CompactTy) → equiv a b = true → equiv b a = true
  | .mk a1 r1 v1 f1 c1, .mk a2 r2 v2 f2 c2 => by
    intro h
    rw [equiv.eq_def] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, hr⟩, hv⟩, hf⟩, hc⟩ := h
    rw [equiv.eq_def]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨h2, h1⟩, ?_⟩, ?_⟩, ?_⟩, refinementsEquiv_symm hc⟩
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
            sizeOf (CompactTy.mk a2 r2 v2 (some (k2, d2, cod2)) c2) +
              sizeOf (CompactTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1) := by
          simp
          omega
        have hszd : sizeOf d2 + sizeOf d1 <
            sizeOf (CompactTy.mk a2 r2 v2 (some (k2, d2, cod2)) c2) +
              sizeOf (CompactTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1) := by
          simp
          omega
        refine ⟨⟨?_, equiv_symm d1 d2 hd⟩, equiv_symm cod1 cod2 hcod⟩
        · simp at hk
          simp [hk]
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals omega

theorem equiv_trans : (a b c : CompactTy) → equiv a b = true → equiv b c = true → equiv a c = true
  | .mk a1 r1 v1 f1 c1, .mk a2 r2 v2 f2 c2, .mk a3 r3 v3 f3 c3 => by
    intro hab hbc
    rw [equiv.eq_def] at hab hbc
    simp only [Bool.and_eq_true] at hab hbc
    obtain ⟨⟨⟨⟨⟨hab1, hab2⟩, habr⟩, habv⟩, habf⟩, habc⟩ := hab
    obtain ⟨⟨⟨⟨⟨hbc1, hbc2⟩, hbcr⟩, hbcv⟩, hbcf⟩, hbcc⟩ := hbc
    rw [equiv.eq_def]
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
    have hmapTrans : ∀ (m1 m2 m3 : List (FieldKey × CompactTy)),
        sizeOf m1 < sizeOf (CompactTy.mk a1 r1 v1 f1 c1) →
        sizeOf m3 < sizeOf (CompactTy.mk a3 r3 v3 f3 c3) →
        (subtypeKeys m1 m2 (m1.map Prod.fst) && subtypeKeys m2 m1 (m2.map Prod.fst)) = true →
        (subtypeKeys m2 m3 (m2.map Prod.fst) && subtypeKeys m3 m2 (m3.map Prod.fst)) = true →
        (subtypeKeys m1 m3 (m1.map Prod.fst) && subtypeKeys m3 m1 (m3.map Prod.fst)) = true := by
      intro m1 m2 m3 hs1 hs3 h12 h23
      rw [mapClause_iff] at h12 h23 ⊢
      obtain ⟨hdom12, hfwd12, hbwd12⟩ := h12
      obtain ⟨hdom23, hfwd23, hbwd23⟩ := h23
      refine ⟨fun k => (hdom12 k).trans (hdom23 k), fun k x z hx hz => ?_, fun k x z hx hz => ?_⟩
      · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ((hdom12 k).mp (by simp [hx]))
        have hxy := hfwd12 k x y hx hy
        have hyz := hfwd23 k y z hy hz
        have hszx : sizeOf x < sizeOf (CompactTy.mk a1 r1 v1 f1 c1) :=
          Nat.lt_trans (lookup_sizeOf hx) hs1
        have hszz : sizeOf z < sizeOf (CompactTy.mk a3 r3 v3 f3 c3) :=
          Nat.lt_trans (lookup_sizeOf hz) hs3
        exact equiv_trans x y z hxy hyz
      · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ((hdom12 k).mp (by simp [hx]))
        have hzy := hbwd23 k y z hy hz
        have hyx := hbwd12 k x y hx hy
        have hszx : sizeOf x < sizeOf (CompactTy.mk a1 r1 v1 f1 c1) :=
          Nat.lt_trans (lookup_sizeOf hx) hs1
        have hszz : sizeOf z < sizeOf (CompactTy.mk a3 r3 v3 f3 c3) :=
          Nat.lt_trans (lookup_sizeOf hz) hs3
        exact equiv_trans z y x hzy hyx
    refine ⟨⟨⟨⟨⟨hsub a1 a2 a3 hab1 hbc1, hsub a3 a2 a1 hbc2 hab2⟩, ?_⟩, ?_⟩, ?_⟩,
      refinementsEquiv_trans habc hbcc⟩
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
          sizeOf (CompactTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1) +
            sizeOf (CompactTy.mk a3 r3 v3 (some (k3, d3, cod3)) c3) := by
        simp
        omega
      have hszd : sizeOf d1 + sizeOf d3 <
          sizeOf (CompactTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1) +
            sizeOf (CompactTy.mk a3 r3 v3 (some (k3, d3, cod3)) c3) := by
        simp
        omega
      refine ⟨⟨?_, equiv_trans d1 d2 d3 habd hbcd⟩, equiv_trans cod1 cod2 cod3 habcod hbccod⟩
      · simp at habk hbck
        simp [habk, hbck]
termination_by a _ c => sizeOf a + sizeOf c
decreasing_by all_goals omega

/-! ## The domain alternatives: the algebra -/

/-! ### The negative arm, characterized

`meetDomains` is defined on a singleton pair and nowhere else, so every proof about
a negative merge splits on that once, here, rather than over nine list shapes. -/

/-! ## Pointwise readings of the merged maps -/

/-- `intersectMap`, read through `lookup`: defined exactly when both sides have
the key, payload the merge of the two firsts. -/
theorem intersectMap_lookup {pol : Bool} {m1 m2 : List (FieldKey × CompactTy)} {k : FieldKey} :
    (intersectMap pol m1 m2).lookup k =
      match m1.lookup k, m2.lookup k with
      | some v, some w => some (merge pol v w)
      | _, _ => none := by
  induction m1 with
  | nil => simp [intersectMap, List.lookup]
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    rw [intersectMap]
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
theorem unionMapGo_lookup {pol : Bool} {m1 m2 : List (FieldKey × CompactTy)} {k : FieldKey} :
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
    · simp only [ih]
    · have : k = k' := by simpa using hk
      subst this
      rcases h2 : m2.lookup k with _ | w' <;> simp

/-- Looking up in the `m2` leftovers (keys absent from `m1`): the filter
predicate depends only on the key, so the first `k`-entry survives exactly
when `m1` lacks `k`. -/
theorem lookup_filter_leftover {m1 m2 : List (FieldKey × CompactTy)} {k : FieldKey} :
    (m2.filter (fun kw => (m1.lookup kw.1).isNone)).lookup k =
      if (m1.lookup k).isNone then m2.lookup k else none := by
  induction m2 with
  | nil => simp [List.lookup]
  | cons hd tl ih =>
    obtain ⟨k', w'⟩ := hd
    rw [List.filter_cons]
    rcases h1 : (m1.lookup k').isNone with _ | _
    · simp only [Bool.false_eq_true, if_false, ih]
      rcases hk : k == k' with _ | _
      · rw [List.lookup_cons]
        simp [hk]
      · have : k = k' := by simpa using hk
        subst this
        rw [List.lookup_cons]
        simp [h1]
    · simp only [if_true]
      rw [List.lookup_cons, List.lookup_cons]
      rcases hk : k == k' with _ | _
      · simp only [ih]
      · have : k = k' := by simpa using hk
        subst this
        simp [h1]

/-- `unionMap`, read through `lookup`. -/
theorem unionMap_lookup {pol : Bool} {m1 m2 : List (FieldKey × CompactTy)} {k : FieldKey} :
    (unionMap pol m1 m2).lookup k =
      match m1.lookup k, m2.lookup k with
      | some v, some w => some (merge pol v w)
      | some v, none => some v
      | none, some w => some w
      | none, none => none := by
  rw [unionMap, List.lookup_append, unionMapGo_lookup, lookup_filter_leftover]
  rcases h1 : m1.lookup k with _ | v <;> rcases h2 : m2.lookup k with _ | w <;> simp

/-- The merge leaves a slot absent only when both operands do: the atom lists
concatenate, each shape slot takes the other side's when one is the identity, and the refinement
slots merge. What a slot *holds* is the polarity's question; that
it is populated at all is not. -/
theorem merge_slots (pol : Bool) (a1 a2 : List Atom)
    (r1 r2 v1 v2 : Option (List (FieldKey × CompactTy)))
    (f1 f2 : Option (KindMerge × CompactTy × CompactTy)) (c1 c2 : Option (List Predicate)) :
    ∃ r v f, merge pol (.mk a1 r1 v1 f1 c1) (.mk a2 r2 v2 f2 c2)
        = .mk (a1 ++ a2) r v f (mergeRefinements pol c1 c2) ∧
      (r = none ↔ r1 = none ∧ r2 = none) ∧ (v = none ↔ v1 = none ∧ v2 = none) ∧
      (f = none ↔ f1 = none ∧ f2 = none) := by
  rw [merge.eq_def]
  refine ⟨_, _, _, rfl, ?_, ?_, ?_⟩
  · rcases r1 with _ | m1 <;> rcases r2 with _ | m2 <;> simp
  · rcases v1 with _ | m1 <;> rcases v2 with _ | m2 <;> simp
  · rcases f1 with _ | g1 <;> rcases f2 with _ | g2 <;> simp

/-! ## The merge algebra: commutativity -/

/-- The dedup gate is symmetric as a *Bool*: `equiv x y = equiv y x`. -/
theorem equiv_comm_bool (x y : CompactTy) : equiv x y = equiv y x := by
  rcases h : equiv y x with _ | _
  · rcases h' : equiv x y with _ | _
    · rfl
    · rw [equiv_symm x y h'] at h
      exact h
  · exact equiv_symm y x h

/-- `subtypeKeys` is reflexive on any map (shadowed duplicates are unobservable). -/
theorem subtypeKeys_self (m : List (FieldKey × CompactTy)) : subtypeKeys m m (m.map Prod.fst) = true
    := by
  rw [subtypeKeys_iff]
  intro k hk
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (lookup_of_mem_keys hk)
  exact ⟨v, v, hv, hv, equiv_refl v⟩

/-- The function-slot equivalence, as a `Prop` (the shape `equiv`'s fn clause
checks, lifted off the Bool so case analyses stay readable). -/
def FunEquiv : KindMerge × CompactTy × CompactTy → KindMerge × CompactTy × CompactTy →
    Prop
  | (k1, d1, c1), (k2, d2, c2) =>
    k1 = k2
      ∧ equiv d1 d2 = true
      ∧ equiv c1 c2 = true

/-- `FunEquiv` is exactly `equiv`'s fn clause. -/
theorem funClause_of_funEquiv {s1 s2 : KindMerge × CompactTy × CompactTy}
    (h : FunEquiv s1 s2) :
    (s1.1 == s2.1
      && equiv s1.2.1 s2.2.1
      && equiv s1.2.2 s2.2.2) = true := by
  obtain ⟨k1, d1, c1⟩ := s1
  obtain ⟨k2, d2, c2⟩ := s2
  obtain ⟨hk, hd, hc⟩ := h
  subst hk
  simp only [Bool.and_eq_true]
  refine ⟨⟨by simp, ?_⟩, hc⟩
  rcases d1 with _ | x <;> rcases d2 with _ | y <;> simp_all

mutual

theorem merge_comm (pol : Bool) : (a b : CompactTy) → equiv (merge pol a b) (merge pol b a) = true
  | .mk a1 r1 v1 f1 c1, .mk a2 r2 v2 f2 c2 => by
    -- Pointwise commutativity of the two keyed merges, packaged with the size
    -- bounds the recursive calls need.
    have hinter : ∀ (p : Bool) (m1 m2 : List (FieldKey × CompactTy)),
        (∀ x y k, m1.lookup k = some x → m2.lookup k = some y →
          equiv (merge p x y) (merge p y x) = true) →
        (subtypeKeys (intersectMap p m1 m2) (intersectMap p m2 m1)
            ((intersectMap p m1 m2).map Prod.fst) &&
          subtypeKeys (intersectMap p m2 m1) (intersectMap p m1 m2)
            ((intersectMap p m2 m1).map Prod.fst)) = true := by
      intro p m1 m2 hcomm
      rw [mapClause_iff]
      refine ⟨fun k => ?_, fun k x y hx hy => ?_, fun k x y hx hy => ?_⟩
      · rw [intersectMap_lookup, intersectMap_lookup]
        rcases m1.lookup k with _ | v <;> rcases m2.lookup k with _ | w <;> simp
      · rw [intersectMap_lookup] at hx hy
        rcases h1 : m1.lookup k with _ | v <;> rcases h2 : m2.lookup k with _ | w <;>
            rw [h1, h2] at hx hy <;> dsimp only at hx hy
        · exact absurd hx (by simp)
        · exact absurd hx (by simp)
        · exact absurd hx (by simp)
        · cases hx
          cases hy
          exact hcomm v w k h1 h2
      · rw [intersectMap_lookup] at hx hy
        rcases h1 : m1.lookup k with _ | v <;> rcases h2 : m2.lookup k with _ | w <;>
            rw [h1, h2] at hx hy <;> dsimp only at hx hy
        · exact absurd hx (by simp)
        · exact absurd hx (by simp)
        · exact absurd hx (by simp)
        · cases hx
          cases hy
          exact equiv_symm _ _ (hcomm v w k h1 h2)
    have hunion : ∀ (p : Bool) (m1 m2 : List (FieldKey × CompactTy)),
        (∀ x y k, m1.lookup k = some x → m2.lookup k = some y →
          equiv (merge p x y) (merge p y x) = true) →
        (subtypeKeys (unionMap p m1 m2) (unionMap p m2 m1)
            ((unionMap p m1 m2).map Prod.fst) &&
          subtypeKeys (unionMap p m2 m1) (unionMap p m1 m2)
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
          exact equiv_refl _
        · cases hx
          cases hy
          exact equiv_refl _
        · cases hx
          cases hy
          exact hcomm v w k h1 h2
      · rw [unionMap_lookup] at hx hy
        rcases h1 : m1.lookup k with _ | v <;> rcases h2 : m2.lookup k with _ | w <;>
            rw [h1, h2] at hx hy <;> dsimp only at hx hy
        · exact absurd hx (by simp)
        · cases hx
          cases hy
          exact equiv_refl _
        · cases hx
          cases hy
          exact equiv_refl _
        · cases hx
          cases hy
          exact equiv_symm _ _ (hcomm v w k h1 h2)
    rw [merge.eq_def, merge.eq_def, equiv.eq_def]
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
      · simp [subtypeKeys_self]
      · simp [subtypeKeys_self]
      · have hpay : ∀ x y k, m1.lookup k = some x → m2.lookup k = some y →
            equiv (merge pol x y) (merge pol y x) = true := by
          intro x y k hx hy
          have hszx := lookup_sizeOf hx
          have hszy := lookup_sizeOf hy
          exact merge_comm pol x y
        cases pol
        · simpa [unionMap] using hunion false m1 m2 hpay
        · simpa [unionMap] using hinter true m1 m2 hpay
    · rcases v1 with _ | m1 <;> rcases v2 with _ | m2
      · rfl
      · simp [subtypeKeys_self]
      · simp [subtypeKeys_self]
      · have hpay : ∀ x y k, m1.lookup k = some x → m2.lookup k = some y →
            equiv (merge pol x y) (merge pol y x) = true := by
          intro x y k hx hy
          have hszx := lookup_sizeOf hx
          have hszy := lookup_sizeOf hy
          exact merge_comm pol x y
        cases pol
        · simpa [unionMap] using hinter false m1 m2 hpay
        · simpa [unionMap] using hunion true m1 m2 hpay
    · rcases f1 with _ | ⟨k1, d1, cod1⟩ <;> rcases f2 with _ | ⟨k2, d2, cod2⟩
      · rfl
      · simpa using funClause_of_funEquiv (s1 := (k2, d2, cod2)) (s2 := (k2, d2, cod2))
          ⟨rfl, equiv_refl d2, equiv_refl cod2⟩
      · simpa using funClause_of_funEquiv (s1 := (k1, d1, cod1)) (s2 := (k1, d1, cod1))
          ⟨rfl, equiv_refl d1, equiv_refl cod1⟩
      · have hsz : sizeOf (k1, d1, cod1) + sizeOf (k2, d2, cod2) <
            sizeOf (CompactTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1) +
              sizeOf (CompactTy.mk a2 r2 v2 (some (k2, d2, cod2)) c2) := by
          simp
          omega
        simpa using funClause_of_funEquiv
          (mergeFun_comm pol (k1, d1, cod1) (k2, d2, cod2))
    · exact mergeRefinements_comm pol c1 c2
termination_by a b => (sizeOf a + sizeOf b, 1)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

theorem mergeFun_comm (pol : Bool) : (s1 s2 : KindMerge × CompactTy × CompactTy) →
    FunEquiv (mergeFun pol s1 s2) (mergeFun pol s2 s1)
  | (k1, d1, c1), (k2, d2, c2) => by
    have hszd : sizeOf d1 + sizeOf d2 < sizeOf (k1, d1, c1) + sizeOf (k2, d2, c2) := by
      simp
      omega
    have hszc : sizeOf c1 + sizeOf c2 < sizeOf (k1, d1, c1) + sizeOf (k2, d2, c2) := by
      simp
      omega
    rw [mergeFun, mergeFun]
    exact ⟨joinKind_comm k1 k2, merge_comm (!pol) d1 d2, merge_comm pol c1 c2⟩
termination_by a b => (sizeOf a + sizeOf b, 0)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; omega)
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

end

/-! ## Depth

The measure materialization terminates on. `merge` combines contributions pointwise and never nests
one inside another, so a merged position is no deeper than the deeper of its inputs
(`merge_depth_le`) — which is what bounds `coalesce`'s recursion through a `Compute` slot's folded
alternatives, a call no
`sizeOf` measure reaches. -/

mutual

/-- Nesting depth: one for the position, plus the deepest child. Atoms and refinements
do not nest, so they do not count. -/
def depth : CompactTy → Nat
  | .mk _ recF varT fn _ =>
    1 + Nat.max (optMapDepth recF) (Nat.max (optMapDepth varT) (optFnDepth fn))

def optMapDepth : Option (List (FieldKey × CompactTy)) → Nat
  | none => 0
  | some m => mapDepth m

def mapDepth : List (FieldKey × CompactTy) → Nat
  | [] => 0
  | (_, w) :: rest => Nat.max (depth w) (mapDepth rest)

def optFnDepth : Option (KindMerge × CompactTy × CompactTy) → Nat
  | none => 0
  | some (_, d, cod) => Nat.max (depth d) (depth cod)

end

/-! ### Reading `depth` -/

theorem depth_pos (t : CompactTy) : 1 ≤ depth t := by
  rcases t with ⟨a, r, v, f, c⟩
  rw [depth]
  omega

theorem le_mapDepth {m : List (FieldKey × CompactTy)} {p : FieldKey × CompactTy} (h : p ∈ m) :
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

theorem mapDepth_le {m : List (FieldKey × CompactTy)} {b : Nat}
    (h : ∀ p ∈ m, depth p.2 ≤ b) : mapDepth m ≤ b := by
  induction m with
  | nil => simp [mapDepth]
  | cons hd tl ih =>
    rcases hd with ⟨k, w⟩
    rw [mapDepth]
    exact Nat.max_le.mpr ⟨h (k, w) (by simp), ih fun p hp => h p (by simp [hp])⟩

/-- A resolved key names a real binding. Over an arbitrary key type, since the
model looks keys up in `Ty`-valued and `CompactTy`-valued maps alike. -/
theorem mem_of_lookup {α β} [BEq α] [LawfulBEq α] {m : List (α × β)} {k : α} {w : β}
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

/-- Every entry of `intersectMap` is a merge of one from each side. -/
theorem mem_intersectMap {pol : Bool} {m1 m2 : List (FieldKey × CompactTy)}
    {p : FieldKey × CompactTy}
    (hp : p ∈ intersectMap pol m1 m2) :
    ∃ v w, (p.1, v) ∈ m1 ∧ (p.1, w) ∈ m2 ∧ p.2 = merge pol v w := by
  induction m1 with
  | nil => exact absurd hp (by simp [intersectMap])
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    rw [intersectMap] at hp
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
theorem mem_unionMapGo {pol : Bool} {m1 m2 : List (FieldKey × CompactTy)} {p : FieldKey × CompactTy}
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
      · exact ⟨v, by simp, Or.inl (by simp)⟩
      · exact ⟨v, by simp, Or.inr ⟨w, mem_of_lookup hw, by simp⟩⟩
    · obtain ⟨v', hv', hrest⟩ := ih h'
      exact ⟨v', List.mem_cons.mpr (Or.inr hv'), hrest⟩

/-- The codomain is merged whatever else the slots do. -/
theorem mergeFun_cod (pol : Bool) (s1 s2 : KindMerge × CompactTy × CompactTy) :
    (mergeFun pol s1 s2).2.2 = merge pol s1.2.2 s2.2.2 := by
  obtain ⟨k1, d1, c1⟩ := s1
  obtain ⟨k2, d2, c2⟩ := s2
  rw [mergeFun]

/-- A slot whose kinds join to a conflict merges to the conflicted slot, at either polarity. Its
domain is merged like any other, since `CompactFun::merge` computes the domain before the kinds
join. -/
theorem mergeFun_of_conflict (pol : Bool) (s1 s2 : KindMerge × CompactTy × CompactTy)
    (h : joinKind s1.1 s2.1 = .conflict) :
    mergeFun pol s1 s2
      = (.conflict, merge (!pol) s1.2.1 s2.2.1, merge pol s1.2.2 s2.2.2) := by
  obtain ⟨k1, d1, c1⟩ := s1
  obtain ⟨k2, d2, c2⟩ := s2
  rw [mergeFun, h]

/-! ### `merge` does not deepen a position

Each component of the merged position is built from components of the inputs, so the whole is no
deeper than the deeper input. The three lemmas below take the recursion as a hypothesis, which keeps
them out of any mutual block; `merge_depth_le`
supplies it by induction on a depth bound. -/

theorem intersectMap_depth_le {pol : Bool} {m1 m2 : List (FieldKey × CompactTy)} {bnd : Nat}
    (h1 : mapDepth m1 ≤ bnd) (h2 : mapDepth m2 ≤ bnd)
    (hrec : ∀ v w, depth v ≤ mapDepth m1 → depth w ≤ mapDepth m2 →
      depth (merge pol v w) ≤ Nat.max (depth v) (depth w)) :
    mapDepth (intersectMap pol m1 m2) ≤ bnd := by
  refine mapDepth_le fun p hp => ?_
  obtain ⟨v, w, hv, hw, he⟩ := mem_intersectMap hp
  rw [he]
  exact Nat.le_trans (hrec v w (le_mapDepth (p := (p.1, v)) hv) (le_mapDepth (p := (p.1, w)) hw))
    (Nat.max_le.mpr ⟨Nat.le_trans (le_mapDepth (p := (p.1, v)) hv) h1,
      Nat.le_trans (le_mapDepth (p := (p.1, w)) hw) h2⟩)

theorem unionMap_depth_le {pol : Bool} {m1 m2 : List (FieldKey × CompactTy)} {bnd : Nat}
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

theorem mergeFun_depth_le {pol : Bool} {k1 k2 : KindMerge} {d1 d2 c1 c2 : CompactTy}
    (hdom : depth (merge (!pol) d1 d2) ≤ Nat.max (depth d1) (depth d2))
    (hcod : depth (merge pol c1 c2) ≤ Nat.max (depth c1) (depth c2)) :
    optFnDepth (some (mergeFun pol (k1, d1, c1) (k2, d2, c2)))
      ≤ Nat.max (optFnDepth (some (k1, d1, c1))) (optFnDepth (some (k2, d2, c2))) := by
  rw [mergeFun, optFnDepth, optFnDepth, optFnDepth]
  refine Nat.max_le.mpr ⟨?_, ?_⟩
  · refine Nat.le_trans hdom (Nat.max_le.mpr ⟨?_, ?_⟩)
    · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  · refine Nat.le_trans hcod (Nat.max_le.mpr ⟨?_, ?_⟩)
    · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

theorem succ_max_le (A B : Nat) : 1 + Nat.max A B ≤ Nat.max (1 + A) (1 + B) := by
  simp only [Nat.max_def]
  split <;> split <;> omega

/-- A position is one deeper than its deepest component. -/
theorem depth_mk_le {a1 : List Atom} {r v : Option (List (FieldKey × CompactTy))}
    {f : Option (KindMerge × CompactTy × CompactTy)} {c : Option (List Predicate)} {bnd : Nat}
    (hr : optMapDepth r ≤ bnd) (hv : optMapDepth v ≤ bnd) (hf : optFnDepth f ≤ bnd) :
    depth (CompactTy.mk a1 r v f c) ≤ 1 + bnd := by
  rw [depth]
  exact Nat.add_le_add_left (Nat.max_le.mpr ⟨hr, Nat.max_le.mpr ⟨hv, hf⟩⟩) 1

/-- **`merge` does not deepen a position.** Every component of the merged position
is built from components of the inputs — atoms and refinements union, map payloads merge pointwise,
a function slot's alternatives come from one side or are a meet of one from each, and its codomain
is a merge of the two — so the whole is no deeper than the deeper input.

By induction on a depth bound rather than on the term, because the statement is needed exactly where
no structural measure works: `coalesce`'s recursion through a `Compute` slot's folded alternatives
materializes a `merge` result, not a subterm.
`compact.rs` relies on this and states it nowhere. -/
theorem merge_depth_le_bounded : ∀ (n : Nat) (pol : Bool) (a b : CompactTy),
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
    have hchild : ∀ x y : CompactTy,
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
    -- The domain merges **contravariantly**, so the child bound is needed at `!pol` too.
    have hchild' : ∀ x y : CompactTy,
        depth x ≤ Nat.max (optMapDepth r1) (Nat.max (optMapDepth v1) (optFnDepth f1)) →
        depth y ≤ Nat.max (optMapDepth r2) (Nat.max (optMapDepth v2) (optFnDepth f2)) →
        depth (merge (!pol) x y) ≤ Nat.max (depth x) (depth y) := by
      intro x y hx hy
      have hA : Nat.max (optMapDepth r1) (Nat.max (optMapDepth v1) (optFnDepth f1)) ≤ n := by
        rw [depth] at ha
        omega
      have hB : Nat.max (optMapDepth r2) (Nat.max (optMapDepth v2) (optFnDepth f2)) ≤ n := by
        rw [depth] at hb
        omega
      exact ih (!pol) x y (Nat.le_trans hx hA) (Nat.le_trans hy hB)
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
          · simpa [optMapDepth] using intersectMap_depth_le h1 h2 hr
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
          · simpa [optMapDepth] using intersectMap_depth_le h1 h2 hr
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
          have hdom : depth (merge (!pol) d1 d2) ≤ Nat.max (depth d1) (depth d2) :=
            hchild' d1 d2
              (Nat.le_trans (Nat.le_max_left _ _)
                (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
              (Nat.le_trans (Nat.le_max_left _ _)
                (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
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
theorem merge_depth_le (pol : Bool) (a b : CompactTy) :
    depth (merge pol a b) ≤ Nat.max (depth a) (depth b) :=
  merge_depth_le_bounded (Nat.max (depth a) (depth b)) pol a b
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-! ## Well-formedness of input bounds

`compact_go` builds every bound's `CompactTy` from a `Type`: a function contributes exactly one
domain and a concrete kind (`AtomKey::from_type` / the `Type::Fun` arm), so an *input* bound never
carries a `conflict` kind or a multi-domain slot — those states are only ever *produced* by merging.
Idempotence (and the fold's duplicate-invariance) is stated under this invariant: a conflicted or
domain-less slot is an error state the solver never feeds back in, and `equiv`-idempotence genuinely
fails there (the model's conflict arm canonicalizes
the diagnostic payload away). -/

mutual

/-- Keys are duplicate-free, mirroring the `BTreeMap` the map stands for, which
cannot hold two bindings for one key. `equiv` is blind to a shadowed duplicate because it compares
by `lookup`, but `coalesce` materializes every entry and
`subtypeTags` checks every one, so a duplicate is observable in the type. -/
def nodupKeys : List FieldKey → Bool
  | [] => true
  | k :: ks => !ks.contains k && nodupKeys ks

/-- The input-bound invariant (see the section header). -/
def wellFormed : CompactTy → Bool
  | .mk atoms r v f c =>
    (match r with
     | none => true
     | some m => wellFormedKeys m (m.map Prod.fst) && nodupKeys (m.map Prod.fst))
      && (match v with
          | none => true
          | some m => wellFormedKeys m (m.map Prod.fst) && nodupKeys (m.map Prod.fst))
      && (match f with
          | none => true
          | some (k, d, cod) =>
            -- One domain is the slot's *type* now, so well-formedness only asks that it be
            -- well-formed. It used to ask for a singleton list here.
            (k != .conflict) && wellFormed d && wellFormed cod)
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

/-- All payloads of a map are `wellFormed` (worklist form, like `subtypeKeys`). -/
def wellFormedKeys (m : List (FieldKey × CompactTy)) : List FieldKey → Bool
  | [] => true
  | k :: ks =>
    (match h : m.lookup k with
     | some v => wellFormed v
     | none => true)
      && wellFormedKeys m ks
termination_by ks => (sizeOf m, ks.length)
decreasing_by
  · have := lookup_sizeOf h
    apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    simp

end

/-- Pointwise reading of `wellFormedKeys`. -/
theorem wfKeys_iff {m : List (FieldKey × CompactTy)} {ks : List FieldKey} :
    wellFormedKeys m ks = true ↔ ∀ k ∈ ks, ∀ v, m.lookup k = some v → wellFormed v = true := by
  induction ks with
  | nil => simp [wellFormedKeys]
  | cons k ks ih =>
    rw [wellFormedKeys, Bool.and_eq_true, ih]
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

theorem merge_idem (pol : Bool) : (a : CompactTy) → wellFormed a = true → equiv (merge pol a a) a =
    true
  | .mk a1 r1 v1 f1 c1 => by
    intro hwf
    rw [wellFormed.eq_def] at hwf
    simp only [Bool.and_eq_true] at hwf
    obtain ⟨⟨⟨hwr, hwv⟩, hwfn⟩, _hwc⟩ := hwf
    -- Both keyed self-merges are pointwise `merge pol v v`, closed by the
    -- recursive call on the (wellFormed) payload.
    have hmap : ∀ (p : Bool) (m : List (FieldKey × CompactTy)),
        (∀ x k, m.lookup k = some x → equiv (merge p x x) x = true) →
        ∀ (mm : List (FieldKey × CompactTy)),
          (∀ k, mm.lookup k =
            match m.lookup k, m.lookup k with
            | some v, some w => some (merge p v w)
            | some v, none => some v
            | none, some _ => none
            | none, none => none) →
        (subtypeKeys mm m (mm.map Prod.fst) && subtypeKeys m mm (m.map Prod.fst)) = true := by
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
          exact equiv_symm _ _ (hidem _ k h1)
    rw [merge.eq_def, equiv.eq_def]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp only [List.all_eq_true, List.contains_iff_mem, List.mem_append]
      exact fun x hx => hx.elim id id
    · simp only [List.all_eq_true, List.contains_iff_mem, List.mem_append]
      exact fun x hx => Or.inl hx
    · rcases r1 with _ | m
      · rfl
      · have hpay : ∀ x k, m.lookup k = some x → equiv (merge pol x x) x = true := by
          intro x k hx
          have hszx := lookup_sizeOf hx
          have hwx : wellFormed x = true :=
            (wfKeys_iff.mp (by simp only [Bool.and_eq_true] at hwr; simpa using hwr.1)) k
            (mem_keys_of_lookup hx) x hx
          exact merge_idem pol x hwx
        cases pol
        · simpa [unionMap] using hmap false m hpay (unionMap false m m)
            (fun k => by
              rw [unionMap_lookup]
              rcases m.lookup k with _ | v <;> rfl)
        · simpa using hmap true m hpay (intersectMap true m m)
            (fun k => by
              rw [intersectMap_lookup]
              rcases m.lookup k with _ | v <;> rfl)
    · rcases v1 with _ | m
      · rfl
      · have hpay : ∀ x k, m.lookup k = some x → equiv (merge pol x x) x = true := by
          intro x k hx
          have hszx := lookup_sizeOf hx
          have hwx : wellFormed x = true :=
            (wfKeys_iff.mp (by simp only [Bool.and_eq_true] at hwv; simpa using hwv.1)) k
            (mem_keys_of_lookup hx) x hx
          exact merge_idem pol x hwx
        cases pol
        · simpa using hmap false m hpay (intersectMap false m m)
            (fun k => by
              rw [intersectMap_lookup]
              rcases m.lookup k with _ | v <;> rfl)
        · simpa [unionMap] using hmap true m hpay (unionMap true m m)
            (fun k => by
              rw [unionMap_lookup]
              rcases m.lookup k with _ | v <;> rfl)
    · rcases f1 with _ | ⟨k1, d1, cod1⟩
      · rfl
      · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hwfn
        obtain ⟨⟨_, hwd⟩, hwcod⟩ := hwfn
        have hszd : sizeOf d1 < sizeOf (CompactTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1) := by
          simp
          omega
        have hszc : sizeOf cod1 <
            sizeOf (CompactTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1) := by
          simp
          omega
        have hd : equiv (merge (!pol) d1 d1) d1 = true := merge_idem (!pol) d1 hwd
        have hcod : equiv (merge pol cod1 cod1) cod1 = true := merge_idem pol cod1 hwcod
        dsimp only
        rw [mergeFun]
        simpa [joinKind_idem] using funClause_of_funEquiv
          (s1 := (k1, merge (!pol) d1 d1, merge pol cod1 cod1))
          (s2 := (k1, d1, cod1)) ⟨rfl, hd, hcod⟩
    · exact mergeRefinements_idem pol c1
termination_by a => sizeOf a
decreasing_by all_goals (simp; omega)

/-! ## Congruence: `merge` respects `equiv`

The one gate inside `merge` — the positive `data ⊔ data` domain dedup — is `equiv` itself, so it
cannot distinguish `equiv`-equal inputs (`equiv_congr_bool`). That is the whole reason congruence
holds; a gate keyed on anything finer
(e.g. structural equality, with `equiv` coarser than it) would break it. -/

/-- Replacing one side of the gate by an `equiv`-equal value leaves the gate's
verdict unchanged. -/
theorem equiv_congr_bool {x x' : CompactTy} (h : equiv x x' = true) (y : CompactTy) :
    equiv x y = equiv x' y := by
  rcases hg : equiv x' y with _ | _
  · rcases hg' : equiv x y with _ | _
    · rfl
    · rw [equiv_trans x' x y (equiv_symm x x' h) hg'] at hg
      exact hg
  · exact equiv_trans x x' y h hg

/-- `FunEquiv` is reflexive. -/
theorem funEquiv_refl (s : KindMerge × CompactTy × CompactTy) : FunEquiv s s := by
  obtain ⟨k, d, c⟩ := s
  exact ⟨rfl, equiv_refl d, equiv_refl c⟩

mutual

theorem merge_congr_left (pol : Bool) :
    (a a' b : CompactTy) → equiv a a' = true → equiv (merge pol a b) (merge pol a' b) = true
  | .mk a1 r1 v1 f1 c1, .mk a1' r1' v1' f1' c1', .mk b1 rb vb fb cb => by
    intro h
    rw [equiv.eq_def] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, hr⟩, hv⟩, hf⟩, hcl⟩ := h
    -- Pointwise congruence for the two keyed merges.
    have hinterC : ∀ (p : Bool) (m1 m1' m2 : List (FieldKey × CompactTy)),
        (subtypeKeys m1 m1' (m1.map Prod.fst) && subtypeKeys m1' m1 (m1'.map Prod.fst)) = true →
        (∀ x x' y k, m1.lookup k = some x → m1'.lookup k = some x' → m2.lookup k = some y →
          equiv (merge p x y) (merge p x' y) = true) →
        (subtypeKeys (intersectMap p m1 m2) (intersectMap p m1' m2)
            ((intersectMap p m1 m2).map Prod.fst) &&
          subtypeKeys (intersectMap p m1' m2) (intersectMap p m1 m2)
            ((intersectMap p m1' m2).map Prod.fst)) = true := by
      intro p m1 m1' m2 hcl hcong
      rw [mapClause_iff] at hcl ⊢
      obtain ⟨hdom, hfwd, hbwd⟩ := hcl
      refine ⟨fun k => ?_, fun k x y hx hy => ?_, fun k x y hx hy => ?_⟩
      · rw [intersectMap_lookup, intersectMap_lookup]
        rcases hl1 : m1.lookup k with _ | v <;> rcases hl2 : m2.lookup k with _ | w <;>
          rcases hl1' : m1'.lookup k with _ | v' <;>
          first
          | (simp; done)
          | (have hcontra := hdom k; simp [hl1, hl1'] at hcontra)
      · rw [intersectMap_lookup] at hx hy
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
      · rw [intersectMap_lookup] at hx hy
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
            exact equiv_symm _ _ (hcong _ _ _ k hv hl1' hl2)
    have hunionC : ∀ (p : Bool) (m1 m1' m2 : List (FieldKey × CompactTy)),
        (subtypeKeys m1 m1' (m1.map Prod.fst) && subtypeKeys m1' m1 (m1'.map Prod.fst)) = true →
        (∀ x x' y k, m1.lookup k = some x → m1'.lookup k = some x' → m2.lookup k = some y →
          equiv (merge p x y) (merge p x' y) = true) →
        (subtypeKeys (unionMap p m1 m2) (unionMap p m1' m2)
            ((unionMap p m1 m2).map Prod.fst) &&
          subtypeKeys (unionMap p m1' m2) (unionMap p m1 m2)
            ((unionMap p m1' m2).map Prod.fst)) = true := by
      intro p m1 m1' m2 hcl hcong
      have hpay : ∀ x x' k, m1.lookup k = some x → m1'.lookup k = some x' →
          equiv x x' = true := (mapClause_iff.mp hcl).2.1 |> fun hh => fun x x' k hx hx' =>
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
            exact equiv_refl _
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
            exact equiv_refl _
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
            exact equiv_symm _ _ (hpay _ _ k hv hl1')
          | some w =>
            rw [hl2] at hx hy
            dsimp only at hx hy
            cases hx
            cases hy
            exact equiv_symm _ _ (hcong _ _ _ k hv hl1' hl2)
    rw [merge.eq_def, merge.eq_def, equiv.eq_def]
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
        · simp [subtypeKeys_self]
      · rcases rb with _ | mb
        · simpa using hr
        · have hcong : ∀ x x' y k, m1.lookup k = some x → m1'.lookup k = some x' →
              mb.lookup k = some y → equiv (merge pol x y) (merge pol x' y) = true := by
            intro x x' y k hx hx' hy
            have hszx := lookup_sizeOf hx
            have hszx' := lookup_sizeOf hx'
            have hszy := lookup_sizeOf hy
            have hxx' : equiv x x' = true :=
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
        · simp [subtypeKeys_self]
      · rcases vb with _ | mb
        · simpa using hv
        · have hcong : ∀ x x' y k, m1.lookup k = some x → m1'.lookup k = some x' →
              mb.lookup k = some y → equiv (merge pol x y) (merge pol x' y) = true := by
            intro x x' y k hx hx' hy
            have hszx := lookup_sizeOf hx
            have hszx' := lookup_sizeOf hx'
            have hszy := lookup_sizeOf hy
            have hxx' : equiv x x' = true :=
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
        · simpa using funClause_of_funEquiv (funEquiv_refl sb)
      · rcases fb with _ | sb
        · simpa using hf
        · obtain ⟨k1, d1, cod1⟩ := s1
          obtain ⟨k1', d1', cod1'⟩ := s1'
          simp only [Bool.and_eq_true] at hf
          obtain ⟨⟨hk, hd⟩, hcod⟩ := hf
          have hk' : k1 = k1' := by simpa using hk
          have hsz : sizeOf (k1, d1, cod1) + sizeOf (k1', d1', cod1') + sizeOf sb <
              sizeOf (CompactTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1) +
                sizeOf (CompactTy.mk a1' r1' v1' (some (k1', d1', cod1')) c1') +
                sizeOf (CompactTy.mk b1 rb vb (some sb) cb) := by
            simp
            omega
          have hde : FunEquiv (k1, d1, cod1) (k1', d1', cod1') := ⟨hk', hd, hcod⟩
          simpa using funClause_of_funEquiv
            (mergeFun_congr_left pol (k1, d1, cod1) (k1', d1', cod1') sb hde)
    · exact mergeRefinements_congr_left pol cb hcl
termination_by a a' b => (sizeOf a + sizeOf a' + sizeOf b, 1)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; omega)
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

theorem mergeFun_congr_left (pol : Bool) :
    (s1 s1' sb : KindMerge × CompactTy × CompactTy) → FunEquiv s1 s1' →
      FunEquiv (mergeFun pol s1 sb) (mergeFun pol s1' sb)
  | (k1, d1, c1), (k1', d1', c1'), (kb, db, cb) => by
    intro ⟨hk, hd, hc⟩
    subst hk
    have hszd : sizeOf d1 + sizeOf d1' + sizeOf db <
        sizeOf (k1, d1, c1) + sizeOf (k1, d1', c1') + sizeOf (kb, db, cb) := by
      simp
      omega
    have hszc : sizeOf c1 + sizeOf c1' + sizeOf cb <
        sizeOf (k1, d1, c1) + sizeOf (k1, d1', c1') + sizeOf (kb, db, cb) := by
      simp
      omega
    rw [mergeFun, mergeFun]
    exact ⟨rfl, merge_congr_left (!pol) d1 d1' db hd, merge_congr_left pol c1 c1' cb hc⟩
termination_by s1 s1' sb => (sizeOf s1 + sizeOf s1' + sizeOf sb, 0)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; assumption)
  | (apply Prod.Lex.left; omega)
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

end

/-- Congruence in the right argument (via commutativity). -/
theorem merge_congr_right (pol : Bool) (a b b' : CompactTy) (h : equiv b b' = true) :
    equiv (merge pol a b) (merge pol a b') = true :=
  equiv_trans _ _ _ (merge_comm pol a b)
    (equiv_trans _ _ _ (merge_congr_left pol b b' a h) (merge_comm pol b' a))

/-- Full congruence. -/
theorem merge_congr (pol : Bool) {a a' b b' : CompactTy}
    (ha : equiv a a' = true) (hb : equiv b b' = true) :
    equiv (merge pol a b) (merge pol a' b') = true :=
  equiv_trans _ _ _ (merge_congr_left pol a a' b ha) (merge_congr_right pol a' b b' hb)

/-! ## Associativity

The kinds join in a semilattice and the domains are combined by polarity alone ([`mergeFun`]), so no
step of the fold reads a value that a later step can change, and the merge is associative with no
side condition. That is what makes the fold below a function of the bound *set*.

An earlier rule selected the domain combination from the slot's kind, and that was **not**
associative: three bounds at one position — a `data` function over one domain and two whose kind
variable nothing had pinned, over two others — merged to a conflict in one association and to an
accepted `data` function in another, whose domain was the meet of two of the three. `compact.rs` now
defers that choice to `coalesce_compact_go`, where the kind is resolved
(`undetermined_kinds_join_without_deciding_the_domain_rule` pins the exhibit). -/

/-- A merged slot's kind is the kinds' join. Nothing else can force a conflict: the domain
merges like any other position, so it has no verdict of its own to contribute. -/
theorem mergeFun_kind (pol : Bool) (s1 s2 : KindMerge × CompactTy × CompactTy) :
    (mergeFun pol s1 s2).1 = joinKind s1.1 s2.1 := by
  obtain ⟨k1, d1, c1⟩ := s1
  obtain ⟨k2, d2, c2⟩ := s2
  rw [mergeFun]

/-- `joinKind` is absorbed by a conflict on either side. -/
theorem joinKind_conflict_left (k : KindMerge) : joinKind .conflict k = .conflict := by
  cases k <;> rfl

theorem joinKind_conflict_right (k : KindMerge) : joinKind k .conflict = .conflict := by
  cases k <;> rfl

mutual

theorem merge_assoc (pol : Bool) :
    (a b c : CompactTy) →
      equiv (merge pol (merge pol a b) c) (merge pol a (merge pol b c)) = true
  | .mk a1 r1 v1 f1 c1, .mk a2 r2 v2 f2 c2, .mk a3 r3 v3 f3 c3 => by
    -- Pointwise associativity for the two keyed merges.
    have hinterA : ∀ (p : Bool) (m1 m2 m3 : List (FieldKey × CompactTy)),
        (∀ x y z k, m1.lookup k = some x → m2.lookup k = some y → m3.lookup k = some z →
          equiv (merge p (merge p x y) z) (merge p x (merge p y z)) = true) →
        (subtypeKeys (intersectMap p (intersectMap p m1 m2) m3) (intersectMap p m1 (intersectMap p m2 m3))
            ((intersectMap p (intersectMap p m1 m2) m3).map Prod.fst) &&
          subtypeKeys (intersectMap p m1 (intersectMap p m2 m3))
            (intersectMap p (intersectMap p m1 m2) m3)
            ((intersectMap p m1 (intersectMap p m2 m3)).map Prod.fst)) = true := by
      intro p m1 m2 m3 hassoc
      rw [mapClause_iff]
      refine ⟨fun k => ?_, fun k x y hx hy => ?_, fun k x y hx hy => ?_⟩
      · rw [intersectMap_lookup, intersectMap_lookup, intersectMap_lookup, intersectMap_lookup]
        rcases m1.lookup k with _ | v <;> rcases m2.lookup k with _ | w <;>
          rcases m3.lookup k with _ | u <;> simp
      · rw [intersectMap_lookup, intersectMap_lookup] at hx
        rw [intersectMap_lookup, intersectMap_lookup] at hy
        rcases h1 : m1.lookup k with _ | v <;> rw [h1] at hx hy <;>
          rcases h2 : m2.lookup k with _ | w <;> rw [h2] at hx hy <;>
          rcases h3 : m3.lookup k with _ | u <;> rw [h3] at hx hy <;>
          dsimp only at hx hy <;>
          first
          | (simp only [reduceCtorEq] at hx)
          | (cases hx; cases hy; exact hassoc _ _ _ k h1 h2 h3)
      · rw [intersectMap_lookup, intersectMap_lookup] at hx
        rw [intersectMap_lookup, intersectMap_lookup] at hy
        rcases h1 : m1.lookup k with _ | v <;> rw [h1] at hx hy <;>
          rcases h2 : m2.lookup k with _ | w <;> rw [h2] at hx hy <;>
          rcases h3 : m3.lookup k with _ | u <;> rw [h3] at hx hy <;>
          dsimp only at hx hy <;>
          first
          | (simp only [reduceCtorEq] at hx)
          | (cases hx; cases hy; exact equiv_symm _ _ (hassoc _ _ _ k h1 h2 h3))
    have hunionA : ∀ (p : Bool) (m1 m2 m3 : List (FieldKey × CompactTy)),
        (∀ x y z k, m1.lookup k = some x → m2.lookup k = some y → m3.lookup k = some z →
          equiv (merge p (merge p x y) z) (merge p x (merge p y z)) = true) →
        (subtypeKeys (unionMap p (unionMap p m1 m2) m3) (unionMap p m1 (unionMap p m2 m3))
            ((unionMap p (unionMap p m1 m2) m3).map Prod.fst) &&
          subtypeKeys (unionMap p m1 (unionMap p m2 m3)) (unionMap p (unionMap p m1 m2) m3)
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
             | exact equiv_refl _
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
             | exact equiv_refl _
             | exact equiv_symm _ _ (hassoc _ _ _ k h1 h2 h3))
    rw [merge.eq_def, merge.eq_def, merge.eq_def, merge.eq_def, equiv.eq_def]
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
        | (simp [subtypeKeys_self]; done)
        | skip
      have hassoc : ∀ x y z k, m1.lookup k = some x → m2.lookup k = some y →
          m3.lookup k = some z →
          equiv (merge pol (merge pol x y) z) (merge pol x (merge pol y z)) = true := by
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
        | (simp [subtypeKeys_self]; done)
        | skip
      have hassoc : ∀ x y z k, m1.lookup k = some x → m2.lookup k = some y →
          m3.lookup k = some z →
          equiv (merge pol (merge pol x y) z) (merge pol x (merge pol y z)) = true := by
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
        | (simpa using funClause_of_funEquiv (funEquiv_refl _))
        | skip
      obtain ⟨k1, d1, cod1⟩ := s1
      obtain ⟨k2, d2, cod2⟩ := s2
      obtain ⟨k3, d3, cod3⟩ := s3
      have hsz : sizeOf (k1, d1, cod1) + sizeOf (k2, d2, cod2) + sizeOf (k3, d3, cod3) <
          sizeOf (CompactTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1) +
            sizeOf (CompactTy.mk a2 r2 v2 (some (k2, d2, cod2)) c2) +
            sizeOf (CompactTy.mk a3 r3 v3 (some (k3, d3, cod3)) c3) := by
        simp
        omega
      simpa using funClause_of_funEquiv
        (mergeFun_assoc pol (k1, d1, cod1) (k2, d2, cod2) (k3, d3, cod3))
    · exact mergeRefinements_assoc pol c1 c2 c3
termination_by a b c => (sizeOf a + sizeOf b + sizeOf c, 1)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; omega)
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

theorem mergeFun_assoc (pol : Bool) :
    (s1 s2 s3 : KindMerge × CompactTy × CompactTy) →
      FunEquiv (mergeFun pol (mergeFun pol s1 s2) s3) (mergeFun pol s1 (mergeFun pol s2 s3))
  | (k1, d1, c1), (k2, d2, c2), (k3, d3, c3) => by
    have hszd : sizeOf d1 + sizeOf d2 + sizeOf d3 <
        sizeOf (k1, d1, c1) + sizeOf (k2, d2, c2) + sizeOf (k3, d3, c3) := by
      simp
      omega
    have hszc : sizeOf c1 + sizeOf c2 + sizeOf c3 <
        sizeOf (k1, d1, c1) + sizeOf (k2, d2, c2) + sizeOf (k3, d3, c3) := by
      simp
      omega
    rw [mergeFun, mergeFun, mergeFun, mergeFun]
    exact ⟨joinKind_assoc k1 k2 k3, merge_assoc (!pol) d1 d2 d3, merge_assoc pol c1 c2 c3⟩
termination_by s1 s2 s3 => (sizeOf s1 + sizeOf s2 + sizeOf s3, 0)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; omega)
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

end

/-! ## The fold: coalescing a bound list is order- and duplicate-invariant

`compact_go` folds a variable's bounds through `merge` from the first bound (no identity element
exists — see the module docs). The outcome is a function of the bound *set*: permutations
(`foldMerge_perm`) cannot change it, and neither can duplicates (`foldMerge_dup`, which needs
`wellFormed` on the repeated bound because idempotence does). This is the algebraic statement behind
the type-merge fuzz's
\"outcomes agree under permuted constraint orders\". -/

/-- The fold `compact_go` performs over a variable's bound list, seeded at the
first bound. -/
def foldMerge (pol : Bool) (t : CompactTy) (ts : List CompactTy) : CompactTy :=
  ts.foldl (merge pol) t

/-- The fold respects `equiv` in its seed (any polarity). -/
theorem foldMerge_congr (pol : Bool) {t t' : CompactTy} (ts : List CompactTy)
    (h : equiv t t' = true) :
    equiv (foldMerge pol t ts) (foldMerge pol t' ts) = true := by
  induction ts generalizing t t' with
  | nil => exact h
  | cons x ts ih => exact ih (merge_congr_left pol t t' x h)

/-- **Order-invariance**: permuting the bound list cannot change the coalesced
outcome (up to `equiv`), at either polarity and with no side condition. -/
theorem foldMerge_perm (pol : Bool) {l1 l2 : List CompactTy} (h : l1.Perm l2) :
    ∀ (t : CompactTy), equiv (foldMerge pol t l1) (foldMerge pol t l2) = true := by
  induction h with
  | nil => exact fun t => equiv_refl _
  | @cons x l1 l2 hp ih => exact fun t => ih (merge pol t x)
  | @swap x y l =>
    intro t
    -- merge (merge t y) x ~ merge t (merge y x) ~ merge t (merge x y)
    --   ~ merge (merge t x) y
    have hseed : equiv (merge pol (merge pol t y) x) (merge pol (merge pol t x) y) = true :=
      equiv_trans _ _ _ (merge_assoc pol t y x)
        (equiv_trans _ _ _ (merge_congr_right pol t _ _ (merge_comm pol y x))
          (equiv_symm _ _ (merge_assoc pol t x y)))
    simpa [foldMerge, List.foldl_cons] using foldMerge_congr pol l hseed
  | @trans l1 l2 l3 h12 h23 ih1 ih2 => exact fun t => equiv_trans _ _ _ (ih1 t) (ih2 t)

/-- **Duplicate-invariance**: a bound occurring twice contributes once — the
other half of \"the outcome is a function of the bound set\". Needs `wellFormed` for
the duplicated bound (idempotence does). -/
theorem foldMerge_dup (pol : Bool) {t x : CompactTy} (l : List CompactTy)
    (hwx : wellFormed x = true) :
    equiv (foldMerge pol t (x :: x :: l)) (foldMerge pol t (x :: l)) = true := by
  -- merge (merge t x) x ~ merge t (merge x x) ~ merge t x
  have hseed : equiv (merge pol (merge pol t x) x) (merge pol t x) = true :=
    equiv_trans _ _ _ (merge_assoc pol t x x)
      (merge_congr_right pol t _ _ (merge_idem pol x hwx))
  simpa [foldMerge, List.foldl_cons] using foldMerge_congr pol l hseed

/-! ## The order the merge induces, and uniqueness

`merge pol` is commutative, associative and idempotent, so it comes with an order: `absorbedBy pol a
b` reads "merging `a` into `b` adds nothing". `merge pol` is that order's least upper bound, and any
least upper bound is `equiv`-equal to it (`least_absorber_unique`).

The scope is narrow and worth stating. These proofs use only commutativity, associativity,
idempotence and congruence, so they are the semilattice-to-poset correspondence and carry exactly
that content — `merge` is a join *of the order it defines*. That it is the join with respect to
**subtyping** is a different statement, needing a denotation into a lattice of types, and it is not
made here (`formal/design.md`, "The lattice is a semantic statement").

Absorption and distributivity hold of the types and are not stated here, because `CompactTy` is the
wrong carrier for them. There is one type lattice, and `merge true` computes its join while `merge
false` computes its meet; what is polarity-indexed is the *denotation*. One `CompactTy` denotes two
types — a contribution set is the union of its contributions read positively and their intersection
read negatively — so `CompactTy` is one syntax carrying two representations rather than a lattice
carrier.

Writing `a ⊓ (a ⊔ b) = a` over `CompactTy` needs one syntactic `a` in both a join argument (read
positively) and a meet argument (read negatively), which needs `⟦a⟧⁺ = ⟦a⟧⁻`. That holds for a
single contribution (`{Int}` is `Int` either way) and fails once a set holds two, which is the case
the law is about. So the laws proved here are the ones a single polarity's operation has, and the
cross-polarity laws wait on a carrier where both operations act on the same object
(`formal/design.md`, "The lattice is a semantic statement").

Reflexivity needs `wellFormed` because idempotence does; nothing else here has a side
condition. -/

/-- The empty position: no contribution at any slot, which is what a `Hole`
compacts to (`CompactType::empty`). -/
def emptyPosition : CompactTy := .mk [] none none none none

/-- The empty position is the merge identity, at either polarity. Every slot's
`none` is its own identity, the atom list unions, and the refinement slot's sentinel supplies the
one the refinement *set* cannot (an empty set is absorbing under the positive intersect, not
neutral) — so the merged position is the other side itself, not merely `equiv` to it. `compact_go`
still folds from the first bound,
but nothing in the algebra requires that any more. -/
theorem merge_cempty_left (pol : Bool) (a : CompactTy) : merge pol emptyPosition a = a := by
  rcases a with ⟨a1, r1, v1, f1, c1⟩
  rw [merge.eq_def]
  rfl

theorem merge_cempty_right (pol : Bool) (a : CompactTy) : equiv (merge pol a emptyPosition) a = true
    := by
  exact equiv_trans _ _ _ (merge_comm pol a emptyPosition)
    (by rw [merge_cempty_left]; exact equiv_refl a)

/-- `b` absorbs `a` at this polarity: merging `a` into `b` adds nothing.

This is the order `merge pol` induces on *representations*, and it is **not** subtyping. It is
strictly finer: a positive merge accumulates a function slot's domain alternatives rather than
deciding between them, so `(Int ⇒ Int)` and `({Int | __elem} ⇒ Int)` merge to a slot carrying both —
a different `CompactTy` from either, though `coalesce` materializes it to the second, which is their
subtyping join. Two positions can therefore materialize to the same type and absorb neither the
other. `Subtyping` is the subtyping relation; nothing here is stated over it except
by way of `coalesce` (`coalesce_monotone`). -/
def absorbedBy (pol : Bool) (a b : CompactTy) : Prop := equiv (merge pol a b) b = true

theorem absorbedBy_refl (pol : Bool) {a : CompactTy} (h : wellFormed a = true) : absorbedBy pol a a
    :=
  merge_idem pol a h

theorem absorbedBy_trans (pol : Bool) {a b c : CompactTy} (hab : absorbedBy pol a b)
    (hbc : absorbedBy pol b c) :
    absorbedBy pol a c := by
  -- a ⊔ c ~ a ⊔ (b ⊔ c) ~ (a ⊔ b) ⊔ c ~ b ⊔ c ~ c
  have h1 : equiv (merge pol a c) (merge pol a (merge pol b c)) = true :=
    merge_congr_right pol a c (merge pol b c) (equiv_symm _ _ hbc)
  have h2 : equiv (merge pol a (merge pol b c)) (merge pol (merge pol a b) c) = true :=
    equiv_symm _ _ (merge_assoc pol a b c)
  have h3 : equiv (merge pol (merge pol a b) c) c = true :=
    equiv_trans _ _ _ (merge_congr_left pol (merge pol a b) b c hab) hbc
  exact equiv_trans _ _ _ h1 (equiv_trans _ _ _ h2 h3)

/-- Antisymmetry up to `equiv`: the order is a partial order on the quotient. -/
theorem absorbedBy_antisymm (pol : Bool) {a b : CompactTy} (hab : absorbedBy pol a b)
    (hba : absorbedBy pol b a) :
    equiv a b = true :=
  equiv_trans _ _ _ (equiv_symm _ _ hba) (equiv_trans _ _ _ (merge_comm pol b a) hab)

/-- `merge pol a b` is an upper bound of `a`. -/
theorem absorbedBy_merge_left (pol : Bool) (a b : CompactTy) (ha : wellFormed a = true) :
    absorbedBy pol a (merge pol a b) := by
  -- a ⊔ (a ⊔ b) ~ (a ⊔ a) ⊔ b ~ a ⊔ b
  exact equiv_trans _ _ _ (equiv_symm _ _ (merge_assoc pol a a b))
    (merge_congr_left pol (merge pol a a) a b (merge_idem pol a ha))

/-- …and of `b`. -/
theorem absorbedBy_merge_right (pol : Bool) (a b : CompactTy) (hb : wellFormed b = true) :
    absorbedBy pol b (merge pol a b) :=
  equiv_trans _ _ _ (merge_congr_right pol b (merge pol a b) (merge pol b a)
      (merge_comm pol a b))
    (equiv_trans _ _ _ (absorbedBy_merge_left pol b a hb) (merge_comm pol b a))

/-- …and it is the *least* one: anything above both is above it. No side
condition — this is associativity and congruence alone. -/
theorem merge_absorbedBy (pol : Bool) {a b c : CompactTy} (ha : absorbedBy pol a c)
    (hb : absorbedBy pol b c) :
    absorbedBy pol (merge pol a b) c :=
  equiv_trans _ _ _ (merge_assoc pol a b c)
    (equiv_trans _ _ _ (merge_congr_right pol a (merge pol b c) c hb) ha)

/-- Least upper bound **of the absorption order**, spelled out: `m` absorbs both
and is absorbed by anything that absorbs both. Not a statement about subtyping —
see [`absorbedBy`]. -/
def IsLeastAbsorber (pol : Bool) (a b m : CompactTy) : Prop :=
  absorbedBy pol a m ∧ absorbedBy pol b m ∧
    ∀ u : CompactTy, absorbedBy pol a u → absorbedBy pol b u → absorbedBy pol m u

/-- `emptyPosition` is the order's least element: it is below everything, with no side
condition (`absorbedBy_refl` needs `wellFormed`; this does not). -/
theorem absorbedBy_cempty (pol : Bool) (a : CompactTy) : absorbedBy pol emptyPosition a := by
  rw [absorbedBy, merge_cempty_left]
  exact equiv_refl a

theorem merge_is_least_absorber (pol : Bool) (a b : CompactTy) (ha : wellFormed a = true)
    (hb : wellFormed b = true) :
    IsLeastAbsorber pol a b (merge pol a b) :=
  ⟨absorbedBy_merge_left pol a b ha, absorbedBy_merge_right pol a b hb, fun _ hau hbu =>
    merge_absorbedBy pol hau hbu⟩

/-- **Uniqueness**: a least upper bound of two positions is the merge, up to
`equiv`. The merge is not *a* way to combine two bounds; it is the only one the
order admits. -/
theorem least_absorber_unique (pol : Bool) {a b m : CompactTy} (ha : wellFormed a = true)
    (hb : wellFormed b = true)
    (h : IsLeastAbsorber pol a b m) : equiv m (merge pol a b) = true :=
  absorbedBy_antisymm pol
    (h.2.2 (merge pol a b) (absorbedBy_merge_left pol a b ha) (absorbedBy_merge_right pol a b hb))
    (merge_absorbedBy pol h.1 h.2.1)

end CompactTy

end CclFormal
