import CclFormal.Ty

/-!
# The solver's polar merge and its algebra

The Lean mirror of `src/ccl/infer/solver/compact.rs`'s bound-merging — the
operation `coalesce` folds over a variable's bounds (`CompactType::merge`,
`CompactFun::merge`, `merge_refinements`, `merge_records`, `merge_variants`) —
and the theorems that make the solver's order-independence claim a proof
obligation instead of a fuzz observation:

- `eqv` is an equivalence relation (`eqv_refl`, `eqv_symm`, `eqv_trans`);
- `merge` is commutative (`merge_comm`), idempotent (`merge_idem`), and a
  congruence for `eqv` (`merge_congr_left`/`_right`);
- `merge` is associative on the kind-uniform fragments
  (`merge_assoc_of_computeFree`) — and **not in general**: mixing `data` and
  `compute` function bounds over distinct domains makes the outcome depend on
  association (`merge_not_assoc`), which means arrival order can decide
  accept-vs-reject. See `formal/design.md`, "M4b — the merge algebra".
- The fold `coalesce` performs is invariant under permutation and duplication
  of the bound list on the associative fragment (`fold_perm`, `fold_dup`).

## What the model is a mirror of, and what it drops

`CTy` is the ground fragment of `CompactType`: atoms, the optional
record/variant maps, the optional function slot, the refinement claim set,
and an error flag. Deliberately dropped, with the reasoning:

- **Inference variables** (`vars`) — the ground algebra doesn't read them;
  they union like atoms and would only pad every proof.
- **History slots** — transients erased before the strict wall, exactly as
  `Ty` excludes `History` (same-polarity componentwise merge; nothing new).
- **The Pi binder** (`CompactFun::name`, merged `a.name.or(b.name)`) —
  first-wins is order-dependent as written, but `Subst::canonical_pi_binder`
  renames both sides to the same depth-indexed `__pi{n}` during compaction,
  so by merge time the slots agree; the asymmetry is unobservable.
- **`reduce_error`'s payload** (`lhs.or(rhs)`, first-wins) — *which* error is
  diagnostic; the flag (`err`) is what the algebra observes.
- **Domain-alternative payloads beyond one** — `union_domains` keeps a `Vec`
  in arrival order, but every path that could read a second alternative ends
  in a coalesce error (`DomainJoinConflict`; a `Data` function materializes
  only when exactly one domain survives), so the tail of the list is
  diagnostic. `fn`'s domain slot is therefore `Option CTy`: `some d` for a
  single domain, `none` for "two or more distinct alternatives" (and for a
  conflicted slot's payload). If the Σ collections work ever materializes a
  multi-domain join, the alternatives become semantic and this adjudication
  must be revisited.

## The equivalence is the code's own equality

`eqv` mirrors `CompactType`'s `PartialEq`: set-semantic on atoms and claims
(mirroring `BTreeSet` and `RefinementSet`), key-set + payload on the maps
(mirroring `BTreeMap`), componentwise on the function slot. The merge's one
internal comparison — `union_domains` deduplicating two `Data` domains — uses
that same equality, which is what makes every theorem quotient-compatible:
the gate cannot distinguish two `eqv`-equal inputs.

There is **no identity element**, by design: `compact_go` folds a variable's
bounds from the *first bound*, never from `CompactType::default()`, because
an empty claim set is absorbing (not neutral) under the positive intersect —
the fold theorems are stated over nonempty lists accordingly.
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

/-- Mirror of `compact.rs :: KindMerge`: the two ground kinds plus the
`conflict` absorbing state a bad kind meeting leaves behind (coalesce turns it
into an error; it never materializes). -/
inductive KindM where
  | data | compute | conflict
deriving Repr, DecidableEq

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
       (fn : Option (KindM × Option CTy × CTy))
       (claims : List Pred)
       (err : Bool)
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
  | .mk a1 r1 v1 f1 c1 e1, .mk a2 r2 v2 f2 c2 e2 =>
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
              && (match d1, d2 with
                  | none, none => true
                  | some x, some y => eqv x y
                  | _, _ => false)
              && eqv c1 c2
          | _, _ => false)
      && c1.all (c2.contains ·) && c2.all (c1.contains ·)
      && e1 == e2
termination_by a b => (sizeOf a + sizeOf b, 0)

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

/-! ## The merge -/

mutual

/-- Mirror of `CompactType::merge` (ground fragment). `pol` is the polarity:
positive merges are joins (types union, claims/record-keys intersect, variant
tags union), negative merges are meets (the duals). -/
def merge (pol : Bool) : CTy → CTy → CTy
  | .mk a1 r1 v1 f1 c1 e1, .mk a2 r2 v2 f2 c2 e2 =>
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
        (if pol then c1.filter (c2.contains ·) else c1 ++ c2)
        (e1 || e2)
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

/-- Mirror of `CompactFun::merge` (see module docs for the `Option CTy`
domain encoding and the dropped binder/diagnostic payloads).

The domain-dedup gate in the positive `data ⊔ data` arm is `eqv` — the same
equality `union_domains`' `contains` uses — which is what keeps the whole
algebra quotient-compatible. -/
def mergeFun (pol : Bool) :
    KindM × Option CTy × CTy → KindM × Option CTy × CTy → KindM × Option CTy × CTy
  | (k1, d1, c1), (k2, d2, c2) =>
    let cod := merge pol c1 c2
    if k1 == .conflict || k2 == .conflict then
      (.conflict, none, cod)
    else if pol then
      match k1, k2, d1, d2 with
      -- Data ⊔ Data: the union of the alternatives. Two alternatives that
      -- compare equal are one domain; otherwise the join has no lossless
      -- single-domain answer and coalesce will error (`none` = "many").
      | .data, .data, some x, some y =>
        (.data, if eqv x y then some x else none, cod)
      | .data, .data, _, _ => (.data, none, cod)
      -- Compute ⊔ Compute: the contravariant domain meet.
      | .compute, .compute, some x, some y =>
        (.compute, some (merge (!pol) x y), cod)
      -- Data ⊔ Compute: an honest upcast to a callable iff the data side is a
      -- single domain; collapsing several alternatives to a meet would drop
      -- domains.
      | _, _, some x, some y => (.compute, some (merge (!pol) x y), cod)
      | _, _, _, _ => (.conflict, none, cod)
    else
      -- Negative (meet): the stronger contract wins (`data` if either is).
      let k := if k1 == .data || k2 == .data then KindM.data else KindM.compute
      match d1, d2 with
      | some x, some y => (k, some (merge (!pol) x y), cod)
      | _, _ => (.conflict, none, cod)
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
  | .mk a r v f c e => by
    have hmap : ∀ (m : List (FieldKey × CTy)), sizeOf m < sizeOf (CTy.mk a r v f c e) →
        subKeys m m (m.map Prod.fst) = true := by
      intro m hm
      rw [subKeys_iff]
      intro k hk
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (lookup_of_mem_keys hk)
      have hsz : sizeOf w < sizeOf (CTy.mk a r v f c e) :=
        Nat.lt_trans (lookup_sizeOf hw) hm
      exact ⟨w, w, hw, hw, eqv_refl w⟩
    rw [eqv.eq_def]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp [List.all_eq_true]
    · simp [List.all_eq_true]
    · rcases r with _ | m
      · rfl
      · have hm : sizeOf m < sizeOf (CTy.mk a (some m) v f c e) := by
          simp
          omega
        simp [hmap m hm]
    · rcases v with _ | m
      · rfl
      · have hm : sizeOf m < sizeOf (CTy.mk a r (some m) f c e) := by
          simp
          omega
        simp [hmap m hm]
    · rcases f with _ | ⟨k, d, cod⟩
      · rfl
      · have hszc : sizeOf cod < sizeOf (CTy.mk a r v (some (k, d, cod)) c e) := by
          simp
          omega
        rcases d with _ | d
        · simp [eqv_refl cod]
        · have hszd : sizeOf d < sizeOf (CTy.mk a r v (some (k, some d, cod)) c e) := by
            simp
            omega
          simp [eqv_refl d, eqv_refl cod]
    · simp [List.all_eq_true]
    · simp [List.all_eq_true]
    · simp
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
  | .mk a1 r1 v1 f1 c1 e1, .mk a2 r2 v2 f2 c2 e2 => by
    intro h
    rw [eqv.eq_def] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hr⟩, hv⟩, hf⟩, hc1⟩, hc2⟩, he⟩ := h
    rw [eqv.eq_def]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨h2, h1⟩, ?_⟩, ?_⟩, ?_⟩, hc2⟩, hc1⟩, ?_⟩
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
            sizeOf (CTy.mk a2 r2 v2 (some (k2, d2, cod2)) c2 e2) +
              sizeOf (CTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1 e1) := by
          simp
          omega
        refine ⟨⟨?_, ?_⟩, eqv_symm cod1 cod2 hcod⟩
        · simp at hk
          simp [hk]
        · rcases d1 with _ | x <;> rcases d2 with _ | y
          · rfl
          · simp at hd
          · simp at hd
          · have hszd : sizeOf y + sizeOf x <
                sizeOf (CTy.mk a2 r2 v2 (some (k2, some y, cod2)) c2 e2) +
                  sizeOf (CTy.mk a1 r1 v1 (some (k1, some x, cod1)) c1 e1) := by
              simp
              omega
            exact eqv_symm x y hd
    · simp at he
      simp [he]
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals omega

theorem eqv_trans : (a b c : CTy) → eqv a b = true → eqv b c = true → eqv a c = true
  | .mk a1 r1 v1 f1 c1 e1, .mk a2 r2 v2 f2 c2 e2, .mk a3 r3 v3 f3 c3 e3 => by
    intro hab hbc
    rw [eqv.eq_def] at hab hbc
    simp only [Bool.and_eq_true] at hab hbc
    obtain ⟨⟨⟨⟨⟨⟨⟨hab1, hab2⟩, habr⟩, habv⟩, habf⟩, habc1⟩, habc2⟩, habe⟩ := hab
    obtain ⟨⟨⟨⟨⟨⟨⟨hbc1, hbc2⟩, hbcr⟩, hbcv⟩, hbcf⟩, hbcc1⟩, hbcc2⟩, hbce⟩ := hbc
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
        sizeOf m1 < sizeOf (CTy.mk a1 r1 v1 f1 c1 e1) →
        sizeOf m3 < sizeOf (CTy.mk a3 r3 v3 f3 c3 e3) →
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
        have hszx : sizeOf x < sizeOf (CTy.mk a1 r1 v1 f1 c1 e1) :=
          Nat.lt_trans (lookup_sizeOf hx) hs1
        have hszz : sizeOf z < sizeOf (CTy.mk a3 r3 v3 f3 c3 e3) :=
          Nat.lt_trans (lookup_sizeOf hz) hs3
        exact eqv_trans x y z hxy hyz
      · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ((hdom12 k).mp (by simp [hx]))
        have hzy := hbwd23 k y z hy hz
        have hyx := hbwd12 k x y hx hy
        have hszx : sizeOf x < sizeOf (CTy.mk a1 r1 v1 f1 c1 e1) :=
          Nat.lt_trans (lookup_sizeOf hx) hs1
        have hszz : sizeOf z < sizeOf (CTy.mk a3 r3 v3 f3 c3 e3) :=
          Nat.lt_trans (lookup_sizeOf hz) hs3
        exact eqv_trans z y x hzy hyx
    refine ⟨⟨⟨⟨⟨⟨⟨hsub a1 a2 a3 hab1 hbc1, hsub a3 a2 a1 hbc2 hab2⟩, ?_⟩, ?_⟩, ?_⟩,
      hsub c1 c2 c3 habc1 hbcc1⟩, hsub c3 c2 c1 hbcc2 habc2⟩, ?_⟩
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
          sizeOf (CTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1 e1) +
            sizeOf (CTy.mk a3 r3 v3 (some (k3, d3, cod3)) c3 e3) := by
        simp
        omega
      refine ⟨⟨?_, ?_⟩, eqv_trans cod1 cod2 cod3 habcod hbccod⟩
      · simp at habk hbck
        simp [habk, hbck]
      · rcases d1 with _ | x <;> rcases d2 with _ | y <;> rcases d3 with _ | z <;>
          first
          | rfl
          | (simp at habd; done)
          | (simp at hbcd; done)
          | skip
        have hszd : sizeOf x + sizeOf z <
            sizeOf (CTy.mk a1 r1 v1 (some (k1, some x, cod1)) c1 e1) +
              sizeOf (CTy.mk a3 r3 v3 (some (k3, some z, cod3)) c3 e3) := by
          simp
          omega
        exact eqv_trans x y z habd hbcd
    · simp at habe hbce
      simp [habe, hbce]
termination_by a _ c => sizeOf a + sizeOf c
decreasing_by all_goals omega

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
def FunEqv : KindM × Option CTy × CTy → KindM × Option CTy × CTy → Prop
  | (k1, d1, c1), (k2, d2, c2) =>
    k1 = k2
      ∧ (match d1, d2 with
         | none, none => True
         | some x, some y => eqv x y = true
         | _, _ => False)
      ∧ eqv c1 c2 = true

/-- `FunEqv` is exactly `eqv`'s fn clause. -/
theorem funClause_of_funEqv {s1 s2 : KindM × Option CTy × CTy} (h : FunEqv s1 s2) :
    (s1.1 == s2.1
      && (match s1.2.1, s2.2.1 with
          | none, none => true
          | some x, some y => eqv x y
          | _, _ => false)
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
  | .mk a1 r1 v1 f1 c1 e1, .mk a2 r2 v2 f2 c2 e2 => by
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
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
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
      · simpa using funClause_of_funEqv (s1 := (k2, d2, cod2)) (s2 := (k2, d2, cod2))
          ⟨rfl, by rcases d2 with _ | x <;> simp [eqv_refl], eqv_refl cod2⟩
      · simpa using funClause_of_funEqv (s1 := (k1, d1, cod1)) (s2 := (k1, d1, cod1))
          ⟨rfl, by rcases d1 with _ | x <;> simp [eqv_refl], eqv_refl cod1⟩
      · have hsz : sizeOf (k1, d1, cod1) + sizeOf (k2, d2, cod2) <
            sizeOf (CTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1 e1) +
              sizeOf (CTy.mk a2 r2 v2 (some (k2, d2, cod2)) c2 e2) := by
          simp
          omega
        simpa using funClause_of_funEqv (mergeFun_comm pol (k1, d1, cod1) (k2, d2, cod2))
    · cases pol
      · simp only [Bool.false_eq_true, reduceIte, List.all_eq_true, List.contains_iff_mem,
          List.mem_append]
        exact fun x hx => hx.symm
      · simp only [reduceIte, List.all_eq_true, List.contains_iff_mem, List.mem_filter]
        exact fun x hx => ⟨hx.2, hx.1⟩
    · cases pol
      · simp only [Bool.false_eq_true, reduceIte, List.all_eq_true, List.contains_iff_mem,
          List.mem_append]
        exact fun x hx => hx.symm
      · simp only [reduceIte, List.all_eq_true, List.contains_iff_mem, List.mem_filter]
        exact fun x hx => ⟨hx.2, hx.1⟩
    · simp [Bool.or_comm]
termination_by a b => (sizeOf a + sizeOf b, 1)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

theorem mergeFun_comm (pol : Bool) : (s1 s2 : KindM × Option CTy × CTy) →
    FunEqv (mergeFun pol s1 s2) (mergeFun pol s2 s1)
  | (k1, d1, c1), (k2, d2, c2) => by
    have hszc : sizeOf c1 + sizeOf c2 < sizeOf (k1, d1, c1) + sizeOf (k2, d2, c2) := by
      simp
      omega
    have hcod : eqv (merge pol c1 c2) (merge pol c2 c1) = true := merge_comm pol c1 c2
    rw [mergeFun.eq_def, mergeFun.eq_def]
    simp only
    rcases hc1 : k1 == KindM.conflict with _ | _ <;>
      rcases hc2 : k2 == KindM.conflict with _ | _ <;>
      simp only [hc1, hc2, Bool.true_or, Bool.or_true, Bool.false_or, if_true]
    case true.true | true.false | false.true => exact ⟨rfl, trivial, hcod⟩
    -- Neither side conflicted.
    simp only [Bool.or_false, if_false, Bool.false_eq_true]
    cases pol
    · -- Negative: the meet.
      simp only [if_false, Bool.false_eq_true]
      have hk : (if k1 == KindM.data || k2 == KindM.data then KindM.data else KindM.compute) =
          (if k2 == KindM.data || k1 == KindM.data then KindM.data else KindM.compute) := by
        rw [Bool.or_comm]
      rcases d1 with _ | x <;> rcases d2 with _ | y
      · exact ⟨rfl, trivial, hcod⟩
      · exact ⟨rfl, trivial, hcod⟩
      · exact ⟨rfl, trivial, hcod⟩
      · have hszd : sizeOf x + sizeOf y < sizeOf (k1, some x, c1) + sizeOf (k2, some y, c2) := by
          simp
          omega
        exact ⟨hk, merge_comm true x y, hcod⟩
    · -- Positive: the join.
      simp only [if_true]
      rcases k1 with _ | _ | _ <;> rcases k2 with _ | _ | _ <;> simp_all
      -- data ⊔ data
      · rcases d1 with _ | x <;> rcases d2 with _ | y
        · exact ⟨rfl, trivial, hcod⟩
        · exact ⟨rfl, trivial, hcod⟩
        · exact ⟨rfl, trivial, hcod⟩
        · dsimp only
          rw [eqv_comm_bool y x]
          rcases hg : eqv x y with _ | _ <;> simp only [hg, Bool.false_eq_true, reduceIte]
          · exact ⟨rfl, trivial, hcod⟩
          · exact ⟨rfl, hg, hcod⟩
      -- data ⊔ compute
      · rcases d1 with _ | x <;> rcases d2 with _ | y
        · exact ⟨rfl, trivial, hcod⟩
        · exact ⟨rfl, trivial, hcod⟩
        · exact ⟨rfl, trivial, hcod⟩
        · have hszd : sizeOf x + sizeOf y <
              sizeOf (KindM.data, some x, c1) + sizeOf (KindM.compute, some y, c2) := by
            simp
            omega
          exact ⟨rfl, merge_comm false x y, hcod⟩
      -- compute ⊔ data
      · rcases d1 with _ | x <;> rcases d2 with _ | y
        · exact ⟨rfl, trivial, hcod⟩
        · exact ⟨rfl, trivial, hcod⟩
        · exact ⟨rfl, trivial, hcod⟩
        · have hszd : sizeOf x + sizeOf y <
              sizeOf (KindM.compute, some x, c1) + sizeOf (KindM.data, some y, c2) := by
            simp
            omega
          exact ⟨rfl, merge_comm false x y, hcod⟩
      -- compute ⊔ compute
      · rcases d1 with _ | x <;> rcases d2 with _ | y
        · exact ⟨rfl, trivial, hcod⟩
        · exact ⟨rfl, trivial, hcod⟩
        · exact ⟨rfl, trivial, hcod⟩
        · have hszd : sizeOf x + sizeOf y <
              sizeOf (KindM.compute, some x, c1) + sizeOf (KindM.compute, some y, c2) := by
            simp
            omega
          exact ⟨rfl, merge_comm false x y, hcod⟩
termination_by s1 s2 => (sizeOf s1 + sizeOf s2, 0)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

end

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

/-- The input-bound invariant (see the section header). -/
def wf : CTy → Bool
  | .mk _ r v f _ _ =>
    (match r with
     | none => true
     | some m => wfKeys m (m.map Prod.fst))
      && (match v with
          | none => true
          | some m => wfKeys m (m.map Prod.fst))
      && (match f with
          | none => true
          | some (k, d, cod) =>
            (k != .conflict)
              && (match d with
                  | some x => wf x
                  | none => false)
              && wf cod)
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
  | .mk a1 r1 v1 f1 c1 e1 => by
    intro hwf
    rw [wf.eq_def] at hwf
    simp only [Bool.and_eq_true] at hwf
    obtain ⟨⟨hwr, hwv⟩, hwfn⟩ := hwf
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
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp only [List.all_eq_true, List.contains_iff_mem, List.mem_append]
      exact fun x hx => hx.elim id id
    · simp only [List.all_eq_true, List.contains_iff_mem, List.mem_append]
      exact fun x hx => Or.inl hx
    · rcases r1 with _ | m
      · rfl
      · have hpay : ∀ x k, m.lookup k = some x → eqv (merge pol x x) x = true := by
          intro x k hx
          have hszx := lookup_sizeOf hx
          have hwx : wf x = true := (wfKeys_iff.mp (by simpa using hwr)) k
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
          have hwx : wf x = true := (wfKeys_iff.mp (by simpa using hwv)) k
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
      · simp only [Option.isSome] at hwfn
        rcases d1 with _ | x
        · simp at hwfn
        · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hwfn
          obtain ⟨⟨hk1, hwx⟩, hwcod⟩ := hwfn
          have hszx : sizeOf x < sizeOf (CTy.mk a1 r1 v1 (some (k1, some x, cod1)) c1 e1) := by
            simp
            omega
          have hszc : sizeOf cod1 <
              sizeOf (CTy.mk a1 r1 v1 (some (k1, some x, cod1)) c1 e1) := by
            simp
            omega
          have hx : eqv (merge (!pol) x x) x = true := merge_idem (!pol) x hwx
          have hxp : eqv (merge pol x x) x = true := merge_idem pol x hwx
          have hcod : eqv (merge pol cod1 cod1) cod1 = true := merge_idem pol cod1 hwcod
          dsimp only
          rw [mergeFun.eq_def]
          have hk1' : (k1 == KindM.conflict) = false := by
            rcases k1 with _ | _ | _ <;> simp_all
          simp only [hk1', Bool.or_self, Bool.false_eq_true, reduceIte]
          cases pol
          · simp only [Bool.false_eq_true, reduceIte]
            rcases k1 with _ | _ | _
            · simpa using funClause_of_funEqv
                (s1 := (KindM.data, some (merge true x x), merge false cod1 cod1))
                (s2 := (KindM.data, some x, cod1)) ⟨by simp, by simpa using hx, hcod⟩
            · simpa using funClause_of_funEqv
                (s1 := (KindM.compute, some (merge true x x), merge false cod1 cod1))
                (s2 := (KindM.compute, some x, cod1)) ⟨by simp, by simpa using hx, hcod⟩
            · simp at hk1
          · simp only [reduceIte]
            rcases k1 with _ | _ | _
            · simp [eqv_refl x, hcod]
            · simpa using funClause_of_funEqv
                (s1 := (KindM.compute, some (merge false x x), merge true cod1 cod1))
                (s2 := (KindM.compute, some x, cod1)) ⟨rfl, by simpa using hx, hcod⟩
            · simp at hk1
    · cases pol
      · simp only [Bool.false_eq_true, reduceIte, List.all_eq_true, List.contains_iff_mem,
          List.mem_append]
        exact fun x hx => hx.elim id id
      · simp only [reduceIte, List.all_eq_true, List.contains_iff_mem, List.mem_filter]
        exact fun x hx => hx.1
    · cases pol
      · simp only [Bool.false_eq_true, reduceIte, List.all_eq_true, List.contains_iff_mem,
          List.mem_append]
        exact fun x hx => Or.inl hx
      · simp only [reduceIte, List.all_eq_true, List.contains_iff_mem, List.mem_filter]
        exact fun x hx => ⟨hx, by simpa using hx⟩
    · simp
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
theorem funEqv_refl (s : KindM × Option CTy × CTy) : FunEqv s s := by
  obtain ⟨k, d, c⟩ := s
  refine ⟨rfl, ?_, eqv_refl c⟩
  rcases d with _ | x
  · trivial
  · exact eqv_refl x

mutual

theorem merge_congr_left (pol : Bool) :
    (a a' b : CTy) → eqv a a' = true → eqv (merge pol a b) (merge pol a' b) = true
  | .mk a1 r1 v1 f1 c1 e1, .mk a1' r1' v1' f1' c1' e1', .mk b1 rb vb fb cb eb => by
    intro h
    rw [eqv.eq_def] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hr⟩, hv⟩, hf⟩, hc1'⟩, hc2'⟩, he⟩ := h
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
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
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
        · simpa using funClause_of_funEqv (funEqv_refl sb)
      · rcases fb with _ | sb
        · simpa using hf
        · obtain ⟨k1, d1, cod1⟩ := s1
          obtain ⟨k1', d1', cod1'⟩ := s1'
          simp only [Bool.and_eq_true] at hf
          obtain ⟨⟨hk, hd⟩, hcod⟩ := hf
          have hk' : k1 = k1' := by simpa using hk
          have hsz : sizeOf (k1, d1, cod1) + sizeOf (k1', d1', cod1') + sizeOf sb <
              sizeOf (CTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1 e1) +
                sizeOf (CTy.mk a1' r1' v1' (some (k1', d1', cod1')) c1' e1') +
                sizeOf (CTy.mk b1 rb vb (some sb) cb eb) := by
            simp
            omega
          have hde : FunEqv (k1, d1, cod1) (k1', d1', cod1') := by
            refine ⟨hk', ?_, hcod⟩
            rcases d1 with _ | x <;> rcases d1' with _ | x' <;> simp_all
          simpa using funClause_of_funEqv
            (mergeFun_congr_left pol (k1, d1, cod1) (k1', d1', cod1') sb hde)
    · cases pol
      · simp only [Bool.false_eq_true, reduceIte, List.all_eq_true, List.contains_iff_mem,
          List.mem_append]
        simp only [List.all_eq_true, List.contains_iff_mem] at hc1'
        exact fun x hx => hx.imp (fun hm => by simpa using hc1' x hm) id
      · simp only [reduceIte, List.all_eq_true, List.contains_iff_mem, List.mem_filter]
        simp only [List.all_eq_true, List.contains_iff_mem] at hc1'
        exact fun x hx => ⟨by simpa using hc1' x hx.1, hx.2⟩
    · cases pol
      · simp only [Bool.false_eq_true, reduceIte, List.all_eq_true, List.contains_iff_mem,
          List.mem_append]
        simp only [List.all_eq_true, List.contains_iff_mem] at hc2'
        exact fun x hx => hx.imp (fun hm => by simpa using hc2' x hm) id
      · simp only [reduceIte, List.all_eq_true, List.contains_iff_mem, List.mem_filter]
        simp only [List.all_eq_true, List.contains_iff_mem] at hc2'
        exact fun x hx => ⟨by simpa using hc2' x hx.1, hx.2⟩
    · simp at he
      simp [he]
termination_by a a' b => (sizeOf a + sizeOf a' + sizeOf b, 1)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; omega)
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

theorem mergeFun_congr_left (pol : Bool) :
    (s1 s1' sb : KindM × Option CTy × CTy) → FunEqv s1 s1' →
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
    rw [mergeFun.eq_def, mergeFun.eq_def]
    simp only
    rcases hcf1 : k1 == KindM.conflict with _ | _ <;>
      rcases hcf2 : kb == KindM.conflict with _ | _ <;>
      simp only [hcf1, hcf2, Bool.true_or, Bool.or_true, Bool.false_or, if_true]
    case true.true | true.false | false.true => exact ⟨rfl, trivial, hcod⟩
    simp only [Bool.or_false, if_false, Bool.false_eq_true]
    cases pol
    · simp only [if_false, Bool.false_eq_true]
      rcases d1 with _ | x <;> rcases d1' with _ | x' <;>
        first
        | (simp at hd; done)
        | skip
        <;> rcases db with _ | y
      · exact ⟨rfl, trivial, hcod⟩
      · exact ⟨rfl, trivial, hcod⟩
      · exact ⟨rfl, trivial, hcod⟩
      · simp only at hd
        have hszd : sizeOf x + sizeOf x' + sizeOf y <
            sizeOf (k1, some x, c1) + sizeOf (k1, some x', c1') + sizeOf (kb, some y, cb) := by
          simp
          omega
        exact ⟨rfl, merge_congr_left true x x' y hd, hcod⟩
    · simp only [if_true]
      rcases k1 with _ | _ | _ <;> rcases kb with _ | _ | _ <;> simp_all
      -- data ⊔ data
      · rcases d1 with _ | x <;> rcases d1' with _ | x' <;>
          first
          | (simp at hd; done)
          | skip
          <;> rcases db with _ | y
        · exact ⟨rfl, trivial, hcod⟩
        · exact ⟨rfl, trivial, hcod⟩
        · exact ⟨rfl, trivial, hcod⟩
        · simp only at hd
          dsimp only
          rw [eqv_congr_bool hd y]
          rcases hg : eqv x' y with _ | _ <;> simp only [hg, Bool.false_eq_true, reduceIte]
          · exact ⟨rfl, trivial, hcod⟩
          · exact ⟨rfl, hd, hcod⟩
      -- data ⊔ compute
      · rcases d1 with _ | x <;> rcases d1' with _ | x' <;>
          first
          | (simp at hd; done)
          | skip
          <;> rcases db with _ | y
        · exact ⟨rfl, trivial, hcod⟩
        · exact ⟨rfl, trivial, hcod⟩
        · exact ⟨rfl, trivial, hcod⟩
        · simp only at hd
          have hszd : sizeOf x + sizeOf x' + sizeOf y <
              sizeOf (KindM.data, some x, c1) + sizeOf (KindM.data, some x', c1') +
                sizeOf (KindM.compute, some y, cb) := by
            simp
            omega
          exact ⟨rfl, merge_congr_left false x x' y hd, hcod⟩
      -- compute ⊔ data
      · rcases d1 with _ | x <;> rcases d1' with _ | x' <;>
          first
          | (simp at hd; done)
          | skip
          <;> rcases db with _ | y
        · exact ⟨rfl, trivial, hcod⟩
        · exact ⟨rfl, trivial, hcod⟩
        · exact ⟨rfl, trivial, hcod⟩
        · simp only at hd
          have hszd : sizeOf x + sizeOf x' + sizeOf y <
              sizeOf (KindM.compute, some x, c1) + sizeOf (KindM.compute, some x', c1') +
                sizeOf (KindM.data, some y, cb) := by
            simp
            omega
          exact ⟨rfl, merge_congr_left false x x' y hd, hcod⟩
      -- compute ⊔ compute
      · rcases d1 with _ | x <;> rcases d1' with _ | x' <;>
          first
          | (simp at hd; done)
          | skip
          <;> rcases db with _ | y
        · exact ⟨rfl, trivial, hcod⟩
        · exact ⟨rfl, trivial, hcod⟩
        · exact ⟨rfl, trivial, hcod⟩
        · simp only at hd
          have hszd : sizeOf x + sizeOf x' + sizeOf y <
              sizeOf (KindM.compute, some x, c1) + sizeOf (KindM.compute, some x', c1') +
                sizeOf (KindM.compute, some y, cb) := by
            simp
            omega
          exact ⟨rfl, merge_congr_left false x x' y hd, hcod⟩
termination_by s1 s1' sb => (sizeOf s1 + sizeOf s1' + sizeOf sb, 0)
decreasing_by all_goals
  first
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

/-! ## Associativity fails in general: the mixed-kind counterexample

Three function bounds at one position — two `data` collections over *distinct*
domains and one `compute` capability — merge to different outcomes depending
on association:

- `(D{Int} ⊔ D{Str}) ⊔ C{Int}`: the data join accumulates two alternatives,
  and a multi-domain data side meeting a compute side has no honest upcast —
  **conflict** (coalesce rejects the program).
- `(D{Int} ⊔ C{Int}) ⊔ D{Str}` (any association that pairs a single-domain
  data side with the compute side first): each step is the honest upcast —
  **compute** (accepted).

`compact_go` folds a variable's bounds left-to-right in arrival order, so this
is arrival order deciding accept-vs-reject. The fuzz's generated vocabulary
has not covered this shape (`confluence.rs` reports clean runs); whether a
real program can place these three bounds on one variable is a Rust-side
question this model can only pose. Until it is answered, associativity — and
therefore fold-order invariance — is proved on the compute-free fragment
(`merge_assoc_of_computeFree`), where the mixed arm cannot fire. -/

/-- The empty position (no contribution). -/
private def cxTop : CTy := .mk [] none none none [] false

/-- An atom position. -/
private def cxAtom (b : BaseTy) : CTy := .mk [.prim b] none none none [] false

/-- A single-domain function bound of the given kind. -/
private def cxFun (k : KindM) (d : CTy) : CTy :=
  .mk [] none none (some (k, some d, cxTop)) [] false

/-- The kind of a position's function slot. -/
private def fnKind : CTy → Option KindM
  | .mk _ _ _ f _ _ => f.map (·.1)

/-- One association conflicts (coalesce rejects)… -/
theorem merge_mixed_left_conflicts :
    fnKind (merge true (merge true (cxFun .data (cxAtom .int)) (cxFun .data (cxAtom .string)))
        (cxFun .compute (cxAtom .int))) = some .conflict := by
  simp [cxFun, cxTop, cxAtom, merge, mergeFun, fnKind, eqv]

/-- …while the other association is an accepted compute function: association
(hence bound arrival order) decides accept-vs-reject. -/
theorem merge_mixed_right_accepts :
    fnKind (merge true (cxFun .data (cxAtom .int)) (merge true (cxFun .data (cxAtom .string))
        (cxFun .compute (cxAtom .int)))) = some .compute := by
  simp [cxFun, cxTop, cxAtom, merge, mergeFun, fnKind, eqv]

/-- The headline: `merge` is **not** associative up to `eqv`. -/
theorem merge_not_assoc :
    ∃ (pol : Bool) (a b c : CTy),
      eqv (merge pol (merge pol a b) c) (merge pol a (merge pol b c)) = false := by
  refine ⟨true, cxFun .data (cxAtom .int), cxFun .data (cxAtom .string),
    cxFun .compute (cxAtom .int), ?_⟩
  simp [cxFun, cxTop, cxAtom, merge, mergeFun, eqv, subKeys]

/-! ## The compute-free fragment: associativity

On bounds whose function slots are all `data` — collections, the common case —
the mixed-kind arm cannot fire and the merge is associative. (`compute`-only
inputs are symmetric but meet through the contravariant domain, whose `none`
states conflict; the all-`data` fragment is the one the fold theorems need.) -/

mutual

/-- Every function slot reachable from this position is a `data` slot. -/
def computeFree : CTy → Bool
  | .mk _ r v f _ _ =>
    (match r with
     | none => true
     | some m => cfKeys m (m.map Prod.fst))
      && (match v with
          | none => true
          | some m => cfKeys m (m.map Prod.fst))
      && (match f with
          | none => true
          | some (k, d, cod) =>
            (k == .data)
              && (match d with
                  | some x => computeFree x
                  | none => true)
              && computeFree cod)
termination_by t => (sizeOf t, 0)

/-- All payloads of a map are `computeFree` (worklist form). -/
def cfKeys (m : List (FieldKey × CTy)) : List FieldKey → Bool
  | [] => true
  | k :: ks =>
    (match h : m.lookup k with
     | some v => computeFree v
     | none => true)
      && cfKeys m ks
termination_by ks => (sizeOf m, ks.length)
decreasing_by
  · have := lookup_sizeOf h
    apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    simp

end

/-- Pointwise reading of `cfKeys`. -/
theorem cfKeys_iff {m : List (FieldKey × CTy)} {ks : List FieldKey} :
    cfKeys m ks = true ↔ ∀ k ∈ ks, ∀ v, m.lookup k = some v → computeFree v = true := by
  induction ks with
  | nil => simp [cfKeys]
  | cons k ks ih =>
    rw [cfKeys, Bool.and_eq_true, ih]
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

mutual

theorem merge_assoc_cf (pol : Bool) :
    (a b c : CTy) → computeFree a = true → computeFree b = true → computeFree c = true →
      eqv (merge pol (merge pol a b) c) (merge pol a (merge pol b c)) = true
  | .mk a1 r1 v1 f1 c1 e1, .mk a2 r2 v2 f2 c2 e2, .mk a3 r3 v3 f3 c3 e3 => by
    intro ha hb hc
    rw [computeFree.eq_def] at ha hb hc
    simp only [Bool.and_eq_true] at ha hb hc
    obtain ⟨⟨har, hav⟩, haf⟩ := ha
    obtain ⟨⟨hbr, hbv⟩, hbf⟩ := hb
    obtain ⟨⟨hcr, hcv⟩, hcf⟩ := hc
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
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
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
        exact merge_assoc_cf pol x y z
          ((cfKeys_iff.mp (by simpa using har)) k (mem_keys_of_lookup hx) x hx)
          ((cfKeys_iff.mp (by simpa using hbr)) k (mem_keys_of_lookup hy) y hy)
          ((cfKeys_iff.mp (by simpa using hcr)) k (mem_keys_of_lookup hz) z hz)
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
        exact merge_assoc_cf pol x y z
          ((cfKeys_iff.mp (by simpa using hav)) k (mem_keys_of_lookup hx) x hx)
          ((cfKeys_iff.mp (by simpa using hbv)) k (mem_keys_of_lookup hy) y hy)
          ((cfKeys_iff.mp (by simpa using hcv)) k (mem_keys_of_lookup hz) z hz)
      cases pol
      · simpa using hinterA false m1 m2 m3 hassoc
      · simpa [unionMap] using hunionA true m1 m2 m3 hassoc
    · rcases f1 with _ | s1 <;> rcases f2 with _ | s2 <;> rcases f3 with _ | s3 <;>
        first
        | rfl
        | (simpa using funClause_of_funEqv (funEqv_refl _))
        | skip
      obtain ⟨k1, d1, cod1⟩ := s1
      obtain ⟨k2, d2, cod2⟩ := s2
      obtain ⟨k3, d3, cod3⟩ := s3
      simp only [Bool.and_eq_true] at haf hbf hcf
      have hsz : sizeOf (k1, d1, cod1) + sizeOf (k2, d2, cod2) + sizeOf (k3, d3, cod3) <
          sizeOf (CTy.mk a1 r1 v1 (some (k1, d1, cod1)) c1 e1) +
            sizeOf (CTy.mk a2 r2 v2 (some (k2, d2, cod2)) c2 e2) +
            sizeOf (CTy.mk a3 r3 v3 (some (k3, d3, cod3)) c3 e3) := by
        simp
        omega
      simpa using funClause_of_funEqv
        (mergeFun_assoc_cf pol (k1, d1, cod1) (k2, d2, cod2) (k3, d3, cod3)
          (by simpa using haf.1.1) (by simpa using hbf.1.1) (by simpa using hcf.1.1)
          (by
            rcases d1 with _ | x
            · intro x hx
              cases hx
            · intro x' hx'
              cases hx'
              simpa using haf.1.2)
          (by
            rcases d2 with _ | x
            · intro x hx
              cases hx
            · intro x' hx'
              cases hx'
              simpa using hbf.1.2)
          (by
            rcases d3 with _ | x
            · intro x hx
              cases hx
            · intro x' hx'
              cases hx'
              simpa using hcf.1.2)
          haf.2 hbf.2 hcf.2)
    · cases pol
      · simp only [Bool.false_eq_true, reduceIte, List.all_eq_true, List.contains_iff_mem,
          List.mem_append]
        exact fun x hx => by simpa [or_assoc] using hx
      · simp only [reduceIte, List.all_eq_true, List.contains_iff_mem, List.mem_filter]
        exact fun x hx => by simpa [and_assoc] using hx
    · cases pol
      · simp only [Bool.false_eq_true, reduceIte, List.all_eq_true, List.contains_iff_mem,
          List.mem_append]
        exact fun x hx => by simpa [or_assoc] using hx
      · simp only [reduceIte, List.all_eq_true, List.contains_iff_mem, List.mem_filter]
        exact fun x hx => by simpa [and_assoc] using hx
    · simp [Bool.or_assoc]
termination_by a b c => (sizeOf a + sizeOf b + sizeOf c, 1)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; omega)
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

theorem mergeFun_assoc_cf (pol : Bool) :
    (s1 s2 s3 : KindM × Option CTy × CTy) →
      s1.1 = .data → s2.1 = .data → s3.1 = .data →
      (∀ x, s1.2.1 = some x → computeFree x = true) →
      (∀ x, s2.2.1 = some x → computeFree x = true) →
      (∀ x, s3.2.1 = some x → computeFree x = true) →
      computeFree s1.2.2 = true → computeFree s2.2.2 = true → computeFree s3.2.2 = true →
      FunEqv (mergeFun pol (mergeFun pol s1 s2) s3) (mergeFun pol s1 (mergeFun pol s2 s3))
  | (k1, d1, c1), (k2, d2, c2), (k3, d3, c3) => by
    intro hk1 hk2 hk3 hd1 hd2 hd3 hc1 hc2 hc3
    subst hk1
    subst hk2
    subst hk3
    simp only at hd1 hd2 hd3 hc1 hc2 hc3
    have hszc : sizeOf c1 + sizeOf c2 + sizeOf c3 <
        sizeOf (KindM.data, d1, c1) + sizeOf (KindM.data, d2, c2) +
          sizeOf (KindM.data, d3, c3) := by
      simp
      omega
    have hcod : eqv (merge pol (merge pol c1 c2) c3) (merge pol c1 (merge pol c2 c3)) = true :=
      merge_assoc_cf pol c1 c2 c3 hc1 hc2 hc3
    have hgdc : (KindM.data == KindM.conflict) = false := rfl
    have hgdd : (KindM.data == KindM.data) = true := rfl
    have hgcc : (KindM.conflict == KindM.conflict) = true := rfl
    cases pol
    · -- Negative: kinds stay data; a missing domain conflicts on both sides.
      rcases d1 with _ | x <;> rcases d2 with _ | y <;> rcases d3 with _ | z <;>
        simp only [mergeFun.eq_def, hgdc, hgdd, hgcc, Bool.or_self, Bool.or_false,
          Bool.false_or, Bool.true_or, Bool.or_true, Bool.false_eq_true, reduceIte] <;>
        first
        | exact ⟨rfl, trivial, hcod⟩
        | (have hszd : sizeOf x + sizeOf y + sizeOf z <
              sizeOf (KindM.data, some x, c1) + sizeOf (KindM.data, some y, c2) +
                sizeOf (KindM.data, some z, c3) := by
            simp
            omega
           exact ⟨rfl, merge_assoc_cf true x y z (hd1 x rfl) (hd2 y rfl) (hd3 z rfl), hcod⟩)
    · -- Positive: the gate algebra.
      rcases d1 with _ | x <;> rcases d2 with _ | y <;> rcases d3 with _ | z <;>
        simp only [mergeFun.eq_def, hgdc, hgdd, hgcc, Bool.or_self, Bool.or_false,
          Bool.false_or, Bool.true_or, Bool.or_true, Bool.false_eq_true, reduceIte] <;>
        first
        | exact ⟨rfl, trivial, hcod⟩
        | (rcases hxy : eqv x y with _ | _ <;>
             simp only [hxy, Bool.false_eq_true, reduceIte] <;>
             exact ⟨rfl, trivial, hcod⟩)
        | (rcases hyz : eqv y z with _ | _ <;>
             simp only [hyz, Bool.false_eq_true, reduceIte] <;>
             exact ⟨rfl, trivial, hcod⟩)
        | (rcases hxy : eqv x y with _ | _
           · simp only [hxy, Bool.false_eq_true, reduceIte]
             rcases hyz : eqv y z with _ | _ <;>
               simp only [hyz, hxy, Bool.false_eq_true, reduceIte] <;>
               exact ⟨rfl, trivial, hcod⟩
           · simp only [hxy, reduceIte]
             have hxz : eqv x z = eqv y z := eqv_congr_bool hxy z
             rcases hyz : eqv y z with _ | _
             · rw [hxz, hyz]
               simp only [Bool.false_eq_true, reduceIte]
               exact ⟨rfl, trivial, hcod⟩
             · rw [hxz, hyz]
               simp only [hxy, reduceIte]
               exact ⟨rfl, eqv_refl x, hcod⟩)
termination_by s1 s2 s3 => (sizeOf s1 + sizeOf s2 + sizeOf s3, 0)
decreasing_by all_goals
  first
  | (apply Prod.Lex.left; omega)
  | (apply Prod.Lex.left; simp; omega)
  | (apply Prod.Lex.right; simp; omega)

end

/-! ## The fold: coalescing a bound list is order- and duplicate-invariant

`compact_go` folds a variable's bounds through `merge` from the first bound
(no identity element exists — see the module docs). On the compute-free
fragment the outcome is a function of the bound *set*: permutations
(`foldMerge_perm`) and duplicates (`foldMerge_dup`) cannot change it. This is
the algebraic statement behind the confluence fuzz's \"outcomes agree under
permuted constraint orders\". -/

/-- Positive merges stay compute-free (the join of two `data` slots is a
`data` slot). The *negative* direction genuinely does not preserve the
fragment — a multi-alternative domain meeting anything conflicts — which is
why the fold theorems are stated at positive polarity. -/
theorem computeFree_merge_pos : (a b : CTy) → computeFree a = true → computeFree b = true →
    computeFree (merge true a b) = true
  | .mk a1 r1 v1 f1 c1 e1, .mk a2 r2 v2 f2 c2 e2 => by
    intro ha hb
    rw [computeFree.eq_def] at ha hb
    simp only [Bool.and_eq_true] at ha hb
    obtain ⟨⟨har, hav⟩, haf⟩ := ha
    obtain ⟨⟨hbr, hbv⟩, hbf⟩ := hb
    have hmapI : ∀ (m1 m2 : List (FieldKey × CTy)),
        (∀ x k, m1.lookup k = some x → computeFree x = true) →
        (∀ x k, m2.lookup k = some x → computeFree x = true) →
        (∀ x y k, m1.lookup k = some x → m2.lookup k = some y →
          computeFree (merge true x y) = true) →
        cfKeys (interMap true m1 m2) ((interMap true m1 m2).map Prod.fst) = true := by
      intro m1 m2 _ _ hrec
      rw [cfKeys_iff]
      intro k _ v hv
      rw [interMap_lookup] at hv
      cases h1 : m1.lookup k with
      | none =>
        rw [h1] at hv
        exact absurd hv (by simp)
      | some x =>
        rw [h1] at hv
        cases h2 : m2.lookup k with
        | none =>
          rw [h2] at hv
          exact absurd hv (by simp)
        | some y =>
          rw [h2] at hv
          dsimp only at hv
          cases hv
          exact hrec _ _ k h1 h2
    have hmapU : ∀ (m1 m2 : List (FieldKey × CTy)),
        (∀ x k, m1.lookup k = some x → computeFree x = true) →
        (∀ x k, m2.lookup k = some x → computeFree x = true) →
        (∀ x y k, m1.lookup k = some x → m2.lookup k = some y →
          computeFree (merge true x y) = true) →
        cfKeys (unionMap true m1 m2) ((unionMap true m1 m2).map Prod.fst) = true := by
      intro m1 m2 hm1 hm2 hrec
      rw [cfKeys_iff]
      intro k _ v hv
      rw [unionMap_lookup] at hv
      cases h1 : m1.lookup k with
      | none =>
        rw [h1] at hv
        cases h2 : m2.lookup k with
        | none =>
          rw [h2] at hv
          exact absurd hv (by simp)
        | some y =>
          rw [h2] at hv
          dsimp only at hv
          cases hv
          exact hm2 _ k h2
      | some x =>
        rw [h1] at hv
        cases h2 : m2.lookup k with
        | none =>
          rw [h2] at hv
          dsimp only at hv
          cases hv
          exact hm1 _ k h1
        | some y =>
          rw [h2] at hv
          dsimp only at hv
          cases hv
          exact hrec _ _ k h1 h2
    rw [merge.eq_def, computeFree.eq_def]
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rcases r1 with _ | m1 <;> rcases r2 with _ | m2
      · rfl
      · simpa using hbr
      · simpa using har
      · have hrec : ∀ x y k, m1.lookup k = some x → m2.lookup k = some y →
            computeFree (merge true x y) = true := by
          intro x y k hx hy
          have hszx := lookup_sizeOf hx
          have hszy := lookup_sizeOf hy
          exact computeFree_merge_pos x y
            ((cfKeys_iff.mp (by simpa using har)) k (mem_keys_of_lookup hx) x hx)
            ((cfKeys_iff.mp (by simpa using hbr)) k (mem_keys_of_lookup hy) y hy)
        simpa using hmapI m1 m2
          (fun x k hx => (cfKeys_iff.mp (by simpa using har)) k (mem_keys_of_lookup hx) x hx)
          (fun x k hx => (cfKeys_iff.mp (by simpa using hbr)) k (mem_keys_of_lookup hx) x hx)
          hrec
    · rcases v1 with _ | m1 <;> rcases v2 with _ | m2
      · rfl
      · simpa using hbv
      · simpa using hav
      · have hrec : ∀ x y k, m1.lookup k = some x → m2.lookup k = some y →
            computeFree (merge true x y) = true := by
          intro x y k hx hy
          have hszx := lookup_sizeOf hx
          have hszy := lookup_sizeOf hy
          exact computeFree_merge_pos x y
            ((cfKeys_iff.mp (by simpa using hav)) k (mem_keys_of_lookup hx) x hx)
            ((cfKeys_iff.mp (by simpa using hbv)) k (mem_keys_of_lookup hy) y hy)
        simpa [unionMap] using hmapU m1 m2
          (fun x k hx => (cfKeys_iff.mp (by simpa using hav)) k (mem_keys_of_lookup hx) x hx)
          (fun x k hx => (cfKeys_iff.mp (by simpa using hbv)) k (mem_keys_of_lookup hx) x hx)
          hrec
    · rcases f1 with _ | ⟨k1, d1, cod1⟩ <;> rcases f2 with _ | ⟨k2, d2, cod2⟩
      · rfl
      · simpa using hbf
      · simpa using haf
      · simp only [Bool.and_eq_true] at haf hbf
        have hk1 : k1 = .data := by
          have := haf.1.1
          rcases k1 with _ | _ | _ <;> simp_all
        have hk2 : k2 = .data := by
          have := hbf.1.1
          rcases k2 with _ | _ | _ <;> simp_all
        subst hk1
        subst hk2
        have hszc : sizeOf cod1 + sizeOf cod2 <
            sizeOf (CTy.mk a1 r1 v1 (some (KindM.data, d1, cod1)) c1 e1) +
              sizeOf (CTy.mk a2 r2 v2 (some (KindM.data, d2, cod2)) c2 e2) := by
          simp
          omega
        have hcod : computeFree (merge true cod1 cod2) = true :=
          computeFree_merge_pos cod1 cod2 haf.2 hbf.2
        dsimp only
        rw [mergeFun.eq_def]
        simp only [show (KindM.data == KindM.conflict) = false from rfl, Bool.or_self,
          Bool.false_eq_true, reduceIte]
        rcases d1 with _ | x <;> rcases d2 with _ | y <;>
          first
          | (simp [hcod]; done)
          | skip
        have hcfx : computeFree x = true := by simpa using haf.1.2
        rcases hg : eqv x y with _ | _ <;> simp [hg, hcod, hcfx]
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp; omega)

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

/-- **Order-invariance**: on compute-free bounds, permuting the bound list
cannot change the coalesced outcome (up to `eqv`). -/
theorem foldMerge_perm {l1 l2 : List CTy} (h : l1.Perm l2) :
    ∀ (t : CTy), computeFree t = true → (∀ x ∈ l1, computeFree x = true) →
      eqv (foldMerge true t l1) (foldMerge true t l2) = true := by
  induction h with
  | nil => exact fun t _ _ => eqv_refl _
  | @cons x l1 l2 hp ih =>
    intro t ht hl
    exact ih (merge true t x) (computeFree_merge_pos t x ht (hl x (by simp)))
      (fun u hu => hl u (by simp [hu]))
  | @swap x y l =>
    intro t ht hl
    have hx : computeFree x = true := hl x (by simp)
    have hy : computeFree y = true := hl y (by simp)
    -- merge (merge t y) x ~ merge t (merge y x) ~ merge t (merge x y)
    --   ~ merge (merge t x) y
    have hseed : eqv (merge true (merge true t y) x) (merge true (merge true t x) y) = true :=
      eqv_trans _ _ _ (merge_assoc_cf true t y x ht hy hx)
        (eqv_trans _ _ _ (merge_congr_right true t _ _ (merge_comm true y x))
          (eqv_symm _ _ (merge_assoc_cf true t x y ht hx hy)))
    simpa [foldMerge, List.foldl_cons] using foldMerge_congr true l hseed
  | @trans l1 l2 l3 h12 h23 ih1 ih2 =>
    intro t ht hl
    exact eqv_trans _ _ _ (ih1 t ht hl)
      (ih2 t ht (fun u hu => hl u (h12.mem_iff.mpr hu)))

/-- **Duplicate-invariance**: a bound occurring twice contributes once — the
other half of \"the outcome is a function of the bound set\". Needs `wf` for
the duplicated bound (idempotence does). -/
theorem foldMerge_dup {t x : CTy} (l : List CTy)
    (ht : computeFree t = true) (hx : computeFree x = true) (hwx : wf x = true) :
    eqv (foldMerge true t (x :: x :: l)) (foldMerge true t (x :: l)) = true := by
  -- merge (merge t x) x ~ merge t (merge x x) ~ merge t x
  have hseed : eqv (merge true (merge true t x) x) (merge true t x) = true :=
    eqv_trans _ _ _ (merge_assoc_cf true t x x ht hx hx)
      (merge_congr_right true t _ _ (merge_idem true x hwx))
  simpa [foldMerge, List.foldl_cons] using foldMerge_congr true l hseed

end CTy

end CclFormal
