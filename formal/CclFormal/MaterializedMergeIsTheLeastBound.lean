import CclFormal.MaterializedMergeIsABound
import CclFormal.SubtypingIsTransitive

/-!
# The materialized merge is the least bound, over types

`MaterializedMergeIsABound.lean` proves leastness among positions (`merge_is_least_position`) by transporting the
merge's own order. This module proves it over `Ty` (`merge_is_least_type`): every well-formed type
bounding both operands' materializations bounds the merge's, with no position standing in for the
type and `absorbedBy` never mentioned. Reflecting `Subtyping` into that order is false, so the
induction is on the materializations.

One induction (`bounds_merge`) carries four statements, because the side the bound sits on is a
parameter (`bounds`) independent of the merge's polarity. The two instances where side and polarity
agree are leastness. The other two say a type both operands bound is bounded by the merge, which is
what the function case needs of its domains: a domain flips the polarity and the subtyping edge
together, and a `data` domain is invariant, so leastness alone does not close that case.

`coalesce_wellFormed` is what connects the theorem to `MaterializedMergeIsABound.lean`'s sample: a `wellFormed`
position materializes to a well-formed type, so every candidate bound in the pool is one
`merge_is_least_type` applies to, and the sample's leastness line becomes
`leastness_failures_eq_nil` rather than a `#guard`.
-/

namespace CclFormal
namespace CompactTy

/-! ## The side a bound sits on -/

/-- `u` bounds `t` from above or from below, the side a parameter:
`bounds true u t` is `Subtyping t u` and `bounds false u t` is `Subtyping u t`. In both, `u` is the
bound and `t` the type it bounds.

The bound's side is independent of the merge's polarity. A positive merge's least bound is an upper
one and a negative merge's is a lower one, so leastness is the diagonal. The off-diagonal is what a
function's domains need, since a domain
flips the polarity and the bound's side together. -/
def bounds (above : Bool) (u t : Ty) : Prop := if above then Subtyping t u else Subtyping u t

theorem bounds_true {u t : Ty} (h : Subtyping t u) : bounds true u t := by
  simpa [bounds] using h

theorem bounds_false {u t : Ty} (h : Subtyping u t) : bounds false u t := by
  simpa [bounds] using h

theorem of_bounds_true {u t : Ty} (h : bounds true u t) : Subtyping t u := by
  simpa [bounds] using h

theorem of_bounds_false {u t : Ty} (h : bounds false u t) : Subtyping u t := by
  simpa [bounds] using h

/-! ## Refinements, on and off a materialized shape

`coalesce` builds every type it returns as `attachRefinements shape c`, and the shape is never
itself a refinement node. So the peel of what it returns is known outright, and the refinement half
of every case is `Subtyping`'s peel inversion read
against that. -/

/-- The refinement slot's set, with the identity reading as none. -/
def refinementsOf : Option (List Predicate) → List Predicate
  | none => []
  | some ps => ps

theorem attachRefinements_peel {t : Ty} (h : t.isRefined = false) (c : Option (List Predicate)) :
    (attachRefinements t c).peel = (t, refinementsOf c) := by
  rcases c with _ | ps
  · exact Ty.peel_of_not_refined h
  rcases ps with _ | ⟨p, ps⟩
  · exact Ty.peel_of_not_refined h
  · have : attachRefinements t (some (p :: ps)) = .refined t (p :: ps) := by
      cases t <;> simp_all [attachRefinements, Ty.isRefined]
    rw [this, Ty.peel, Ty.peel_of_not_refined h]
    simp [refinementsOf]

/-- A materialized type is its own peel when the slot contributes nothing. -/
theorem attachRefinements_peel_self {t : Ty} (h : t.isRefined = false)
    (c : Option (List Predicate)) :
    (attachRefinements t c).peel.2 = [] → (attachRefinements t c).peel.1
      = attachRefinements t c := by
  intro hnil
  rw [attachRefinements_peel h] at hnil ⊢
  rcases c with _ | ps
  · rfl
  rcases ps with _ | ⟨p, ps⟩
  · rfl
  · exact absurd hnil (by simp [refinementsOf])

/-- A subtyping edge from its peeled halves. The two hypotheses say a type is its
own peel when its refinement set is empty, which `Ty.peel_nil_self` supplies for
a well-formed type and `attachRefinements_peel_self` for a materialized one. -/
theorem subtyping_of_peel {x y : Ty} (hx : x.peel.2 = [] → x.peel.1 = x)
    (hy : y.peel.2 = [] → y.peel.1 = y)
    (hbase : Subtyping x.peel.1 y.peel.1) (href : ∀ p ∈ y.peel.2, p ∈ x.peel.2) : Subtyping x y :=
      by
  by_cases h : x.peel.2 = [] ∧ y.peel.2 = []
  · rw [← hx h.1, ← hy h.2]
    exact hbase
  · exact .refined rfl rfl (by
      rcases not_and_or' h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h') (deficit_eq_nil_iff.mpr href) hbase

/-- Peel inversion and reconstruction together: a subtyping edge is its peeled
base edge and refinement containment, and nothing else. -/
theorem subtyping_iff_peel {x y : Ty} (hx : x.peel.2 = [] → x.peel.1 = x)
    (hy : y.peel.2 = [] → y.peel.1 = y) :
    Subtyping x y ↔ (Subtyping x.peel.1 y.peel.1 ∧ ∀ p ∈ y.peel.2, p ∈ x.peel.2) := by
  constructor
  · intro h
    obtain ⟨hdef, hbase⟩ := subtyping_peel_inv h
    exact ⟨hbase, deficit_eq_nil_iff.mp hdef⟩
  · intro ⟨hbase, href⟩
    exact subtyping_of_peel hx hy hbase href

/-! ## Products, viewed by key

A tuple and a record are the same shape read with two spellings of the key, and `coalesce`'s record
slot materializes to whichever its map's keys call for. `Subtyping` has one rule for each spelling,
differing only in how the key is written, so the statements below are about the key-indexed view and
the two rules are recovered
from it. -/

/-- A key's spelling: a tuple's position or a record's name. `coalesce` refuses a
map that mixes them (`CoalesceError.partialRecord`, the Rust's `UnresolvedPartial`). -/
inductive KeyKind where
  | positional | named
deriving DecidableEq, Repr

/-- A key's own spelling. -/
def keyKind : FieldKey → KeyKind
  | .idx _ => .positional
  | .name _ => .named

/-- A product's spelling, and `none` for what is not a product. -/
def productKind : Ty → Option KeyKind
  | .tuple _ => some .positional
  | .record _ => some .named
  | _ => none

/-- The field a product carries at a key: a tuple's position, a record's name. A
key of the other spelling resolves nowhere. -/
def productAt : Ty → FieldKey → Option Ty
  | .tuple ts, .idx i => ts[i]?
  | .record fs, .name n => List.lookup n fs
  | _, _ => none

/-- The payload a variant accepts at a tag. -/
def variantAt : Ty → FieldKey → Option Ty
  | .variant tags, k => List.lookup k tags
  | _, _ => none

theorem nodupKeys_iff {l : List FieldKey} : nodupKeys l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [nodupKeys]
  | cons k ks ih => simp [nodupKeys, ih]

/-! ## Product subtyping, read through the view -/

theorem productKind_positional : ∀ {x : Ty}, productKind x = some .positional → ∃ ts, x = .tuple ts
  | .tuple ts, _ => ⟨ts, rfl⟩
  | .base _, h | .uintRange _, h | .dataSource _, h | .txn, h | .fn .., h
  | .record _, h | .variant _, h | .refined .., h => by simp [productKind] at h

theorem productKind_named : ∀ {x : Ty}, productKind x = some .named → ∃ fs, x = .record fs
  | .record fs, _ => ⟨fs, rfl⟩
  | .base _, h | .uintRange _, h | .dataSource _, h | .txn, h | .fn .., h
  | .tuple _, h | .variant _, h | .refined .., h => by simp [productKind] at h

/-- A product edge, inverted: with neither operand refined and one of them a
product, both are, at the same spelling, and every field the supertype demands resolves above it in
the subtype. One statement for both product rules and for either operand being the known one, since
whether the product under discussion is
the subtype or the supertype depends on the bound's side. -/
theorem product_subtyping_edge {x y : Ty} (h : Subtyping x y) (hx : x.peel.2 = [])
    (hy : y.peel.2 = [])
    (hprod : (productKind x).isSome = true ∨ (productKind y).isSome = true) :
    ∃ k, productKind x = some k ∧ productKind y = some k ∧
      ∀ key t, productAt y key = some t → ∃ s, productAt x key = some s ∧ Subtyping s t := by
  cases h with
  | tuple hlen hget =>
    rename_i ts bs
    refine ⟨.positional, rfl, rfl, ?_⟩
    rintro (i | n) t hk
    · simp only [productAt] at hk ⊢
      have hi : i < bs.length := by
        rcases Nat.lt_or_ge i bs.length with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none hge] at hk
          cases hk
      obtain ⟨s, hs⟩ : ∃ s, ts[i]? = some s :=
        ⟨_, List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hi hlen)⟩
      exact ⟨s, hs, hget i s t hs hk⟩
    · simp [productAt] at hk
  | record hpres hpay =>
    refine ⟨.named, rfl, rfl, ?_⟩
    rintro (i | n) t hk
    · simp [productAt] at hk
    · simp only [productAt] at hk ⊢
      have hmem := mem_of_lookup hk
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hpres n t hmem)
      exact ⟨s, by rw [← lookupBy_eq_lookup]; exact hs, hpay n s t hmem hs⟩
  | refined hpl hpr hg _ _ =>
    rw [hpl] at hx
    rw [hpr] at hy
    rcases hg with hg | hg
    · exact absurd hx hg
    · exact absurd hy hg
  | _ => rcases hprod with hp | hp <;> simp [productKind] at hp

/-- Construction: matching spellings, and a field of the subtype above every field
the supertype demands. `Ty.WellFormed` supplies the unique keys the record rule's
membership premise needs. -/
theorem product_subtyping_of {x y : Ty} {k : KeyKind} (hx : productKind x = some k)
    (hy : productKind y = some k)
    (hndy : ∀ gs : List (String × Ty), y = .record gs → (gs.map (·.1)).Nodup)
    (hfields : ∀ k t, productAt y k = some t → ∃ s, productAt x k = some s ∧ Subtyping s t) :
    Subtyping x y := by
  cases k
  · obtain ⟨ts, rfl⟩ := productKind_positional hx
    obtain ⟨bs, rfl⟩ := productKind_positional hy
    have hlen : bs.length ≤ ts.length := by
      rcases Nat.lt_or_ge ts.length bs.length with hlt | hge
      · obtain ⟨t, ht⟩ : ∃ t, bs[ts.length]? = some t :=
          ⟨_, List.getElem?_eq_getElem hlt⟩
        obtain ⟨s, hs, -⟩ := hfields (.idx ts.length) t (by simpa [productAt] using ht)
        rw [productAt, List.getElem?_eq_none (Nat.le_refl _)] at hs
        cases hs
      · exact hge
    refine .tuple hlen fun i t0 t1 h0 h1 => ?_
    obtain ⟨s, hs, hsub⟩ := hfields (.idx i) t1 (by simpa [productAt] using h1)
    rw [productAt, h0] at hs
    cases hs
    exact hsub
  · obtain ⟨fs, rfl⟩ := productKind_named hx
    obtain ⟨gs, rfl⟩ := productKind_named hy
    have hnd : (gs.map (·.1)).Nodup := hndy gs rfl
    have hstep : ∀ n t1, (n, t1) ∈ gs → ∃ s, lookupBy fs n = some s ∧ Subtyping s t1 := by
      intro n t1 hmem
      obtain ⟨s, hs, hsub⟩ := hfields (.name n) t1 (by
        rw [productAt, ← lookupBy_eq_lookup]
        exact lookupBy_of_mem_nodup hnd hmem)
      rw [productAt] at hs
      exact ⟨s, by rw [lookupBy_eq_lookup]; exact hs, hsub⟩
    exact .record (fun n t1 hmem => by obtain ⟨s, hs, -⟩ := hstep n t1 hmem; simp [hs])
      (fun n t0 t1 hmem hlk => by
        obtain ⟨s, hs, hsub⟩ := hstep n t1 hmem
        rw [hlk] at hs
        cases hs
        exact hsub)

/-! ## Variant subtyping, read through the view

The dual reading: a variant's tags run with the subtyping edge rather than against it, so the
quantifier is over the subtype's tags and the supertype is the
one that must resolve them. -/

def isVariant : Ty → Bool
  | .variant _ => true
  | _ => false

theorem isVariant_ex : ∀ {x : Ty}, isVariant x = true → ∃ tags, x = .variant tags
  | .variant tags, _ => ⟨tags, rfl⟩
  | .base _, h | .uintRange _, h | .dataSource _, h | .txn, h | .fn .., h
  | .tuple _, h | .record _, h | .refined .., h => by simp [isVariant] at h

/-- A variant edge, inverted: with neither operand refined and one of them a
variant, both are, and every tag the subtype may produce the supertype accepts
above it. -/
theorem variant_subtyping_edge {x y : Ty} (h : Subtyping x y) (hx : x.peel.2 = [])
    (hy : y.peel.2 = [])
    (hvar : isVariant x = true ∨ isVariant y = true) :
    isVariant x = true ∧ isVariant y = true ∧
      ∀ k s, variantAt x k = some s → ∃ t, variantAt y k = some t ∧ Subtyping s t := by
  cases h with
  | variant hacc hpay =>
    refine ⟨rfl, rfl, ?_⟩
    intro k s hk
    simp only [variantAt] at hk ⊢
    have hmem := mem_of_lookup hk
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hacc k s hmem)
    exact ⟨t, by rw [← lookupBy_eq_lookup]; exact ht, hpay k s t hmem ht⟩
  | refined hpl hpr hg _ _ =>
    rw [hpl] at hx
    rw [hpr] at hy
    rcases hg with hg | hg
    · exact absurd hx hg
    · exact absurd hy hg
  | _ => rcases hvar with hv | hv <;> simp [isVariant] at hv

/-- Construction: a variant whose every tag the other accepts above it. `Ty.WellFormed`
supplies the unique tags the rule's membership premise needs, on the subtype
this time. -/
theorem variant_subtyping_of {x y : Ty} (hx : isVariant x = true) (hy : isVariant y = true)
    (hndx : ∀ tags : List (FieldKey × Ty), x = .variant tags → (tags.map (·.1)).Nodup)
    (htags : ∀ k s, variantAt x k = some s → ∃ t, variantAt y k = some t ∧ Subtyping s t) :
      Subtyping x y := by
  obtain ⟨tx, rfl⟩ := isVariant_ex hx
  obtain ⟨ty, rfl⟩ := isVariant_ex hy
  have hnd : (tx.map (·.1)).Nodup := hndx tx rfl
  have hstep : ∀ k s, (k, s) ∈ tx → ∃ t, lookupBy ty k = some t ∧ Subtyping s t := by
    intro k s hmem
    obtain ⟨t, ht, hsub⟩ := htags k s (by
      rw [variantAt, ← lookupBy_eq_lookup]
      exact lookupBy_of_mem_nodup hnd hmem)
    rw [variantAt] at ht
    exact ⟨t, by rw [lookupBy_eq_lookup]; exact ht, hsub⟩
  exact .variant (fun k s hmem => by obtain ⟨t, ht, -⟩ := hstep k s hmem; simp [ht])
    (fun k s t hmem hlk => by
      obtain ⟨t', ht, hsub⟩ := hstep k s hmem
      rw [hlk] at ht
      cases ht
      exact hsub)

/-! ## Function subtyping, read off the edge -/

/-- Whether a type is a function. -/
def isFn : Ty → Bool
  | .fn .. => true
  | _ => false

/-- A function edge, inverted: with neither operand refined and one of them a
function, both are, their kinds agree, the domain runs against the edge, a `data`
domain runs both ways, and the codomains run with it. -/
theorem fn_subtyping_edge {x y : Ty} (h : Subtyping x y) (hx : x.peel.2 = []) (hy : y.peel.2 = [])
    (hfn : isFn x = true ∨ isFn y = true) :
    ∃ n0 n1 k d0 c0 d1 c1, x = .fn n0 k d0 c0 ∧ y = .fn n1 k d1 c1 ∧
      Subtyping d1 d0 ∧ (k = .data → Subtyping d0 d1) ∧ Subtyping c0 c1 := by
  cases h with
  | fnCompute hk hnd hdom hcod =>
    rename_i n0 n1 k0 k1 d0 c0 d1 c1
    have hkk : k0 = k1 := by cases k0 <;> cases k1 <;> simp_all [kindOk]
    subst hkk
    exact ⟨n0, n1, k0, d0, c0, d1, c1, rfl, rfl, hdom, fun h0 => absurd ⟨h0, h0⟩ hnd, hcod⟩
  | fnData hdom hinv hcod =>
    exact ⟨_, _, _, _, _, _, _, rfl, rfl, hdom, fun _ => hinv, hcod⟩
  | refined hpl hpr hg _ _ =>
    rw [hpl] at hx
    rw [hpr] at hy
    rcases hg with hg | hg
    · exact absurd hx hg
    · exact absurd hy hg
  | _ => rcases hfn with hf | hf <;> simp [isFn] at hf

/-- Construction: the same edge, assembled. -/
theorem fn_subtyping_of {n0 n1 : Option String} {k : FunKind} {d0 c0 d1 c1 : Ty}
    (hdom : Subtyping d1 d0) (hinv : k = .data → Subtyping d0 d1) (hcod : Subtyping c0 c1) :
    Subtyping (.fn n0 k d0 c0) (.fn n1 k d1 c1) := by
  cases k
  · exact .fnCompute trivial (by simp) hdom hcod
  · exact .fnData hdom (hinv rfl) hcod

/-! ## The merged maps keep their keys unique

`coalesce` materializes every entry of a keyed slot and `Subtyping`'s two keyed rules read the first
binding for a key, so a duplicate is observable in the type. The merge introduces none: an
intersection is a sublist of the left map's keys, and a
union is the left map's keys followed by the keys only the right map has. -/

theorem intersectMap_keys_sublist (pol : Bool) :
    ∀ (m1 m2 : List (FieldKey × CompactTy)),
      ((intersectMap pol m1 m2).map Prod.fst).Sublist (m1.map Prod.fst)
  | [], m2 => by rw [intersectMap]; simp
  | (k, v) :: rest, m2 => by
    rw [intersectMap]
    rcases h : m2.lookup k with _ | w
    · exact (intersectMap_keys_sublist pol rest m2).cons _
    · exact (intersectMap_keys_sublist pol rest m2).cons_cons _

theorem unionMapGo_keys (pol : Bool) :
    ∀ (m1 m2 : List (FieldKey × CompactTy)),
      (unionMapGo pol m1 m2).map Prod.fst = m1.map Prod.fst
  | [], m2 => by rw [unionMapGo]
  | (k, v) :: rest, m2 => by
    rw [unionMapGo]
    simpa using unionMapGo_keys pol rest m2

theorem nodupKeys_intersectMap {pol : Bool} {m1 m2 : List (FieldKey × CompactTy)}
    (h : nodupKeys (m1.map Prod.fst) = true) :
    nodupKeys ((intersectMap pol m1 m2).map Prod.fst) = true :=
  nodupKeys_iff.mpr ((nodupKeys_iff.mp h).sublist (intersectMap_keys_sublist pol m1 m2))

theorem nodupKeys_unionMap {pol : Bool} {m1 m2 : List (FieldKey × CompactTy)}
    (h1 : nodupKeys (m1.map Prod.fst) = true) (h2 : nodupKeys (m2.map Prod.fst) = true) :
    nodupKeys ((unionMapGo pol m1 m2 ++ m2.filter
      (fun kw => (m1.lookup kw.1).isNone)).map Prod.fst) = true := by
  refine nodupKeys_iff.mpr ?_
  rw [List.map_append, unionMapGo_keys]
  refine List.nodup_append.mpr ⟨nodupKeys_iff.mp h1,
    (nodupKeys_iff.mp h2).sublist (List.Sublist.map _ List.filter_sublist), ?_⟩
  rintro k hk1 k' hk2 rfl
  obtain ⟨e, hmem, rfl⟩ := List.mem_map.mp hk2
  have hnone := (List.mem_filter.mp hmem).2
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (lookup_of_mem_keys hk1)
  simp [hv] at hnone

/-! ## What a materialized keyed slot presents

`coalesce` walks a keyed slot's map and materializes each payload, so the type it returns presents
exactly the map's keys carrying exactly those materializations. Stated once against the view, so the
record and variant cases below never touch
the tuple/record split or the association-list representation again. -/

/-- A name-keyed association list resolves no index key. -/
theorem lookup_idx_named_none {i : Nat} : ∀ (names : List String) (ts : List Ty),
    List.lookup (FieldKey.idx i) ((names.map FieldKey.name).zip ts) = none
  | [], _ => by simp
  | _ :: _, [] => by simp
  | n :: ns, _ :: ts => by
    rw [List.map_cons, List.zip_cons_cons, List.lookup_cons,
      show (FieldKey.idx i == FieldKey.name n) = false from rfl]
    exact lookup_idx_named_none ns ts

/-- An index-keyed association list resolves no name key. -/
theorem lookup_name_idx_none {s : String} : ∀ (idxs : List Nat) (ts : List Ty),
    List.lookup (FieldKey.name s) ((idxs.map FieldKey.idx).zip ts) = none
  | [], _ => by simp
  | _ :: _, [] => by simp
  | i :: is, _ :: ts => by
    rw [List.map_cons, List.zip_cons_cons, List.lookup_cons,
      show (FieldKey.name s == FieldKey.idx i) = false from rfl]
    exact lookup_name_idx_none is ts

/-- A key absent from an association list resolves nowhere in it. -/
theorem lookup_eq_none_of_not_mem {α β} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α}
    (h : k ∉ l.map Prod.fst) : l.lookup k = none := by
  rcases hl : l.lookup k with _ | v
  · rfl
  · exact absurd (List.mem_map_of_mem (mem_of_lookup hl)) h

theorem nodup_map_idx : ∀ {l : List Nat}, l.Nodup → (l.map FieldKey.idx).Nodup
  | [], _ => by simp
  | i :: is, h => by
    rw [List.nodup_cons] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_map_idx h.2⟩
    obtain ⟨j, hj, hij⟩ := List.mem_map.mp hm
    cases hij
    exact h.1 hj

/-- A dense index key list with unique keys and one entry per position holds only
positions — the counting argument the tuple shape rests on. -/
theorem dense_idxs_lt {idxs : List Nat} {n : Nat}
    (hlen : idxs.length = n) (hall : ∀ i, i < n → i ∈ idxs) : ∀ i ∈ idxs, i < n := by
  intro i hi
  rcases Nat.lt_or_ge i n with hlt | hge
  · exact hlt
  exfalso
  have hsub : ∀ x ∈ ((i :: List.range n).map FieldKey.idx), x ∈ idxs.map FieldKey.idx := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    refine List.mem_map_of_mem ?_
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact hi
    · exact hall j (List.mem_range.mp hj')
  have hndc : nodupKeys ((i :: List.range n).map FieldKey.idx) = true :=
    nodupKeys_iff.mpr (nodup_map_idx (List.nodup_cons.mpr
      ⟨fun hm => absurd (List.mem_range.mp hm) (Nat.not_lt.mpr hge), List.nodup_range⟩))
  have hle := nodupKeys_length_le hndc hsub
  simp only [List.length_map, List.length_cons, List.length_range, hlen] at hle
  omega

/-- A zip's left components are a prefix of the left list. -/
theorem zip_fst_sublist {α β} : ∀ (l₁ : List α) (l₂ : List β),
    ((l₁.zip l₂).map Prod.fst).Sublist l₁
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, _ :: ys => by simpa using (zip_fst_sublist xs ys).cons_cons x

/-- The materialized record slot, keyed: the product presents the map's keys, each
carrying its payload's materialization, and takes its spelling from the keys. -/
theorem coalesce_record_view (pol : Bool) {m : List (FieldKey × CompactTy)}
    {c : Option (List Predicate)}
    {ty : Ty} (hnd : nodupKeys (m.map Prod.fst) = true)
    (h : coalesce pol (.mk [] (some m) none none c) = .ok (some ty)) :
    ∃ base, ty = attachRefinements base c ∧ base.isRefined = false ∧ m ≠ [] ∧
      (∀ k ∈ m.map Prod.fst, productKind base = some (keyKind k)) ∧
      (∀ k v, m.lookup k = some v → ∃ t, productAt base k = some t ∧
        coalesce pol v = .ok (some t)) ∧
      (∀ k t, productAt base k = some t → ∃ v, m.lookup k = some v ∧
        coalesce pol v = .ok (some t)) ∧
      (∀ gs : List (String × Ty), base = .record gs → (gs.map (·.1)).Nodup) := by
  obtain ⟨hne, ts, base, rfl, hrel, hshape⟩ := coalesce_record_ok pol h
  -- The whole case rests on one equation: the product resolves a key exactly as
  -- the map-keyed payload list does.
  have hat : ∀ k, productAt base k = ((m.map Prod.fst).zip ts).lookup k ∧
      (∀ k' ∈ m.map Prod.fst, productKind base = some (keyKind k')) ∧
      base.isRefined = false := by
    rcases hshape with ⟨idxs, hi, hb⟩ | ⟨names, hn, rfl⟩
    · obtain ⟨ts', rfl, hlen', hget⟩ := byIndex_get hb
      have hkeys := indexKeys_keys hi
      have hinj : ∀ a b : Nat, FieldKey.idx a = FieldKey.idx b → a = b := by
        intro a b hab; cases hab; rfl
      have hilen : idxs.length = m.length := by
        have := congrArg List.length hkeys
        simpa using this.symm
      have hall : ∀ i, i < m.length → i ∈ idxs := by
        intro i hi'
        obtain ⟨z, hz⟩ : ∃ z, ts'[i]? = some z :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        exact (List.of_mem_zip (mem_of_lookup (hget i z hi' hz))).1
      have hlt := dense_idxs_lt hilen hall
      refine fun k => ⟨?_, fun k' hk' => ?_, rfl⟩
      · cases k with
        | name s =>
          show (none : Option Ty) = _
          rw [hkeys, lookup_name_idx_none]
        | idx i =>
          show ts'[i]? = _
          rw [hkeys, lookup_zip_map_key FieldKey.idx hinj]
          rcases Nat.lt_or_ge i m.length with hi' | hi'
          · obtain ⟨z, hz⟩ : ∃ z, ts'[i]? = some z :=
              ⟨_, List.getElem?_eq_getElem (by omega)⟩
            rw [hz, hget i z hi' hz]
          · rw [List.getElem?_eq_none (by omega),
              lookup_eq_none_of_not_mem (fun hm => by
                obtain ⟨e, hem, he⟩ := List.mem_map.mp hm
                have hlti := hlt e.1 (List.of_mem_zip hem).1
                rw [he] at hlti
                omega)]
      · rw [hkeys] at hk'
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hk'
        rfl
    · have hkeys := nameKeys_keys hn
      refine fun k => ⟨?_, fun k' hk' => ?_, rfl⟩
      · cases k with
        | idx i =>
          show (none : Option Ty) = _
          rw [hkeys, lookup_idx_named_none]
        | name s =>
          show List.lookup s (names.zip ts) = _
          rw [hkeys, lookup_zip_map_key FieldKey.name (fun a b hab => by cases hab; rfl)]
      · rw [hkeys] at hk'
        obtain ⟨s, -, rfl⟩ := List.mem_map.mp hk'
        rfl
  refine ⟨base, rfl, (hat (.idx 0)).2.2, hne, (hat (.idx 0)).2.1, ?_, ?_, ?_⟩
  · intro k v hv
    obtain ⟨t, ht, hct⟩ := hrel.lookup hv
    exact ⟨t, by rw [(hat k).1]; exact ht, hct⟩
  · intro k t ht
    rw [(hat k).1] at ht
    exact hrel.lookup' ht
  · rcases hshape with ⟨idxs, hi, hb⟩ | ⟨names, hn, rfl⟩
    · obtain ⟨ts', rfl, -, -⟩ := byIndex_get hb
      intro gs hgs
      cases hgs
    · intro gs hgs
      cases hgs
      have hnames : names.Nodup := by
        have := nodupKeys_iff.mp hnd
        rw [nameKeys_keys hn] at this
        exact List.Pairwise.of_map FieldKey.name (fun a b hne heq => hne (by rw [heq])) this
      exact hnames.sublist (zip_fst_sublist names ts)

/-- The materialized variant slot, keyed. -/
theorem coalesce_variant_view (pol : Bool) {m : List (FieldKey × CompactTy)}
    {c : Option (List Predicate)}
    {ty : Ty} (hnd : nodupKeys (m.map Prod.fst) = true)
    (h : coalesce pol (.mk [] none (some m) none c) = .ok (some ty)) :
    ∃ base, ty = attachRefinements base c ∧ base.isRefined = false ∧ isVariant base = true ∧
      (∀ k v, m.lookup k = some v → ∃ t, variantAt base k = some t ∧
        coalesce pol v = .ok (some t)) ∧
      (∀ k t, variantAt base k = some t → ∃ v, m.lookup k = some v ∧
        coalesce pol v = .ok (some t)) ∧
      (∀ tags : List (FieldKey × Ty), base = .variant tags → (tags.map (·.1)).Nodup) := by
  obtain ⟨kvs, rfl, hrel⟩ := coalesce_variant_ok pol h
  refine ⟨.variant kvs, rfl, rfl, rfl, fun k v hv => hrel.lookup hv,
    fun k t ht => hrel.lookup' ht, fun tags htags => ?_⟩
  cases htags
  rw [← hrel.keys] at hnd
  exact nodupKeys_iff.mp hnd

/-! ## A function slot with more than one alternative

The merge accumulates domain alternatives at a positive position, so the merged slot is outside the
one-domain shape `wellFormed` guarantees of an input bound and the inversions `MaterializedMergeIsABound.lean`
states over that shape do not reach it. These two take the alternatives as they come: a `data`
slot's must all materialize to one type,
which is what its dedup demands, and a `compute` slot's are folded first. -/

theorem mapM_ok_mem {α β ε} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → ∀ a ∈ l, ∃ b, b ∈ l' ∧ f a = .ok b
  | [], _, h, a, ha => by simp at ha
  | x :: xs, l', h, a, ha => by
    obtain ⟨b, bs, hfx, hbs, rfl⟩ := mapM_ok_cons h
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact ⟨b, by simp, hfx⟩
    · obtain ⟨b', hb', hfa⟩ := mapM_ok_mem hbs a ha'
      exact ⟨b', List.mem_cons_of_mem _ hb', hfa⟩

/-! ## Assembling one edge

Every case below ends the same way: the shapes are related and the refinement sets sit on the
bound's side. Both halves are stated once here, so the four cases
differ only in what they do to the shape. -/

/-- The refinement half of a bound: the demanded set is supplied, on whichever
side the bound sits. -/
def refinementsBound (above : Bool) (u : Ty) (c : Option (List Predicate)) : Prop :=
  if above then ∀ x ∈ u.peel.2, x ∈ refinementsOf c else ∀ x ∈ refinementsOf c, x ∈ u.peel.2

/-- A bound on a materialized type is a bound on its shape together with the
refinement half, and nothing else. -/
theorem bounds_attach_iff (above : Bool) {base u : Ty} {c : Option (List Predicate)}
    (hnr : base.isRefined = false) (hwu : u.WellFormed) :
    bounds above u (attachRefinements base c) ↔
      (bounds above u.peel.1 base ∧ refinementsBound above u c) := by
  cases above
  · simp only [bounds, refinementsBound, Bool.false_eq_true, if_false]
    rw [subtyping_iff_peel (Ty.peel_nil_self hwu) (attachRefinements_peel_self hnr c),
      attachRefinements_peel hnr]
  · simp only [bounds, refinementsBound, if_true]
    rw [subtyping_iff_peel (attachRefinements_peel_self hnr c) (Ty.peel_nil_self hwu),
      attachRefinements_peel hnr]

/-- The refinement half survives the merge at either polarity: a positive merge
intersects the two sets, so it is contained in each, and a negative one unites
them, so it contains each — and that is the containment the bound's side wants. -/
theorem refinementsBound_merge (pol above : Bool) {u : Ty} {p q : List Predicate}
    (h1 : refinementsBound above u (some p)) (h2 : refinementsBound above u (some q)) :
    refinementsBound above u (mergeRefinements pol (some p) (some q)) := by
  simp only [refinementsBound, refinementsOf, mergeRefinements] at h1 h2 ⊢
  cases above <;> cases pol <;>
    simp only [Bool.false_eq_true, if_false, if_true] at h1 h2 ⊢
  · exact fun x hx => (List.mem_append.mp hx).elim (h1 x) (h2 x)
  · exact fun x hx => h1 x (List.mem_filter.mp hx).1
  · exact fun x hx => List.mem_append.mpr (Or.inl (h1 x hx))
  · exact fun x hx => List.mem_filter.mpr ⟨h1 x hx, by simpa using h2 x hx⟩

/-! ## The merged position, slot by slot -/

theorem merge_atoms_slot (pol : Bool) (as bs : List Atom) (c₁ c₂ : Option (List Predicate)) :
    merge pol (.mk as none none none c₁) (.mk bs none none none c₂)
      = .mk (as ++ bs) none none none (mergeRefinements pol c₁ c₂) := by
  rw [merge.eq_def]

theorem merge_record_slot (pol : Bool) (ma mb : List (FieldKey × CompactTy))
    (c₁ c₂ : Option (List Predicate)) :
    merge pol (.mk [] (some ma) none none c₁) (.mk [] (some mb) none none c₂)
      = .mk [] (some (if pol then intersectMap pol ma mb
          else unionMapGo pol ma mb ++ mb.filter (fun kw => (ma.lookup kw.1).isNone)))
        none none (mergeRefinements pol c₁ c₂) := by
  rw [merge.eq_def]
  rfl

theorem merge_variant_slot (pol : Bool) (ma mb : List (FieldKey × CompactTy))
    (c₁ c₂ : Option (List Predicate)) :
    merge pol (.mk [] none (some ma) none c₁) (.mk [] none (some mb) none c₂)
      = .mk [] none (some (if pol then
            unionMapGo pol ma mb ++ mb.filter (fun kw => (ma.lookup kw.1).isNone)
          else intersectMap pol ma mb)) none (mergeRefinements pol c₁ c₂) := by
  rw [merge.eq_def]
  rfl

theorem merge_fn_slot (pol : Bool) (g₁ g₂ : KindMerge × CompactTy × CompactTy)
    (c₁ c₂ : Option (List Predicate)) :
    merge pol (.mk [] none none (some g₁) c₁) (.mk [] none none (some g₂) c₂)
      = .mk [] none none (some (mergeFun pol g₁ g₂)) (mergeRefinements pol c₁ c₂) := by
  rw [merge.eq_def]
  rfl

/-- Materializing the merge forces both operands to the same shape. The merge
leaves a slot absent only when both operands do, so a slot only one of them
carries lands beside the other's and `combine` sees two contributions. -/
theorem merge_shape_agrees (pol : Bool) {as bs : List Atom}
    {ra va rb vb : Option (List (FieldKey × CompactTy))}
      {fa fb : Option (KindMerge × CompactTy × CompactTy)}
    {ca cb : Option (List Predicate)} {tm : Ty}
    (hm : coalesce pol (merge pol (.mk as ra va fa ca) (.mk bs rb vb fb cb))
      = .ok (some tm)) :
    (ra = none ∧ rb = none ∧ va = none ∧ vb = none ∧ fa = none ∧ fb = none) ∨
    (as = [] ∧ bs = [] ∧ va = none ∧ vb = none ∧ fa = none ∧ fb = none) ∨
    (as = [] ∧ bs = [] ∧ ra = none ∧ rb = none ∧ fa = none ∧ fb = none) ∨
    (as = [] ∧ bs = [] ∧ ra = none ∧ rb = none ∧ va = none ∧ vb = none) := by
  obtain ⟨r, v, f, heq, hr, hv, hf⟩ := merge_slots pol as bs ra rb va vb fa fb ca cb
  rw [heq] at hm
  have hnil : as ++ bs = [] → as = [] ∧ bs = [] := by
    intro h
    exact ⟨List.append_eq_nil_iff.mp h |>.1, List.append_eq_nil_iff.mp h |>.2⟩
  rcases coalesce_shape pol hm with ⟨-, h2, h3, h4⟩ | ⟨h1, -, h3, h4⟩
    | ⟨h1, h2, -, h4⟩ | ⟨h1, h2, h3, -⟩
  · exact Or.inl ⟨(hr.mp h2).1, (hr.mp h2).2, (hv.mp h3).1, (hv.mp h3).2,
      (hf.mp h4).1, (hf.mp h4).2⟩
  · exact Or.inr (Or.inl ⟨(hnil h1).1, (hnil h1).2, (hv.mp h3).1, (hv.mp h3).2,
      (hf.mp h4).1, (hf.mp h4).2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨(hnil h1).1, (hnil h1).2, (hr.mp h2).1, (hr.mp h2).2,
      (hf.mp h4).1, (hf.mp h4).2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨(hnil h1).1, (hnil h1).2, (hr.mp h2).1, (hr.mp h2).2,
      (hv.mp h3).1, (hv.mp h3).2⟩))

/-! ## Edges, on the bound's side

The three edge inversions above are stated on `Subtyping`, whose subtype and supertype swap with the
bound's side. Restated on `bounds`, the payload relation comes out the same on either side, and only
which of the two must resolve the other's keys flips — which is the whole difference the bound's
side makes in the keyed
cases. -/

theorem product_bounds_edge (above : Bool) {P y : Ty} (h : bounds above y P)
    (hP : (productKind P).isSome = true) (hpP : P.peel.2 = []) (hpy : y.peel.2 = []) :
    ∃ k, productKind P = some k ∧ productKind y = some k ∧
      (if above then ∀ key t, productAt y key = some t → (productAt P key).isSome = true
        else ∀ key s, productAt P key = some s → (productAt y key).isSome = true) ∧
      (∀ key s t, productAt P key = some s → productAt y key = some t → bounds above t s) := by
  cases above
  · obtain ⟨k, hky, hkP, hfields⟩ :=
      product_subtyping_edge (of_bounds_false h) hpy hpP (Or.inr hP)
    refine ⟨k, hkP, hky, ?_, ?_⟩
    · simp only [Bool.false_eq_true, if_false]
      intro key s hs
      obtain ⟨t, ht, -⟩ := hfields key s hs
      simp [ht]
    · intro key s t hs ht
      obtain ⟨t', ht', hsub⟩ := hfields key s hs
      rw [ht] at ht'
      cases ht'
      exact bounds_false hsub
  · obtain ⟨k, hkP, hky, hfields⟩ :=
      product_subtyping_edge (of_bounds_true h) hpP hpy (Or.inl hP)
    refine ⟨k, hkP, hky, ?_, ?_⟩
    · simp only [if_true]
      intro key t ht
      obtain ⟨s, hs, -⟩ := hfields key t ht
      simp [hs]
    · intro key s t hs ht
      obtain ⟨s', hs', hsub⟩ := hfields key t ht
      rw [hs] at hs'
      cases hs'
      exact bounds_true hsub

theorem product_bounds_of (above : Bool) {P y : Ty} {k : KeyKind}
    (hP : productKind P = some k) (hy : productKind y = some k)
    (hndP : ∀ gs : List (String × Ty), P = .record gs → (gs.map (·.1)).Nodup)
    (hndy : ∀ gs : List (String × Ty), y = .record gs → (gs.map (·.1)).Nodup)
    (hpres : if above then ∀ key t, productAt y key = some t → (productAt P key).isSome = true
      else ∀ key s, productAt P key = some s → (productAt y key).isSome = true)
    (hpay : ∀ key s t, productAt P key = some s → productAt y key = some t → bounds above t s) :
    bounds above y P := by
  cases above
  · simp only [Bool.false_eq_true, if_false] at hpres
    refine bounds_false (product_subtyping_of hy hP hndP fun key s hs => ?_)
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hpres key s hs)
    exact ⟨t, ht, of_bounds_false (hpay key s t hs ht)⟩
  · simp only [if_true] at hpres
    refine bounds_true (product_subtyping_of hP hy hndy fun key t ht => ?_)
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hpres key t ht)
    exact ⟨s, hs, of_bounds_true (hpay key s t hs ht)⟩

theorem variant_bounds_edge (above : Bool) {P y : Ty} (h : bounds above y P)
    (hP : isVariant P = true) (hpP : P.peel.2 = []) (hpy : y.peel.2 = []) :
    isVariant y = true ∧
      (if above then ∀ key s, variantAt P key = some s → (variantAt y key).isSome = true
        else ∀ key t, variantAt y key = some t → (variantAt P key).isSome = true) ∧
      (∀ key s t, variantAt P key = some s → variantAt y key = some t → bounds above t s) := by
  cases above
  · obtain ⟨hy, -, htags⟩ := variant_subtyping_edge (of_bounds_false h) hpy hpP (Or.inr hP)
    refine ⟨hy, ?_, ?_⟩
    · simp only [Bool.false_eq_true, if_false]
      intro key t ht
      obtain ⟨s, hs, -⟩ := htags key t ht
      simp [hs]
    · intro key s t hs ht
      obtain ⟨s', hs', hsub⟩ := htags key t ht
      rw [hs] at hs'
      cases hs'
      exact bounds_false hsub
  · obtain ⟨-, hy, htags⟩ := variant_subtyping_edge (of_bounds_true h) hpP hpy (Or.inl hP)
    refine ⟨hy, ?_, ?_⟩
    · simp only [if_true]
      intro key s hs
      obtain ⟨t, ht, -⟩ := htags key s hs
      simp [ht]
    · intro key s t hs ht
      obtain ⟨t', ht', hsub⟩ := htags key s hs
      rw [ht] at ht'
      cases ht'
      exact bounds_true hsub

theorem variant_bounds_of (above : Bool) {P y : Ty}
    (hP : isVariant P = true) (hy : isVariant y = true)
    (hndP : ∀ tags : List (FieldKey × Ty), P = .variant tags → (tags.map (·.1)).Nodup)
    (hndy : ∀ tags : List (FieldKey × Ty), y = .variant tags → (tags.map (·.1)).Nodup)
    (hpres : if above then ∀ key s, variantAt P key = some s → (variantAt y key).isSome = true
      else ∀ key t, variantAt y key = some t → (variantAt P key).isSome = true)
    (hpay : ∀ key s t, variantAt P key = some s → variantAt y key = some t → bounds above t s) :
    bounds above y P := by
  cases above
  · simp only [Bool.false_eq_true, if_false] at hpres
    refine bounds_false (variant_subtyping_of hy hP hndy fun key t ht => ?_)
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hpres key t ht)
    exact ⟨s, hs, of_bounds_false (hpay key s t hs ht)⟩
  · simp only [if_true] at hpres
    refine bounds_true (variant_subtyping_of hP hy hndP fun key s hs => ?_)
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hpres key s hs)
    exact ⟨t, ht, of_bounds_true (hpay key s t hs ht)⟩

/-- A field of a well-formed product is well-formed. -/
theorem productAt_wellFormed {y : Ty} {k : FieldKey} {t : Ty} (hwy : y.WellFormed)
    (h : productAt y k = some t) :
    t.WellFormed := by
  cases y <;> cases k <;> simp only [productAt] at h <;> try cases h
  · exact hwy.tuple_mem (List.mem_of_getElem? h)
  · exact hwy.record_mem (mem_of_lookup h)

/-- A payload of a well-formed variant is well-formed. -/
theorem variantAt_wellFormed {y : Ty} {k : FieldKey} {t : Ty} (hwy : y.WellFormed)
    (h : variantAt y k = some t) :
    t.WellFormed := by
  cases y <;> simp only [variantAt] at h <;> try cases h
  exact hwy.variant_mem (mem_of_lookup h)

/-! ## The keyed core

A record's key set intersects at a positive position and unites at a negative one, and a variant's
does the opposite; the payload merges at the outer polarity either way. So the operation is a
parameter, and what the two cases share — the
payload's bound — is stated once against it. -/

/-- The keyed slot a merge produces, with the key rule as a parameter — the shape
`compact.rs`'s `merge_keyed` has. `Merge.lean` splits that into `intersectMap` and `unionMap`
because `merge` reads the rule off the slot and the polarity together; this puts the two back under
one name for the cases that are indifferent to
which. -/
def mergeKeyed (intersectKeys pol : Bool) (ma mb : List (FieldKey × CompactTy)) : List
    (FieldKey × CompactTy) :=
  if intersectKeys then intersectMap pol ma mb else unionMap pol ma mb

theorem mergeKeyed_lookup (intersectKeys pol : Bool) (ma mb : List (FieldKey × CompactTy))
    (k : FieldKey) :
    (mergeKeyed intersectKeys pol ma mb).lookup k =
      match ma.lookup k, mb.lookup k with
      | some v, some w => some (merge pol v w)
      | some v, none => if intersectKeys then none else some v
      | none, some w => if intersectKeys then none else some w
      | none, none => none := by
  cases intersectKeys <;> simp only [mergeKeyed, if_true, Bool.false_eq_true, if_false]
  · rw [unionMap_lookup]
    rcases ma.lookup k with _ | v <;> rcases mb.lookup k with _ | w <;> rfl
  · rw [intersectMap_lookup]
    rcases ma.lookup k with _ | v <;> rcases mb.lookup k with _ | w <;> rfl

/-- A key the merged map carries came from one of the operands. -/
theorem mergeKeyed_key {intersectKeys pol : Bool} {ma mb : List (FieldKey × CompactTy)}
    {k : FieldKey}
    {vw : CompactTy} (h : (mergeKeyed intersectKeys pol ma mb).lookup k = some vw) :
    (ma.lookup k).isSome = true ∨ (mb.lookup k).isSome = true := by
  rw [mergeKeyed_lookup] at h
  rcases hva : ma.lookup k with _ | v <;> rcases hvb : mb.lookup k with _ | w <;>
    rw [hva, hvb] at h
  · cases h
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- The merged payload's bound: whatever bounds both operands' payloads at a key
bounds the merged one. Where only one operand carries the key the merge copies
its payload, so there is nothing to combine. -/
theorem keyed_payload_bounds (intersectKeys pol above : Bool) {ma mb : List (FieldKey × CompactTy)}
    {k : FieldKey} {vw : CompactTy} {sm t : Ty}
    (ih : ∀ (v w : CompactTy) (tv tw tvw : Ty), ma.lookup k = some v → mb.lookup k = some w →
      coalesce pol v = .ok (some tv) → coalesce pol w = .ok (some tw) →
      coalesce pol (merge pol v w) = .ok (some tvw) →
      bounds above t tv → bounds above t tw → bounds above t tvw)
    (hM : (mergeKeyed intersectKeys pol ma mb).lookup k = some vw)
    (hsm : coalesce pol vw = .ok (some sm))
    (hta : ∀ v, ma.lookup k = some v → ∃ sa, coalesce pol v = .ok (some sa) ∧ bounds above t sa)
    (htb : ∀ w, mb.lookup k = some w → ∃ sb, coalesce pol w = .ok (some sb) ∧ bounds above t sb) :
    bounds above t sm := by
  rw [mergeKeyed_lookup] at hM
  rcases hva : ma.lookup k with _ | v <;> rcases hvb : mb.lookup k with _ | w <;>
    rw [hva, hvb] at hM
  · cases hM
  · cases intersectKeys
    · simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hM
      subst hM
      obtain ⟨sb, hcb, hbb⟩ := htb w hvb
      rw [hcb] at hsm
      cases hsm
      exact hbb
    · cases hM
  · cases intersectKeys
    · simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hM
      subst hM
      obtain ⟨sa, hca, hba⟩ := hta v hva
      rw [hca] at hsm
      cases hsm
      exact hba
    · cases hM
  · simp only [Option.some.injEq] at hM
    subst hM
    obtain ⟨sa, hca, hba⟩ := hta v hva
    obtain ⟨sb, hcb, hbb⟩ := htb w hvb
    exact ih v w sa sb sm hva hvb hca hcb hsm hba hbb

/-- A non-empty map has a key. -/
theorem exists_mem_keys {m : List (FieldKey × CompactTy)} (h : m ≠ []) : ∃ k, k ∈ m.map Prod.fst :=
    by
  rcases m with _ | ⟨⟨k, v⟩, rest⟩
  · exact absurd rfl h
  · exact ⟨k, by simp⟩

/-! ## The record case -/

theorem bounds_record (pol above : Bool) {ma mb : List (FieldKey × CompactTy)}
    {p q : List Predicate}
    {u ta tb tm : Ty}
    (hnda : nodupKeys (ma.map Prod.fst) = true) (hndb : nodupKeys (mb.map Prod.fst) = true)
    (hwu : u.WellFormed)
    (ih : ∀ (k : FieldKey) (v w : CompactTy) (tv tw tvw t : Ty),
      ma.lookup k = some v → mb.lookup k = some w →
      coalesce pol v = .ok (some tv) → coalesce pol w = .ok (some tw) →
      coalesce pol (merge pol v w) = .ok (some tvw) →
      t.WellFormed → bounds above t tv → bounds above t tw → bounds above t tvw)
    (ha : coalesce pol (.mk [] (some ma) none none (some p)) = .ok (some ta))
    (hb : coalesce pol (.mk [] (some mb) none none (some q)) = .ok (some tb))
    (hm : coalesce pol (merge pol (.mk [] (some ma) none none (some p))
      (.mk [] (some mb) none none (some q))) = .ok (some tm))
    (hba : bounds above u ta) (hbb : bounds above u tb) : bounds above u tm := by
  obtain ⟨Pa, rfl, hnra, hnea, hkia, hfwa, hbwa, hnpa⟩ := coalesce_record_view pol hnda ha
  obtain ⟨Pb, rfl, hnrb, hneb, hkib, hfwb, hbwb, hnpb⟩ := coalesce_record_view pol hndb hb
  rw [merge_record_slot, show (if pol then intersectMap pol ma mb
      else unionMapGo pol ma mb ++ mb.filter (fun kw => (ma.lookup kw.1).isNone))
      = mergeKeyed pol pol ma mb from by cases pol <;> rfl] at hm
  have hndM : nodupKeys ((mergeKeyed pol pol ma mb).map Prod.fst) = true := by
    cases pol
    · exact nodupKeys_unionMap hnda hndb
    · exact nodupKeys_intersectMap hnda
  obtain ⟨Pm, rfl, hnrm, hnem, hkim, hfwm, hbwm, hnpm⟩ := coalesce_record_view pol hndM hm
  rw [bounds_attach_iff above hnra hwu] at hba
  rw [bounds_attach_iff above hnrb hwu] at hbb
  rw [bounds_attach_iff above hnrm hwu]
  refine ⟨?_, refinementsBound_merge pol above hba.2 hbb.2⟩
  -- The shape half. Both operands' products and `u`'s peel share a spelling, and
  -- the merged map's keys come from the operands, so it shares theirs.
  have hwup : u.peel.1.WellFormed := Ty.WellFormed.peel_fst hwu
  have hpu : u.peel.1.peel.2 = [] := by rw [Ty.peel_fst_peel]
  have hpPa : Pa.peel.2 = [] := by rw [Ty.peel_of_not_refined hnra]
  have hpPb : Pb.peel.2 = [] := by rw [Ty.peel_of_not_refined hnrb]
  have hpPm : Pm.peel.2 = [] := by rw [Ty.peel_of_not_refined hnrm]
  obtain ⟨k0, hk0⟩ := exists_mem_keys hnea
  obtain ⟨ka, hkPa, hkU, hpresa, hpaya⟩ :=
    product_bounds_edge above hba.1 (by rw [hkia k0 hk0]; rfl) hpPa hpu
  obtain ⟨k1, hk1⟩ := exists_mem_keys hneb
  obtain ⟨kb, hkPb, hkU', hpresb, hpayb⟩ :=
    product_bounds_edge above hbb.1 (by rw [hkib k1 hk1]; rfl) hpPb hpu
  have hkab : kb = ka := by rw [hkU] at hkU'; exact (Option.some.injEq _ _ ▸ hkU').symm
  subst hkab
  -- Every key either operand carries is spelled the way `u`'s are.
  have hspell : ∀ k, (ma.lookup k).isSome = true ∨ (mb.lookup k).isSome = true →
      keyKind k = kb := by
    intro k hk
    rcases hk with hk | hk
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
      have := hkia k (mem_keys_of_lookup hv)
      rw [hkPa] at this
      exact (Option.some.injEq _ _ ▸ this).symm
    · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hk
      have := hkib k (mem_keys_of_lookup hw)
      rw [hkPb] at this
      exact (Option.some.injEq _ _ ▸ this).symm
  obtain ⟨km, hkm⟩ := exists_mem_keys hnem
  have hkPm : productKind Pm = some kb := by
    rw [hkim km hkm, hspell km (mergeKeyed_key
      (Option.isSome_iff_exists.mp (lookup_of_mem_keys hkm)).choose_spec)]
  refine product_bounds_of above hkPm hkU hnpm (fun gs hgs => by
    rw [hgs] at hwup
    cases hwup with | record hnd _ => exact hnd) ?_ ?_
  · -- Which of the two must resolve the other's keys, by the bound's side.
    cases above
    · simp only [Bool.false_eq_true, if_false] at hpresa hpresb ⊢
      intro key sm hsm
      obtain ⟨vw, hvw, -⟩ := hbwm key sm hsm
      rcases mergeKeyed_key hvw with hk | hk
      · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
        obtain ⟨sa, hsa, -⟩ := hfwa key v hv
        exact hpresa key sa hsa
      · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hk
        obtain ⟨sb, hsb, -⟩ := hfwb key w hw
        exact hpresb key sb hsb
    · simp only [if_true] at hpresa hpresb ⊢
      intro key t ht
      obtain ⟨sa, hsa⟩ := Option.isSome_iff_exists.mp (hpresa key t ht)
      obtain ⟨sb, hsb⟩ := Option.isSome_iff_exists.mp (hpresb key t ht)
      obtain ⟨v, hv, -⟩ := hbwa key sa hsa
      obtain ⟨w, hw, -⟩ := hbwb key sb hsb
      have hvw : (mergeKeyed pol pol ma mb).lookup key = some (merge pol v w) := by
        rw [mergeKeyed_lookup, hv, hw]
      obtain ⟨sm, hsm, -⟩ := hfwm key _ hvw
      simp [hsm]
  · -- The payload, the same on either side.
    intro key sm t hsm ht
    obtain ⟨vw, hvw, hcvw⟩ := hbwm key sm hsm
    refine keyed_payload_bounds pol pol above ?_ hvw hcvw ?_ ?_
    · intro v w tv tw tvw hv hw hcv hcw hcvw' hbv hbw
      exact ih key v w tv tw tvw t hv hw hcv hcw hcvw' (productAt_wellFormed hwup ht) hbv hbw
    · intro v hv
      obtain ⟨sa, hsa, hcv⟩ := hfwa key v hv
      exact ⟨sa, hcv, hpaya key sa t hsa ht⟩
    · intro w hw
      obtain ⟨sb, hsb, hcw⟩ := hfwb key w hw
      exact ⟨sb, hcw, hpayb key sb t hsb ht⟩

/-! ## The variant case

The dual of the record case, and the same proof read with two things swapped: the polarity picks the
other map operation, and which of the two must resolve the other's keys is the mirror image, because
a variant's tags run with the subtyping
edge rather than against it. -/

theorem bounds_variant (pol above : Bool) {ma mb : List (FieldKey × CompactTy)}
    {p q : List Predicate}
    {u ta tb tm : Ty}
    (hnda : nodupKeys (ma.map Prod.fst) = true) (hndb : nodupKeys (mb.map Prod.fst) = true)
    (hwu : u.WellFormed)
    (ih : ∀ (k : FieldKey) (v w : CompactTy) (tv tw tvw t : Ty),
      ma.lookup k = some v → mb.lookup k = some w →
      coalesce pol v = .ok (some tv) → coalesce pol w = .ok (some tw) →
      coalesce pol (merge pol v w) = .ok (some tvw) →
      t.WellFormed → bounds above t tv → bounds above t tw → bounds above t tvw)
    (ha : coalesce pol (.mk [] none (some ma) none (some p)) = .ok (some ta))
    (hb : coalesce pol (.mk [] none (some mb) none (some q)) = .ok (some tb))
    (hm : coalesce pol (merge pol (.mk [] none (some ma) none (some p))
      (.mk [] none (some mb) none (some q))) = .ok (some tm))
    (hba : bounds above u ta) (hbb : bounds above u tb) : bounds above u tm := by
  obtain ⟨Pa, rfl, hnra, hva, hfwa, hbwa, hnpa⟩ := coalesce_variant_view pol hnda ha
  obtain ⟨Pb, rfl, hnrb, hvb, hfwb, hbwb, hnpb⟩ := coalesce_variant_view pol hndb hb
  rw [merge_variant_slot, show (if pol then
        unionMapGo pol ma mb ++ mb.filter (fun kw => (ma.lookup kw.1).isNone)
      else intersectMap pol ma mb) = mergeKeyed (!pol) pol ma mb from by cases pol <;> rfl] at hm
  have hndM : nodupKeys ((mergeKeyed (!pol) pol ma mb).map Prod.fst) = true := by
    cases pol
    · exact nodupKeys_intersectMap hnda
    · exact nodupKeys_unionMap hnda hndb
  obtain ⟨Pm, rfl, hnrm, hvm, hfwm, hbwm, hnpm⟩ := coalesce_variant_view pol hndM hm
  rw [bounds_attach_iff above hnra hwu] at hba
  rw [bounds_attach_iff above hnrb hwu] at hbb
  rw [bounds_attach_iff above hnrm hwu]
  refine ⟨?_, refinementsBound_merge pol above hba.2 hbb.2⟩
  have hwup : u.peel.1.WellFormed := Ty.WellFormed.peel_fst hwu
  have hpu : u.peel.1.peel.2 = [] := by rw [Ty.peel_fst_peel]
  have hpPa : Pa.peel.2 = [] := by rw [Ty.peel_of_not_refined hnra]
  have hpPb : Pb.peel.2 = [] := by rw [Ty.peel_of_not_refined hnrb]
  have hpPm : Pm.peel.2 = [] := by rw [Ty.peel_of_not_refined hnrm]
  obtain ⟨hvU, hpresa, hpaya⟩ := variant_bounds_edge above hba.1 hva hpPa hpu
  obtain ⟨-, hpresb, hpayb⟩ := variant_bounds_edge above hbb.1 hvb hpPb hpu
  refine variant_bounds_of above hvm hvU hnpm (fun tags htags => by
    rw [htags] at hwup
    cases hwup with | variant hnd _ => exact hnd) ?_ ?_
  · cases above
    · simp only [Bool.false_eq_true, if_false] at hpresa hpresb ⊢
      intro key t ht
      obtain ⟨sa, hsa⟩ := Option.isSome_iff_exists.mp (hpresa key t ht)
      obtain ⟨sb, hsb⟩ := Option.isSome_iff_exists.mp (hpresb key t ht)
      obtain ⟨v, hv, -⟩ := hbwa key sa hsa
      obtain ⟨w, hw, -⟩ := hbwb key sb hsb
      have hvw : (mergeKeyed (!pol) pol ma mb).lookup key = some (merge pol v w) := by
        rw [mergeKeyed_lookup, hv, hw]
      obtain ⟨sm, hsm, -⟩ := hfwm key _ hvw
      simp [hsm]
    · simp only [if_true] at hpresa hpresb ⊢
      intro key sm hsm
      obtain ⟨vw, hvw, -⟩ := hbwm key sm hsm
      rcases mergeKeyed_key hvw with hk | hk
      · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
        obtain ⟨sa, hsa, -⟩ := hfwa key v hv
        exact hpresa key sa hsa
      · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hk
        obtain ⟨sb, hsb, -⟩ := hfwb key w hw
        exact hpresb key sb hsb
  · intro key sm t hsm ht
    obtain ⟨vw, hvw, hcvw⟩ := hbwm key sm hsm
    refine keyed_payload_bounds (!pol) pol above ?_ hvw hcvw ?_ ?_
    · intro v w tv tw tvw hv hw hcv hcw hcvw' hbv hbw
      exact ih key v w tv tw tvw t hv hw hcv hcw hcvw' (variantAt_wellFormed hwup ht) hbv hbw
    · intro v hv
      obtain ⟨sa, hsa, hcv⟩ := hfwa key v hv
      exact ⟨sa, hcv, hpaya key sa t hsa ht⟩
    · intro w hw
      obtain ⟨sb, hsb, hcw⟩ := hfwb key w hw
      exact ⟨sb, hcw, hpayb key sb t hsb ht⟩

/-! ## The atoms case

Both operands materialize to one and the same atom, because the merge unions the atom lists and
materializing demands one after dedup. The shape half is then an
identity, and only the refinement sets move. -/

theorem atomTy_wellFormed (α : Atom) : (atomTy α).WellFormed := by
  cases α <;> constructor

theorem coalesce_atoms_ok (pol : Bool) {as : List Atom} {c : Option (List Predicate)} {ty : Ty}
    (h : coalesce pol (.mk as none none none c) = .ok (some ty)) :
    ∃ t, (as.map atomTy).eraseDups = [t] ∧ ty = attachRefinements t c ∧
      t.isRefined = false ∧ t.WellFormed := by
  rw [coalesce_atoms] at h
  rcases he : (as.map atomTy).eraseDups with _ | ⟨t, rest⟩ <;> rw [he] at h
  · cases h
  rcases rest with _ | ⟨_, _⟩
  · cases h
    refine ⟨t, rfl, rfl, ?_⟩
    obtain ⟨α, -, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp
      (show t ∈ (as.map atomTy).eraseDups by rw [he]; simp))
    exact ⟨(atomTy_leaf α).1, atomTy_wellFormed α⟩
  · cases h

theorem bounds_atoms (pol above : Bool) {as bs : List Atom} {p q : List Predicate}
    {u ta tb tm : Ty} (hane : as ≠ []) (hbne : bs ≠ [])
    (hwu : u.WellFormed)
    (ha : coalesce pol (.mk as none none none (some p)) = .ok (some ta))
    (hb : coalesce pol (.mk bs none none none (some q)) = .ok (some tb))
    (hm : coalesce pol (merge pol (.mk as none none none (some p))
      (.mk bs none none none (some q))) = .ok (some tm))
    (hba : bounds above u ta) (hbb : bounds above u tb) : bounds above u tm := by
  obtain ⟨sa, hea, rfl, hnra, -⟩ := coalesce_atoms_ok pol ha
  obtain ⟨sb, heb, rfl, hnrb, -⟩ := coalesce_atoms_ok pol hb
  rw [merge_atoms_slot] at hm
  obtain ⟨sm, hem, rfl, hnrm, -⟩ := coalesce_atoms_ok pol hm
  -- One atom survives the union, so it is the one each operand contributed.
  have hone : ∀ (xs : List Atom) (s : Ty), xs ≠ [] → (xs.map atomTy).eraseDups = [s] →
      (∀ x ∈ xs, x ∈ as ++ bs) → s = sm := by
    rintro (_ | ⟨α, rest⟩) s hne hs hsub
    · exact absurd rfl hne
    have h1 : atomTy α ∈ [s] := by
      rw [← hs]
      exact List.mem_eraseDups.mpr (by simp)
    have h2 : atomTy α ∈ [sm] := by
      rw [← hem]
      exact List.mem_eraseDups.mpr (List.mem_map_of_mem (hsub α (by simp)))
    simp only [List.mem_singleton] at h1 h2
    rw [← h1, h2]
  have hsa : sa = sm := hone as sa hane hea (fun x hx => List.mem_append_left _ hx)
  have hsb : sb = sm := hone bs sb hbne heb (fun x hx => List.mem_append_right _ hx)
  subst hsa
  subst hsb
  rw [bounds_attach_iff above hnra hwu] at hba
  rw [bounds_attach_iff above hnrb hwu] at hbb
  rw [bounds_attach_iff above hnrm hwu]
  exact ⟨hba.1, refinementsBound_merge pol above hba.2 hbb.2⟩

/-! ## The function case

The domains merge at the flipped polarity and on the flipped side, since a function's domain runs
against the subtyping edge. That is what the second parameter is for: a `data` domain is invariant
and needs the bound carried both ways, which leastness alone does not supply.

A positive merge accumulates the alternatives rather than combining them, so the merged domain is
either an operand's outright or the two folded together; the `data` reading demands they materialize
alike and the `compute` reading folds
them. Either way the merged domain is one the induction hypothesis reaches. -/

theorem fn_bounds_edge (above : Bool) {n0 : Option String} {k : FunKind} {d0 c0 y : Ty}
    (h : bounds above y (.fn n0 k d0 c0)) (hpy : y.peel.2 = []) :
    ∃ n1 du cu, y = .fn n1 k du cu ∧ bounds (!above) du d0 ∧
      (k = .data → bounds above du d0) ∧ bounds above cu c0 := by
  cases above
  · obtain ⟨n1, n0', k', du, cu, d0', c0', rfl, heq, hdom, hinv, hcod⟩ :=
      fn_subtyping_edge (of_bounds_false h) hpy rfl (Or.inr rfl)
    cases heq
    exact ⟨n1, du, cu, rfl, bounds_true hdom, fun hk => bounds_false (hinv hk),
      bounds_false hcod⟩
  · obtain ⟨n0', n1, k', d0', c0', du, cu, heq, rfl, hdom, hinv, hcod⟩ :=
      fn_subtyping_edge (of_bounds_true h) rfl hpy (Or.inl rfl)
    cases heq
    exact ⟨n1, du, cu, rfl, bounds_false hdom, fun hk => bounds_true (hinv hk),
      bounds_true hcod⟩

theorem fn_bounds_of (above : Bool) {n0 n1 : Option String} {k : FunKind} {d0 c0 du cu : Ty}
    (hdom : bounds (!above) du d0) (hinv : k = .data → bounds above du d0)
    (hcod : bounds above cu c0) :
    bounds above (.fn n1 k du cu) (.fn n0 k d0 c0) := by
  cases above
  · exact bounds_false (fn_subtyping_of (of_bounds_true hdom) (fun hk => of_bounds_false (hinv hk))
      (of_bounds_false hcod))
  · exact bounds_true (fn_subtyping_of (of_bounds_false hdom) (fun hk => of_bounds_true (hinv hk))
      (of_bounds_true hcod))

/-- A conflicted slot has no type, so a pair of concrete kinds that disagree never
reaches the comparison. -/
theorem coalesce_fun_conflict (pol : Bool) {ds cod : CompactTy}
    {c : Option (List Predicate)} {ty : Ty}
    (h : coalesce pol (.mk [] none none (some (.conflict, ds, cod)) c) = .ok (some ty)) :
    False := by
  rcases hf : funShapes pol (.mk [] none none (some (KindMerge.conflict, ds, cod)) c) with e | x <;>
    rw [coalesce_fun_only, hf] at h
  · cases h
  rw [funShapes] at hf
  rcases hc : coalesce pol cod with e | oc <;>
    simp [hc, Bind.bind, Except.bind] at hf

theorem mergeFun_same (pol : Bool) {kf : KindMerge} (hkf : kf ≠ .conflict)
    (d₁ d₂ cod₁ cod₂ : CompactTy) :
    mergeFun pol (kf, d₁, cod₁) (kf, d₂, cod₂)
      = (kf, merge (!pol) d₁ d₂, merge pol cod₁ cod₂) := by
  rw [mergeFun, joinKind_idem]

/-- The `FunKind` a resolved kind slot materializes at, which
`coalesce_compact_go` writes as a literal at each of its arms. -/
def funKindOf : KindMerge → FunKind
  | .data => .data
  | _ => .compute

theorem bounds_fun (pol above : Bool) {k₁ k₂ : KindMerge} {d₁ d₂ cod₁ cod₂ : CompactTy}
    {p q : List Predicate} {u ta tb tm : Ty}
    (hk₁ : k₁ = .data ∨ k₁ = .compute) (hk₂ : k₂ = .data ∨ k₂ = .compute)
    (hwu : u.WellFormed)
    (ihd : ∀ (above' : Bool) (tx ty' tz t : Ty),
      coalesce (!pol) d₁ = .ok (some tx) → coalesce (!pol) d₂ = .ok (some ty') →
      coalesce (!pol) (merge (!pol) d₁ d₂) = .ok (some tz) →
      t.WellFormed → bounds above' t tx → bounds above' t ty' → bounds above' t tz)
    (ihc : ∀ (tx ty' tz t : Ty),
      coalesce pol cod₁ = .ok (some tx) → coalesce pol cod₂ = .ok (some ty') →
      coalesce pol (merge pol cod₁ cod₂) = .ok (some tz) →
      t.WellFormed → bounds above t tx → bounds above t ty' → bounds above t tz)
    (ha : coalesce pol (.mk [] none none (some (k₁, d₁, cod₁)) (some p)) = .ok (some ta))
    (hb : coalesce pol (.mk [] none none (some (k₂, d₂, cod₂)) (some q)) = .ok (some tb))
    (hm : coalesce pol (merge pol (.mk [] none none (some (k₁, d₁, cod₁)) (some p))
      (.mk [] none none (some (k₂, d₂, cod₂)) (some q))) = .ok (some tm))
    (hba : bounds above u ta) (hbb : bounds above u tb) : bounds above u tm := by
  rw [merge_fn_slot] at hm
  -- Concrete kinds that disagree join to `conflict`, which has no type.
  have hkk : k₁ = k₂ := by
    rcases hk₁ with rfl | rfl <;> rcases hk₂ with rfl | rfl <;> try rfl
    all_goals (exfalso; rw [mergeFun] at hm; exact coalesce_fun_conflict pol hm)
  subst hkk
  have hkf : k₁ ≠ .conflict := by rcases hk₁ with rfl | rfl <;> simp
  rw [mergeFun_same pol hkf] at hm
  -- Both operands, materialized.
  have hop : ∀ (d cod : CompactTy) (c : List Predicate) (t : Ty),
      coalesce pol (.mk [] none none (some (k₁, d, cod)) (some c)) = .ok (some t) →
      ∃ dt ct, coalesce (!pol) d = .ok (some dt) ∧ coalesce pol cod = .ok (some ct) ∧
        t = attachRefinements (.fn none (funKindOf k₁) dt ct) (some c) := by
    intro d cod c t ht
    rcases hk₁ with rfl | rfl
    · exact coalesce_fun_data_ok pol ht
    · exact coalesce_fun_compute_ok pol ht
  obtain ⟨D₁, C₁, hd₁, hc₁, rfl⟩ := hop d₁ cod₁ p ta ha
  obtain ⟨D₂, C₂, hd₂, hc₂, rfl⟩ := hop d₂ cod₂ q tb hb
  -- The merged slot: its codomain is the merged codomain and its domain is the merged
  -- domain, at both polarities and either kind — the domain is one position now, so a
  -- positive merge combines it like any other rather than accumulating alternatives.
  obtain ⟨Dm, Cm, hDm, hCm, rfl⟩ :
      ∃ dt ct, coalesce (!pol) (merge (!pol) d₁ d₂) = .ok (some dt) ∧
        coalesce pol (merge pol cod₁ cod₂) = .ok (some ct) ∧
        tm = attachRefinements (.fn none (funKindOf k₁) dt ct)
          (mergeRefinements pol (some p) (some q)) := by
    rcases hk₁ with rfl | rfl
    · exact coalesce_fun_data_ok pol (by simpa using hm)
    · exact coalesce_fun_compute_ok pol (by simpa using hm)
  -- The refinement half, and the edge's three parts.
  rw [bounds_attach_iff above (by simp [Ty.isRefined]) hwu] at hba hbb
  rw [bounds_attach_iff above (by simp [Ty.isRefined]) hwu]
  refine ⟨?_, refinementsBound_merge pol above hba.2 hbb.2⟩
  have hpu : u.peel.1.peel.2 = [] := by rw [Ty.peel_fst_peel]
  obtain ⟨n1, Du, Cu, hueq, hdoma, hinva, hcoda⟩ := fn_bounds_edge above hba.1 hpu
  obtain ⟨n1', Du', Cu', hueq', hdomb, hinvb, hcodb⟩ := fn_bounds_edge above hbb.1 hpu
  rw [hueq] at hueq'
  cases hueq'
  rw [hueq]
  have hwup : u.peel.1.WellFormed := Ty.WellFormed.peel_fst hwu
  rw [hueq] at hwup
  have hwDu : Du.WellFormed := hwup.fn_domain
  have hwCu : Cu.WellFormed := hwup.fn_codomain
  refine fn_bounds_of above ?_ ?_ (ihc C₁ C₂ Cm Cu hc₁ hc₂ hCm hwCu hcoda hcodb)
  · exact ihd (!above) D₁ D₂ Dm Du hd₁ hd₂ hDm hwDu hdoma hdomb
  · intro hkd
    have hkd' : k₁ = .data := by
      rcases hk₁ with rfl | rfl
      · rfl
      · exact absurd hkd (by simp [funKindOf])
    exact ihd above D₁ D₂ Dm Du hd₁ hd₂ hDm hwDu (hinva hkd) (hinvb hkd)

/-! ## The lemma, assembled

Fuel on the summed size, as `coalesce_monotone`. `coalesce_shape` pins each materializing operand to
one of the atom, record, variant, and function shapes, and this time what refutes a mismatched
pairing is the merge rather than the order: it leaves both slots populated and `combine` refuses two
contributions, so twelve of the
sixteen cases close on `merge_shape_agrees`. -/

/-- A position with content carries a refinement slot; `wellFormed` says so, and every
case reads the slot as a set. -/
theorem wellFormed_refs {as : List Atom} {r v : Option (List (FieldKey × CompactTy))}
    {f : Option (KindMerge × CompactTy × CompactTy)} {c : Option (List Predicate)}
    (hw : wellFormed (.mk as r v f c) = true)
    (hcontent : as ≠ [] ∨ r ≠ none ∨ v ≠ none ∨ f ≠ none) : ∃ ps, c = some ps := by
  rcases c with _ | ps
  · exfalso
    rw [wellFormed.eq_def] at hw
    simp only [Bool.and_eq_true] at hw
    rcases hcontent with h | h | h | h <;> simp_all
  · exact ⟨ps, rfl⟩

theorem bounds_merge : ∀ (n : Nat) (pol above : Bool) (a b : CompactTy) (u : Ty),
    sizeOf a + sizeOf b < n → concrete a = true → concrete b = true → u.WellFormed →
    ∀ (ta tb tm : Ty),
      coalesce pol a = .ok (some ta) → coalesce pol b = .ok (some tb) →
      coalesce pol (merge pol a b) = .ok (some tm) →
      bounds above u ta → bounds above u tb → bounds above u tm := by
  intro n
  induction n with
  | zero =>
    intro _ _ _ _ _ hfuel
    exact absurd hfuel (by omega)
  | succ n ih =>
    intro pol above a b u hfuel hga hgb hwu ta tb tm ha hb hm hba hbb
    obtain ⟨as, ra, va, fa, ca⟩ := a
    obtain ⟨bs, rb, vb, fb, cb⟩ := b
    -- `concrete`, projected onto a shared keyed payload, as the keyed cases want it.
    have hkeyed : ∀ (ma mb : List (FieldKey × CompactTy)),
        wellFormedKeys ma (ma.map Prod.fst) = true → wellFormedKeys mb (mb.map Prod.fst) = true →
        kindResolvedKeys ma (ma.map Prod.fst) = true →
        kindResolvedKeys mb (mb.map Prod.fst) = true →
        sizeOf ma + sizeOf mb < n →
        ∀ (k : FieldKey) (v w : CompactTy) (tv tw tvw t : Ty),
          ma.lookup k = some v → mb.lookup k = some w →
          coalesce pol v = .ok (some tv) → coalesce pol w = .ok (some tw) →
          coalesce pol (merge pol v w) = .ok (some tvw) →
          t.WellFormed → bounds above t tv → bounds above t tw → bounds above t tvw := by
      intro ma mb hwa hwb hka hkb hsz k v w tv tw tvw t hv hw hcv hcw hcvw hwt hbv hbw
      have hsv := lookup_sizeOf hv
      have hsw := lookup_sizeOf hw
      refine ih pol above v w t (by omega) ?_ ?_ hwt tv tw tvw hcv hcw hcvw hbv hbw
      · simp only [concrete, Bool.and_eq_true]
        exact ⟨wfKeys_iff.mp hwa k (mem_keys_of_lookup hv) v hv,
          kindResolvedKeys_iff.mp hka k (mem_keys_of_lookup hv) v hv⟩
      · simp only [concrete, Bool.and_eq_true]
        exact ⟨wfKeys_iff.mp hwb k (mem_keys_of_lookup hw) w hw,
          kindResolvedKeys_iff.mp hkb k (mem_keys_of_lookup hw) w hw⟩
    rcases coalesce_shape pol ha with ⟨hane, rfl, rfl, rfl⟩ | ⟨rfl, ⟨ma, rfl⟩, rfl, rfl⟩
        | ⟨rfl, rfl, ⟨ma, rfl⟩, rfl⟩ | ⟨rfl, rfl, rfl, ⟨ga, rfl⟩⟩ <;>
      rcases coalesce_shape pol hb with ⟨hbne, rfl, rfl, rfl⟩ | ⟨rfl, ⟨mb, rfl⟩, rfl, rfl⟩
        | ⟨rfl, rfl, ⟨mb, rfl⟩, rfl⟩ | ⟨rfl, rfl, rfl, ⟨gb, rfl⟩⟩
    -- atoms / atoms
    · simp only [concrete, Bool.and_eq_true] at hga hgb
      obtain ⟨p, rfl⟩ := wellFormed_refs hga.1 (Or.inl hane)
      obtain ⟨q, rfl⟩ := wellFormed_refs hgb.1 (Or.inl hbne)
      exact bounds_atoms pol above hane hbne hwu ha hb hm hba hbb
    -- atoms / record, variant, function
    · exact absurd (merge_shape_agrees pol hm) (by simp_all)
    · exact absurd (merge_shape_agrees pol hm) (by simp_all)
    · exact absurd (merge_shape_agrees pol hm) (by simp_all)
    -- record / atoms
    · exact absurd (merge_shape_agrees pol hm) (by simp_all)
    -- record / record
    · obtain ⟨hwka, hkka⟩ := concrete_record_keys hga
      obtain ⟨hwkb, hkkb⟩ := concrete_record_keys hgb
      have hsz : sizeOf ma + sizeOf mb < n := by simp at hfuel; omega
      simp only [concrete, Bool.and_eq_true] at hga hgb
      obtain ⟨p, rfl⟩ := wellFormed_refs hga.1 (Or.inr (Or.inl (by simp)))
      obtain ⟨q, rfl⟩ := wellFormed_refs hgb.1 (Or.inr (Or.inl (by simp)))
      rw [wellFormed.eq_def] at hga hgb
      simp only [Bool.and_eq_true] at hga hgb
      exact bounds_record pol above hga.1.1.1.1.2 hgb.1.1.1.1.2 hwu
        (hkeyed ma mb hwka hwkb hkka hkkb hsz) ha hb hm hba hbb
    -- record / variant, function
    · exact absurd (merge_shape_agrees pol hm) (by simp_all)
    · exact absurd (merge_shape_agrees pol hm) (by simp_all)
    -- variant / atoms, record
    · exact absurd (merge_shape_agrees pol hm) (by simp_all)
    · exact absurd (merge_shape_agrees pol hm) (by simp_all)
    -- variant / variant
    · obtain ⟨hwka, hkka⟩ := concrete_variant_keys hga
      obtain ⟨hwkb, hkkb⟩ := concrete_variant_keys hgb
      have hsz : sizeOf ma + sizeOf mb < n := by simp at hfuel; omega
      simp only [concrete, Bool.and_eq_true] at hga hgb
      obtain ⟨p, rfl⟩ := wellFormed_refs hga.1 (Or.inr (Or.inr (Or.inl (by simp))))
      obtain ⟨q, rfl⟩ := wellFormed_refs hgb.1 (Or.inr (Or.inr (Or.inl (by simp))))
      rw [wellFormed.eq_def] at hga hgb
      simp only [Bool.and_eq_true] at hga hgb
      exact bounds_variant pol above hga.1.1.1.2.2 hgb.1.1.1.2.2 hwu
        (hkeyed ma mb hwka hwkb hkka hkkb hsz) ha hb hm hba hbb
    -- variant / function
    · exact absurd (merge_shape_agrees pol hm) (by simp_all)
    -- function / atoms, record, variant
    · exact absurd (merge_shape_agrees pol hm) (by simp_all)
    · exact absurd (merge_shape_agrees pol hm) (by simp_all)
    · exact absurd (merge_shape_agrees pol hm) (by simp_all)
    -- function / function
    · obtain ⟨k₁, d₁, cod₁⟩ := ga
      obtain ⟨k₂, d₂, cod₂⟩ := gb
      obtain ⟨hgd₁, hgc₁, hk₁⟩ := concrete_fun hga
      obtain ⟨hgd₂, hgc₂, hk₂⟩ := concrete_fun hgb
      simp only [concrete, Bool.and_eq_true] at hga hgb
      obtain ⟨p, rfl⟩ := wellFormed_refs hga.1 (Or.inr (Or.inr (Or.inr (by simp))))
      obtain ⟨q, rfl⟩ := wellFormed_refs hgb.1 (Or.inr (Or.inr (Or.inr (by simp))))
      refine bounds_fun pol above hk₁ hk₂ hwu (fun above' tx ty' tz t h1 h2 h3 hwt hb1 hb2 =>
        ih (!pol) above' d₁ d₂ t (by simp at hfuel; omega) hgd₁ hgd₂ hwt tx ty' tz
          h1 h2 h3 hb1 hb2)
        (fun tx ty' tz t h1 h2 h3 hwt hb1 hb2 =>
          ih pol above cod₁ cod₂ t (by simp at hfuel; omega) hgc₁ hgc₂ hwt tx ty' tz
            h1 h2 h3 hb1 hb2)
        ha hb hm hba hbb

/-! ## Materialization produces well-formed types

`Ty.WellFormed` is the invariant the Rust builders maintain and the representation does not enforce:
uniquely-keyed records and variants, non-empty refinement sets, no refinement under a refinement.
`coalesce` maintains it out of `wellFormed`, which is the same invariant one level down — so a type
the solver reports is a type the
relation's theorems apply to. -/

theorem attachRefinements_wellFormed {base : Ty} (hnr : base.isRefined = false)
    (hw : base.WellFormed)
    (c : Option (List Predicate)) : (attachRefinements base c).WellFormed := by
  rcases c with _ | ps
  · exact hw
  rcases ps with _ | ⟨p, ps⟩
  · exact hw
  · rw [show attachRefinements base (some (p :: ps)) = .refined base (p :: ps) from by
      cases base <;> simp_all [attachRefinements, Ty.isRefined]]
    exact .refined (by simp) hnr hw

/-- A product is well-formed when its fields are and its names are unique — read
through the view, so the tuple and record shapes are one case. -/
theorem product_wellFormed {base : Ty} (hk : (productKind base).isSome = true)
    (hnd : ∀ gs : List (String × Ty), base = .record gs → (gs.map (·.1)).Nodup)
    (hpay : ∀ k t, productAt base k = some t → t.WellFormed) : base.WellFormed := by
  rcases hkb : productKind base with _ | pk
  · rw [hkb] at hk
    cases hk
  cases pk
  · obtain ⟨ts, rfl⟩ := productKind_positional hkb
    exact .tuple fun t ht => by
      obtain ⟨i, hi⟩ := List.getElem?_of_mem ht
      exact hpay (.idx i) t hi
  · obtain ⟨fs, rfl⟩ := productKind_named hkb
    refine .record (hnd fs rfl) fun f hf => ?_
    obtain ⟨nm, t⟩ := f
    exact hpay (.name nm) t (by
      rw [productAt, ← lookupBy_eq_lookup]
      exact lookupBy_of_mem_nodup (hnd fs rfl) hf)

/-- A variant is well-formed when its payloads are and its tags are unique. -/
theorem variant_wellFormed {base : Ty} (hv : isVariant base = true)
    (hnd : ∀ tags : List (FieldKey × Ty), base = .variant tags → (tags.map (·.1)).Nodup)
    (hpay : ∀ k t, variantAt base k = some t → t.WellFormed) : base.WellFormed := by
  obtain ⟨tags, rfl⟩ := isVariant_ex hv
  refine .variant (hnd tags rfl) fun e he => ?_
  obtain ⟨k, t⟩ := e
  exact hpay k t (by
    rw [variantAt, ← lookupBy_eq_lookup]
    exact lookupBy_of_mem_nodup (hnd tags rfl) he)

/-- An unpinned kind slot materializes by the `compute` reading, which is the
same branch of `funShapes` — the default is in the match, not in a second rule. -/
theorem funShapes_unknown_eq_compute (pol : Bool) (ds cod : CompactTy)
    (c : Option (List Predicate)) :
    funShapes pol (.mk [] none none (some (.unknown, ds, cod)) c)
      = funShapes pol (.mk [] none none (some (.compute, ds, cod)) c) := by
  rw [funShapes, funShapes]
  simp

theorem coalesce_fun_unknown_ok (pol : Bool) {d cod : CompactTy} {c : Option (List Predicate)}
    {ty : Ty}
    (h : coalesce pol (.mk [] none none (some (.unknown, d, cod)) c) = .ok (some ty)) :
    ∃ dt ct, coalesce (!pol) d = .ok (some dt) ∧ coalesce pol cod = .ok (some ct) ∧
      ty = attachRefinements (.fn none .compute dt ct) c := by
  refine coalesce_fun_compute_ok pol ?_
  rw [coalesce_fun_only] at h ⊢
  rw [← funShapes_unknown_eq_compute]
  exact h

/-- **Materialization is well-formed.** Fuel on `depth`, the measure `coalesce`'s
own recursion uses. -/
theorem coalesce_wellFormed : ∀ (n : Nat) (pol : Bool) (t : CompactTy) (ty : Ty),
    depth t < n → wellFormed t = true → coalesce pol t = .ok (some ty) → ty.WellFormed := by
  intro n
  induction n with
  | zero =>
    intro _ _ _ hd
    exact absurd hd (by omega)
  | succ n ih =>
    intro pol t ty hd hw hc
    obtain ⟨as, r, v, f, c⟩ := t
    rcases coalesce_shape pol hc with ⟨-, rfl, rfl, rfl⟩ | ⟨rfl, ⟨m, rfl⟩, rfl, rfl⟩
      | ⟨rfl, rfl, ⟨m, rfl⟩, rfl⟩ | ⟨rfl, rfl, rfl, ⟨g, rfl⟩⟩
    · obtain ⟨s, -, rfl, hnrs, hws⟩ := coalesce_atoms_ok pol hc
      exact attachRefinements_wellFormed hnrs hws c
    · rw [wellFormed.eq_def] at hw
      simp only [Bool.and_eq_true] at hw
      obtain ⟨hwk, hndk⟩ := hw.1.1.1
      obtain ⟨base, rfl, hnr, hne, hkind, -, hbw, hnp⟩ := coalesce_record_view pol hndk hc
      refine attachRefinements_wellFormed hnr (product_wellFormed ?_ hnp fun k t hpa => ?_) c
      · obtain ⟨k0, hk0⟩ := exists_mem_keys hne
        rw [hkind k0 hk0]
        rfl
      · obtain ⟨w, hwlk, hcw⟩ := hbw k t hpa
        have hdw : depth w < depth (CompactTy.mk [] (some m) none none c) :=
          depth_recordPayload_lt (mem_of_lookup hwlk)
        exact ih pol w t (by omega) (wfKeys_iff.mp hwk k (mem_keys_of_lookup hwlk) w hwlk) hcw
    · rw [wellFormed.eq_def] at hw
      simp only [Bool.and_eq_true] at hw
      obtain ⟨hwk, hndk⟩ := hw.1.1.2
      obtain ⟨base, rfl, hnr, hvb, -, hbw, hnp⟩ := coalesce_variant_view pol hndk hc
      refine attachRefinements_wellFormed hnr (variant_wellFormed hvb hnp fun k t hpa => ?_) c
      obtain ⟨w, hwlk, hcw⟩ := hbw k t hpa
      have hdw : depth w < depth (CompactTy.mk [] none (some m) none c) :=
        depth_variantPayload_lt (mem_of_lookup hwlk)
      exact ih pol w t (by omega) (wfKeys_iff.mp hwk k (mem_keys_of_lookup hwlk) w hwlk) hcw
    · obtain ⟨k, d, cod⟩ := g
      rw [wellFormed.eq_def] at hw
      simp only [Bool.and_eq_true] at hw
      obtain ⟨⟨hknc, hwd⟩, hwcod⟩ := hw.1.2
      have hdd : depth d < depth (CompactTy.mk [] none none (some (k, d, cod)) c) :=
        depth_dom_lt
      have hdc : depth cod < depth (CompactTy.mk [] none none (some (k, d, cod)) c) :=
        depth_cod_lt
      have hbuild : ∀ (kf : FunKind) (dt ct : Ty), coalesce (!pol) d = .ok (some dt) →
          coalesce pol cod = .ok (some ct) → (Ty.fn none kf dt ct).WellFormed :=
        fun kf dt ct hdt hct =>
          .fn (ih (!pol) d dt (by omega) hwd hdt) (ih pol cod ct (by omega) hwcod hct)
      cases k
      · obtain ⟨dt, ct, hdt, hct, rfl⟩ := coalesce_fun_data_ok pol hc
        exact attachRefinements_wellFormed (by simp [Ty.isRefined]) (hbuild _ dt ct hdt hct) c
      · obtain ⟨dt, ct, hdt, hct, rfl⟩ := coalesce_fun_compute_ok pol hc
        exact attachRefinements_wellFormed (by simp [Ty.isRefined]) (hbuild _ dt ct hdt hct) c
      · simp at hknc
      · obtain ⟨dt, ct, hdt, hct, rfl⟩ := coalesce_fun_unknown_ok pol hc
        exact attachRefinements_wellFormed (by simp [Ty.isRefined]) (hbuild _ dt ct hdt hct) c

/-! ## The two instances

`bounds_merge` quantifies the bound's side independently of the polarity, and the two settings of
that parameter are two different statements. The diagonal is leastness. The off-diagonal says a type
both operands bound is bounded by the merge, which the function case consumes; it is not leastness,
since at a positive
merge leastness is about upper bounds and that is about lower ones. -/

/-- **Leastness, over types.** A type above both operands is above the merge at a
positive position, and one below both is below it at a negative one — over every well-formed type,
with no position standing in for it.

`Ty.WellFormed` is the same invariant transitivity and reflexivity assume: uniquely-keyed records
and variants, without which the find-first rules and the equality
short-circuit disagree. -/
theorem merge_is_least_type (pol : Bool) {a b : CompactTy} {u ta tb tm : Ty}
    (hga : concrete a = true) (hgb : concrete b = true) (hwu : u.WellFormed)
    (ha : coalesce pol a = .ok (some ta)) (hb : coalesce pol b = .ok (some tb))
    (hm : coalesce pol (merge pol a b) = .ok (some tm))
    (h1 : bounds pol u ta) (h2 : bounds pol u tb) : bounds pol u tm :=
  bounds_merge (sizeOf a + sizeOf b + 1) pol pol a b u (by omega) hga hgb hwu
    ta tb tm ha hb hm h1 h2

/-- Leastness spelled with `Subtyping` at each polarity, which is `MergeIsLeastAt`'s
statement over one candidate. -/
theorem merge_is_least_type_pos {a b : CompactTy} {u ta tb tm : Ty}
    (hga : concrete a = true) (hgb : concrete b = true) (hwu : u.WellFormed)
    (ha : coalesce true a = .ok (some ta)) (hb : coalesce true b = .ok (some tb))
    (hm : coalesce true (merge true a b) = .ok (some tm))
    (h1 : Subtyping ta u) (h2 : Subtyping tb u) : Subtyping tm u :=
  of_bounds_true (merge_is_least_type true hga hgb hwu ha hb hm (bounds_true h1) (bounds_true h2))

theorem merge_is_least_type_neg {a b : CompactTy} {u ta tb tm : Ty}
    (hga : concrete a = true) (hgb : concrete b = true) (hwu : u.WellFormed)
    (ha : coalesce false a = .ok (some ta)) (hb : coalesce false b = .ok (some tb))
    (hm : coalesce false (merge false a b) = .ok (some tm))
    (h1 : Subtyping u ta) (h2 : Subtyping u tb) : Subtyping u tm :=
  of_bounds_false
    (merge_is_least_type false hga hgb hwu ha hb hm (bounds_false h1) (bounds_false h2))

/-! ## The sample, as a theorem

`MaterializedMergeIsABound.lean`'s sample states leastness as `MergeIsLeastAt` over a pool of candidate bounds.
Every candidate is a `wellFormed` position's materialization, so `coalesce_wellFormed` makes it a
well-formed type and `merge_is_least_type` applies to it: the sample's
leastness line is a corollary rather than a measurement. -/

theorem pool_wellFormed : ∀ u ∈ pool, u.WellFormed := by
  intro u hu
  obtain ⟨pol, t, hwt, hct⟩ := mem_pool hu
  exact coalesce_wellFormed (depth t + 1) pol t u (by omega) hwt hct

theorem merge_is_least_at_of_concrete (pol : Bool) {a b : CompactTy}
    (hga : concrete a = true) (hgb : concrete b = true) : MergeIsLeastAt pol a b = true := by
  rw [MergeIsLeastAt]
  rcases ha : coalesce pol a with ea | oa
  · rfl
  rcases oa with _ | ta
  · rfl
  rcases hb : coalesce pol b with eb | ob
  · rfl
  rcases ob with _ | tb
  · rfl
  rcases hm : coalesce pol (merge pol a b) with em | om
  · rfl
  rcases om with _ | tm
  · rfl
  refine List.all_eq_true.mpr fun u hu => ?_
  have hwu := pool_wellFormed u hu
  cases pol
  · by_cases hcond : (subtypeCheck u ta && subtypeCheck u tb) = true
    · obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hcond
      have hsub := subtypeCheck_of_subtyping (merge_is_least_type_neg hga hgb hwu ha hb hm
        (subtyping_of_subtypeCheck _ _ h1) (subtyping_of_subtypeCheck _ _ h2))
      simp [hsub]
    · simp [hcond]
  · by_cases hcond : (subtypeCheck ta u && subtypeCheck tb u) = true
    · obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hcond
      have hsub := subtypeCheck_of_subtyping (merge_is_least_type_pos hga hgb hwu ha hb hm
        (subtyping_of_subtypeCheck _ _ h1) (subtyping_of_subtypeCheck _ _ h2))
      simp [hsub]
    · simp [hcond]

/-- The sample's leastness line, proved rather than evaluated: no gated pair of
the sample has a candidate bound the merge fails to sit under. -/
theorem leastness_failures_eq_nil :
    ((cases concrete).filter fun c => !MergeIsLeastAt c.1 c.2.1 c.2.2) = [] := by
  refine List.filter_eq_nil_iff.mpr fun c hc => ?_
  obtain ⟨pol, a, b⟩ := c
  obtain ⟨hga, hgb⟩ := mem_cases hc
  simp [merge_is_least_at_of_concrete pol hga hgb]

end CompactTy
end CclFormal
