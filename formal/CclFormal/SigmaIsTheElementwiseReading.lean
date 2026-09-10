import CclFormal.TypeKind

/-!
# The kind premise is the elementwise reading, and that is what fixes its direction

A Σ over a candidate list denotes the collections whose domain is one of those candidates:
`Σ (σ : [𝐷₀, 𝐷₁]). σ ⤇ 𝑉` is `𝐷₀ ⤇ 𝑉` or `𝐷₁ ⤇ 𝑉`, not knowing which. So one Σ lies below
another exactly when **each** of the lower one's candidates, taken as a domain, gives a data
function below the upper Σ at some candidate of its own — and because a data domain is
invariant, "some candidate of its own" is that same domain, hence membership.

[`sigma_below_iff_elementwise`] proves that equivalence. It is what fixes the premise's
direction: containment is asked `ContainedIn K₀ K₁` — **unswapped**, unlike the domain
premise beside it — because the candidates of the *lower* Σ are the ones that must be
accounted for. [`swapped_premise_is_unsound`] exhibits a pair the swapped premise admits and
the elementwise reading rejects, so the two readings are not interchangeable.

Transitivity does **not** decide this: the reverse of a transitive relation is transitive, so
both directions compose. Only the reading of what a Σ denotes tells them apart.
-/

namespace CclFormal

/-- One candidate of a Σ, as the data function it stands for: the collection over that
domain. The Pi binder is `none` — a Σ's witness is not a Pi binder, and nothing here reads
one. -/
def collectionOver (d v : Ty) : Ty := .fn none .data d v

/-- The Σ rule's two premises, over a candidate list: the kind premise (unswapped) and the
element premise. Stated for `candidates` because that is the kind whose members are named,
and the elementwise reading quantifies over members. -/
def SigmaBelow (ds : List Ty) (v0 : Ty) (k1 : TypeKind) (v1 : Ty) : Prop :=
  ContainedIn (.candidates ds) k1 ∧ Subtyping v0 v1

/-- **The premise is the elementwise reading.** Each candidate of the lower Σ is admitted by
the upper kind and its collection lies below the upper Σ's collection at that same domain.

The right-to-left direction needs a candidate to exist, since a Σ over no candidates
constrains nothing elementwise while still owing the element premise — an empty candidate
list is a kind nothing inhabits, which is why the Rust builds no sum for one
(`Type::sum_over`). -/
theorem sigma_below_iff_elementwise {ds : List Ty} {v0 v1 : Ty} {k1 : TypeKind}
    (hds : ∀ d ∈ ds, Ty.WellFormed d) :
    SigmaBelow ds v0 k1 v1 ↔
      ((∀ d ∈ ds, Admits k1 d) ∧ ∀ d ∈ ds, Subtyping (collectionOver d v0) (collectionOver d v1))
      ∧ Subtyping v0 v1 := by
  constructor
  · intro ⟨hc, hv⟩
    cases hc with
    | everyType =>
        exact ⟨⟨fun _ _ => .everyType, fun d hd =>
          .fnData (Subtyping.refl d (hds d hd)) (Subtyping.refl d (hds d hd)) hv⟩, hv⟩
    | candidates hall =>
        exact ⟨⟨hall, fun d hd =>
          .fnData (Subtyping.refl d (hds d hd)) (Subtyping.refl d (hds d hd)) hv⟩, hv⟩
  · intro ⟨⟨hadm, _⟩, hv⟩
    exact ⟨.candidates hadm, hv⟩

/-- **The swapped premise is not the same relation.** A Σ over one candidate sits below a Σ
over both, and not the other way round: the wider Σ has a candidate the narrower one cannot
account for. Asking containment of the *upper* kind in the lower would admit that pair, so
the direction is not a convention.

Concretely: `Σ (σ : [[0,1]]). σ ⤇ Int` is below `Σ (σ : [[0,1], [0,2]]). σ ⤇ Int`; the
converse fails because `[0,2]` is no member of `[[0,1]]`. -/
theorem swapped_premise_is_unsound :
    ContainedIn (.candidates [.uintRange 1]) (.candidates [.uintRange 1, .uintRange 2])
    ∧ ¬ ContainedIn (.candidates [.uintRange 1, .uintRange 2]) (.candidates [.uintRange 1]) := by
  refine ⟨.candidates fun d hd => ?_, ?_⟩
  · simp only [List.mem_singleton] at hd
    exact .candidates (by simp [hd])
  · intro h
    cases h with
    | candidates hall =>
        have h2 := hall (.uintRange 2) (by simp)
        cases h2 with
        | candidates hmem => simp at hmem

/-- Σ edges compose, which is [`ContainedIn.trans`] on the kind premise and subtyping's own
transitivity on the element premise. Recorded because a chain of consumers is the shape every
conditional collection reaches: an arm below a join below a consumer. -/
theorem SigmaBelow.trans {ds : List Ty} {v0 v1 v2 : Ty} {k1 k2 : TypeKind}
    (hds : ∀ d ∈ ds, Ty.WellFormed d) (hk1 : k1.WellFormed) (hk2 : k2.WellFormed)
    (hv0 : Ty.WellFormed v0) (hv1 : Ty.WellFormed v1) (hv2 : Ty.WellFormed v2)
    (h1 : SigmaBelow ds v0 k1 v1) (h2 : ContainedIn k1 k2 ∧ Subtyping v1 v2) :
    SigmaBelow ds v0 k2 v2 :=
  ⟨ContainedIn.trans (.candidates hds) hk1 hk2 h1.1 h2.1,
   subtyping_trans hv0 hv1 hv2 h1.2 h2.2⟩

end CclFormal
