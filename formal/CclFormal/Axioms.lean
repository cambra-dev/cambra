import CclFormal.MaterializedMergeIsTheLeastBound
import CclFormal.WellTypedTermsAreSafe
import CclFormal.SigmaIsTheElementwiseReading
import CclFormal.TypeKindIsALattice
import CclFormal.TypeKindMerge

/-!
# The axiom gate

Every headline result depends on `propext` and `Quot.sound`, most of them on `Classical.choice` as
well, and on nothing else. Those three are Lean's own classical axioms, shipped with the standard
library; a fourth name in any list below would mean this development had assumed something of its
own. The three merge-algebra results need only two of the three: over a one-domain function slot
their proofs are `rw` plus a triple of componentwise facts, with no case analysis that reaches for
choice.

`#print axioms` reports the list and `#guard_msgs` compares it to the docstring, so `lake build`
fails on a mismatch. Without the pairing the report is a build message nobody reads, and an axiom
added anywhere under `CclFormal/` reaches every theorem that uses it silently.

A `sorry` is caught the same way: it is an axiom (`sorryAx`), so it appears in these lists rather
than only in the build log.
-/

/-- info: 'CclFormal.subtyping_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.subtyping_trans

/-- info: 'CclFormal.CompactTy.merge_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.CompactTy.merge_assoc

/-- info: 'CclFormal.CompactTy.merge_is_least_absorber' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.CompactTy.merge_is_least_absorber

/-- info: 'CclFormal.CompactTy.least_absorber_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.CompactTy.least_absorber_unique

/-- info: 'CclFormal.CompactTy.coalesce_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.CompactTy.coalesce_wellFormed

/-- info: 'CclFormal.CompactTy.merge_is_a_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.CompactTy.merge_is_a_bound

/-- info: 'CclFormal.CompactTy.merge_is_least_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.CompactTy.merge_is_least_type

/-- info: 'CclFormal.CompactTy.leastness_failures_eq_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.CompactTy.leastness_failures_eq_nil

/-- info: 'CclFormal.Admits.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.Admits.mono

/-- info: 'CclFormal.not_admits_of_refuses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.not_admits_of_refuses

/-- info: 'CclFormal.a_bound_admits_what_equality_refuses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.a_bound_admits_what_equality_refuses

/-- info: 'CclFormal.ContainedIn.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.ContainedIn.trans

/-! The lattice rows need neither choice: each is two derivations exhibited and one
inversion, with no case analysis over a quantifier. The two `subtypesOf` rows carry the
type-order bound as a hypothesis rather than computing it. -/

/-- info: 'CclFormal.lub_candidates_subtypesOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.lub_candidates_subtypesOf

/-- info: 'CclFormal.glb_candidates_subtypesOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.glb_candidates_subtypesOf

/-- info: 'CclFormal.lub_candidates_uintRanges_of_not_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.lub_candidates_uintRanges_of_not_all

/-- info: 'CclFormal.sigma_below_iff_elementwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.sigma_below_iff_elementwise

/-! The one result below needs neither choice: it is two derivations exhibited and one
refuted, with no case analysis over a quantifier. -/

/-- info: 'CclFormal.swapped_premise_is_unsound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.swapped_premise_is_unsound

/-! The two kind-merge laws need neither choice, for the reason the merge-algebra results
above do not: the candidate case is two membership lemmas and a propositional commuting, with
no case analysis that reaches for it. -/

/-- info: 'CclFormal.CompactTypeKind.mergeTypeKind_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.CompactTypeKind.mergeTypeKind_comm

/-- info: 'CclFormal.CompactTypeKind.mergeTypeKind_idem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.CompactTypeKind.mergeTypeKind_idem

/-- info: 'CclFormal.CompactTypeKind.mergeTypeKind_join_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.CompactTypeKind.mergeTypeKind_join_assoc

/-- info: 'CclFormal.kind_glb_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.kind_glb_assoc

/-- info: 'CclFormal.kind_lub_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.kind_lub_assoc

/-- info: 'CclFormal.CompactTypeKind.joinAll_unionCandidates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.CompactTypeKind.joinAll_unionCandidates

/-- info: 'CclFormal.CompactTypeKind.denotesAUIntRange_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.CompactTypeKind.denotesAUIntRange_congr

/-- info: 'CclFormal.CompactTypeKind.all_union_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.CompactTypeKind.all_union_range

/-- info: 'CclFormal.CompactTypeKind.mem_atoms_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.CompactTypeKind.mem_atoms_congr

/-- info: 'CclFormal.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.progress

/-- info: 'CclFormal.preservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.preservation

/-- info: 'CclFormal.refinement_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.refinement_soundness
