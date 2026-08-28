import CclFormal.MaterializedMergeIsTheLeastBound
import CclFormal.WellTypedTermsAreSafe

/-!
# The axiom gate

Every headline result depends on `propext`, `Classical.choice`, and `Quot.sound` and on nothing
else. Those three are Lean's own classical axioms, shipped with the standard library; a fourth name
in any list below would mean this development had assumed something of its own.

`#print axioms` reports the list and `#guard_msgs` compares it to the docstring, so `lake build`
fails on a mismatch. Without the pairing the report is a build message nobody reads, and an axiom
added anywhere under `CclFormal/` reaches every theorem that uses it silently.

A `sorry` is caught the same way: it is an axiom (`sorryAx`), so it appears in these lists rather
than only in the build log.
-/

/-- info: 'CclFormal.subtyping_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.subtyping_trans

/-- info: 'CclFormal.CompactTy.merge_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.CompactTy.merge_assoc

/-- info: 'CclFormal.CompactTy.merge_is_least_absorber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.CompactTy.merge_is_least_absorber

/-- info: 'CclFormal.CompactTy.least_absorber_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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

/-- info: 'CclFormal.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.progress

/-- info: 'CclFormal.preservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.preservation

/-- info: 'CclFormal.refinement_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CclFormal.refinement_soundness
