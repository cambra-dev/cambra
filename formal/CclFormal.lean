-- The concrete subtype relation: its grammar, the relation, and its metatheory.
import CclFormal.Ty
import CclFormal.Subtyping
import CclFormal.SubtypingIsReflexive
import CclFormal.SubtypeChecker
import CclFormal.SubtypeCheckDecidesSubtyping
import CclFormal.SubtypingIsTransitive
-- Terms and typing, an independent limb over the same grammar.
import CclFormal.Term
import CclFormal.WellTypedTermsAreSafe
-- What a Σ's witness ranges over, and the order the kind premise draws on it.
import CclFormal.TypeKind
import CclFormal.TypeKindIsALattice
import CclFormal.SigmaIsTheElementwiseReading
import CclFormal.TypeKindMerge
-- The compact form: the solver's polar merge, its materialization, and how the
-- merge's order carries back to the relation above.
import CclFormal.Merge
import CclFormal.Coalesce
import CclFormal.MaterializedMergeIsABound
import CclFormal.MaterializedMergeIsTheLeastBound
-- The wire codec the differential oracle speaks.
import CclFormal.Json
-- Every headline result's axiom list, gated against its docstring.
import CclFormal.Axioms
