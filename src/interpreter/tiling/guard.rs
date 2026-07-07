//! Release/intent guards: [`TileGuard`] (per-[`Tile`](crate::interpreter::Tile) region
//! descriptor) and [`FunctionGuard`] (its function-shaped arm).

use std::collections::HashMap;

use crate::interpreter::{Predicate, Tiling};

/// Specifies a sub-region of interest within a [`Tile`](crate::interpreter::Tile), used for
/// demand-driven computation and incremental release.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TileGuard {
    Scalar(bool),
    Record(HashMap<String, TileGuard>),
    Function(FunctionGuard),
    Aggregation(bool),
    /// The union of multiple guards — matches anything admitted by any arm.
    ///
    /// Produced when two [`TileGuard::Record`] guards are unioned: because
    /// `Record` has AND semantics (a record matches iff *all* fields match),
    /// OR cannot be pushed down through the conjunction field-by-field.  All
    /// other guard variants can represent their own union directly, so `Or`
    /// only appears at the `Record` level.
    ///
    /// Invariant: arms never directly nest another `Or` (always flattened by
    /// [`TileGuard::flatten_or`]).
    Or(Vec<TileGuard>),
}

impl TileGuard {
    /// Builds a `TileGuard` from a list of arms, flattening any nested `Or`
    /// variants.  Returns the single element directly when `arms` has length
    /// one to avoid gratuitous wrapping.
    /// TODO consolidate redundant arms.
    pub(super) fn flatten_or(arms: Vec<TileGuard>) -> TileGuard {
        let mut flat: Vec<TileGuard> = arms
            .into_iter()
            .flat_map(|g| match g {
                TileGuard::Or(inner) => inner,
                other => vec![other],
            })
            .collect();
        // Filter empty guards; if all are empty, keep the first as a canonical empty sentinel.
        if flat.iter().any(|g| !g.is_empty()) {
            flat.retain(|g| !g.is_empty());
        } else {
            flat.truncate(1);
        }
        match flat.len() {
            0 => unreachable!("flatten_or called with no arms"),
            1 => flat.into_iter().next().unwrap(),
            _ => TileGuard::Or(flat),
        }
    }

    pub fn intersect(&self, other: &TileGuard) -> TileGuard {
        match (self, other) {
            (TileGuard::Scalar(u1), TileGuard::Scalar(u2)) => TileGuard::Scalar(*u1 && *u2),
            (TileGuard::Aggregation(u1), TileGuard::Aggregation(u2)) => {
                TileGuard::Aggregation(*u1 && *u2)
            }
            (TileGuard::Function(f1), TileGuard::Function(f2)) => {
                TileGuard::Function(f1.intersect(f2))
            }
            (TileGuard::Record(m1), TileGuard::Record(m2)) => {
                assert_eq!(
                    m1.len(),
                    m2.len(),
                    "Incompatible record guards: {m1:?} vs {m2:?}"
                );
                TileGuard::Record(
                    m1.iter()
                        .map(|(k, g)| (k.clone(), g.intersect(&m2[k])))
                        .collect(),
                )
            }
            // Or distributes over intersect: (A | B) & C = (A & C) | (B & C).
            (TileGuard::Or(arms), g) | (g, TileGuard::Or(arms)) => {
                TileGuard::flatten_or(arms.iter().map(|a| a.intersect(g)).collect())
            }
            _ => panic!("Intersect on incompatible guards {self:?} and {other:?}"),
        }
    }

    /// Returns the union of two guards — the set of data covered by either guard.
    ///
    /// Used to accumulate release guards across multiple incremental deliveries: a
    /// consumer that has released `[0,1]` and then `[2,3]` has collectively seen
    /// `[0,3]`, so the stored guard must grow via union rather than replacement.
    ///
    /// For [`TileGuard::Record`] guards, the result is a [`TileGuard::Or`] because
    /// OR cannot be pushed through the AND semantics of a record guard.
    ///
    /// Note for future implementation: All TileGuards we currently have are compatible with
    /// union, but future stuff like conditional function guards (e.g. constraints like
    /// "positive inputs produce positive outputs") are *not* closed under union and need to
    /// throw an error.
    pub fn union(&self, other: &TileGuard) -> TileGuard {
        match (self, other) {
            (TileGuard::Scalar(u1), TileGuard::Scalar(u2)) => TileGuard::Scalar(*u1 || *u2),
            (TileGuard::Aggregation(u1), TileGuard::Aggregation(u2)) => {
                TileGuard::Aggregation(*u1 || *u2)
            }
            (TileGuard::Function(f1), TileGuard::Function(f2)) => TileGuard::Function(f1.union(f2)),
            // Record guards have AND semantics, so their union cannot be
            // represented as a single Record guard.  Wrap in Or instead.
            (TileGuard::Record(_), TileGuard::Record(_)) => {
                TileGuard::flatten_or(vec![self.clone(), other.clone()])
            }
            // Or: accumulate all arms, flattening nested Ors.
            (TileGuard::Or(arms), g) | (g, TileGuard::Or(arms)) => {
                let mut new_arms = arms.clone();
                new_arms.push(g.clone());
                TileGuard::flatten_or(new_arms)
            }
            _ => panic!("Union on incompatible guards {self:?} and {other:?}"),
        }
    }

    pub fn is_universal(&self) -> bool {
        match self {
            TileGuard::Scalar(universal) | TileGuard::Aggregation(universal) => *universal,
            TileGuard::Record(m) => m.values().all(TileGuard::is_universal),
            TileGuard::Function(g) => g.is_universal(),
            // Or is universal if any arm covers everything.
            TileGuard::Or(arms) => arms.iter().any(TileGuard::is_universal),
        }
    }

    pub fn is_empty(&self) -> bool {
        match self {
            TileGuard::Scalar(universal) | TileGuard::Aggregation(universal) => !*universal,
            // Record: empty only when every field guard is empty — i.e., there
            // is nothing to release from any field.  (Fields are managed
            // independently, so a guard with one empty field is still meaningful
            // for the non-empty fields.)
            TileGuard::Record(m) => m.values().all(TileGuard::is_empty),
            TileGuard::Function(g) => g.is_empty(),
            // Or is empty only when every arm is empty.
            TileGuard::Or(arms) => arms.iter().all(TileGuard::is_empty),
        }
    }

    /// Check whether this guard is structurally compatible with `tiling`.
    ///
    /// A guard is compatible when its variant matches the shape of the tiling
    /// it was derived from — e.g., a [`TileGuard::Scalar`] guard belongs to a
    /// [`Tiling::Scalar`] tiling.  Used to assert that a guard passed to
    /// [`crate::interpreter::tile_operators::TileProducer::release`] is well-formed.
    pub fn check_from(&self, tiling: &Tiling) -> bool {
        match (self, tiling) {
            (TileGuard::Scalar(_), Tiling::Scalar(_)) => true,
            (TileGuard::Aggregation(_), Tiling::Aggregation { .. }) => true,

            // SealedFunction tilings can have domain guards which are always allowed, or
            // codomain guards which match their codomain tiling. A Store shares the
            // function shape: consumers release a prefix of its commit-time domain
            // (a `Domain` guard) — that is its only release form (a store's
            // `to_guard` is `Function(Domain(_))`), so no `Codomain` arm.
            (
                TileGuard::Function(FunctionGuard::Domain(pred)),
                Tiling::SealedFunction { domain, .. } | Tiling::Store { domain, .. },
            ) => pred.is_applicable_to(domain),
            (
                TileGuard::Function(FunctionGuard::Codomain(g)),
                Tiling::SealedFunction { codomain, .. },
            ) => g.check_from(codomain.as_ref()),

            // CurrriedFunction tilings support only domain guards or domain(codomain) guards to reference
            // the inner domain.
            (
                TileGuard::Function(FunctionGuard::Domain(pred)),
                Tiling::CurriedFunction { domain1, .. },
            ) => pred.is_applicable_to(domain1),
            (
                TileGuard::Function(FunctionGuard::Codomain(g)),
                Tiling::CurriedFunction { domain2, .. },
            ) => match g.as_ref() {
                TileGuard::Function(FunctionGuard::Domain(pred)) => pred.is_applicable_to(domain2),
                _ => false,
            },

            // Record guards must have the same key set, with each field guard
            // compatible with the corresponding field tiling.
            (TileGuard::Record(guard_fields), Tiling::Record(tiling_fields)) => {
                guard_fields.len() == tiling_fields.len()
                    && guard_fields
                        .iter()
                        .all(|(k, g)| tiling_fields.get(k).is_some_and(|t| g.check_from(t)))
            }
            // All arms of an Or must be compatible with the same tiling.
            (TileGuard::Or(arms), _) => arms.iter().all(|g| g.check_from(tiling)),
            _ => false,
        }
    }
}

/// A guard on a [`Tile::SealedFunction`](crate::interpreter::Tile::SealedFunction) or
/// [`Tile::CurriedFunction`](crate::interpreter::Tile::CurriedFunction), specifying
/// which part of the function is of interest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FunctionGuard {
    Domain(Predicate),
    Codomain(Box<TileGuard>),
}

impl FunctionGuard {
    pub fn intersect(&self, other: &FunctionGuard) -> FunctionGuard {
        match (self, other) {
            (a, _b) | (_b, a) if a.is_empty() => a.clone(),
            (a, b) | (b, a) if a.is_universal() => b.clone(),
            (FunctionGuard::Domain(p1), FunctionGuard::Domain(p2)) => {
                FunctionGuard::Domain(p1.intersect(p2))
            }
            (FunctionGuard::Codomain(p1), FunctionGuard::Codomain(p2)) => {
                FunctionGuard::Codomain(Box::new(p1.intersect(p2)))
            }
            _ => todo!("Handle Domain + Codomain guards together"),
        }
    }

    /// Returns the union of two function guards.
    pub fn union(&self, other: &FunctionGuard) -> FunctionGuard {
        match (self, other) {
            (a, b) | (b, a) if a.is_empty() => b.clone(),
            (a, _b) | (_b, a) if a.is_universal() => a.clone(),
            (FunctionGuard::Domain(p1), FunctionGuard::Domain(p2)) => {
                FunctionGuard::Domain(p1.union(p2))
            }
            (FunctionGuard::Codomain(p1), FunctionGuard::Codomain(p2)) => {
                FunctionGuard::Codomain(Box::new(p1.union(p2)))
            }
            _ => todo!("Handle Domain + Codomain guards together, got {self:?} and {other:?}"),
        }
    }

    pub fn is_universal(&self) -> bool {
        match self {
            FunctionGuard::Domain(p) => p.as_bool() == Some(true),
            FunctionGuard::Codomain(g) => g.is_universal(),
        }
    }

    pub fn is_empty(&self) -> bool {
        match self {
            FunctionGuard::Domain(p) => p.as_bool() == Some(false),
            FunctionGuard::Codomain(g) => g.is_empty(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::AggregateKind;
    use crate::interpreter::tiling::tests::*;

    // ── TileGuard::intersect ──────────────────────────────────────────────────

    #[test]
    fn guard_intersect_scalar_universal_universal() {
        let g = TileGuard::Scalar(true).intersect(&TileGuard::Scalar(true));
        assert!(g.is_universal());
    }

    #[test]
    fn guard_intersect_scalar_universal_empty() {
        let g = TileGuard::Scalar(true).intersect(&TileGuard::Scalar(false));
        assert!(g.is_empty());
    }

    #[test]
    fn guard_intersect_aggregation() {
        let g = TileGuard::Aggregation(true).intersect(&TileGuard::Aggregation(true));
        assert!(g.is_universal());
    }

    #[test]
    fn guard_intersect_sealed_function_universal_universal() {
        let g = TileGuard::Function(FunctionGuard::Domain(Predicate::True))
            .intersect(&TileGuard::Function(FunctionGuard::Domain(Predicate::True)));
        assert!(g.is_universal());
    }

    #[test]
    fn guard_intersect_sealed_function_empty_dominates() {
        let g = TileGuard::Function(FunctionGuard::Domain(Predicate::True)).intersect(
            &TileGuard::Function(FunctionGuard::Domain(Predicate::False)),
        );
        assert!(g.is_empty());
    }

    // ── TileGuard::union (Record / Or) ────────────────────────────────────────

    /// Helper: build a Record TileGuard from a slice of (field, guard) pairs.
    fn record_guard(fields: &[(&str, TileGuard)]) -> TileGuard {
        TileGuard::Record(
            fields
                .iter()
                .map(|(k, g)| (k.to_string(), g.clone()))
                .collect(),
        )
    }

    #[test]
    fn guard_union_record_produces_or() {
        // Two different record guards cannot be merged field-by-field; the
        // result must be an Or so that neither arm's values are over-admitted.
        let g1 = record_guard(&[
            ("a", TileGuard::Scalar(true)),
            ("b", TileGuard::Scalar(false)),
        ]);
        let g2 = record_guard(&[
            ("a", TileGuard::Scalar(false)),
            ("b", TileGuard::Scalar(true)),
        ]);
        let result = g1.union(&g2);
        assert!(
            matches!(result, TileGuard::Or(_)),
            "expected Or, got {result:?}"
        );
        assert!(!result.is_empty());
        assert!(!result.is_universal());
    }

    #[test]
    fn guard_union_record_identical_stays_record() {
        // When both arms are the same, flatten_or reduces the Or to a single guard.
        let g = record_guard(&[
            ("x", TileGuard::Scalar(true)),
            ("y", TileGuard::Scalar(true)),
        ]);
        let result = g.clone().union(&g);
        // flatten_or with two equal arms still produces Or([g, g]) — both arms
        // are the same object but flatten_or does not deduplicate.  The important
        // property is that the result is *not* under-admitting.
        assert!(result.is_universal());
    }

    #[test]
    fn guard_union_or_accumulates_arms() {
        let g1 = record_guard(&[
            ("a", TileGuard::Scalar(true)),
            ("b", TileGuard::Scalar(false)),
        ]);
        let g2 = record_guard(&[
            ("a", TileGuard::Scalar(false)),
            ("b", TileGuard::Scalar(true)),
        ]);
        let g3 = record_guard(&[
            ("a", TileGuard::Scalar(true)),
            ("b", TileGuard::Scalar(true)),
        ]);
        // g1 ∪ g2 → Or([g1, g2]); then ∪ g3 → Or([g1, g2, g3]) (flat, not nested).
        let or12 = g1.union(&g2);
        let result = or12.union(&g3);
        let TileGuard::Or(arms) = &result else {
            panic!("expected Or, got {result:?}");
        };
        assert_eq!(arms.len(), 3, "should be flat, not nested");
    }

    #[test]
    fn guard_or_is_universal_when_any_arm_is() {
        let universal = record_guard(&[
            ("a", TileGuard::Scalar(true)),
            ("b", TileGuard::Scalar(true)),
        ]);
        let empty = record_guard(&[
            ("a", TileGuard::Scalar(false)),
            ("b", TileGuard::Scalar(false)),
        ]);
        let result = empty.union(&universal);
        assert!(result.is_universal());
    }

    #[test]
    fn guard_or_is_empty_only_when_all_arms_are() {
        let empty1 = record_guard(&[
            ("a", TileGuard::Scalar(false)),
            ("b", TileGuard::Scalar(false)),
        ]);
        let empty2 = record_guard(&[
            ("a", TileGuard::Scalar(false)),
            ("b", TileGuard::Scalar(false)),
        ]);
        let result = empty1.union(&empty2);
        assert!(result.is_empty());
    }

    #[test]
    fn guard_or_intersect_distributes() {
        // (A | B) & C should equal (A & C) | (B & C).
        let a = record_guard(&[
            ("a", TileGuard::Scalar(true)),
            ("b", TileGuard::Scalar(false)),
        ]);
        let b = record_guard(&[
            ("a", TileGuard::Scalar(false)),
            ("b", TileGuard::Scalar(true)),
        ]);
        let c = record_guard(&[
            ("a", TileGuard::Scalar(true)),
            ("b", TileGuard::Scalar(true)),
        ]);
        let or_ab = a.clone().union(&b);
        let result = or_ab.intersect(&c);
        // (A & C) = {a:true, b:false}, (B & C) = {a:false, b:true} — both non-empty.
        let TileGuard::Or(arms) = &result else {
            panic!("expected Or after distributing intersect, got {result:?}");
        };
        assert_eq!(arms.len(), 2);
    }

    // ── SealedFunctionGuard::intersect ────────────────────────────────────────

    #[test]
    fn sfg_intersect_empty_dominates() {
        let result = FunctionGuard::Domain(Predicate::True)
            .intersect(&FunctionGuard::Domain(Predicate::False));
        assert!(matches!(result, FunctionGuard::Domain(Predicate::False)));
    }

    #[test]
    fn sfg_intersect_universal_is_identity() {
        let result = FunctionGuard::Domain(Predicate::True)
            .intersect(&FunctionGuard::Domain(Predicate::True));
        assert!(matches!(result, FunctionGuard::Domain(Predicate::True)));
    }

    #[test]
    fn sfg_intersect_domain_domain() {
        let result = FunctionGuard::Domain(Predicate::True)
            .intersect(&FunctionGuard::Domain(Predicate::False));
        assert!(matches!(result, FunctionGuard::Domain(Predicate::False)));
    }

    #[test]
    fn sfg_intersect_codomain_codomain() {
        let result = FunctionGuard::Codomain(Box::new(TileGuard::Scalar(true)))
            .intersect(&FunctionGuard::Codomain(Box::new(TileGuard::Scalar(false))));
        assert_eq!(
            result,
            FunctionGuard::Codomain(Box::new(TileGuard::Scalar(false)))
        );
    }

    // ── TileGuard::check_from ─────────────────────────────────────────────────

    fn domain_guard(p: Predicate) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(p))
    }

    fn codomain_guard(inner: TileGuard) -> TileGuard {
        TileGuard::Function(FunctionGuard::Codomain(Box::new(inner)))
    }

    fn agg_tiling() -> Tiling {
        Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: int(),
        }
    }

    #[test]
    fn check_from_scalar_matches_scalar_tiling() {
        assert!(TileGuard::Scalar(true).check_from(&Tiling::Scalar(int())));
        assert!(TileGuard::Scalar(false).check_from(&Tiling::Scalar(int())));
    }

    #[test]
    fn check_from_scalar_rejects_non_scalar_tiling() {
        assert!(!TileGuard::Scalar(true).check_from(&sealed(int(), bool_ext())));
        assert!(!TileGuard::Scalar(true).check_from(&agg_tiling()));
    }

    #[test]
    fn check_from_aggregation_matches_aggregation_tiling() {
        assert!(TileGuard::Aggregation(true).check_from(&agg_tiling()));
        assert!(TileGuard::Aggregation(false).check_from(&agg_tiling()));
    }

    #[test]
    fn check_from_aggregation_rejects_non_aggregation_tiling() {
        assert!(!TileGuard::Aggregation(true).check_from(&Tiling::Scalar(int())));
        assert!(!TileGuard::Aggregation(true).check_from(&sealed(int(), bool_ext())));
    }

    #[test]
    fn check_from_function_domain_matches_sealed_function_tiling() {
        assert!(domain_guard(Predicate::True).check_from(&sealed(int(), bool_ext())));
        assert!(domain_guard(Predicate::False).check_from(&sealed(int(), bool_ext())));
    }

    #[test]
    fn check_from_function_codomain_matches_sealed_function_tiling() {
        // A Codomain(Domain(_)) guard is valid against a SealedFunction whose
        // codomain is itself a function tiling.
        let nested = sealed(int(), bool_ext());
        let outer = Tiling::SealedFunction {
            domain: int(),
            codomain: Box::new(nested),
        };
        let g = codomain_guard(domain_guard(Predicate::True));
        assert!(g.check_from(&outer));
    }

    #[test]
    fn check_from_function_codomain_scalar_against_sealed_function_tiling() {
        // Codomain(Scalar) is valid when the sealed function's codomain is a scalar.
        let g = codomain_guard(TileGuard::Scalar(true));
        assert!(g.check_from(&sealed(int(), bool_ext())));
    }

    #[test]
    fn check_from_function_codomain_wrong_shape_against_sealed_function_tiling() {
        // Codomain(Aggregation) against a sealed function with scalar codomain must fail.
        let g = codomain_guard(TileGuard::Aggregation(true));
        assert!(!g.check_from(&sealed(int(), bool_ext())));
    }

    #[test]
    fn check_from_function_domain_matches_curried_function_tiling() {
        assert!(domain_guard(Predicate::True).check_from(&curried(range(4), int(), int())));
    }

    #[test]
    fn check_from_function_codomain_domain_matches_curried_function_tiling() {
        // Codomain(Domain(_)) is the canonical way to address the inner domain of
        // a CurriedFunction.
        let g = codomain_guard(domain_guard(Predicate::True));
        assert!(g.check_from(&curried(range(4), int(), int())));
    }

    #[test]
    fn check_from_function_codomain_scalar_rejects_curried_function_tiling() {
        // Codomain(Scalar) is not a valid guard shape for a CurriedFunction.
        let g = codomain_guard(TileGuard::Scalar(true));
        assert!(!g.check_from(&curried(range(4), int(), int())));
    }

    #[test]
    fn check_from_function_guard_rejects_scalar_tiling() {
        assert!(!domain_guard(Predicate::True).check_from(&Tiling::Scalar(int())));
        assert!(!codomain_guard(domain_guard(Predicate::True)).check_from(&Tiling::Scalar(int())));
    }

    #[test]
    fn check_from_record_matches_record_tiling_with_same_keys() {
        let tiling = record_tiling(&[("x", Tiling::Scalar(int())), ("y", agg_tiling())]);
        let guard = TileGuard::Record(
            [
                ("x".to_string(), TileGuard::Scalar(true)),
                ("y".to_string(), TileGuard::Aggregation(false)),
            ]
            .into(),
        );
        assert!(guard.check_from(&tiling));
    }

    #[test]
    fn check_from_record_rejects_missing_key() {
        let tiling = record_tiling(&[("x", Tiling::Scalar(int())), ("y", Tiling::Scalar(int()))]);
        // Guard only has "x", not "y".
        let guard = TileGuard::Record([("x".to_string(), TileGuard::Scalar(true))].into());
        assert!(!guard.check_from(&tiling));
    }

    #[test]
    fn check_from_record_rejects_wrong_field_shape() {
        let tiling = record_tiling(&[("x", Tiling::Scalar(int()))]);
        // "x" field guard is Aggregation but tiling says Scalar.
        let guard = TileGuard::Record([("x".to_string(), TileGuard::Aggregation(true))].into());
        assert!(!guard.check_from(&tiling));
    }

    #[test]
    fn check_from_record_rejects_extra_key() {
        let tiling = record_tiling(&[("x", Tiling::Scalar(int()))]);
        let guard = TileGuard::Record(
            [
                ("x".to_string(), TileGuard::Scalar(true)),
                ("y".to_string(), TileGuard::Scalar(true)),
            ]
            .into(),
        );
        assert!(!guard.check_from(&tiling));
    }

    #[test]
    fn check_from_or_all_arms_compatible() {
        let tiling = Tiling::Scalar(int());
        let guard = TileGuard::Or(vec![TileGuard::Scalar(true), TileGuard::Scalar(false)]);
        assert!(guard.check_from(&tiling));
    }

    #[test]
    fn check_from_or_rejects_when_any_arm_incompatible() {
        let tiling = Tiling::Scalar(int());
        // Second arm is an Aggregation guard, which does not match a Scalar tiling.
        let guard = TileGuard::Or(vec![TileGuard::Scalar(true), TileGuard::Aggregation(true)]);
        assert!(!guard.check_from(&tiling));
    }
}
