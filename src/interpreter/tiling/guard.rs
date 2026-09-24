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
    /// Built where no single variant holds the union. A collection of collections is
    /// covered partly by its own keys and partly by the inner ones, so
    /// [`Tile::to_guard`](crate::interpreter::Tile::to_guard) names both and
    /// [`FunctionGuard::union`] has no `Domain`-with-`Codomain` arm to merge them.
    /// Every other shape represents its own union directly — a record's union is its
    /// fields'.
    ///
    /// Invariant: arms never directly nest another `Or` (always flattened by
    /// [`TileGuard::flatten_or`]).
    Or(Vec<TileGuard>),
}

/// Whether two guards name the same place — the same nesting, down to the predicate.
fn same_place(a: &TileGuard, b: &TileGuard) -> bool {
    match (a, b) {
        (
            TileGuard::Function(FunctionGuard::Domain(_)),
            TileGuard::Function(FunctionGuard::Domain(_)),
        ) => true,
        (
            TileGuard::Function(FunctionGuard::Codomain(x)),
            TileGuard::Function(FunctionGuard::Codomain(y)),
        ) => same_place(x, y),
        _ => false,
    }
}

/// The union of two guards naming the same place, which [`same_place`] has established.
fn union_in_place(a: &TileGuard, b: &TileGuard) -> TileGuard {
    match (a, b) {
        (
            TileGuard::Function(FunctionGuard::Domain(p)),
            TileGuard::Function(FunctionGuard::Domain(q)),
        ) => TileGuard::Function(FunctionGuard::Domain(p.union(q))),
        (
            TileGuard::Function(FunctionGuard::Codomain(x)),
            TileGuard::Function(FunctionGuard::Codomain(y)),
        ) => TileGuard::Function(FunctionGuard::Codomain(Box::new(union_in_place(x, y)))),
        _ => unreachable!("only two guards naming one place are unioned this way"),
    }
}

/// Combine two record guards field by field.
///
/// Both guards describe the same `Tiling::Record`, so they name the same fields;
/// a mismatch means two guards for different tilings met, which no producer can
/// act on.
fn zip_fields(
    m1: &HashMap<String, TileGuard>,
    m2: &HashMap<String, TileGuard>,
    combine: impl Fn(&TileGuard, &TileGuard) -> TileGuard,
) -> HashMap<String, TileGuard> {
    assert_eq!(
        m1.len(),
        m2.len(),
        "Incompatible record guards: {m1:?} vs {m2:?}"
    );
    m1.iter()
        .map(|(k, g)| {
            let other = m2.get(k).unwrap_or_else(|| {
                panic!("Incompatible record guards: {m1:?} vs {m2:?}");
            });
            (k.clone(), combine(g, other))
        })
        .collect()
}

impl TileGuard {
    /// Builds a `TileGuard` from a list of arms, flattening any nested `Or`
    /// variants.  Returns the single element directly when `arms` has length
    /// one to avoid gratuitous wrapping.
    /// TODO consolidate redundant arms.
    pub(crate) fn flatten_or(arms: Vec<TileGuard>) -> TileGuard {
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
        // Two arms naming the same place are one arm over the union of what they name.
        // Leaving them apart would make a guard's shape depend on how it was assembled,
        // and a consumer that matches on the shape reads that as a different guard.
        let mut merged: Vec<TileGuard> = Vec::with_capacity(flat.len());
        for arm in flat {
            match merged.iter().position(|g| same_place(g, &arm)) {
                Some(i) => {
                    merged[i] = union_in_place(&merged[i], &arm);
                }
                None => merged.push(arm),
            }
        }
        match merged.len() {
            0 => unreachable!("flatten_or called with no arms"),
            1 => merged.into_iter().next().unwrap(),
            _ => TileGuard::Or(merged),
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
                TileGuard::Record(zip_fields(m1, m2, TileGuard::intersect))
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
            // A record guard covers the cells of each field its map names, so two of
            // them union field by field, as `intersect` above combines them.
            //
            // [`Predicate::Record`](crate::interpreter::Predicate::Record) reads
            // alike and does not union alike: it admits a record *value* only when
            // every field admits its component, so it is a product and two products
            // do not union to one. That is why `Predicate` keeps an `Or` arm for this
            // and a guard does not need one. Reaching for `TileGuard::Or` here leaves
            // a guard no record-tiled producer can act on: a consumer releasing one
            // field twice hands `MakeRecord` two arms naming that field, and the
            // operand that owns it hears about neither.
            (TileGuard::Record(m1), TileGuard::Record(m2)) => {
                TileGuard::Record(zip_fields(m1, m2, TileGuard::union))
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

    /// Returns whether this guard is universal, panicking unless it is universal
    /// or empty — for producers that can only reclaim all or nothing. Quietly
    /// dropping a partial guard would leave them free to re-emit the released
    /// region, since a producer records the guard either way. `context` names the
    /// producer in the panic message.
    pub fn expect_universal_or_empty(&self, context: &str) -> bool {
        if self.is_empty() {
            false
        } else if self.is_universal() {
            true
        } else {
            panic!("{context} cannot honor the partial release guard {self:?}")
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

            // DataFunction tilings can have domain guards which are always allowed, or
            // codomain guards which match their codomain tiling. A Store shares the
            // function shape: consumers release a prefix of its commit-time domain
            // (a `Domain` guard) — that is its only release form (a store's
            // `to_guard` is `Function(Domain(_))`), so no `Codomain` arm.
            (TileGuard::Function(FunctionGuard::Domain(pred)), Tiling::Store { domain, .. }) => {
                pred.is_applicable_to(domain)
            }

            // A collection supports a `Domain` guard naming its own keys and a `Codomain`
            // guard naming what sits under them. The guard nests exactly as the tiling does,
            // so stepping in is one recursion with nothing to translate.
            (
                TileGuard::Function(FunctionGuard::Domain(pred)),
                Tiling::DataFunction { domain, .. },
            ) => pred.is_applicable_to(domain),
            (
                TileGuard::Function(FunctionGuard::Codomain(g)),
                Tiling::DataFunction { codomain, .. },
            ) => g.check_from(codomain),

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

/// A guard on a [`Tile::DataFunction`](crate::interpreter::Tile::DataFunction), naming which
/// part of it is of interest: its own keys, or what those keys hold.
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
    fn guard_intersect_one_level_universal_universal() {
        let g = TileGuard::Function(FunctionGuard::Domain(Predicate::True))
            .intersect(&TileGuard::Function(FunctionGuard::Domain(Predicate::True)));
        assert!(g.is_universal());
    }

    #[test]
    fn guard_intersect_one_level_empty_dominates() {
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

    /// A domain guard over the positions up to and including `bound`.
    fn upto(bound: usize) -> TileGuard {
        domain_guard(Predicate::LessThanEq(crate::interpreter::Value::UInt(
            bound,
        )))
    }

    /// `upto` one level in, so an `Or` of the two has an arm per level.
    fn inner_upto(bound: usize) -> TileGuard {
        codomain_guard(upto(bound))
    }

    /// A record guard names a region per field, so two of them union field by
    /// field and the result is a record guard again. That is what a record-tiled
    /// producer can act on: each field's operand is handed its own field's union.
    #[test]
    fn guard_union_record_is_field_wise() {
        let g1 = record_guard(&[
            ("a", TileGuard::Scalar(true)),
            ("b", TileGuard::Scalar(false)),
        ]);
        let g2 = record_guard(&[
            ("a", TileGuard::Scalar(false)),
            ("b", TileGuard::Scalar(true)),
        ]);
        assert_eq!(
            g1.union(&g2),
            record_guard(&[
                ("a", TileGuard::Scalar(true)),
                ("b", TileGuard::Scalar(true)),
            ]),
        );
    }

    /// A field unions as that field's own shape does. A collection field released
    /// in pieces therefore accumulates the positions it has handed over, which is
    /// what a consumer reading one field of a growing product does every pull.
    #[test]
    fn guard_union_record_accumulates_a_function_field() {
        let first = record_guard(&[("n", TileGuard::Scalar(false)), ("xs", upto(0))]);
        let second = record_guard(&[("n", TileGuard::Scalar(false)), ("xs", upto(2))]);
        assert_eq!(
            first.union(&second),
            record_guard(&[("n", TileGuard::Scalar(false)), ("xs", upto(2))]),
        );
    }

    #[test]
    fn guard_union_record_identical_is_that_record() {
        let g = record_guard(&[
            ("x", TileGuard::Scalar(true)),
            ("y", TileGuard::Scalar(true)),
        ]);
        assert_eq!(g.union(&g), g);
    }

    #[test]
    fn guard_union_record_is_universal_when_every_field_is() {
        let universal = record_guard(&[
            ("a", TileGuard::Scalar(true)),
            ("b", TileGuard::Scalar(true)),
        ]);
        let empty = record_guard(&[
            ("a", TileGuard::Scalar(false)),
            ("b", TileGuard::Scalar(false)),
        ]);
        assert!(empty.union(&universal).is_universal());
    }

    #[test]
    fn guard_union_record_is_empty_when_every_field_is() {
        let empty = record_guard(&[
            ("a", TileGuard::Scalar(false)),
            ("b", TileGuard::Scalar(false)),
        ]);
        assert!(empty.union(&empty).is_empty());
    }

    // ── TileGuard::Or ─────────────────────────────────────────────────────────
    //
    // Arms are built here rather than taken from a producer: what is under test is
    // the algebra, and the one production shape that needs it (`Tile::to_guard` on a
    // nested collection) mixes a `Domain` arm with a `Codomain` one, whose intersect is
    // unimplemented.

    /// Arms stay flat: a union against an existing `Or` appends rather than nests.
    #[test]
    fn guard_or_accumulates_arms() {
        let or = TileGuard::Or(vec![upto(0), inner_upto(1)]);
        let result = or.union(&codomain_guard(inner_upto(2)));
        let TileGuard::Or(arms) = &result else {
            panic!("expected Or, got {result:?}");
        };
        assert_eq!(arms.len(), 3, "should be flat, not nested");
    }

    /// Arms naming one level are one arm: the `Or` carries a predicate per level, so two
    /// at the same level are that level's union. Without this a guard's shape would depend
    /// on how it was assembled, and a consumer that matches on the shape would read two
    /// spellings of one region as different guards.
    #[test]
    fn guard_or_merges_arms_at_one_level() {
        let result = TileGuard::Or(vec![upto(0), upto(1)]).union(&upto(2));
        assert_eq!(result, upto(2));
    }

    /// `Or` distributes through `intersect`: `(A | B) & C = (A & C) | (B & C)`, which for
    /// arms at one level is that level's union — here `upto(1) | upto(3)`.
    #[test]
    fn guard_or_intersect_distributes() {
        let or = TileGuard::Or(vec![upto(1), upto(5)]);
        assert_eq!(or.intersect(&upto(3)), upto(3));
    }

    /// An `Or` is universal when any arm is, and empty only when every arm is.
    #[test]
    fn guard_or_is_universal_when_any_arm_is() {
        let with_universal = TileGuard::Or(vec![
            upto(1),
            TileGuard::Function(FunctionGuard::Domain(Predicate::True)),
        ]);
        assert!(with_universal.is_universal());
        assert!(!TileGuard::Or(vec![upto(1), upto(2)]).is_universal());
    }

    // ── FunctionGuard::intersect ───────────────────────────────────────────────

    #[test]
    fn function_guard_intersect_empty_dominates() {
        let result = FunctionGuard::Domain(Predicate::True)
            .intersect(&FunctionGuard::Domain(Predicate::False));
        assert!(matches!(result, FunctionGuard::Domain(Predicate::False)));
    }

    #[test]
    fn function_guard_intersect_universal_is_identity() {
        let result = FunctionGuard::Domain(Predicate::True)
            .intersect(&FunctionGuard::Domain(Predicate::True));
        assert!(matches!(result, FunctionGuard::Domain(Predicate::True)));
    }

    #[test]
    fn function_guard_intersect_domain_domain() {
        let result = FunctionGuard::Domain(Predicate::True)
            .intersect(&FunctionGuard::Domain(Predicate::False));
        assert!(matches!(result, FunctionGuard::Domain(Predicate::False)));
    }

    #[test]
    fn function_guard_intersect_codomain_codomain() {
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
            accumulator: Box::new(Tiling::Scalar(int())),
        }
    }

    #[test]
    fn check_from_scalar_matches_scalar_tiling() {
        assert!(TileGuard::Scalar(true).check_from(&Tiling::Scalar(int())));
        assert!(TileGuard::Scalar(false).check_from(&Tiling::Scalar(int())));
    }

    #[test]
    fn check_from_scalar_rejects_non_scalar_tiling() {
        assert!(!TileGuard::Scalar(true).check_from(&scalar_function(int(), bool_ext())));
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
        assert!(!TileGuard::Aggregation(true).check_from(&scalar_function(int(), bool_ext())));
    }

    #[test]
    fn check_from_function_domain_matches_a_one_level_tiling() {
        assert!(domain_guard(Predicate::True).check_from(&scalar_function(int(), bool_ext())));
        assert!(domain_guard(Predicate::False).check_from(&scalar_function(int(), bool_ext())));
    }

    #[test]
    fn check_from_function_codomain_matches_a_one_level_tiling() {
        // A Codomain(Domain(_)) guard is valid against a Function whose
        // codomain is itself a function tiling.
        let nested = scalar_function(int(), bool_ext());
        let outer = Tiling::data_function(int(), nested);
        let g = codomain_guard(domain_guard(Predicate::True));
        assert!(g.check_from(&outer));
    }

    #[test]
    fn check_from_function_codomain_scalar_against_a_one_level_tiling() {
        // Codomain(Scalar) is valid when the function's codomain is a scalar.
        let g = codomain_guard(TileGuard::Scalar(true));
        assert!(g.check_from(&scalar_function(int(), bool_ext())));
    }

    #[test]
    fn check_from_function_codomain_wrong_shape_against_a_one_level_tiling() {
        // Codomain(Aggregation) against a function with scalar codomain must fail.
        let g = codomain_guard(TileGuard::Aggregation(true));
        assert!(!g.check_from(&scalar_function(int(), bool_ext())));
    }

    #[test]
    fn check_from_function_domain_matches_a_two_level_tiling() {
        assert!(domain_guard(Predicate::True).check_from(&two_level(range(4), int(), int())));
    }

    #[test]
    fn check_from_function_codomain_domain_matches_a_two_level_tiling() {
        // Codomain(Domain(_)) is the canonical way to address the inner domain of
        // a Function.
        let g = codomain_guard(domain_guard(Predicate::True));
        assert!(g.check_from(&two_level(range(4), int(), int())));
    }

    #[test]
    fn check_from_function_codomain_scalar_rejects_a_two_level_tiling() {
        // Codomain(Scalar) is not a valid guard shape for a Function.
        let g = codomain_guard(TileGuard::Scalar(true));
        assert!(!g.check_from(&two_level(range(4), int(), int())));
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
