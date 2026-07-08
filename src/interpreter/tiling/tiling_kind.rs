//! The [`Tiling`] type: the static shape descriptor for what a
//! [`TileOperator`](crate::interpreter::tile_operators::TileOperator) produces.

use std::{collections::HashMap, fmt};

use bit_set::BitSet;
use bit_vec::BitVec;

use crate::{
    ccl::AggregateKind,
    interpreter::{
        ColumnValue, Extent, FunctionGuard, Predicate, Tile, TileGuard, transform_hashmap_values,
        tuple_field,
    },
    util::fmt_record,
};

/// Every [`TileOperator`](crate::interpreter::tile_operators::TileOperator) has a tiling that
/// describes what kind of [`Tile`] it produces.
#[derive(Debug, Clone, PartialEq)]
pub enum Tiling {
    /// A single value, which may or may not be known.
    Scalar(Extent),
    /// A record of tilings.
    Record(HashMap<String, Tiling>),
    /// A function from a domain extent to a (possibly structured) codomain tiling,
    /// represented as a mapping plus progress information (the seal).
    SealedFunction {
        domain: Extent,
        codomain: Box<Tiling>,
    },
    /// A function of type A -> B -> C
    CurriedFunction {
        domain1: Extent,
        domain2: Extent,
        codomain: Extent,
    },
    /// Result of an aggregation
    Aggregation {
        kind: AggregateKind,
        accumulator: Extent,
    },
    /// A transactional store — the static shape of a [`Tile::Store`]: a step
    /// function from the commit-time domain to a per-key state record. Its
    /// extent is `Fun(domain, codomain)`, identical to a `SealedFunction`; the
    /// distinction is the runtime step semantics (see [`Tile::Store`]).
    Store {
        /// The commit-time domain (`Txn`).
        domain: Extent,
        /// The per-key state record `{key: value}` the store maps each commit
        /// time to.
        codomain: Box<Tiling>,
    },
}

impl Tiling {
    pub fn extent(&self) -> Extent {
        match self {
            Tiling::Scalar(e) => e.clone(),
            Tiling::Record(m) => Extent::Record(transform_hashmap_values(m, Tiling::extent)),
            Tiling::SealedFunction { domain, codomain } | Tiling::Store { domain, codomain } => {
                Extent::Function {
                    domain: Box::new(domain.clone()),
                    codomain: Box::new(codomain.extent()),
                }
            }
            Tiling::CurriedFunction {
                domain1,
                domain2,
                codomain,
            } => Extent::Function {
                domain: Box::new(domain1.clone()),
                codomain: Box::new(Extent::Function {
                    domain: Box::new(domain2.clone()),
                    codomain: Box::new(codomain.clone()),
                }),
            },
            Tiling::Aggregation { accumulator, .. } => accumulator.clone(),
        }
    }

    pub fn universal_guard(&self) -> TileGuard {
        match self {
            Tiling::Scalar(..) => TileGuard::Scalar(true),
            Tiling::Record(m) => {
                TileGuard::Record(transform_hashmap_values(m, |t| t.universal_guard()))
            }
            Tiling::SealedFunction { .. }
            | Tiling::CurriedFunction { .. }
            | Tiling::Store { .. } => TileGuard::Function(FunctionGuard::Domain(Predicate::True)),
            Tiling::Aggregation { .. } => TileGuard::Aggregation(true),
        }
    }

    pub fn empty_guard(&self) -> TileGuard {
        match self {
            Tiling::Scalar(..) => TileGuard::Scalar(false),
            Tiling::Record(m) => {
                TileGuard::Record(transform_hashmap_values(m, |t| t.empty_guard()))
            }
            Tiling::SealedFunction { .. }
            | Tiling::CurriedFunction { .. }
            | Tiling::Store { .. } => TileGuard::Function(FunctionGuard::Domain(Predicate::False)),
            Tiling::Aggregation { .. } => TileGuard::Aggregation(false),
        }
    }

    pub fn codomain(&self) -> Option<Tiling> {
        match self {
            Tiling::Scalar(Extent::Function { codomain, .. }) => {
                Some(Tiling::Scalar(*codomain.clone()))
            }
            Tiling::SealedFunction { codomain, .. } | Tiling::Store { codomain, .. } => {
                Some(*codomain.clone())
            }
            _ => None,
        }
    }

    /// Return the domain extent if the the tiling represents a function.  This returns Some
    /// for Scalar(Function), SealedFunction, CurriedFunction, and Store.
    pub fn domain_extent(&self) -> Option<Extent> {
        match self {
            Tiling::Scalar(Extent::Function { domain, .. }) => Some(*domain.clone()),
            Tiling::SealedFunction { domain, .. } | Tiling::Store { domain, .. } => {
                Some(domain.clone())
            }
            Tiling::CurriedFunction { domain1, .. } => Some(domain1.clone()),
            _ => None,
        }
    }

    /// Gets the domain and codomain extents if the tiling represents a function, otherwise None.
    pub fn split_function_extent(&self) -> Option<(Extent, Extent)> {
        match self {
            Tiling::Scalar(Extent::Function { domain, codomain }) => {
                Some((*domain.clone(), *codomain.clone()))
            }
            Tiling::SealedFunction { domain, codomain } | Tiling::Store { domain, codomain } => {
                Some((domain.clone(), codomain.extent()))
            }
            _ => None,
        }
    }

    pub fn empty_tile(&self) -> Tile {
        match self {
            Tiling::Scalar(e) => Tile::Scalar(ColumnValue::from_values(Vec::new(), e)),
            Tiling::Record(m) => Tile::Record(transform_hashmap_values(m, |t| t.empty_tile())),
            Tiling::SealedFunction { domain, codomain } => Tile::SealedFunction {
                domain: ColumnValue::from_values(Vec::new(), domain),
                codomain: Box::new(codomain.empty_tile()),
                domain_predicate: Predicate::False,
                deleted: BitSet::new(),
            },
            Tiling::CurriedFunction {
                domain1: domain1_extent,
                domain2: domain2_extent,
                codomain: codomain_extent,
            } => Tile::curried_function(
                ColumnValue::from_values(Vec::new(), domain1_extent),
                ColumnValue::UInts(Vec::new()),
                ColumnValue::from_values(Vec::new(), domain2_extent),
                ColumnValue::from_values(Vec::new(), codomain_extent),
                Predicate::False,
                BitSet::new(),
            ),
            Tiling::Aggregation { kind, accumulator } => Tile::Aggregation {
                kind: *kind,
                terminal: ColumnValue::Bools(BitVec::new()),
                accumulator: ColumnValue::from_values(Vec::new(), accumulator),
            },
            // An empty store: no change events yet, frontier undecided.
            Tiling::Store { domain, .. } => Tile::Store {
                changes: ColumnValue::from_values(Vec::new(), domain),
                deltas: ColumnValue::Variants(Vec::new()),
                frontier: Predicate::False,
            },
        }
    }

    pub fn is_scalar(&self) -> bool {
        match self {
            Tiling::Scalar(..) => true,
            Tiling::Record(m) if m.values().all(Tiling::is_scalar) => true,
            _ => false,
        }
    }

    pub fn is_function(&self) -> bool {
        self.domain_extent().is_some()
    }

    /// Return the tiling produced by mapping `output_extent` over this tiling's
    /// domain (if any).
    ///
    /// If `self` has no domain (i.e. is scalar), returns `Tiling::Scalar(output_extent)`.
    /// If `self` is a `SealedFunction`, returns a new `SealedFunction` with the same
    /// domain but `Tiling::Scalar(output_extent)` as the codomain.
    pub fn map_output(&self, output_extent: Extent) -> Tiling {
        match self.domain_extent() {
            None => Tiling::Scalar(output_extent),
            Some(domain) => Tiling::SealedFunction {
                domain: domain.clone(),
                codomain: Box::new(Tiling::Scalar(output_extent)),
            },
        }
    }

    /// Helper to create a tuple tiling, i.e. a Record tiling where all fields are from `tuple_field`
    pub fn tuple(tilings: &[Tiling]) -> Tiling {
        Tiling::Record(
            tilings
                .iter()
                .enumerate()
                .map(|(i, t)| (tuple_field(i), t.clone()))
                .collect(),
        )
    }
}

impl fmt::Display for Tiling {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Tiling::Scalar(e) => write!(f, "{e:?}"),
            Tiling::Record(fields) => fmt_record(f, fields),
            Tiling::SealedFunction { domain, codomain } => write!(f, "SF({domain:?} → {codomain})"),
            Tiling::Store { domain, codomain } => write!(f, "Store({domain:?} → {codomain})"),
            Tiling::CurriedFunction {
                domain1,
                domain2,
                codomain,
            } => {
                write!(f, "CF({domain1:?} → {domain2:?} → {codomain:?}])")
            }
            Tiling::Aggregation { kind, accumulator } => {
                write!(f, "agg({kind:?}, {accumulator:?})")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::AggregateKind;
    use crate::interpreter::{Extent, tiling::tests::*};

    // ── Tiling::extent ────────────────────────────────────────────────────────

    #[test]
    fn tiling_extent_scalar() {
        assert_eq!(Tiling::Scalar(int()).extent(), int());
    }

    #[test]
    fn tiling_extent_sealed_function() {
        let t = sealed(int(), bool_ext());
        assert_eq!(
            t.extent(),
            Extent::Function {
                domain: Box::new(int()),
                codomain: Box::new(bool_ext()),
            }
        );
    }

    #[test]
    fn tiling_extent_lookup_function() {
        let t = curried(range(4), int(), int());
        assert_eq!(
            t.extent(),
            Extent::Function {
                domain: Box::new(range(4)),
                codomain: Box::new(Extent::Function {
                    domain: Box::new(int()),
                    codomain: Box::new(int()),
                }),
            }
        );
    }

    #[test]
    fn tiling_extent_aggregation() {
        let t = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: int(),
        };
        assert_eq!(t.extent(), int());
    }

    // ── Tiling::universal_guard / empty_guard ─────────────────────────────────

    #[test]
    fn universal_guard_scalar() {
        assert!(Tiling::Scalar(int()).universal_guard().is_universal());
    }

    #[test]
    fn empty_guard_scalar() {
        assert!(Tiling::Scalar(int()).empty_guard().is_empty());
    }

    #[test]
    fn universal_guard_lookup_function() {
        assert!(
            curried(int(), int(), bool_ext())
                .universal_guard()
                .is_universal()
        );
    }

    #[test]
    fn empty_guard_lookup_function() {
        assert!(curried(int(), int(), bool_ext()).empty_guard().is_empty());
    }

    #[test]
    fn universal_guard_aggregation() {
        let t = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: int(),
        };
        assert!(t.universal_guard().is_universal());
    }

    #[test]
    fn empty_guard_aggregation() {
        let t = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: int(),
        };
        assert!(t.empty_guard().is_empty());
    }

    #[test]
    fn universal_guard_sealed_function() {
        let g = sealed(int(), bool_ext()).universal_guard();
        assert!(g.is_universal());
        assert!(!g.is_empty());
    }

    #[test]
    fn empty_guard_sealed_function() {
        let g = sealed(int(), bool_ext()).empty_guard();
        assert!(g.is_empty());
        assert!(!g.is_universal());
    }

    #[test]
    fn universal_guard_record_all_universal() {
        let t = record_tiling(&[("x", Tiling::Scalar(int())), ("y", Tiling::Scalar(int()))]);
        assert!(t.universal_guard().is_universal());
    }

    // ── Tiling::codomain ──────────────────────────────────────────────────────

    #[test]
    fn codomain_sealed_function() {
        let t = sealed(int(), bool_ext());
        assert_eq!(t.codomain(), Some(Tiling::Scalar(bool_ext())));
    }

    #[test]
    fn codomain_scalar_function_extent() {
        let t = Tiling::Scalar(Extent::Function {
            domain: Box::new(int()),
            codomain: Box::new(bool_ext()),
        });
        assert_eq!(t.codomain(), Some(Tiling::Scalar(bool_ext())));
    }

    #[test]
    fn codomain_scalar_non_function_is_none() {
        assert_eq!(Tiling::Scalar(int()).codomain(), None);
    }

    #[test]
    fn codomain_lookup_function_is_none() {
        // CurriedFunction has no structured codomain tiling via codomain().
        // Its codomain is accessed through domain2 and codomain extents directly.
        assert_eq!(curried(int(), bool_ext(), int()).codomain(), None);
    }

    // ── Tiling::domain_extent ─────────────────────────────────────────────────

    #[test]
    fn domain_extent_sealed_function() {
        assert_eq!(sealed(int(), bool_ext()).domain_extent(), Some(int()));
    }

    #[test]
    fn domain_extent_lookup_function() {
        assert_eq!(
            curried(range(4), int(), bool_ext()).domain_extent(),
            Some(range(4))
        );
    }

    #[test]
    fn domain_extent_scalar_function() {
        let t = Tiling::Scalar(Extent::Function {
            domain: Box::new(int()),
            codomain: Box::new(bool_ext()),
        });
        assert_eq!(t.domain_extent(), Some(int()));
    }

    #[test]
    fn domain_extent_plain_scalar_is_none() {
        assert_eq!(Tiling::Scalar(int()).domain_extent(), None);
    }

    // ── Tiling::split_function_extent ─────────────────────────────────────────

    #[test]
    fn split_function_extent_sealed() {
        assert_eq!(
            sealed(int(), bool_ext()).split_function_extent(),
            Some((int(), bool_ext()))
        );
    }

    #[test]
    fn split_function_extent_scalar_function() {
        let t = Tiling::Scalar(Extent::Function {
            domain: Box::new(int()),
            codomain: Box::new(bool_ext()),
        });
        assert_eq!(t.split_function_extent(), Some((int(), bool_ext())));
    }

    #[test]
    fn split_function_extent_non_function_is_none() {
        assert_eq!(Tiling::Scalar(int()).split_function_extent(), None);
        assert_eq!(
            curried(int(), bool_ext(), int()).split_function_extent(),
            None
        );
    }

    // ── Tiling::is_scalar / is_function ──────────────────────────────────────

    #[test]
    fn is_scalar_plain_scalar() {
        assert!(Tiling::Scalar(int()).is_scalar());
    }

    #[test]
    fn is_scalar_record_of_scalars() {
        let t = record_tiling(&[
            ("a", Tiling::Scalar(int())),
            ("b", Tiling::Scalar(bool_ext())),
        ]);
        assert!(t.is_scalar());
    }

    #[test]
    fn is_scalar_record_with_non_scalar_field() {
        let t = record_tiling(&[("a", sealed(int(), bool_ext()))]);
        assert!(!t.is_scalar());
    }

    #[test]
    fn is_scalar_sealed_function_is_false() {
        assert!(!sealed(int(), bool_ext()).is_scalar());
    }

    #[test]
    fn is_function_sealed() {
        assert!(sealed(int(), bool_ext()).is_function());
    }

    #[test]
    fn is_function_lookup() {
        assert!(curried(int(), bool_ext(), int()).is_function());
    }

    #[test]
    fn is_function_scalar_is_false() {
        assert!(!Tiling::Scalar(int()).is_function());
    }

    // ── Tiling::map_output ────────────────────────────────────────────────────

    #[test]
    fn map_output_from_scalar_gives_scalar() {
        let result = Tiling::Scalar(int()).map_output(bool_ext());
        assert_eq!(result, Tiling::Scalar(bool_ext()));
    }

    #[test]
    fn map_output_from_sealed_preserves_domain() {
        let t = sealed(int(), bool_ext());
        let result = t.map_output(range(3));
        assert_eq!(
            result,
            Tiling::SealedFunction {
                domain: int(),
                codomain: Box::new(Tiling::Scalar(range(3))),
            }
        );
    }

    // ── Tiling::empty_tile ────────────────────────────────────────────────────

    #[test]
    fn empty_tile_scalar_is_empty() {
        let tile = Tiling::Scalar(int()).empty_tile();
        assert!(tile.is_empty());
        assert!(!tile.is_terminal());
    }

    #[test]
    fn empty_tile_sealed_function_is_empty() {
        let tile = sealed(int(), bool_ext()).empty_tile();
        assert!(tile.is_empty());
        assert!(!tile.is_terminal());
    }

    #[test]
    fn empty_tile_lookup_function_is_empty() {
        let tile = curried(int(), bool_ext(), int()).empty_tile();
        assert!(tile.is_empty());
        assert!(!tile.is_terminal());
    }

    // ── Tiling Display ────────────────────────────────────────────────────────

    #[test]
    fn display_scalar() {
        assert_eq!(Tiling::Scalar(int()).to_string(), "Int");
    }

    #[test]
    fn display_sealed_function() {
        let s = sealed(int(), bool_ext()).to_string();
        assert!(s.contains("→"), "expected arrow in '{s}'");
    }

    #[test]
    fn display_lookup_function() {
        let s = curried(range(4), int(), bool_ext()).to_string();
        assert!(
            s.contains("→") && s.contains('['),
            "expected '→ [' in '{s}'"
        );
    }

    #[test]
    fn display_aggregation() {
        let s = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: int(),
        }
        .to_string();
        assert!(s.starts_with("agg("), "expected 'agg(' in '{s}'");
    }
}
