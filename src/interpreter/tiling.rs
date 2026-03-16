//! Core tiling types: [`Tiling`], [`Tile`], [`TileGuard`], [`SealedFunctionGuard`], [`Predicate`].
//!
//! These types describe the shape, data, and region-tracking for the tile-based
//! dataflow evaluation model.

use std::{collections::HashMap, fmt, hash::Hash};

use bit_vec::BitVec;
use intervalsets::{ops::Intersection, Interval, IntervalSet, MaybeEmpty};

use crate::{
    interpreter::{ColumnValue, Extent, Value},
    util::fmt_record,
};

/// Every [`TileOperator`](super::tile_operators::TileOperator) has a tiling that
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
    /// A lookup-table function: domain values map to lists of codomain values.
    LookupFunction { domain: Extent, codomain: Extent },
    /// Result of an aggregation
    Aggregation { accumulator: Extent },
}

impl Tiling {
    pub fn extent(&self) -> Extent {
        match self {
            Tiling::Scalar(e) => e.clone(),
            Tiling::Record(m) => Extent::Record(transform_hashmap_values(m, Tiling::extent)),
            Tiling::SealedFunction { domain, codomain } => Extent::Function {
                domain: Box::new(domain.clone()),
                codomain: Box::new(codomain.extent()),
            },
            Tiling::LookupFunction { domain, codomain } => Extent::Function {
                domain: Box::new(domain.clone()),
                codomain: Box::new(codomain.clone()),
            },
            Tiling::Aggregation { accumulator } => accumulator.clone(),
        }
    }

    pub fn universal_guard(&self) -> TileGuard {
        match self {
            Tiling::Scalar(..) => TileGuard::Scalar(true),
            Tiling::Record(m) => {
                TileGuard::Record(transform_hashmap_values(m, |t| t.universal_guard()))
            }
            Tiling::SealedFunction { .. } => {
                TileGuard::SealedFunction(SealedFunctionGuard::Universal)
            }
            Tiling::LookupFunction { .. } => TileGuard::LookupFunction(true),
            Tiling::Aggregation { .. } => TileGuard::Aggregation(true),
        }
    }

    pub fn empty_guard(&self) -> TileGuard {
        match self {
            Tiling::Scalar(..) => TileGuard::Scalar(false),
            Tiling::Record(m) => {
                TileGuard::Record(transform_hashmap_values(m, |t| t.empty_guard()))
            }
            Tiling::SealedFunction { .. } => TileGuard::SealedFunction(SealedFunctionGuard::Empty),
            Tiling::LookupFunction { .. } => TileGuard::LookupFunction(false),
            Tiling::Aggregation { .. } => TileGuard::Aggregation(false),
        }
    }

    pub fn codomain(&self) -> Option<Tiling> {
        match self {
            Tiling::Scalar(Extent::Function { codomain, .. }) => {
                Some(Tiling::Scalar(*codomain.clone()))
            }
            Tiling::SealedFunction { codomain, .. } => Some(*codomain.clone()),
            _ => None,
        }
    }

    /// Return the domain extent if the the tiling represents a function.  This returns Some
    /// for Scalar(Function), SealedFunction, and LookupFunction
    pub fn domain_extent(&self) -> Option<Extent> {
        match self {
            Tiling::Scalar(Extent::Function { domain, .. }) => Some(*domain.clone()),
            Tiling::SealedFunction { domain, .. } => Some(domain.clone()),
            Tiling::LookupFunction { domain, .. } => Some(domain.clone()),
            _ => None,
        }
    }

    /// Gets the domain and codomain extents if the tiling represents a function, otherwise None.
    pub fn split_function_extent(&self) -> Option<(Extent, Extent)> {
        match self {
            Tiling::Scalar(Extent::Function { domain, codomain }) => {
                Some((*domain.clone(), *codomain.clone()))
            }
            Tiling::SealedFunction { domain, codomain } => {
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
            },
            Tiling::LookupFunction { .. } => Tile::LookupFunction {
                map: HashMap::new(),
                domain_predicate: Predicate::False,
            },
            Tiling::Aggregation { accumulator } => Tile::Aggregation {
                terminal: ColumnValue::Bools(BitVec::new()),
                accumulator: ColumnValue::from_values(Vec::new(), accumulator),
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
}

impl fmt::Display for Tiling {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Tiling::Scalar(e) => write!(f, "{e:?}"),
            Tiling::Record(fields) => fmt_record(f, fields),
            Tiling::SealedFunction { domain, codomain } => write!(f, "{domain:?} → {codomain}"),
            Tiling::LookupFunction { domain, codomain } => {
                write!(f, "{domain:?} → [{codomain:?}]")
            }
            Tiling::Aggregation { accumulator } => write!(f, "agg({accumulator:?})"),
        }
    }
}

/// A materialized data tile produced by a [`TileProducer`](super::tile_operators::TileProducer).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tile {
    /// A Tile representing a known or unknown single value.
    ///
    /// Scalars are represented as ColumnValues so that they can be operated on as a vector when
    /// embedded inside other tilings.  Empty ColumnValue represents a still-unknown scalar.
    Scalar(ColumnValue),
    /// A Record composed of other Tiles
    Record(HashMap<String, Tile>),
    /// A function mapping values to elements of another Tiling
    SealedFunction {
        domain: ColumnValue,
        codomain: Box<Tile>,
        domain_predicate: Predicate,
    },
    /// A function mapping values to bags of values.
    LookupFunction {
        /// The per-key value lists.
        /// TODO: change this representation so that the values can be operated on
        /// with vectorized code
        map: HashMap<Value, Vec<Value>>,
        /// Whether all domain keys and their value lists have been fully received.
        domain_predicate: Predicate,
    },
    /// A Tile representing the state of a scalar aggregation.
    Aggregation {
        /// The accumulator state of the specific aggregate; may be any type
        accumulator: ColumnValue,
        /// Boolean representing whether the aggregate is complete
        terminal: ColumnValue,
    },
}

impl Tile {
    pub fn len(&self) -> usize {
        match self {
            Tile::Scalar(cv) => cv.len(),
            Tile::Record(m) => m.values().map(Tile::len).max().unwrap_or(0),
            Tile::SealedFunction { domain, .. } => domain.len(),
            Tile::LookupFunction { map, .. } => map.len(),
            Tile::Aggregation { accumulator, .. } => accumulator.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn is_terminal(&self) -> bool {
        match self {
            Tile::Scalar(cv) => !cv.is_empty(),
            Tile::Record(m) => m.values().all(Tile::is_terminal),
            Tile::SealedFunction {
                domain_predicate, ..
            } => domain_predicate.as_bool().unwrap_or(false),
            Tile::LookupFunction {
                domain_predicate, ..
            } => domain_predicate.as_bool().unwrap_or(false),
            Tile::Aggregation { terminal, .. } => {
                terminal.as_single().map(|t| t.as_bool()).unwrap_or(false)
            }
        }
    }
}

/// Specifies a sub-region of interest within a [`Tile`], used for demand-driven
/// computation and incremental release.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TileGuard {
    Scalar(bool),
    Record(HashMap<String, TileGuard>),
    SealedFunction(SealedFunctionGuard),
    LookupFunction(bool),
    Aggregation(bool),
}

impl TileGuard {
    pub fn intersect(&self, other: &TileGuard) -> TileGuard {
        match (self, other) {
            (TileGuard::Scalar(u1), TileGuard::Scalar(u2)) => TileGuard::Scalar(*u1 && *u2),
            (TileGuard::LookupFunction(u1), TileGuard::LookupFunction(u2)) => {
                TileGuard::LookupFunction(*u1 && *u2)
            }
            (TileGuard::Aggregation(u1), TileGuard::Aggregation(u2)) => {
                TileGuard::Aggregation(*u1 && *u2)
            }
            (TileGuard::SealedFunction(f1), TileGuard::SealedFunction(f2)) => {
                TileGuard::SealedFunction(f1.intersect(f2))
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
            _ => panic!("Intersect on incompatible guards {self:?} and {other:?}"),
        }
    }

    pub fn is_universal(&self) -> bool {
        match self {
            TileGuard::Scalar(universal)
            | TileGuard::LookupFunction(universal)
            | TileGuard::Aggregation(universal) => *universal,
            TileGuard::Record(m) => m.values().all(TileGuard::is_universal),
            TileGuard::SealedFunction(g) => g.is_univeral(),
        }
    }

    pub fn is_empty(&self) -> bool {
        match self {
            TileGuard::Scalar(universal)
            | TileGuard::LookupFunction(universal)
            | TileGuard::Aggregation(universal) => !*universal,
            TileGuard::Record(m) => m.values().all(TileGuard::is_empty),
            TileGuard::SealedFunction(g) => g.is_empty(),
        }
    }
}

/// A guard on a [`SealedFunction`](Tile::SealedFunction) tile, specifying
/// which part of the function is of interest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SealedFunctionGuard {
    Universal,
    Empty,
    Domain(Predicate),
    Codomain(Box<TileGuard>),
}

impl SealedFunctionGuard {
    pub fn intersect(&self, other: &SealedFunctionGuard) -> SealedFunctionGuard {
        match (self, other) {
            (_, SealedFunctionGuard::Empty) | (SealedFunctionGuard::Empty, _) => {
                SealedFunctionGuard::Empty
            }
            (g, SealedFunctionGuard::Universal) | (SealedFunctionGuard::Universal, g) => g.clone(),
            (SealedFunctionGuard::Domain(p1), SealedFunctionGuard::Domain(p2)) => {
                SealedFunctionGuard::Domain(p1.intersect(p2))
            }
            (SealedFunctionGuard::Codomain(p1), SealedFunctionGuard::Codomain(p2)) => {
                SealedFunctionGuard::Codomain(Box::new(p1.intersect(p2)))
            }
            _ => todo!("Handle Domain + Codomain guards together"),
        }
    }

    pub fn is_univeral(&self) -> bool {
        match self {
            SealedFunctionGuard::Universal => true,
            SealedFunctionGuard::Empty => false,
            SealedFunctionGuard::Domain(p) if p.as_bool().is_some() => p.as_bool().unwrap(),
            SealedFunctionGuard::Domain(..) => false,
            SealedFunctionGuard::Codomain(g) => g.is_universal(),
        }
    }

    pub fn is_empty(&self) -> bool {
        match self {
            SealedFunctionGuard::Universal => false,
            SealedFunctionGuard::Empty => true,
            SealedFunctionGuard::Domain(p) if p.as_bool().is_some() => !p.as_bool().unwrap(),
            SealedFunctionGuard::Domain(..) => false,
            SealedFunctionGuard::Codomain(g) => g.is_empty(),
        }
    }
}

/// A predicate that describes a subset of values in an extent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Predicate {
    True,
    False,
    LessThanEq(Value),
    Intervals(IntervalSet<Value>),
    Record(HashMap<String, Predicate>),
}

impl Predicate {
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Predicate::False => Some(false),
            Predicate::True => Some(true),
            Predicate::Record(m) if m.iter().all(|(_, p)| p.as_bool().unwrap_or(false)) => {
                Some(true)
            }
            Predicate::Record(m) if m.iter().all(|(_, p)| !p.as_bool().unwrap_or(true)) => {
                Some(false)
            }
            _ => None,
        }
    }

    pub fn split_record<V>(&self, fields: &HashMap<String, V>) -> HashMap<String, Predicate> {
        match self {
            p if p.as_bool().is_some() => fields
                .keys()
                .map(|f| {
                    (
                        f.clone(),
                        if p.as_bool().unwrap() {
                            Predicate::True
                        } else {
                            Predicate::False
                        },
                    )
                })
                .collect(),
            Predicate::Record(m) => {
                assert!(fields.len() == m.len() && fields.keys().all(|f| m.contains_key(f)));
                m.clone()
            }
            _ => panic!(
                "Cannot split as record with keys [{:?}]: {:?}",
                fields.keys().collect::<Vec<_>>(),
                self
            ),
        }
    }

    /// Returns the predicate that admits exactly the values accepted by both `self` and `other`.
    pub fn intersect(&self, other: &Predicate) -> Predicate {
        match (self, other) {
            // True is the universal predicate: identity under intersection.
            (Predicate::True, p) | (p, Predicate::True) => p.clone(),
            // False is the empty predicate: annihilator under intersection.
            (Predicate::False, _) | (_, Predicate::False) => Predicate::False,
            // Two upper bounds: keep the tighter (smaller) one.
            (Predicate::LessThanEq(a), Predicate::LessThanEq(b)) => match a.partial_cmp(b) {
                Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal) => {
                    Predicate::LessThanEq(a.clone())
                }
                Some(std::cmp::Ordering::Greater) => Predicate::LessThanEq(b.clone()),
                None => panic!("Cannot compare values in LessThanEq predicates: {a:?} and {b:?}"),
            },
            // Upper bound intersected with an interval set: restrict to (-∞, v].
            (Predicate::LessThanEq(v), Predicate::Intervals(s))
            | (Predicate::Intervals(s), Predicate::LessThanEq(v)) => {
                let upper = IntervalSet::new(vec![Interval::unbound_closed(v.clone())]);
                let result = s.intersection(&upper);
                if result.is_empty() {
                    Predicate::False
                } else {
                    Predicate::Intervals(result)
                }
            }
            // Two interval sets: standard set intersection.
            (Predicate::Intervals(a), Predicate::Intervals(b)) => {
                let result = a.intersection(b);
                if result.is_empty() {
                    Predicate::False
                } else {
                    Predicate::Intervals(result)
                }
            }
            // Records: intersect field-by-field.
            (Predicate::Record(m1), Predicate::Record(m2)) => {
                assert_eq!(
                    m1.len(),
                    m2.len(),
                    "Cannot intersect Record predicates with different schemas"
                );
                Predicate::Record(
                    m1.iter()
                        .map(|(k, p1)| (k.clone(), p1.intersect(&m2[k])))
                        .collect(),
                )
            }
            _ => panic!("Cannot intersect incompatible predicates: {self:?} and {other:?}"),
        }
    }
}

/// Apply `f` to every value in a `HashMap`, producing a new map with the same keys.
pub(super) fn transform_hashmap_values<K: Clone + Eq + Hash, InputV, V, F: Fn(&InputV) -> V>(
    source: &HashMap<K, InputV>,
    f: F,
) -> HashMap<K, V> {
    source.iter().map(|(k, v)| (k.clone(), f(v))).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::{BaseType, ColumnValue, Extent, Value};

    // ── helpers ───────────────────────────────────────────────────────────────

    fn int() -> Extent {
        Extent::Base(BaseType::Int)
    }

    fn bool_ext() -> Extent {
        Extent::Base(BaseType::Bool)
    }

    fn range(end: usize) -> Extent {
        Extent::UIntRange { start: 0, end }
    }

    fn sealed(domain: Extent, codomain: Extent) -> Tiling {
        Tiling::SealedFunction {
            domain,
            codomain: Box::new(Tiling::Scalar(codomain)),
        }
    }

    fn lookup(domain: Extent, codomain: Extent) -> Tiling {
        Tiling::LookupFunction { domain, codomain }
    }

    fn record_tiling(fields: &[(&str, Tiling)]) -> Tiling {
        Tiling::Record(
            fields
                .iter()
                .map(|(k, v)| (k.to_string(), v.clone()))
                .collect(),
        )
    }

    fn record_pred(fields: &[(&str, Predicate)]) -> Predicate {
        Predicate::Record(
            fields
                .iter()
                .map(|(k, v)| (k.to_string(), v.clone()))
                .collect(),
        )
    }

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
        let t = lookup(range(4), int());
        assert_eq!(
            t.extent(),
            Extent::Function {
                domain: Box::new(range(4)),
                codomain: Box::new(int()),
            }
        );
    }

    #[test]
    fn tiling_extent_aggregation() {
        let t = Tiling::Aggregation { accumulator: int() };
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
        assert!(lookup(int(), int()).universal_guard().is_universal());
    }

    #[test]
    fn empty_guard_lookup_function() {
        assert!(lookup(int(), int()).empty_guard().is_empty());
    }

    #[test]
    fn universal_guard_aggregation() {
        let t = Tiling::Aggregation { accumulator: int() };
        assert!(t.universal_guard().is_universal());
    }

    #[test]
    fn empty_guard_aggregation() {
        let t = Tiling::Aggregation { accumulator: int() };
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
        // LookupFunction has no structured codomain tiling.
        assert_eq!(lookup(int(), bool_ext()).codomain(), None);
    }

    // ── Tiling::domain_extent ─────────────────────────────────────────────────

    #[test]
    fn domain_extent_sealed_function() {
        assert_eq!(sealed(int(), bool_ext()).domain_extent(), Some(int()));
    }

    #[test]
    fn domain_extent_lookup_function() {
        assert_eq!(lookup(range(4), int()).domain_extent(), Some(range(4)));
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
        assert_eq!(lookup(int(), bool_ext()).split_function_extent(), None);
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
        assert!(lookup(int(), bool_ext()).is_function());
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
        let tile = lookup(int(), bool_ext()).empty_tile();
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
        let s = lookup(range(4), int()).to_string();
        assert!(
            s.contains("→") && s.contains('['),
            "expected '→ [' in '{s}'"
        );
    }

    #[test]
    fn display_aggregation() {
        let s = Tiling::Aggregation { accumulator: int() }.to_string();
        assert!(s.starts_with("agg("), "expected 'agg(' in '{s}'");
    }

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
    fn guard_intersect_lookup_function() {
        let g = TileGuard::LookupFunction(true).intersect(&TileGuard::LookupFunction(false));
        assert!(g.is_empty());
    }

    #[test]
    fn guard_intersect_aggregation() {
        let g = TileGuard::Aggregation(true).intersect(&TileGuard::Aggregation(true));
        assert!(g.is_universal());
    }

    #[test]
    fn guard_intersect_sealed_function_universal_universal() {
        let g = TileGuard::SealedFunction(SealedFunctionGuard::Universal)
            .intersect(&TileGuard::SealedFunction(SealedFunctionGuard::Universal));
        assert!(g.is_universal());
    }

    #[test]
    fn guard_intersect_sealed_function_empty_dominates() {
        let g = TileGuard::SealedFunction(SealedFunctionGuard::Universal)
            .intersect(&TileGuard::SealedFunction(SealedFunctionGuard::Empty));
        assert!(g.is_empty());
    }

    // ── SealedFunctionGuard::intersect ────────────────────────────────────────

    #[test]
    fn sfg_intersect_empty_dominates() {
        let result = SealedFunctionGuard::Universal.intersect(&SealedFunctionGuard::Empty);
        assert!(matches!(result, SealedFunctionGuard::Empty));
    }

    #[test]
    fn sfg_intersect_universal_is_identity() {
        let result =
            SealedFunctionGuard::Domain(Predicate::True).intersect(&SealedFunctionGuard::Universal);
        assert!(matches!(
            result,
            SealedFunctionGuard::Domain(Predicate::True)
        ));
    }

    #[test]
    fn sfg_intersect_domain_domain() {
        let result = SealedFunctionGuard::Domain(Predicate::True)
            .intersect(&SealedFunctionGuard::Domain(Predicate::False));
        assert!(matches!(
            result,
            SealedFunctionGuard::Domain(Predicate::False)
        ));
    }

    #[test]
    fn sfg_intersect_codomain_codomain() {
        let result = SealedFunctionGuard::Codomain(Box::new(TileGuard::Scalar(true))).intersect(
            &SealedFunctionGuard::Codomain(Box::new(TileGuard::Scalar(false))),
        );
        assert_eq!(
            result,
            SealedFunctionGuard::Codomain(Box::new(TileGuard::Scalar(false)))
        );
    }

    // ── Predicate::as_bool ────────────────────────────────────────────────────

    #[test]
    fn predicate_as_bool_true() {
        assert_eq!(Predicate::True.as_bool(), Some(true));
    }

    #[test]
    fn predicate_as_bool_false() {
        assert_eq!(Predicate::False.as_bool(), Some(false));
    }

    #[test]
    fn predicate_as_bool_less_than_eq_is_none() {
        assert_eq!(Predicate::LessThanEq(Value::Int(5)).as_bool(), None);
    }

    #[test]
    fn predicate_as_bool_record_all_true() {
        let p = record_pred(&[("a", Predicate::True), ("b", Predicate::True)]);
        assert_eq!(p.as_bool(), Some(true));
    }

    #[test]
    fn predicate_as_bool_record_all_false() {
        let p = record_pred(&[("a", Predicate::False), ("b", Predicate::False)]);
        assert_eq!(p.as_bool(), Some(false));
    }

    #[test]
    fn predicate_as_bool_record_mixed_is_none() {
        let p = record_pred(&[("a", Predicate::True), ("b", Predicate::False)]);
        assert_eq!(p.as_bool(), None);
    }

    // ── Predicate::intersect ──────────────────────────────────────────────────

    #[test]
    fn predicate_intersect_true_is_identity() {
        assert_eq!(
            Predicate::True.intersect(&Predicate::LessThanEq(Value::Int(3))),
            Predicate::LessThanEq(Value::Int(3))
        );
        assert_eq!(
            Predicate::LessThanEq(Value::Int(3)).intersect(&Predicate::True),
            Predicate::LessThanEq(Value::Int(3))
        );
    }

    #[test]
    fn predicate_intersect_false_is_annihilator() {
        assert_eq!(
            Predicate::False.intersect(&Predicate::True),
            Predicate::False
        );
        assert_eq!(
            Predicate::LessThanEq(Value::Int(3)).intersect(&Predicate::False),
            Predicate::False
        );
    }

    #[test]
    fn predicate_intersect_less_than_eq_picks_tighter() {
        // min(5, 3) → LessThanEq(3)
        assert_eq!(
            Predicate::LessThanEq(Value::Int(5)).intersect(&Predicate::LessThanEq(Value::Int(3))),
            Predicate::LessThanEq(Value::Int(3))
        );
        // min(3, 5) → LessThanEq(3)
        assert_eq!(
            Predicate::LessThanEq(Value::Int(3)).intersect(&Predicate::LessThanEq(Value::Int(5))),
            Predicate::LessThanEq(Value::Int(3))
        );
    }

    #[test]
    fn predicate_intersect_record_field_by_field() {
        let p1 = record_pred(&[("a", Predicate::True), ("b", Predicate::False)]);
        let p2 = record_pred(&[("a", Predicate::False), ("b", Predicate::True)]);
        let result = p1.intersect(&p2);
        let Predicate::Record(m) = result else {
            panic!("expected Record predicate");
        };
        assert_eq!(m["a"], Predicate::False);
        assert_eq!(m["b"], Predicate::False);
    }

    // ── Predicate::split_record ───────────────────────────────────────────────

    #[test]
    fn split_record_true_broadcasts() {
        let fields: HashMap<String, ()> = [("x", ()), ("y", ())]
            .iter()
            .map(|(k, v)| (k.to_string(), *v))
            .collect();
        let result = Predicate::True.split_record(&fields);
        assert_eq!(result["x"], Predicate::True);
        assert_eq!(result["y"], Predicate::True);
    }

    #[test]
    fn split_record_false_broadcasts() {
        let fields: HashMap<String, ()> = [("a", ())]
            .iter()
            .map(|(k, v)| (k.to_string(), *v))
            .collect();
        let result = Predicate::False.split_record(&fields);
        assert_eq!(result["a"], Predicate::False);
    }

    #[test]
    fn split_record_record_returns_its_own_fields() {
        let fields: HashMap<String, ()> = [("a", ()), ("b", ())]
            .iter()
            .map(|(k, v)| (k.to_string(), *v))
            .collect();
        let p = record_pred(&[("a", Predicate::True), ("b", Predicate::False)]);
        let result = p.split_record(&fields);
        assert_eq!(result["a"], Predicate::True);
        assert_eq!(result["b"], Predicate::False);
    }

    // ── Tile::is_terminal ─────────────────────────────────────────────────────

    #[test]
    fn tile_scalar_non_empty_is_terminal() {
        let tile = Tile::Scalar(ColumnValue::Ints(vec![42]));
        assert!(tile.is_terminal());
    }

    #[test]
    fn tile_sealed_function_true_predicate_is_terminal() {
        let tile = Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![1]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2]))),
            domain_predicate: Predicate::True,
        };
        assert!(tile.is_terminal());
    }

    #[test]
    fn tile_sealed_function_false_predicate_not_terminal() {
        let tile = Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![]))),
            domain_predicate: Predicate::False,
        };
        assert!(!tile.is_terminal());
    }

    #[test]
    fn tile_lookup_function_true_predicate_is_terminal() {
        let tile = Tile::LookupFunction {
            map: HashMap::new(),
            domain_predicate: Predicate::True,
        };
        assert!(tile.is_terminal());
    }
}
