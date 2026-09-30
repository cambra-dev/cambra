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
    /// A collection level: the static shape of a
    /// [`Tile::DataFunction`](crate::interpreter::tiling::Tile).
    DataFunction {
        /// The key extent this level introduces.
        domain: Extent,
        /// The values, over those keys — an [`Tiling::Aggregation`] is what a fold leaves
        /// here.
        codomain: Box<Tiling>,
    },
    /// Result of an aggregation
    Aggregation {
        kind: AggregateKind,
        /// The shape the fold leaves, which for `Sole` is the element's own.
        accumulator: Box<Tiling>,
    },
    /// A transactional store — the static shape of a [`Tile::Store`]: a step
    /// function from the commit-time domain to a per-key state record. Its
    /// extent is `Fun(domain, codomain)`, identical to a `DataFunction`; the
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
    /// The tiling a value of `extent` takes: a collection as a `DataFunction`, a record
    /// holding one as a record of its fields' tilings, and anything else as a `Scalar` column,
    /// which is what a consumer reading one row at a time reads. The inverse of
    /// [`Self::extent`] for these shapes.
    ///
    /// See `src/interpreter/design-operators.md`, "A collection inside a value stays a tile".
    pub fn from_extent(extent: &Extent) -> Tiling {
        match extent {
            Extent::Function { domain, codomain } => {
                Tiling::data_function((**domain).clone(), Tiling::from_extent(codomain))
            }
            Extent::Record(fields) if extent.holds_a_collection() => Tiling::Record(
                fields
                    .iter()
                    .map(|(name, e)| (name.clone(), Tiling::from_extent(e)))
                    .collect(),
            ),
            _ => Tiling::Scalar(extent.clone()),
        }
    }

    pub fn extent(&self) -> Extent {
        match self {
            Tiling::Scalar(e) => e.clone(),
            Tiling::Record(m) => Extent::Record(transform_hashmap_values(m, Tiling::extent)),
            Tiling::Store { domain, codomain } => Extent::Function {
                domain: Box::new(domain.clone()),
                codomain: Box::new(codomain.extent()),
            },
            // One level per collection, and the nesting is the tiling's own.
            Tiling::DataFunction { domain, codomain } => Extent::Function {
                domain: Box::new(domain.clone()),
                codomain: Box::new(codomain.extent()),
            },
            Tiling::Aggregation { accumulator, .. } => accumulator.extent(),
        }
    }

    /// This tiling's empty tile at **no rows**, which is what a partial fold seeds with:
    /// its accumulator carries presence in its row count, so an empty one must have none.
    pub fn empty_at_no_rows(&self) -> Tile {
        self.empty_over(0)
    }

    pub fn universal_guard(&self) -> TileGuard {
        match self {
            Tiling::Scalar(..) => TileGuard::Scalar(true),
            Tiling::Record(m) => {
                TileGuard::Record(transform_hashmap_values(m, |t| t.universal_guard()))
            }
            Tiling::DataFunction { .. } | Tiling::Store { .. } => {
                TileGuard::Function(FunctionGuard::Domain(Predicate::True))
            }
            Tiling::Aggregation { .. } => TileGuard::Aggregation(true),
        }
    }

    pub fn empty_guard(&self) -> TileGuard {
        match self {
            Tiling::Scalar(..) => TileGuard::Scalar(false),
            Tiling::Record(m) => {
                TileGuard::Record(transform_hashmap_values(m, |t| t.empty_guard()))
            }
            Tiling::DataFunction { .. } | Tiling::Store { .. } => {
                TileGuard::Function(FunctionGuard::Domain(Predicate::False))
            }
            Tiling::Aggregation { .. } => TileGuard::Aggregation(false),
        }
    }

    pub fn codomain(&self) -> Option<Tiling> {
        match self {
            Tiling::Scalar(Extent::Function { codomain, .. }) => {
                Some(Tiling::Scalar(*codomain.clone()))
            }
            Tiling::Store { codomain, .. } => Some(*codomain.clone()),
            Tiling::DataFunction { codomain, .. } => Some(*codomain.clone()),
            _ => None,
        }
    }

    /// Return the domain extent if the the tiling represents a function.  This returns Some
    /// for Scalar(Function), Function, and Store.
    pub fn domain_extent(&self) -> Option<Extent> {
        match self {
            Tiling::Scalar(Extent::Function { domain, .. }) => Some(*domain.clone()),
            Tiling::Store { domain, .. } => Some(domain.clone()),
            Tiling::DataFunction { domain, .. } => Some(domain.clone()),
            _ => None,
        }
    }

    /// Gets the domain and codomain extents if the tiling represents a function, otherwise None.
    pub fn split_function_extent(&self) -> Option<(Extent, Extent)> {
        match self {
            Tiling::Scalar(Extent::Function { domain, codomain }) => {
                Some((*domain.clone(), *codomain.clone()))
            }
            Tiling::Store { domain, codomain } => Some((domain.clone(), codomain.extent())),
            // Split this collection off the front; what is left is its values' extent,
            // which for a deeper tiling is itself a collection.
            Tiling::DataFunction { domain, codomain } => Some((domain.clone(), codomain.extent())),
            _ => None,
        }
    }

    pub fn empty_tile(&self) -> Tile {
        self.empty_over(1)
    }

    /// The empty tile of this tiling, vectorized over `rows` rows.
    ///
    /// A collection's run is empty at every row, so whatever sits under it stands at no rows
    /// at all — which is what makes the chain well formed rather than each level restating
    /// one row it does not have.
    fn empty_over(&self, rows: usize) -> Tile {
        match self {
            Tiling::Scalar(e) => Tile::Scalar(ColumnValue::from_values(Vec::new(), e)),
            Tiling::Record(m) => Tile::Record(transform_hashmap_values(m, |t| t.empty_over(rows))),
            Tiling::DataFunction { domain, codomain } => Tile::grouped(
                ColumnValue::UInts(vec![0; rows]),
                ColumnValue::from_values(Vec::new(), domain),
                Box::new(codomain.empty_over(0)),
                Predicate::False,
                BitSet::new(),
            ),
            Tiling::Aggregation { kind, accumulator } => Tile::Aggregation {
                kind: *kind,
                terminal: ColumnValue::Bools(BitVec::new()),
                accumulator: Box::new(accumulator.empty_at_no_rows()),
            },
            // An empty store: no change events yet, frontier undecided, live, and
            // no key closed — a writer that has not been pulled yet may still
            // write any of them.
            Tiling::Store { domain, .. } => Tile::Store {
                changes: ColumnValue::from_values(Vec::new(), domain),
                deltas: ColumnValue::Variants(Vec::new()),
                frontier: Predicate::False,
                terminal: false,
                closed_keys: Vec::new(),
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

    pub fn has_domain(&self) -> bool {
        self.domain_extent().is_some()
    }

    /// Whether this tiling is a collection **level**, the test an operator makes when it
    /// walks a chain of them.
    ///
    /// Narrower than [`Self::has_domain`], which a materialized function cell and a store
    /// also answer: only this variant has keys in a column and a nested tiling under them.
    pub fn is_data_function(&self) -> bool {
        matches!(self, Tiling::DataFunction { .. })
    }

    /// Whether a level sits here, or inside a record here — the static counterpart of
    /// [`Tile::holds_a_level`](crate::interpreter::Tile::holds_a_level), which carries the rule.
    ///
    /// [`Extent::holds_a_collection`] asks whether the value type contains a collection at
    /// all, which a column of maps answers yes and this no.
    pub fn holds_a_level(&self) -> bool {
        match self {
            Tiling::DataFunction { .. } => true,
            Tiling::Record(fields) => fields.values().any(Tiling::holds_a_level),
            Tiling::Scalar(_) | Tiling::Aggregation { .. } | Tiling::Store { .. } => false,
        }
    }

    /// The tiling `depth` levels in, which is `self` at depth 0 — the static counterpart of
    /// [`Tile::values_at`].
    pub fn values_at(&self, depth: usize) -> &Tiling {
        match (depth, self) {
            (0, _) => self,
            (_, Tiling::DataFunction { codomain, .. }) => codomain.values_at(depth - 1),
            (_, other) => panic!("no level {depth} in {other}"),
        }
    }

    /// The tiling sitting under this chain, the static counterpart of
    /// [`Tile::deepest_values`], which carries the rule. A tiling that is not a collection
    /// is its own deepest values, a record included.
    pub fn deepest_values(&self) -> &Tiling {
        match self {
            Tiling::DataFunction { codomain, .. } => codomain.deepest_values(),
            other => other,
        }
    }

    /// Return the tiling produced by mapping `output_extent` over this tiling's
    /// domain (if any).
    ///
    /// If `self` has no domain (i.e. is scalar), returns `Tiling::Scalar(output_extent)`.
    /// If `self` is a function, returns a one-level function with the same domain but
    /// `Tiling::Scalar(output_extent)` as the codomain.
    pub fn map_output(&self, output_extent: Extent) -> Tiling {
        match self.domain_extent() {
            None => Tiling::Scalar(output_extent),
            Some(domain) => Tiling::data_function(domain, Tiling::Scalar(output_extent)),
        }
    }

    /// The collection `domain ⤇ codomain`.
    pub fn data_function(domain: Extent, codomain: Tiling) -> Tiling {
        Tiling::DataFunction {
            domain,
            codomain: Box::new(codomain),
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
            Tiling::Store { domain, codomain } => write!(f, "Store({domain:?} → {codomain})"),
            // One `→` per level rather than a nested `Fn(…)` each, which is how a curried
            // function reads.
            Tiling::DataFunction { domain, codomain } => {
                write!(f, "Fn({domain:?} → ")?;
                let mut node = codomain.as_ref();
                while let Tiling::DataFunction { domain, codomain } = node {
                    write!(f, "{domain:?} → ")?;
                    node = codomain;
                }
                write!(f, "{node})")
            }
            Tiling::Aggregation { kind, accumulator } => {
                write!(f, "agg({kind:?}, {accumulator})")
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
    fn tiling_extent_one_level() {
        let t = scalar_function(int(), bool_ext());
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
        let t = two_level(range(4), int(), int());
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
            accumulator: Box::new(Tiling::Scalar(int())),
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
            two_level(int(), int(), bool_ext())
                .universal_guard()
                .is_universal()
        );
    }

    #[test]
    fn empty_guard_lookup_function() {
        assert!(two_level(int(), int(), bool_ext()).empty_guard().is_empty());
    }

    #[test]
    fn universal_guard_aggregation() {
        let t = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tiling::Scalar(int())),
        };
        assert!(t.universal_guard().is_universal());
    }

    #[test]
    fn empty_guard_aggregation() {
        let t = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tiling::Scalar(int())),
        };
        assert!(t.empty_guard().is_empty());
    }

    #[test]
    fn universal_guard_one_level() {
        let g = scalar_function(int(), bool_ext()).universal_guard();
        assert!(g.is_universal());
        assert!(!g.is_empty());
    }

    #[test]
    fn empty_guard_one_level() {
        let g = scalar_function(int(), bool_ext()).empty_guard();
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
    fn codomain_one_level() {
        let t = scalar_function(int(), bool_ext());
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

    /// The codomain is what sits one level in, which for a chain is the collection below
    /// rather than the value at the bottom — applying a key yields the rest of the chain.
    #[test]
    fn codomain_of_two_levels_is_the_level_below_it() {
        assert_eq!(
            two_level(int(), bool_ext(), int()).codomain(),
            Some(Tiling::data_function(bool_ext(), Tiling::Scalar(int())))
        );
    }

    // ── Tiling::domain_extent ─────────────────────────────────────────────────

    #[test]
    fn domain_extent_one_level() {
        assert_eq!(
            scalar_function(int(), bool_ext()).domain_extent(),
            Some(int())
        );
    }

    #[test]
    fn domain_extent_lookup_function() {
        assert_eq!(
            two_level(range(4), int(), bool_ext()).domain_extent(),
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
    fn split_function_extent_one_level() {
        assert_eq!(
            scalar_function(int(), bool_ext()).split_function_extent(),
            Some((int(), bool_ext()))
        );
    }

    /// Splitting takes one level off the front, so a deeper tiling's codomain is the
    /// collection that is left.
    #[test]
    fn split_function_extent_two_level_leaves_a_collection() {
        assert_eq!(
            two_level(int(), bool_ext(), int()).split_function_extent(),
            Some((
                int(),
                Extent::Function {
                    domain: Box::new(bool_ext()),
                    codomain: Box::new(int()),
                }
            ))
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
    }

    // ── Tiling::is_scalar / has_domain ──────────────────────────────────────

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
        let t = record_tiling(&[("a", scalar_function(int(), bool_ext()))]);
        assert!(!t.is_scalar());
    }

    #[test]
    fn is_scalar_one_level_is_false() {
        assert!(!scalar_function(int(), bool_ext()).is_scalar());
    }

    #[test]
    fn is_data_function_one_level() {
        assert!(scalar_function(int(), bool_ext()).has_domain());
    }

    #[test]
    fn is_data_function_lookup() {
        assert!(two_level(int(), bool_ext(), int()).has_domain());
    }

    #[test]
    fn is_data_function_scalar_is_false() {
        assert!(!Tiling::Scalar(int()).has_domain());
    }

    // ── Tiling::map_output ────────────────────────────────────────────────────

    #[test]
    fn map_output_from_scalar_gives_scalar() {
        let result = Tiling::Scalar(int()).map_output(bool_ext());
        assert_eq!(result, Tiling::Scalar(bool_ext()));
    }

    #[test]
    fn map_output_from_one_level_preserves_domain() {
        let t = scalar_function(int(), bool_ext());
        let result = t.map_output(range(3));
        assert_eq!(
            result,
            Tiling::data_function(int(), Tiling::Scalar(range(3)))
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
    fn empty_tile_one_level_is_empty() {
        let tile = scalar_function(int(), bool_ext()).empty_tile();
        assert!(tile.is_empty());
        assert!(!tile.is_terminal());
    }

    #[test]
    fn empty_tile_lookup_function_is_empty() {
        let tile = two_level(int(), bool_ext(), int()).empty_tile();
        assert!(tile.is_empty());
        assert!(!tile.is_terminal());
    }

    // ── Tiling Display ────────────────────────────────────────────────────────

    #[test]
    fn display_scalar() {
        assert_eq!(Tiling::Scalar(int()).to_string(), "Int");
    }

    #[test]
    fn display_one_level() {
        let s = scalar_function(int(), bool_ext()).to_string();
        assert!(s.contains("→"), "expected arrow in '{s}'");
    }

    #[test]
    fn display_two_levels() {
        // The whole rendering, not a substring: a `[` test passes on the range
        // domain whichever way the brackets fall, which is how an unbalanced
        // one survived here.
        let s = two_level(range(4), int(), bool_ext()).to_string();
        assert_eq!(s, "Fn({[0, 3]} → Int → Bool)");
    }

    #[test]
    fn display_aggregation() {
        let s = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tiling::Scalar(int())),
        }
        .to_string();
        assert!(s.starts_with("agg("), "expected 'agg(' in '{s}'");
    }
}
