//! Core tiling types: [`Tiling`], [`Tile`], [`TileGuard`], [`SealedFunctionGuard`], [`Predicate`].
//!
//! These types describe the shape, data, and region-tracking for the tile-based
//! dataflow evaluation model.

use std::{
    collections::{HashMap, HashSet},
    fmt,
    hash::Hash,
};

use bit_vec::BitVec;
use intervalsets::{
    numeric::Domain,
    ops::{Contains, Intersection, Union},
    Interval, IntervalSet, MaybeEmpty, Side,
};

use crate::{
    ccl::AggregateKind,
    interpreter::{apply_binop_column, BinOpKind, ColumnValue, Extent, LogicKind, Value},
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
            Tiling::SealedFunction { .. } | Tiling::CurriedFunction { .. } => {
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
            Tiling::SealedFunction { .. } | Tiling::CurriedFunction { .. } => {
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
            Tiling::SealedFunction { codomain, .. } => Some(*codomain.clone()),
            _ => None,
        }
    }

    /// Return the domain extent if the the tiling represents a function.  This returns Some
    /// for Scalar(Function), SealedFunction, and CurriedFunction
    pub fn domain_extent(&self) -> Option<Extent> {
        match self {
            Tiling::Scalar(Extent::Function { domain, .. }) => Some(*domain.clone()),
            Tiling::SealedFunction { domain, .. } => Some(domain.clone()),
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
            ),
            Tiling::Aggregation { kind, accumulator } => Tile::Aggregation {
                kind: kind.clone(),
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
            Tiling::SealedFunction { domain, codomain } => write!(f, "SF({domain:?} → {codomain})"),
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
        /// Domain values of the known elements of the function
        domain: ColumnValue,
        /// Codomain of the function expressed as an implicitly-vectorized Tile.
        codomain: Box<Tile>,
        /// Represents a region of the codomain for which no new elements will ever be seen.
        domain_predicate: Predicate,
    },
    /// A two-level curried function.
    ///
    /// Stored in a Compressed Sparse Row (CSR)-like layout: `domain1` is sorted so lookups can be done
    /// in O(log n) via binary search, `offsets[i]` is the start index in
    /// `codomain` and `domain2` for `domain1[i]`, and `codomain` is the flattened sequence of
    /// all codomain values across all groups.  Group `i` occupies
    /// `codomain[offsets[i]..offsets[i+1]]` (or `codomain[offsets[i]..]` for
    /// the last group).  Because `codomain` is a single `ColumnValue`,
    /// vectorized transformations over the full codomain are straightforward.
    CurriedFunction {
        /// Sorted domain keys, enabling O(log n) lookup by binary search.
        domain1: ColumnValue,
        /// Start offsets into `domain2` and `codomain`, one per value in `domain1`.
        offsets: ColumnValue,
        /// Flattened domain2 values
        domain2: ColumnValue,
        /// Flattened codomain values; supports vectorized transformations.
        codomain: ColumnValue,
        /// Whether all domain keys and their value lists have been fully received.
        domain_predicate: Predicate,
    },
    /// A Tile representing the state of a scalar aggregation.
    Aggregation {
        /// The type of aggregate
        kind: AggregateKind,
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
            Tile::CurriedFunction { domain1, .. } => domain1.len(),
            Tile::Aggregation { accumulator, .. } => accumulator.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Check whether this tile could have been produced by `tiling`.
    pub fn check_from(&self, tiling: &Tiling) -> bool {
        match (self, tiling) {
            (Tile::Scalar(cv), Tiling::Scalar(extent)) => cv.is_compatible_with_extent(extent),
            (Tile::Record(tile_fields), Tiling::Record(tiling_fields)) => {
                tile_fields.len() == tiling_fields.len()
                    && tile_fields
                        .iter()
                        .all(|(k, t)| tiling_fields.get(k).is_some_and(|s| t.check_from(s)))
            }
            (
                Tile::SealedFunction {
                    domain,
                    codomain: codomain_tile,
                    ..
                },
                Tiling::SealedFunction {
                    domain: domain_extent,
                    codomain: codomain_tiling,
                },
            ) => {
                domain.is_compatible_with_extent(domain_extent)
                    && codomain_tile.check_from(codomain_tiling)
            }
            (Tile::CurriedFunction { .. }, Tiling::CurriedFunction { .. }) => true,
            (Tile::Aggregation { .. }, Tiling::Aggregation { .. }) => true,
            _ => false,
        }
    }

    pub fn is_terminal(&self) -> bool {
        match self {
            Tile::Scalar(cv) => !cv.is_empty(),
            Tile::Record(m) => m.values().all(Tile::is_terminal),
            Tile::SealedFunction {
                domain_predicate, ..
            } => domain_predicate.as_bool().unwrap_or(false),
            Tile::CurriedFunction {
                domain_predicate, ..
            } => domain_predicate.as_bool().unwrap_or(false),
            Tile::Aggregation { terminal, .. } => {
                terminal.as_single().map(|t| t.as_bool()).unwrap_or(false)
            }
        }
    }

    /// Merge the contents of `other` into `self`.  Requires the two tiles to be compatible (i.e. non-overlapping)
    pub fn merge(&mut self, other: Tile) {
        match (&mut *self, other) {
            // Append: handles both "unknown → known" (empty + non-empty) and the
            // vectorized case where a Scalar tile holds one value per domain entry inside
            // a SealedFunction/Record codomain.
            (Tile::Scalar(s), Tile::Scalar(o)) => s.append(o),
            (
                Tile::Aggregation {
                    kind: s_kind,
                    accumulator: s_acc,
                    terminal: s_term,
                },
                Tile::Aggregation {
                    kind: o_kind,
                    accumulator: o_acc,
                    terminal: o_term,
                },
            ) => {
                assert_eq!(*s_kind, o_kind);
                s_kind.accumulate(s_acc, &o_acc, 0, s_acc.len());
                let taken = std::mem::replace(s_term, ColumnValue::Units(0));
                *s_term = apply_binop_column(BinOpKind::BoolLogic(LogicKind::Or), taken, &o_term);
            }
            (
                Tile::SealedFunction {
                    domain: s_domain,
                    codomain: s_codomain,
                    domain_predicate: s_pred,
                },
                Tile::SealedFunction {
                    domain: o_domain,
                    codomain: o_codomain,
                    domain_predicate: o_pred,
                },
            ) => {
                s_domain.append(o_domain);
                s_codomain.merge(*o_codomain);
                *s_pred = s_pred.union(&o_pred);
            }
            (
                Tile::CurriedFunction {
                    domain1: s_domain1,
                    offsets: s_offsets,
                    domain2: s_domain2,
                    codomain: s_codomain,
                    domain_predicate: s_pred,
                },
                Tile::CurriedFunction {
                    domain1: o_domain1,
                    offsets: o_offsets,
                    domain2: o_domain2,
                    codomain: o_codomain,
                    domain_predicate: o_pred,
                },
            ) => {
                // Shift o's offsets by the current size of s's domain2 so they index into
                // the combined domain2 = [s_domain2..., o_domain2...].
                let s_d2_len = s_domain2.len();
                let mut o_offsets = o_offsets;
                s_domain1.append(o_domain1);
                o_offsets.for_each_uint(|u| *u += s_d2_len);
                s_offsets.append(o_offsets);
                s_domain2.append(o_domain2);
                s_codomain.append(o_codomain);
                *s_pred = s_pred.union(&o_pred);
            }
            (Tile::Record(s_fields), Tile::Record(ref mut o_fields)) => {
                assert_eq!(s_fields.len(), o_fields.len());
                s_fields.iter_mut().for_each(|(f, t)| {
                    t.merge(
                        o_fields
                            .remove(f)
                            .unwrap_or_else(|| panic!("Record missing field {f}")),
                    )
                })
            }
            (s, o) => panic!("Incompatible tiles {s:?} and {o:?}"),
        };
        debug_assert!(validate_tile(self), "Invalid tile: {self:?}");
    }

    /// Retain in-place only the elements at positions where `mask[i]` is true.
    pub fn retain(&mut self, mask: &BitVec) {
        match self {
            Tile::Scalar(cv) => cv.retain(mask),
            Tile::Record(m) => m.values_mut().for_each(|t| t.retain(mask)),
            Tile::SealedFunction {
                domain, codomain, ..
            } => {
                domain.retain(mask);
                codomain.retain(mask);
            }
            Tile::CurriedFunction {
                domain1,
                offsets,
                domain2,
                codomain,
                ..
            } => {
                // The mask is over the flat domain2/codomain rows.
                assert_eq!(
                    mask.len(),
                    domain2.len(),
                    "retain mask length must equal domain2 length"
                );
                // Clone offsets so we can write to *offsets afterward.
                let old_offsets = match &*offsets {
                    ColumnValue::UInts(v) => v.clone(),
                    _ => panic!("CurriedFunction offsets must be UInts"),
                };
                let n = domain1.len();
                let domain2_total = domain2.len();
                // Recompute domain1 and offsets, dropping groups with no survivors.
                // Collect kept domain2 indices in order so that group contiguity is
                // preserved in the compacted flat arrays.
                let mut new_domain1_keep: Vec<usize> = Vec::new();
                let mut new_offsets: Vec<usize> = Vec::new();
                let mut kept_indices: Vec<usize> = Vec::new();
                for i in 0..n {
                    let start = old_offsets[i];
                    let end = if i + 1 < n {
                        old_offsets[i + 1]
                    } else {
                        domain2_total
                    };
                    let group_kept: Vec<usize> = (start..end).filter(|&j| mask[j]).collect();
                    if !group_kept.is_empty() {
                        new_offsets.push(kept_indices.len());
                        new_domain1_keep.push(i);
                        kept_indices.extend(group_kept);
                    }
                }
                let kept_len = kept_indices.len();
                *domain1 = domain1
                    .select_indices(new_domain1_keep.iter().cloned(), new_domain1_keep.len());
                *offsets = ColumnValue::UInts(new_offsets);
                *domain2 = domain2.select_indices(kept_indices.iter().cloned(), kept_len);
                *codomain = codomain.select_indices(kept_indices.iter().cloned(), kept_len);
            }
            _ => panic!("retain not supported for {self:?}"),
        }
    }

    /// Removes all data in this tile that is specified by the guard.
    pub fn remove_guarded(&mut self, guard: TileGuard) {
        match (&mut *self, guard) {
            // If the guard is empty, do nothing.
            (_, g) if g.is_empty() => {}
            // Scalar: universal guard clears the scalar; empty guard is a no-op.
            (Tile::Scalar(cv), TileGuard::Scalar(true)) => {
                *cv = cv.select_indices(std::iter::empty(), 0);
            }
            (Tile::Scalar(_), TileGuard::Scalar(false)) => {}
            // Aggregation: universal guard clears all state; empty guard is a no-op.
            (
                Tile::Aggregation {
                    accumulator,
                    terminal,
                    ..
                },
                TileGuard::Aggregation(true),
            ) => {
                *accumulator = accumulator.select_indices(std::iter::empty(), 0);
                *terminal = terminal.select_indices(std::iter::empty(), 0);
            }
            (Tile::Aggregation { .. }, TileGuard::Aggregation(false)) => {}
            // Record: recurse per field.
            (Tile::Record(fields), TileGuard::Record(mut guards)) => {
                for (k, t) in fields.iter_mut() {
                    if let Some(g) = guards.remove(k) {
                        t.remove_guarded(g);
                    }
                }
            }
            // Or: apply each arm in sequence.  Each arm removes the elements
            // it describes; together they remove the union of all arms.
            (tile, TileGuard::Or(arms)) => {
                for arm in arms {
                    tile.remove_guarded(arm);
                }
            }
            // SealedFunction: remove domain+codomain entries whose domain value is in the predicate.
            // `domain_predicate` is deliberately NOT updated here: it tracks upstream-committed
            // rows (set via `merge`) and remaining rows are already covered by `from_cv(domain)`
            // in `to_guard()`.  Updating it with `from_cv(remaining)` would be redundant and
            // would cause it to diverge between tiles that share the same domain but receive
            // `remove_guarded` at different times (e.g. the two inputs of a Zip).
            (
                Tile::SealedFunction {
                    domain, codomain, ..
                },
                TileGuard::Function(FunctionGuard::Domain(pred)),
            ) => {
                let mask: BitVec = (0..domain.len())
                    .map(|i| !pred.contains(&domain.index_at(i)))
                    .collect();
                domain.retain(&mask);
                codomain.retain(&mask);
            }
            // CurriedFunction: remove domain2+codomain entries whose domain2 value is in the predicate,
            // and prune any domain1 groups that become empty.
            (
                tile @ Tile::CurriedFunction { .. },
                TileGuard::Function(FunctionGuard::Codomain(inner)),
            ) => {
                let TileGuard::Function(FunctionGuard::Domain(pred)) = *inner else {
                    unimplemented!(
                        "CurriedFunction remove_guarded only supports Codomain(Domain(pred))"
                    )
                };
                // Borrow domain2 only long enough to build the survival mask, then
                // release so retain can take the mutable borrow.
                let mask: BitVec = {
                    let Tile::CurriedFunction { domain2, .. } = &*tile else {
                        unreachable!()
                    };
                    (0..domain2.len())
                        .map(|i| !pred.contains(&domain2.index_at(i)))
                        .collect()
                };
                // domain_predicate tracks domain1 completeness and is not updated on removal.
                tile.retain(&mask);
            }
            (s, g) => panic!("Incompatible tile and guard in remove_guarded: {s:?} and {g:?}"),
        }
    }

    /// Creates a TileGuard representing the contents of this Tile.
    /// For Scalar: universal if the scalar is known and empty otherwise
    /// For Aggregation: universal if terminal and empty otherwise
    /// For SealedFunction: Domain predicate for all domain values
    /// For CurriedFunction, Codomain(Domain(predicate)) for all domain2 values (TODO for now we assume unique domain2)
    pub fn to_guard(&self) -> TileGuard {
        match self {
            Tile::Scalar(cv) => TileGuard::Scalar(!cv.is_empty()),
            Tile::Aggregation { terminal, .. } => {
                TileGuard::Aggregation(terminal.as_single().map(|t| t.as_bool()).unwrap_or(false))
            }
            Tile::Record(m) => {
                TileGuard::Record(m.iter().map(|(k, t)| (k.clone(), t.to_guard())).collect())
            }
            Tile::SealedFunction {
                domain,
                domain_predicate,
                ..
            } => TileGuard::Function(FunctionGuard::Domain(
                Predicate::from_column_value(domain).union(domain_predicate),
            )),
            Tile::CurriedFunction { domain2, .. } => {
                TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Function(
                    FunctionGuard::Domain(Predicate::from_column_value(domain2)),
                ))))
            }
        }
    }

    /// Creates a Tile::CurriedFunction and does dev-build-only validation for correct structure.
    pub fn curried_function(
        domain1: ColumnValue,
        offsets: ColumnValue,
        domain2: ColumnValue,
        codomain: ColumnValue,
        domain_predicate: Predicate,
    ) -> Tile {
        let result = Tile::CurriedFunction {
            domain1,
            offsets,
            domain2,
            codomain,
            domain_predicate,
        };
        debug_assert!(
            validate_tile(&result),
            "Invalid curried function: {result:?}"
        );
        result
    }
}

pub fn validate_tile(tile: &Tile) -> bool {
    match tile {
        Tile::CurriedFunction {
            domain1,
            offsets,
            domain2,
            codomain,
            domain_predicate: _,
        } => {
            let ColumnValue::UInts(offsets) = offsets else {
                return false;
            };
            let domain2_values: Vec<_> = domain2.clone().drain_to_value_iter().collect();
            domain2.len() == codomain.len()
                && HashSet::<Value>::from_iter(domain1.clone().drain_to_value_iter()).len()
                    == domain1.len()
                && offsets.windows(2).all(|w| w[0] < w[1])
                && offsets.windows(2).all(|w| {
                    w[1] - w[0]
                        == HashSet::<Value>::from_iter(domain2_values[w[0]..w[1]].iter().cloned())
                            .len()
                })
                && offsets.last().is_none_or(|o| *o < domain2.len())
        }
        Tile::SealedFunction {
            domain, codomain, ..
        } => {
            HashSet::<Value>::from_iter(domain.clone().drain_to_value_iter()).len() == domain.len()
                && domain.len() == codomain.len()
        }
        _ => true,
    }
}

/// Specifies a sub-region of interest within a [`Tile`], used for demand-driven
/// computation and incremental release.
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
    fn flatten_or(arms: Vec<TileGuard>) -> TileGuard {
        let flat: Vec<TileGuard> = arms
            .into_iter()
            .flat_map(|g| match g {
                TileGuard::Or(inner) => inner,
                other => vec![other],
            })
            .collect();
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
            TileGuard::Function(g) => g.is_univeral(),
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
}

/// A guard on a [Tile::SealedFunction] or [Tile::CurriedFunction], specifying
/// which part of the function is of interest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FunctionGuard {
    Domain(Predicate),
    Codomain(Box<TileGuard>),
}

impl FunctionGuard {
    pub fn intersect(&self, other: &FunctionGuard) -> FunctionGuard {
        match (self, other) {
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
            (FunctionGuard::Domain(p1), FunctionGuard::Domain(p2)) => {
                FunctionGuard::Domain(p1.union(p2))
            }
            (FunctionGuard::Codomain(p1), FunctionGuard::Codomain(p2)) => {
                FunctionGuard::Codomain(Box::new(p1.union(p2)))
            }
            _ => todo!("Handle Domain + Codomain guards together"),
        }
    }

    pub fn is_univeral(&self) -> bool {
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

/// A predicate that describes a subset of values in an extent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Predicate {
    True,
    False,
    LessThanEq(Value),
    Intervals(IntervalSet<Value>),
    /// Represents the AND of each of the sub-predicates.
    Record(HashMap<String, Predicate>),
    /// The union of multiple predicates — admits any value accepted by any arm.
    ///
    /// Produced when two [`Predicate::Record`] predicates are unioned, since OR
    /// cannot be pushed through the AND semantics of a record predicate.
    ///
    /// Invariant: arms never directly nest another `Or` (always flattened by
    /// [`Predicate::flatten_or`]).
    Or(Vec<Predicate>),
}

impl Predicate {
    /// Builds a `Predicate` from a list of arms, flattening any nested `Or`
    /// variants.  Returns the single element directly when `arms` has length
    /// one to avoid gratuitous wrapping.
    fn flatten_or(arms: Vec<Predicate>) -> Predicate {
        let flat: Vec<Predicate> = arms
            .into_iter()
            .flat_map(|p| match p {
                Predicate::Or(inner) => inner,
                other => vec![other],
            })
            .collect();
        if flat.is_empty() {
            unreachable!("flatten_or called with no arms");
        }
        // Drop any arm that is subsumed by another arm in the list.
        // When two arms mutually subsume each other (i.e., are semantically
        // equivalent) the one with the lower index is kept, avoiding both
        // being removed.  The condition reads: remove arm[i] if there exists
        // arm[j] (j ≠ i) that subsumes arm[i], unless arm[i] also subsumes
        // arm[j] and i < j (in which case we prefer arm[i]).
        let keep: Vec<bool> = flat
            .iter()
            .enumerate()
            .map(|(i, arm)| {
                !flat.iter().enumerate().any(|(j, other)| {
                    j != i && other.subsumes(arm) && (j < i || !arm.subsumes(other))
                })
            })
            .collect();
        let reduced: Vec<Predicate> = flat
            .into_iter()
            .zip(keep)
            .filter_map(|(p, k)| k.then_some(p))
            .collect();
        match reduced.len() {
            0 => unreachable!("flatten_or: all arms were removed by subsumption"),
            1 => reduced.into_iter().next().unwrap(),
            _ => Predicate::Or(reduced),
        }
    }

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
            // Or is true if any arm is true; false if all arms are false.
            Predicate::Or(arms) => {
                if arms.iter().any(|p| p.as_bool() == Some(true)) {
                    Some(true)
                } else if arms.iter().all(|p| p.as_bool() == Some(false)) {
                    Some(false)
                } else {
                    None
                }
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
            // Or distributes over intersect: (A | B) & C = (A & C) | (B & C).
            (Predicate::Or(arms), _) => {
                Predicate::flatten_or(arms.iter().map(|a| a.intersect(other)).collect())
            }
            (_, Predicate::Or(arms)) => {
                Predicate::flatten_or(arms.iter().map(|a| self.intersect(a)).collect())
            }
            _ => panic!("Cannot intersect incompatible predicates: {self:?} and {other:?}"),
        }
    }

    /// Returns the predicate that admits exactly the values accepted by either `self` or `other`.
    pub fn union(&self, other: &Predicate) -> Predicate {
        match (self, other) {
            // True is the universal predicate: annihilator under union.
            (Predicate::True, _) | (_, Predicate::True) => Predicate::True,
            // False is the empty predicate: identity under union.
            (Predicate::False, p) | (p, Predicate::False) => p.clone(),
            // Two upper bounds: keep the looser (larger) one.
            (Predicate::LessThanEq(a), Predicate::LessThanEq(b)) => match a.partial_cmp(b) {
                Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal) => {
                    Predicate::LessThanEq(a.clone())
                }
                Some(std::cmp::Ordering::Less) => Predicate::LessThanEq(b.clone()),
                None => panic!("Cannot compare values in LessThanEq predicates: {a:?} and {b:?}"),
            },
            // Upper bound unioned with an interval set: merge (-∞, v] into the set.
            (Predicate::LessThanEq(v), Predicate::Intervals(s))
            | (Predicate::Intervals(s), Predicate::LessThanEq(v)) => {
                let upper = IntervalSet::new(vec![Interval::unbound_closed(v.clone())]);
                Predicate::Intervals(s.union(&upper))
            }
            // Two interval sets: standard set union.
            (Predicate::Intervals(a), Predicate::Intervals(b)) => Predicate::Intervals(a.union(b)),
            // Record predicates have AND semantics, so their union cannot be
            // represented as a single Record predicate.  Wrap in Or instead.
            (Predicate::Record(_), Predicate::Record(_)) => {
                Predicate::flatten_or(vec![self.clone(), other.clone()])
            }
            // Or: accumulate all arms, flattening nested Ors.
            (Predicate::Or(arms), _) => {
                let mut new_arms = arms.clone();
                new_arms.push(other.clone());
                Predicate::flatten_or(new_arms)
            }
            (_, Predicate::Or(arms)) => {
                let mut new_arms = vec![self.clone()];
                new_arms.extend(arms.iter().cloned());
                Predicate::flatten_or(new_arms)
            }
            _ => panic!("Cannot union incompatible predicates: {self:?} and {other:?}"),
        }
    }

    /// Returns `true` if `value` is admitted by this predicate.
    pub fn contains(&self, value: &Value) -> bool {
        match self {
            Predicate::True => true,
            Predicate::False => false,
            Predicate::LessThanEq(v) => value
                .partial_cmp(v)
                .map(|o| o != std::cmp::Ordering::Greater)
                .unwrap_or(false),
            Predicate::Intervals(s) => s.contains(value),
            Predicate::Record(m) => match value {
                Value::Record(fields) => m
                    .iter()
                    .all(|(k, p)| fields.get(k).map(|v| p.contains(v)).unwrap_or(false)),
                _ => false,
            },
            // Or: value is admitted if any arm admits it.
            Predicate::Or(arms) => arms.iter().any(|a| a.contains(value)),
        }
    }

    /// Returns `true` if every value admitted by `other` is also admitted by `self`.
    ///
    /// In set terms: `other ⊆ self`.  Used by [`Predicate::flatten_or`] to
    /// eliminate redundant arms: if arm A subsumes arm B, B adds nothing to the
    /// union and can be dropped.
    pub fn subsumes(&self, other: &Predicate) -> bool {
        match (self, other) {
            // True is the universal set; it subsumes everything.
            (Predicate::True, _) => true,
            // A non-True predicate cannot subsume the universal set.
            (_, Predicate::True) => false,
            // Everything subsumes the empty set.
            (_, Predicate::False) => true,
            // The empty set subsumes nothing non-empty (non-empty handled above).
            (Predicate::False, _) => false,
            // Two upper bounds: (-∞,a] ⊇ (-∞,b] iff a >= b.
            (Predicate::LessThanEq(a), Predicate::LessThanEq(b)) => a
                .partial_cmp(b)
                .map(|o| o != std::cmp::Ordering::Less)
                .unwrap_or(false),
            // (-∞,v] subsumes an interval set iff every interval in s fits within (-∞,v].
            //
            // Note: `IntervalSet::contains(&IntervalSet)` has a known bug in the
            // `intervalsets` crate (it iterates `self` instead of `rhs`), so we
            // iterate the intervals of the rhs ourselves throughout this method.
            (Predicate::LessThanEq(v), Predicate::Intervals(s)) => {
                let upper = Interval::unbound_closed(v.clone());
                s.intervals().iter().all(|iv| upper.contains(iv))
            }
            // An interval set subsumes (-∞,v] only if it contains the whole half-line.
            (Predicate::Intervals(s), Predicate::LessThanEq(v)) => {
                s.contains(&Interval::unbound_closed(v.clone()))
            }
            // Interval set containment: self ⊇ other iff every interval of other
            // is contained within some interval of self.
            (Predicate::Intervals(a), Predicate::Intervals(b)) => {
                b.intervals().iter().all(|iv| a.contains(iv))
            }
            // Record (AND semantics): self ⊇ other iff every field of self subsumes
            // the corresponding field of other.
            (Predicate::Record(m1), Predicate::Record(m2)) if m1.len() == m2.len() => m1
                .iter()
                .all(|(k, p1)| m2.get(k).is_some_and(|p2| p1.subsumes(p2))),
            // A union subsumes `other` if any of its arms subsumes it.
            (Predicate::Or(arms), _) => arms.iter().any(|a| a.subsumes(other)),
            // self subsumes a union iff it subsumes every arm.
            (_, Predicate::Or(arms)) => arms.iter().all(|a| self.subsumes(a)),
            // Incompatible variants (e.g. Record vs LessThanEq): conservative false.
            _ => false,
        }
    }

    /// Converts a batch of concrete domain values into the predicate admitting exactly those values.
    ///
    /// Each scalar value becomes a point interval; records are split field-by-field.
    pub(super) fn from_column_value(cv: &ColumnValue) -> Predicate {
        match cv {
            // Unit is a single-value type; any Unit value satisfies the predicate.
            ColumnValue::Units(len) => {
                if *len > 0 {
                    Predicate::True
                } else {
                    Predicate::False
                }
            }
            ColumnValue::Ints(v) => vec_to_predicate(v),
            ColumnValue::UInts(v) => vec_to_predicate(v),
            ColumnValue::Bools(v) => {
                let mut vec = Vec::new();
                if v.count_ones() > 0 {
                    vec.push(true)
                }
                if v.count_zeros() > 0 {
                    vec.push(false)
                }
                vec_to_predicate(&vec)
            }
            ColumnValue::Strings(v) => vec_to_predicate(v),
            ColumnValue::Variants(v) => vec_to_predicate(v),
            ColumnValue::Records(fields) => {
                let len = fields.values().next().map_or(0, |cv| cv.len());
                if len == 0 {
                    return Predicate::False;
                }
                // Records have no natural total order, so we cannot represent
                // the set as intervals.  Instead, build one point predicate per
                // row and combine them with Or.
                Predicate::flatten_or(
                    (0..len)
                        .map(|i| {
                            Predicate::Record(
                                fields
                                    .iter()
                                    .map(|(k, cv)| {
                                        let single = cv.select_indices(std::iter::once(i), 1);
                                        (k.clone(), Predicate::from_column_value(&single))
                                    })
                                    .collect(),
                            )
                        })
                        .collect(),
                )
            }
            ColumnValue::FunctionBindings { .. } => {
                panic!("Cannot build predicate from FunctionBindings")
            }
        }
    }
}

/// Converts a slice of values into a `Predicate::Intervals` with adjacent discrete values merged
/// into contiguous ranges.
///
/// `IntervalSet::new` has a fast-path that skips `merge_sorted` when intervals are already sorted
/// and non-overlapping — which point intervals always are. By sorting the values ourselves and
/// explicitly extending runs of adjacent discrete values, we produce a minimal interval set.
fn vec_to_predicate<T: Clone>(data: &[T]) -> Predicate
where
    Value: From<T>,
{
    if data.is_empty() {
        return Predicate::False;
    }

    // Sort and deduplicate so we can do a single linear scan for adjacent runs.
    let mut vals: Vec<Value> = data.iter().map(|x| Value::from(x.clone())).collect();
    vals.sort_by(|a, b| {
        a.partial_cmp(b)
            .expect("values in a ColumnValue column must be mutually comparable")
    });
    vals.dedup();

    // Walk the sorted values, extending the current interval whenever the next value
    // is the immediate successor of the current end.
    let mut intervals: Vec<Interval<Value>> = Vec::new();
    let mut start = vals[0].clone();
    let mut end = vals[0].clone();
    for v in &vals[1..] {
        if end.try_adjacent(Side::Right).as_ref() == Some(v) {
            end = v.clone();
        } else {
            intervals.push(Interval::closed(start, end));
            start = v.clone();
            end = v.clone();
        }
    }
    intervals.push(Interval::closed(start, end));

    // Intervals are already sorted and merged, so skip the invariant check.
    Predicate::Intervals(IntervalSet::new_unchecked(intervals))
}

/// Apply `f` to every value in a `HashMap`, producing a new map with the same keys.
pub(super) fn transform_hashmap_values<K: Clone + Eq + Hash, InputV, V, F: Fn(&InputV) -> V>(
    source: &HashMap<K, InputV>,
    f: F,
) -> HashMap<K, V> {
    source.iter().map(|(k, v)| (k.clone(), f(v))).collect()
}

/// Sort a `Tile::SealedFunction` by its domain values for deterministic comparison.
///
/// Handles `Ints` and `UInts` domains paired with `Scalar(Ints)` codomains; all
/// other tile forms are returned unchanged.  This is needed wherever key order
/// depends on [`HashMap`] iteration order (e.g. GroupBy, MapSource).
pub fn sort_sealed_function_by_domain(tile: Tile) -> Tile {
    /// Sort parallel `domain` and `cod_ints` vectors together by `domain` key,
    /// then rebuild the tile.
    fn sort_and_rebuild<K: Ord + Clone>(
        domain_vals: Vec<K>,
        cod_ints: Vec<i64>,
        domain_predicate: Predicate,
        mk_domain: impl Fn(Vec<K>) -> ColumnValue,
    ) -> Tile {
        let mut pairs: Vec<(K, i64)> = domain_vals.into_iter().zip(cod_ints).collect();
        pairs.sort_by(|(a, _), (b, _)| a.cmp(b));
        let (sorted_d, sorted_c): (Vec<K>, Vec<i64>) = pairs.into_iter().unzip();
        Tile::SealedFunction {
            domain: mk_domain(sorted_d),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(sorted_c))),
            domain_predicate,
        }
    }

    match tile {
        Tile::SealedFunction {
            domain,
            codomain,
            domain_predicate,
        } => match (*codomain, domain) {
            (Tile::Scalar(ColumnValue::Ints(cod_ints)), ColumnValue::Ints(dom)) => {
                sort_and_rebuild(dom, cod_ints, domain_predicate, ColumnValue::Ints)
            }
            (Tile::Scalar(ColumnValue::Ints(cod_ints)), ColumnValue::UInts(dom)) => {
                sort_and_rebuild(dom, cod_ints, domain_predicate, ColumnValue::UInts)
            }
            (other_codomain, domain) => Tile::SealedFunction {
                domain,
                codomain: Box::new(other_codomain),
                domain_predicate,
            },
        },
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use intervalsets::ops::Contains;

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
        Extent::uint_range(end)
    }

    fn sealed(domain: Extent, codomain: Extent) -> Tiling {
        Tiling::SealedFunction {
            domain,
            codomain: Box::new(Tiling::Scalar(codomain)),
        }
    }

    fn curried(domain1: Extent, domain2: Extent, codomain: Extent) -> Tiling {
        Tiling::CurriedFunction {
            domain1,
            domain2,
            codomain,
        }
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
        assert!(curried(int(), int(), bool_ext())
            .universal_guard()
            .is_universal());
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
        // CurriedFunction has no structured codomain tiling.
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

    // ── Predicate::from_column_value ─────────────────────────────────────────

    #[test]
    fn from_column_value_empty_ints_is_false() {
        assert_eq!(
            Predicate::from_column_value(&ColumnValue::Ints(vec![])),
            Predicate::False
        );
    }

    #[test]
    fn from_column_value_single_int() {
        let p = Predicate::from_column_value(&ColumnValue::Ints(vec![7]));
        let Predicate::Intervals(s) = p else {
            panic!("expected Intervals");
        };
        // The single point [7, 7] should contain 7 but not 6 or 8.
        assert!(s.contains(&Value::Int(7)));
        assert!(!s.contains(&Value::Int(6)));
        assert!(!s.contains(&Value::Int(8)));
    }

    #[test]
    fn from_column_value_multiple_ints_contains_all() {
        let p = Predicate::from_column_value(&ColumnValue::Ints(vec![1, 3, 5]));
        let Predicate::Intervals(s) = p else {
            panic!("expected Intervals");
        };
        assert!(s.contains(&Value::Int(1)));
        assert!(s.contains(&Value::Int(3)));
        assert!(s.contains(&Value::Int(5)));
        assert!(!s.contains(&Value::Int(2)));
        assert!(!s.contains(&Value::Int(4)));
    }

    #[test]
    fn from_column_value_uints() {
        let p = Predicate::from_column_value(&ColumnValue::UInts(vec![0, 2]));
        let Predicate::Intervals(s) = p else {
            panic!("expected Intervals");
        };
        assert!(s.contains(&Value::UInt(0)));
        assert!(s.contains(&Value::UInt(2)));
        assert!(!s.contains(&Value::UInt(1)));
    }

    #[test]
    fn from_column_value_compact() {
        let p = Predicate::from_column_value(&ColumnValue::UInts(vec![0, 1, 2, 5, 6, 7]));
        let Predicate::Intervals(s) = p else {
            panic!("expected Intervals");
        };
        assert_eq!(s.intervals().len(), 2, "{s:?}");
    }

    #[test]
    fn from_column_value_empty_uints_is_false() {
        assert_eq!(
            Predicate::from_column_value(&ColumnValue::UInts(vec![])),
            Predicate::False
        );
    }

    #[test]
    fn from_column_value_bools_both_values() {
        let mut bv = BitVec::from_elem(2, false);
        bv.set(0, true);
        bv.set(1, false);
        let p = Predicate::from_column_value(&ColumnValue::Bools(bv));
        let Predicate::Intervals(s) = p else {
            panic!("expected Intervals");
        };
        assert!(s.contains(&Value::Bool(true)));
        assert!(s.contains(&Value::Bool(false)));
    }

    #[test]
    fn from_column_value_bools_only_true() {
        let bv = BitVec::from_elem(3, true);
        let p = Predicate::from_column_value(&ColumnValue::Bools(bv));
        let Predicate::Intervals(s) = p else {
            panic!("expected Intervals");
        };
        assert!(s.contains(&Value::Bool(true)));
        assert!(!s.contains(&Value::Bool(false)));
    }

    #[test]
    fn from_column_value_empty_bools_is_false() {
        assert_eq!(
            Predicate::from_column_value(&ColumnValue::Bools(BitVec::new())),
            Predicate::False
        );
    }

    #[test]
    fn from_column_value_units_nonempty_is_true() {
        assert_eq!(
            Predicate::from_column_value(&ColumnValue::Units(3)),
            Predicate::True
        );
    }

    #[test]
    fn from_column_value_units_empty_is_false() {
        assert_eq!(
            Predicate::from_column_value(&ColumnValue::Units(0)),
            Predicate::False
        );
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

    // ── Predicate::union ──────────────────────────────────────────────────────

    /// Helper: assert that a `Predicate::Intervals` contains / does not contain a value.
    fn intervals_contains(p: &Predicate, v: Value) -> bool {
        let Predicate::Intervals(s) = p else {
            panic!("expected Predicate::Intervals, got {p:?}");
        };
        s.contains(&v)
    }

    // True is the annihilator: True ∪ x = True and x ∪ True = True.
    #[test]
    fn union_true_annihilates_lhs() {
        assert_eq!(
            Predicate::True.union(&Predicate::LessThanEq(Value::UInt(5))),
            Predicate::True
        );
    }

    #[test]
    fn union_true_annihilates_rhs() {
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(5)).union(&Predicate::True),
            Predicate::True
        );
    }

    // False is the identity: False ∪ x = x and x ∪ False = x.
    #[test]
    fn union_false_identity_lhs() {
        let p = Predicate::LessThanEq(Value::UInt(3));
        assert_eq!(Predicate::False.union(&p), p);
    }

    #[test]
    fn union_false_identity_rhs() {
        let p = Predicate::LessThanEq(Value::UInt(3));
        assert_eq!(p.union(&Predicate::False), p);
    }

    // LessThanEq ∪ LessThanEq: keep the looser (larger) bound.
    #[test]
    fn union_less_than_eq_keeps_larger() {
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(7)).union(&Predicate::LessThanEq(Value::UInt(3))),
            Predicate::LessThanEq(Value::UInt(7))
        );
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(3)).union(&Predicate::LessThanEq(Value::UInt(7))),
            Predicate::LessThanEq(Value::UInt(7))
        );
    }

    #[test]
    fn union_less_than_eq_equal_bounds() {
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(5)).union(&Predicate::LessThanEq(Value::UInt(5))),
            Predicate::LessThanEq(Value::UInt(5))
        );
    }

    // LessThanEq ∪ Intervals: result is Intervals containing a left-unbounded interval.
    #[test]
    fn union_less_than_eq_with_intervals_lhs() {
        // (-∞, 3] ∪ {7} → Intervals containing both 0, 3, and 7; but not 4 or 6.
        let intervals = Predicate::from_column_value(&ColumnValue::UInts(vec![7]));
        let result = Predicate::LessThanEq(Value::UInt(3)).union(&intervals);
        assert!(intervals_contains(&result, Value::UInt(0)), "0 in (-inf,3]");
        assert!(intervals_contains(&result, Value::UInt(3)), "3 in (-inf,3]");
        assert!(
            !intervals_contains(&result, Value::UInt(4)),
            "4 not in result"
        );
        assert!(
            intervals_contains(&result, Value::UInt(7)),
            "7 in point set"
        );
    }

    #[test]
    fn union_less_than_eq_with_intervals_rhs() {
        // {7} ∪ (-∞, 3] — commutative, same outcome.
        let intervals = Predicate::from_column_value(&ColumnValue::UInts(vec![7]));
        let result = intervals.union(&Predicate::LessThanEq(Value::UInt(3)));
        assert!(intervals_contains(&result, Value::UInt(3)));
        assert!(!intervals_contains(&result, Value::UInt(4)));
        assert!(intervals_contains(&result, Value::UInt(7)));
    }

    // Intervals ∪ Intervals: standard set union.
    #[test]
    fn union_disjoint_interval_sets() {
        // {1, 2} ∪ {5, 6} → values 1, 2, 5, 6 present; 3, 4 absent.
        let a = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2]));
        let b = Predicate::from_column_value(&ColumnValue::UInts(vec![5, 6]));
        let result = a.union(&b);
        for v in [1usize, 2, 5, 6] {
            assert!(
                intervals_contains(&result, Value::UInt(v)),
                "{v} should be in union"
            );
        }
        for v in [3usize, 4] {
            assert!(
                !intervals_contains(&result, Value::UInt(v)),
                "{v} should not be in union"
            );
        }
    }

    #[test]
    fn union_overlapping_interval_sets_merges() {
        // {2, 3, 4} ∪ {3, 4, 5} → {2, 3, 4, 5}, all present.
        let a = Predicate::from_column_value(&ColumnValue::UInts(vec![2, 3, 4]));
        let b = Predicate::from_column_value(&ColumnValue::UInts(vec![3, 4, 5]));
        let result = a.union(&b);
        for v in [2usize, 3, 4, 5] {
            assert!(intervals_contains(&result, Value::UInt(v)));
        }
    }

    // Record ∪ Record: cannot push OR through AND, result must be Or([r1, r2]).
    #[test]
    fn union_record_predicates_produces_or() {
        // Neither record subsumes the other: r1 is looser on x, r2 is looser on y.
        // r1 admits {x≤5, y≤3}; r2 admits {x≤3, y≤7}.  Each admits records the
        // other does not, so neither is redundant and the union must be an Or.
        let r1 = record_pred(&[
            ("x", Predicate::LessThanEq(Value::UInt(5))),
            ("y", Predicate::LessThanEq(Value::UInt(3))),
        ]);
        let r2 = record_pred(&[
            ("x", Predicate::LessThanEq(Value::UInt(3))),
            ("y", Predicate::LessThanEq(Value::UInt(7))),
        ]);
        let result = r1.union(&r2);
        // Must be an Or — OR cannot be pushed through AND for records.
        assert!(
            matches!(result, Predicate::Or(_)),
            "expected Or, got {result:?}"
        );
        assert_eq!(result.as_bool(), None); // non-trivial
    }

    // Predicate::Or::contains: satisfied when any arm matches, regardless of the others.
    #[test]
    fn or_contains_any_arm_matches() {
        // Or([{a: ≤10}, {b: ≤10}]):
        //   - {a:5, b:20}  → first arm matches (5≤10, b unconstrained in first arm)? No —
        //     Record semantics require ALL fields. So first arm is {a:≤10} only;
        //     use single-field records to keep the test unambiguous.
        // Or([{_0: ≤10}, {_1: ≤10}]):
        //   - {_0:5,  _1:20} → first arm:  5≤10 ✓, _1 absent in arm → only _0 checked → true
        //   - {_0:20, _1:5}  → second arm: 5≤10 ✓                                     → true
        //   - {_0:20, _1:20} → neither arm                                             → false
        let pred = Predicate::Or(vec![
            record_pred(&[("_0", Predicate::LessThanEq(Value::UInt(10)))]),
            record_pred(&[("_1", Predicate::LessThanEq(Value::UInt(10)))]),
        ]);

        let only_first = Value::Record(HashMap::from([
            ("_0".to_string(), Value::UInt(5)),
            ("_1".to_string(), Value::UInt(20)),
        ]));
        let only_second = Value::Record(HashMap::from([
            ("_0".to_string(), Value::UInt(20)),
            ("_1".to_string(), Value::UInt(5)),
        ]));
        let neither = Value::Record(HashMap::from([
            ("_0".to_string(), Value::UInt(20)),
            ("_1".to_string(), Value::UInt(20)),
        ]));

        assert!(
            pred.contains(&only_first),
            "{only_first:?} should match the first arm"
        );
        assert!(
            pred.contains(&only_second),
            "{only_second:?} should match the second arm"
        );
        assert!(!pred.contains(&neither), "{neither:?} should match no arm");
    }

    #[test]
    fn union_record_or_is_empty_when_both_arms_empty() {
        // Both records are all-False, so the Or is effectively empty.
        let r1 = record_pred(&[("a", Predicate::False), ("b", Predicate::False)]);
        let r2 = record_pred(&[("a", Predicate::False), ("b", Predicate::False)]);
        let result = r1.union(&r2);
        assert_eq!(result.as_bool(), Some(false));
    }

    #[test]
    fn tile_lookup_function_true_predicate_is_terminal() {
        let tile = Tile::CurriedFunction {
            domain1: ColumnValue::UInts(vec![]),
            offsets: ColumnValue::UInts(vec![]),
            domain2: ColumnValue::UInts(vec![]),
            codomain: ColumnValue::UInts(vec![]),
            domain_predicate: Predicate::True,
        };
        assert!(tile.is_terminal());
    }

    // ── Predicate::subsumes ───────────────────────────────────────────────────

    // True subsumes everything; nothing other than True subsumes True.
    #[test]
    fn subsumes_true_subsumes_all() {
        assert!(Predicate::True.subsumes(&Predicate::True));
        assert!(Predicate::True.subsumes(&Predicate::False));
        assert!(Predicate::True.subsumes(&Predicate::LessThanEq(Value::UInt(5))));
    }

    #[test]
    fn subsumes_non_true_does_not_subsume_true() {
        assert!(!Predicate::False.subsumes(&Predicate::True));
        assert!(!Predicate::LessThanEq(Value::UInt(5)).subsumes(&Predicate::True));
    }

    // False (empty set) is subsumed by everything; it only subsumes itself.
    #[test]
    fn subsumes_everything_subsumes_false() {
        assert!(Predicate::False.subsumes(&Predicate::False));
        assert!(Predicate::True.subsumes(&Predicate::False));
        assert!(Predicate::LessThanEq(Value::UInt(0)).subsumes(&Predicate::False));
    }

    #[test]
    fn subsumes_false_does_not_subsume_nonempty() {
        assert!(!Predicate::False.subsumes(&Predicate::True));
        assert!(!Predicate::False.subsumes(&Predicate::LessThanEq(Value::UInt(3))));
    }

    // LessThanEq: (-∞,a] ⊇ (-∞,b] iff a >= b.
    #[test]
    fn subsumes_less_than_eq_looser_subsumes_tighter() {
        assert!(
            Predicate::LessThanEq(Value::UInt(7)).subsumes(&Predicate::LessThanEq(Value::UInt(3)))
        );
    }

    #[test]
    fn subsumes_less_than_eq_equal_bounds() {
        assert!(
            Predicate::LessThanEq(Value::UInt(5)).subsumes(&Predicate::LessThanEq(Value::UInt(5)))
        );
    }

    #[test]
    fn subsumes_less_than_eq_tighter_does_not_subsume_looser() {
        assert!(
            !Predicate::LessThanEq(Value::UInt(3)).subsumes(&Predicate::LessThanEq(Value::UInt(7)))
        );
    }

    // LessThanEq vs Intervals.
    #[test]
    fn subsumes_less_than_eq_subsumes_contained_interval_set() {
        // (-∞,10] ⊇ {3,7}: both points are <= 10.
        let s = Predicate::from_column_value(&ColumnValue::UInts(vec![3, 7]));
        assert!(Predicate::LessThanEq(Value::UInt(10)).subsumes(&s));
    }

    #[test]
    fn subsumes_less_than_eq_does_not_subsume_escaping_interval_set() {
        // (-∞,5] ⊉ {3,7}: 7 > 5.
        let s = Predicate::from_column_value(&ColumnValue::UInts(vec![3, 7]));
        assert!(!Predicate::LessThanEq(Value::UInt(5)).subsumes(&s));
    }

    #[test]
    fn subsumes_interval_set_does_not_subsume_less_than_eq() {
        // {3,7} ⊉ (-∞,10]: the half-line is unbounded, the set is finite.
        let s = Predicate::from_column_value(&ColumnValue::UInts(vec![3, 7]));
        assert!(!s.subsumes(&Predicate::LessThanEq(Value::UInt(10))));
    }

    // Intervals vs Intervals.
    #[test]
    fn subsumes_interval_superset_subsumes_subset() {
        // {1,2,3,4} ⊇ {2,3}.
        let big = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2, 3, 4]));
        let small = Predicate::from_column_value(&ColumnValue::UInts(vec![2, 3]));
        assert!(big.subsumes(&small));
        assert!(!small.subsumes(&big));
    }

    #[test]
    fn subsumes_equal_interval_sets() {
        let a = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2, 3]));
        let b = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2, 3]));
        assert!(a.subsumes(&b));
        assert!(b.subsumes(&a));
    }

    #[test]
    fn subsumes_disjoint_interval_sets_neither_subsumes() {
        let a = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2]));
        let b = Predicate::from_column_value(&ColumnValue::UInts(vec![3, 4]));
        assert!(!a.subsumes(&b));
        assert!(!b.subsumes(&a));
    }

    // Record: field-by-field AND semantics.
    #[test]
    fn subsumes_record_field_by_field() {
        // {x: ≤10, y: ≤10} ⊇ {x: ≤5, y: ≤3}: both fields are looser in self.
        let big = record_pred(&[
            ("x", Predicate::LessThanEq(Value::UInt(10))),
            ("y", Predicate::LessThanEq(Value::UInt(10))),
        ]);
        let small = record_pred(&[
            ("x", Predicate::LessThanEq(Value::UInt(5))),
            ("y", Predicate::LessThanEq(Value::UInt(3))),
        ]);
        assert!(big.subsumes(&small));
        assert!(!small.subsumes(&big));
    }

    #[test]
    fn subsumes_record_incomparable_fields() {
        // {x: ≤5, y: ≤10}: x-field is tighter than r2, y-field is looser.
        // Neither record subsumes the other.
        let r1 = record_pred(&[
            ("x", Predicate::LessThanEq(Value::UInt(5))),
            ("y", Predicate::LessThanEq(Value::UInt(10))),
        ]);
        let r2 = record_pred(&[
            ("x", Predicate::LessThanEq(Value::UInt(10))),
            ("y", Predicate::LessThanEq(Value::UInt(5))),
        ]);
        assert!(!r1.subsumes(&r2));
        assert!(!r2.subsumes(&r1));
    }

    #[test]
    fn subsumes_record_with_true_field_subsumes_anything_in_that_field() {
        // {x: True, y: ≤3} ⊇ {x: ≤7, y: ≤3}: True subsumes any x predicate.
        let big = record_pred(&[
            ("x", Predicate::True),
            ("y", Predicate::LessThanEq(Value::UInt(3))),
        ]);
        let small = record_pred(&[
            ("x", Predicate::LessThanEq(Value::UInt(7))),
            ("y", Predicate::LessThanEq(Value::UInt(3))),
        ]);
        assert!(big.subsumes(&small));
        assert!(!small.subsumes(&big));
    }

    // Or: union subsumes `other` if any arm does; self subsumes a union iff it
    // subsumes every arm.
    #[test]
    fn subsumes_or_any_arm_suffices() {
        // Or([≤3, ≤10]) ⊇ ≤5 because the ≤10 arm already covers it.
        let or_pred =
            Predicate::LessThanEq(Value::UInt(3)).union(&Predicate::LessThanEq(Value::UInt(10)));
        // union of two LessThanEqs collapses to just LessThanEq(10), so
        // construct an Or via Record union to exercise the Or path.
        let arm_a = record_pred(&[("x", Predicate::LessThanEq(Value::UInt(10)))]);
        let arm_b = record_pred(&[("x", Predicate::LessThanEq(Value::UInt(3)))]);
        let or_rec = arm_a.union(&arm_b); // Or([arm_a, arm_b]) simplified to [arm_a]
        let target = record_pred(&[("x", Predicate::LessThanEq(Value::UInt(5)))]);
        assert!(or_pred.subsumes(&Predicate::LessThanEq(Value::UInt(5))));
        assert!(or_rec.subsumes(&target));
    }

    #[test]
    fn subsumes_value_must_subsume_all_or_arms() {
        // ≤10 ⊇ Or([≤3, ≤7]) because 10 >= both 3 and 7.
        let or_pred =
            Predicate::LessThanEq(Value::UInt(3)).union(&Predicate::LessThanEq(Value::UInt(7)));
        assert!(Predicate::LessThanEq(Value::UInt(10)).subsumes(&or_pred));
    }

    #[test]
    fn subsumes_value_does_not_subsume_or_if_any_arm_escapes() {
        // ≤5 ⊉ Or([≤3, ≤7]) because the ≤7 arm extends beyond 5.
        let or_pred =
            Predicate::LessThanEq(Value::UInt(3)).union(&Predicate::LessThanEq(Value::UInt(7)));
        assert!(!Predicate::LessThanEq(Value::UInt(5)).subsumes(&or_pred));
    }

    // ── helpers for merge / to_guard / remove_guarded tests ──────────────────

    /// A SealedFunction tile mapping `domain` ints to `codomain` ints.
    fn sf_int(domain: Vec<i64>, codomain: Vec<i64>, pred: Predicate) -> Tile {
        Tile::SealedFunction {
            domain: ColumnValue::Ints(domain),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(codomain))),
            domain_predicate: pred,
        }
    }

    /// A CurriedFunction tile with usize domain1, usize domain2 keys, and int codomain.
    fn cf_uint_int(
        d1: Vec<usize>,
        offsets: Vec<usize>,
        d2: Vec<usize>,
        cod: Vec<i64>,
        pred: Predicate,
    ) -> Tile {
        Tile::curried_function(
            ColumnValue::UInts(d1),
            ColumnValue::UInts(offsets),
            ColumnValue::UInts(d2),
            ColumnValue::Ints(cod),
            pred,
        )
    }

    /// Build a TileGuard for releasing domain2 values described by `pred` from a CurriedFunction.
    fn cf_release_guard(pred: Predicate) -> TileGuard {
        TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Function(
            FunctionGuard::Domain(pred),
        ))))
    }

    // ── Tile::merge ───────────────────────────────────────────────────────────

    #[test]
    fn merge_scalar_empty_takes_other() {
        let mut tile = Tile::Scalar(ColumnValue::Ints(vec![]));
        tile.merge(Tile::Scalar(ColumnValue::Ints(vec![42])));
        assert_eq!(tile, Tile::Scalar(ColumnValue::Ints(vec![42])));
    }

    #[test]
    fn merge_sealed_function_appends_domain_and_codomain() {
        let mut tile = sf_int(vec![1], vec![10], Predicate::False);
        tile.merge(sf_int(vec![2], vec![20], Predicate::False));
        let Tile::SealedFunction {
            domain, codomain, ..
        } = &tile
        else {
            panic!("expected SealedFunction");
        };
        assert_eq!(*domain, ColumnValue::Ints(vec![1, 2]));
        assert_eq!(
            *codomain,
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20])))
        );
    }

    #[test]
    fn merge_sealed_function_unions_predicates() {
        let p1 = Predicate::from_column_value(&ColumnValue::Ints(vec![1]));
        let p2 = Predicate::from_column_value(&ColumnValue::Ints(vec![2]));
        let mut tile = sf_int(vec![1], vec![10], p1.clone());
        tile.merge(sf_int(vec![2], vec![20], p2.clone()));
        let Tile::SealedFunction {
            domain_predicate, ..
        } = &tile
        else {
            panic!("expected SealedFunction");
        };
        assert_eq!(*domain_predicate, p1.union(&p2));
    }

    #[test]
    fn merge_curried_function_appends_with_correct_offsets() {
        // Group 0 (d1=0): d2=[10, 11], cod=[100, 110]
        // Group 1 (d1=1): d2=[12],     cod=[120]
        let mut tile = cf_uint_int(
            vec![0],
            vec![0],
            vec![10, 11],
            vec![100, 110],
            Predicate::False,
        );
        tile.merge(cf_uint_int(
            vec![1],
            vec![0],
            vec![12],
            vec![120],
            Predicate::False,
        ));
        assert_eq!(
            tile,
            cf_uint_int(
                vec![0, 1],
                vec![0, 2], // group 1 starts at index 2 in the combined domain2
                vec![10, 11, 12],
                vec![100, 110, 120],
                Predicate::False,
            )
        );
    }

    #[test]
    fn merge_record_recurses_per_field() {
        let make_record = |_: i64| {
            Tile::Record(HashMap::from([(
                "x".to_string(),
                Tile::Scalar(ColumnValue::Ints(vec![])),
            )]))
        };
        let mut tile = Tile::Record(HashMap::from([(
            "x".to_string(),
            Tile::Scalar(ColumnValue::Ints(vec![])),
        )]));
        tile.merge(Tile::Record(HashMap::from([(
            "x".to_string(),
            Tile::Scalar(ColumnValue::Ints(vec![7])),
        )])));
        assert_eq!(
            tile,
            Tile::Record(HashMap::from([(
                "x".to_string(),
                Tile::Scalar(ColumnValue::Ints(vec![7])),
            )]))
        );
        let _ = make_record; // suppress unused warning
    }

    // ── Tile::to_guard ────────────────────────────────────────────────────────

    #[test]
    fn to_guard_scalar_empty_is_empty() {
        assert_eq!(
            Tile::Scalar(ColumnValue::Ints(vec![])).to_guard(),
            TileGuard::Scalar(false)
        );
    }

    #[test]
    fn to_guard_scalar_nonempty_is_universal() {
        assert_eq!(
            Tile::Scalar(ColumnValue::Ints(vec![1])).to_guard(),
            TileGuard::Scalar(true)
        );
    }

    #[test]
    fn to_guard_sealed_function_wraps_domain_predicate() {
        let pred = Predicate::from_column_value(&ColumnValue::Ints(vec![1, 2]));
        let tile = sf_int(vec![1, 2], vec![10, 20], pred.clone());
        assert_eq!(
            tile.to_guard(),
            TileGuard::Function(FunctionGuard::Domain(pred))
        );
    }

    #[test]
    fn to_guard_curried_function_uses_domain2_values() {
        let tile = cf_uint_int(
            vec![0],
            vec![0],
            vec![10, 11],
            vec![100, 110],
            Predicate::False,
        );
        let guard = tile.to_guard();
        // The guard should cover domain2 values 10 and 11.
        let TileGuard::Function(FunctionGuard::Codomain(inner)) = guard else {
            panic!("expected Codomain guard");
        };
        let TileGuard::Function(FunctionGuard::Domain(pred)) = *inner else {
            panic!("expected Domain pred");
        };
        assert!(pred.contains(&Value::UInt(10)));
        assert!(pred.contains(&Value::UInt(11)));
        assert!(!pred.contains(&Value::UInt(99)));
    }

    #[test]
    fn to_guard_record_recurses() {
        let tile = Tile::Record(HashMap::from([
            ("a".to_string(), Tile::Scalar(ColumnValue::Ints(vec![1]))),
            ("b".to_string(), Tile::Scalar(ColumnValue::Ints(vec![]))),
        ]));
        let TileGuard::Record(guards) = tile.to_guard() else {
            panic!("expected Record guard");
        };
        assert_eq!(guards["a"], TileGuard::Scalar(true));
        assert_eq!(guards["b"], TileGuard::Scalar(false));
    }

    // ── Tile::remove_guarded ──────────────────────────────────────────────────

    #[test]
    fn remove_guarded_scalar_universal_clears() {
        let mut tile = Tile::Scalar(ColumnValue::Ints(vec![42]));
        tile.remove_guarded(TileGuard::Scalar(true));
        assert_eq!(tile, Tile::Scalar(ColumnValue::Ints(vec![])));
    }

    #[test]
    fn remove_guarded_scalar_empty_is_noop() {
        let mut tile = Tile::Scalar(ColumnValue::Ints(vec![42]));
        tile.remove_guarded(TileGuard::Scalar(false));
        assert_eq!(tile, Tile::Scalar(ColumnValue::Ints(vec![42])));
    }

    #[test]
    fn remove_guarded_sealed_function_removes_matching_entries() {
        // Remove only domain value 1; domain value 2 survives.
        let pred = Predicate::from_column_value(&ColumnValue::Ints(vec![1]));
        let mut tile = sf_int(vec![1, 2], vec![10, 20], Predicate::True);
        tile.remove_guarded(TileGuard::Function(FunctionGuard::Domain(pred)));
        let Tile::SealedFunction {
            domain, codomain, ..
        } = &tile
        else {
            panic!("expected SealedFunction");
        };
        assert_eq!(*domain, ColumnValue::Ints(vec![2]));
        assert_eq!(
            *codomain,
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![20])))
        );
    }

    #[test]
    fn remove_guarded_sealed_function_full_release_clears() {
        let mut tile = sf_int(vec![1, 2], vec![10, 20], Predicate::True);
        let guard = tile.to_guard();
        tile.remove_guarded(guard);
        let Tile::SealedFunction { domain, .. } = &tile else {
            panic!("expected SealedFunction");
        };
        assert_eq!(domain.len(), 0);
    }

    #[test]
    fn remove_guarded_curried_function_removes_matching_domain2() {
        // d1=[0,1], offsets=[0,2], d2=[10,11,12], cod=[100,110,120]
        // Remove d2=11; 10 and 12 survive.
        let mut tile = cf_uint_int(
            vec![0, 1],
            vec![0, 2],
            vec![10, 11, 12],
            vec![100, 110, 120],
            Predicate::False,
        );
        let pred = Predicate::from_column_value(&ColumnValue::UInts(vec![11]));
        tile.remove_guarded(cf_release_guard(pred));
        assert_eq!(
            tile,
            cf_uint_int(
                vec![0, 1],
                vec![0, 1], // group 0: 1 entry at 0; group 1: 1 entry at 1
                vec![10, 12],
                vec![100, 120],
                Predicate::False,
            )
        );
    }

    #[test]
    fn remove_guarded_curried_function_prunes_empty_group() {
        // d1=[0,1], offsets=[0,2], d2=[10,11,12], cod=[100,110,120]
        // Remove d2=10 and d2=11 (the whole group 0); group 1 (d2=12) survives.
        let mut tile = cf_uint_int(
            vec![0, 1],
            vec![0, 2],
            vec![10, 11, 12],
            vec![100, 110, 120],
            Predicate::False,
        );
        let pred = Predicate::from_column_value(&ColumnValue::UInts(vec![10, 11]));
        tile.remove_guarded(cf_release_guard(pred));
        assert_eq!(
            tile,
            cf_uint_int(vec![1], vec![0], vec![12], vec![120], Predicate::False)
        );
    }

    #[test]
    fn remove_guarded_record_recurses() {
        let mut tile = Tile::Record(HashMap::from([
            ("a".to_string(), Tile::Scalar(ColumnValue::Ints(vec![1]))),
            ("b".to_string(), Tile::Scalar(ColumnValue::Ints(vec![2]))),
        ]));
        tile.remove_guarded(TileGuard::Record(HashMap::from([
            ("a".to_string(), TileGuard::Scalar(true)),
            ("b".to_string(), TileGuard::Scalar(false)),
        ])));
        let Tile::Record(fields) = &tile else {
            panic!()
        };
        assert_eq!(fields["a"], Tile::Scalar(ColumnValue::Ints(vec![])));
        assert_eq!(fields["b"], Tile::Scalar(ColumnValue::Ints(vec![2])));
    }

    // ── round-trip: to_guard → remove_guarded ────────────────────────────────

    #[test]
    fn round_trip_sealed_function_full_release() {
        let mut tile = sf_int(vec![1, 2, 3], vec![10, 20, 30], Predicate::True);
        let guard = tile.to_guard();
        tile.remove_guarded(guard);
        assert_eq!(
            tile.to_guard(),
            TileGuard::Function(FunctionGuard::Domain(Predicate::True))
        );
    }

    #[test]
    fn round_trip_curried_function_full_release() {
        let mut tile = cf_uint_int(
            vec![0, 1],
            vec![0, 2],
            vec![10, 11, 12],
            vec![100, 110, 120],
            Predicate::False,
        );
        let guard = tile.to_guard();
        tile.remove_guarded(guard);
        assert_eq!(tile.to_guard(), cf_release_guard(Predicate::False));
    }

    // ── Tile::retain (CurriedFunction) ────────────────────────────────────────
    //
    // The mask is over the flat domain2/codomain rows.
    // Groups with no surviving rows are pruned from domain1 and offsets.
    //
    // Test tile layout (used throughout):
    //   Group 0 (d1=10): d2=[0,1],     cod=[100,110]       — flat positions 0,1
    //   Group 1 (d1=20): d2=[2,3,4],   cod=[200,210,220]   — flat positions 2,3,4
    //   Group 2 (d1=30): d2=[5],       cod=[300]           — flat position 5

    fn cf_three_groups() -> Tile {
        cf_uint_int(
            vec![10, 20, 30],
            vec![0, 2, 5],
            vec![0, 1, 2, 3, 4, 5],
            vec![100, 110, 200, 210, 220, 300],
            Predicate::False,
        )
    }

    #[test]
    fn retain_curried_function_keep_all_is_noop() {
        let mut tile = cf_three_groups();
        tile.retain(&BitVec::from_elem(6, true));
        assert_eq!(tile, cf_three_groups());
    }

    #[test]
    fn retain_curried_function_keep_none_empties_tile() {
        let mut tile = cf_three_groups();
        tile.retain(&BitVec::from_elem(6, false));
        assert_eq!(
            tile,
            cf_uint_int(vec![], vec![], vec![], vec![], Predicate::False)
        );
    }

    #[test]
    fn retain_curried_function_keep_entire_first_group() {
        let mut tile = cf_three_groups();
        // Keep positions 0,1 (group 0); drop the rest.
        tile.retain(&BitVec::from_fn(6, |i| i < 2));
        assert_eq!(
            tile,
            cf_uint_int(
                vec![10],
                vec![0],
                vec![0, 1],
                vec![100, 110],
                Predicate::False
            )
        );
    }

    #[test]
    fn retain_curried_function_keep_entire_middle_group() {
        let mut tile = cf_three_groups();
        // Keep positions 2,3,4 (group 1); drop the rest.
        tile.retain(&BitVec::from_fn(6, |i| (2..=4).contains(&i)));
        assert_eq!(
            tile,
            cf_uint_int(
                vec![20],
                vec![0],
                vec![2, 3, 4],
                vec![200, 210, 220],
                Predicate::False,
            )
        );
    }

    #[test]
    fn retain_curried_function_keep_entire_last_group() {
        let mut tile = cf_three_groups();
        // Keep position 5 (group 2); drop the rest.
        tile.retain(&BitVec::from_fn(6, |i| i == 5));
        assert_eq!(
            tile,
            cf_uint_int(vec![30], vec![0], vec![5], vec![300], Predicate::False)
        );
    }

    #[test]
    fn retain_curried_function_drop_entire_middle_group() {
        let mut tile = cf_three_groups();
        // Keep groups 0 and 2; drop group 1 (positions 2,3,4).
        tile.retain(&BitVec::from_fn(6, |i| !(2..=4).contains(&i)));
        assert_eq!(
            tile,
            cf_uint_int(
                vec![10, 30],
                vec![0, 2],
                vec![0, 1, 5],
                vec![100, 110, 300],
                Predicate::False,
            )
        );
    }

    #[test]
    fn retain_curried_function_partial_mask_within_group() {
        let mut tile = cf_three_groups();
        // Keep only d2[1] from group 0 and d2[3] from group 1; drop everything else.
        // Positions kept: 1 and 3.
        tile.retain(&BitVec::from_fn(6, |i| i == 1 || i == 3));
        assert_eq!(
            tile,
            cf_uint_int(
                vec![10, 20],
                vec![0, 1],
                vec![1, 3],
                vec![110, 210],
                Predicate::False,
            )
        );
    }

    #[test]
    fn retain_curried_function_partial_mask_prunes_empty_group() {
        let mut tile = cf_three_groups();
        // Keep d2[2] and d2[4] (both in group 1); groups 0 and 2 have no survivors.
        tile.retain(&BitVec::from_fn(6, |i| i == 2 || i == 4));
        assert_eq!(
            tile,
            cf_uint_int(
                vec![20],
                vec![0],
                vec![2, 4],
                vec![200, 220],
                Predicate::False
            )
        );
    }
}
