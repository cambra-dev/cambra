//! The [`Tile`] type: the materialized data exchanged between operators, plus
//! [`validate_tile`] for dev-build structural checks.

use std::collections::{HashMap, HashSet};

use bit_set::BitSet;
use bit_vec::BitVec;

use crate::{
    ccl::AggregateKind,
    interpreter::{
        BinOpKind, ColumnValue, FunctionGuard, LogicKind, Predicate, TileGuard, Tiling, Value,
        apply_binop_column, tuple_field,
    },
};

/// A materialized data tile produced by a [`TileProducer`](crate::interpreter::tile_operators::TileProducer).
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
        /// Calls to `get` can still return tiles with data in this region, but such data is guaranteed to
        /// be the same as data already observed.
        domain_predicate: Predicate,
        /// Set of indices (into `domain`/`codomain`) that have been logically removed by
        /// filtering.  1 = deleted; an empty set means all entries are present.  The full
        /// physical arrays are preserved so that `to_guard` can report every domain value
        /// that has ever been seen—not just the survivors—enabling complete source releasing.
        deleted: BitSet,
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
        /// Set of flat `domain2`/`codomain` row indices that have been logically removed by
        /// filtering.  1 = deleted; empty means all rows are present.  Preserved for the
        /// same reason as [`Tile::SealedFunction::deleted`]: so `to_guard` can report every
        /// domain2 value ever seen, enabling complete source releasing.
        deleted: BitSet,
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
    /// A **transactional store**: a right-continuous step function
    /// `Txn ⇒ {key: value}` over the commit-time domain, materialized as its
    /// **changelog** — the ticks that committed a write, each carrying that
    /// tick's write-set *delta*.
    ///
    /// This is *not* a [`Tile::SealedFunction`] and must not be treated as one:
    /// in a `SealedFunction` a domain position absent from `changes` is
    /// **unknown**, whereas here it is **decided-absent — the value holds from
    /// the latest earlier change** (step interpolation). The value at an
    /// arbitrary commit time is obtained by *folding* the changelog
    /// ([`store_value_at`](crate::interpreter::commit_operator::store_value_at) /
    /// [`store_snapshot_at`](crate::interpreter::commit_operator::store_snapshot_at)),
    /// never by indexing a position directly, and the current value of a *live*
    /// store is
    /// [`store_current`](crate::interpreter::commit_operator::store_current) —
    /// which, unlike `ExtractFinal`, is defined without the stream ever
    /// terminating. Encoding the step semantics in a distinct variant keeps
    /// ordinary-function operations (direct indexing, `ExtractFinal`) from
    /// silently misreading a store. See `src/ccl/design/mutability.md`.
    Store {
        /// Commit ticks that carry a write (the change events), sorted ascending.
        changes: ColumnValue,
        /// Per-tick write-set deltas, parallel to `changes`: `deltas[i]` is the
        /// map of keys written at `changes[i]`, encoded as a `Variants` cell (via
        /// [`crate::interpreter::commit_operator::map_to_value`]). A key absent
        /// from a tick's delta was not written at that tick (its value holds).
        deltas: ColumnValue,
        /// The decided frontier: `LessThanEq(w)` means every tick `≤ w` is decided
        /// — the watermark `w` counts trailing carries (positions past the latest
        /// *change*), because a store is a right-continuous step function over its
        /// whole decided prefix, not a list of change events. `False` while
        /// undecided (never stepped). **Not** `True`: terminality is the separate
        /// `terminal` axis so the numeric watermark is never discarded (a terminal
        /// store with trailing carries keeps `LessThanEq(w)`, so `len` and
        /// `store_frontier` read `w` directly instead of undercounting to the latest
        /// change tick).
        frontier: Predicate,
        /// Whether the frontier is *closed* — no further commits will ever land, so
        /// a *terminal* read (`ExtractFinal` / `final_or_default`) resolves. Distinct
        /// from the decided *extent* (`frontier`): a live store decided up to `w`
        /// has `terminal == false`; the same store, once its writers finish, flips
        /// `terminal` to `true` while keeping `frontier = LessThanEq(w)`.
        terminal: bool,
    },
}

impl Tile {
    /// Helper to create a tuple tile, i.e. a Record tile where all fields are from `tuple_field`
    pub fn tuple(tiles: Vec<Tile>) -> Tile {
        Tile::Record(
            tiles
                .into_iter()
                .enumerate()
                .map(|(i, t)| (tuple_field(i), t))
                .collect(),
        )
    }

    pub fn len(&self) -> usize {
        match self {
            Tile::Scalar(cv) => cv.len(),
            Tile::Record(m) => m.values().map(Tile::len).max().unwrap_or(0),
            Tile::SealedFunction {
                domain, deleted, ..
            } => domain.len() - deleted.len(),
            Tile::CurriedFunction {
                domain2, deleted, ..
            } => domain2.len() - deleted.len(),
            Tile::Aggregation { accumulator, .. } => accumulator.len(),
            // A `Store` is a right-continuous *step function* over its decided
            // prefix, not a list of change events: a tick absent from `changes`
            // but at or below the frontier is *decided* (its value inherits from
            // the latest earlier change). So the length is the number of
            // **decided domain positions** — the frontier watermark `+ 1` — not
            // `changes.len()` (which counts only the ticks that carried a write).
            //
            // The watermark reads straight off `LessThanEq(w)`, which counts
            // trailing carries (positions past the latest change) because terminality
            // rides the separate `terminal` flag, not a `True` frontier that would
            // discard `w`. An undecided (`False`) frontier has no decided positions.
            Tile::Store { frontier, .. } => match frontier {
                Predicate::LessThanEq(Value::UInt(w)) => w + 1,
                _ => 0,
            },
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
            // The change ticks must lie in the commit domain; the per-tick delta
            // encoding is trusted (like `CurriedFunction`).
            (Tile::Store { changes, .. }, Tiling::Store { domain, .. }) => {
                changes.is_compatible_with_extent(domain)
            }
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
            // A store is terminal once its commit frontier is closed (no more
            // writes will commit) — the only state in which a *terminal* read of
            // it resolves. Terminality is its own flag; the `frontier` predicate
            // keeps the numeric watermark either way.
            Tile::Store { terminal, .. } => *terminal,
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
                    deleted: s_deleted,
                },
                Tile::SealedFunction {
                    domain: o_domain,
                    codomain: o_codomain,
                    domain_predicate: o_pred,
                    deleted: o_deleted,
                },
            ) => {
                let s_domain_len = s_domain.len();
                s_domain.append(o_domain);
                s_codomain.merge(*o_codomain);
                *s_pred = s_pred.union(&o_pred);
                // Shift other's deleted indices into the combined physical array.
                for idx in o_deleted.iter() {
                    s_deleted.insert(idx + s_domain_len);
                }
            }
            (
                Tile::CurriedFunction {
                    domain1: s_domain1,
                    offsets: s_offsets,
                    domain2: s_domain2,
                    codomain: s_codomain,
                    domain_predicate: s_pred,
                    deleted: s_deleted,
                },
                Tile::CurriedFunction {
                    domain1: o_domain1,
                    offsets: o_offsets,
                    domain2: o_domain2,
                    codomain: o_codomain,
                    domain_predicate: o_pred,
                    deleted: o_deleted,
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
                // Shift other's deleted row indices into the combined flat array.
                for idx in o_deleted.iter() {
                    s_deleted.insert(idx + s_d2_len);
                }
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
            // Change-append: `other`'s new commit ticks are strictly greater than
            // any already present (the changelog only grows forward in commit
            // time), so appending preserves the ascending order the fold relies
            // on. The frontier advances to the union — for the watermark
            // `LessThanEq(w)` this is `LessThanEq(max(w_self, w_other))`; the
            // `terminal` flag ORs (either side declaring the frontier closed closes
            // it). Mirrors the `SealedFunction` arm sans `deleted`: a store releases
            // by physically dropping a decided prefix (see `remove_guarded`), never
            // by logical tombstoning.
            (
                Tile::Store {
                    changes: s_changes,
                    deltas: s_deltas,
                    frontier: s_frontier,
                    terminal: s_terminal,
                },
                Tile::Store {
                    changes: o_changes,
                    deltas: o_deltas,
                    frontier: o_frontier,
                    terminal: o_terminal,
                },
            ) => {
                s_changes.append(o_changes);
                s_deltas.append(o_deltas);
                *s_frontier = s_frontier.union(&o_frontier);
                *s_terminal = *s_terminal || o_terminal;
            }
            (s, o) => panic!("Incompatible tiles {s:?} and {o:?}"),
        };
        debug_assert!(validate_tile(self), "Invalid tile: {self:?}");
    }

    /// Retain in-place only the elements at positions where `mask[i]` is true.
    ///
    /// After retention the physical arrays are compact and `deleted` is cleared —
    /// every surviving entry is considered live.  Use [`Tile::compact`] to build
    /// the mask automatically from the current `deleted` set.
    pub fn retain(&mut self, mask: &BitVec) {
        match self {
            Tile::Scalar(cv) => cv.retain(mask),
            Tile::Record(m) => m.values_mut().for_each(|t| t.retain(mask)),
            Tile::SealedFunction {
                domain,
                codomain,
                deleted,
                ..
            } => {
                // Combine the caller's mask with the logical-deletion bits:
                // keep entry i only if mask[i] is true AND it is not logically deleted.
                let effective_mask: BitVec = mask
                    .iter()
                    .enumerate()
                    .map(|(i, keep)| keep && !deleted.contains(i))
                    .collect();
                domain.retain(&effective_mask);
                codomain.retain(&effective_mask);
                deleted.clear();
            }
            Tile::CurriedFunction {
                domain1,
                offsets,
                domain2,
                codomain,
                deleted,
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
                    // Keep flat row j if the caller's mask says keep AND j is not logically deleted.
                    let group_kept: Vec<usize> = (start..end)
                        .filter(|&j| mask[j] && !deleted.contains(j))
                        .collect();
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
                deleted.clear();
            }
            _ => panic!("retain not supported for {self:?}"),
        }
    }

    /// Logically remove entries at positions where `mask[i]` is false by setting bits in
    /// `deleted`.  Physical arrays are untouched, so `to_guard` still reports every
    /// domain value that was ever present.  Call [`Tile::compact`] to physically remove
    /// deleted entries when iteration over only live entries is required.
    pub fn mark_deleted(&mut self, mask: &BitVec) {
        match self {
            Tile::SealedFunction { deleted, .. } | Tile::CurriedFunction { deleted, .. } => {
                for (i, keep) in mask.iter().enumerate() {
                    if !keep {
                        deleted.insert(i);
                    }
                }
            }
            _ => panic!("mark_deleted not supported for {self:?}"),
        }
    }

    /// Physically remove all logically-deleted entries and clear `deleted`.
    ///
    /// After this call the tile is compact: every physical slot is live.
    /// This is the counterpart to [`Tile::mark_deleted`] and is called before
    /// operators iterate over tile data so they only process live entries.
    pub fn compact(&mut self) {
        let n = match self {
            Tile::SealedFunction {
                deleted, domain, ..
            } => {
                if deleted.is_empty() {
                    return;
                }
                domain.len()
            }
            Tile::CurriedFunction {
                deleted, domain2, ..
            } => {
                if deleted.is_empty() {
                    return;
                }
                domain2.len()
            }
            _ => return,
        };
        // Build the keep-mask from the deleted set, then let retain() do the work
        // (retain also clears deleted).
        let deleted_clone = match self {
            Tile::SealedFunction { deleted, .. } | Tile::CurriedFunction { deleted, .. } => {
                deleted.clone()
            }
            _ => unreachable!(),
        };
        let mask: BitVec = (0..n).map(|i| !deleted_clone.contains(i)).collect();
        self.retain(&mask);
    }

    /// Removes all data in this tile that is specified by the guard.
    /// TODO: the index_at calls here aren't very efficient; we should optmize this by applying the
    /// predicates in a more columnar way.
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
            // SealedFunction: mark domain entries whose value is in the predicate as deleted.
            // Physical arrays are preserved so that to_guard() reports all ever-seen values.
            (
                Tile::SealedFunction {
                    domain, deleted, ..
                },
                TileGuard::Function(FunctionGuard::Domain(pred)),
            ) => {
                for i in 0..domain.len() {
                    if pred.contains(&domain.index_at(i)) {
                        deleted.insert(i);
                    }
                }
            }
            // CurriedFunction + Domain: mark all flat rows belonging to matching domain1 groups.
            (
                Tile::CurriedFunction {
                    domain1,
                    offsets,
                    domain2,
                    deleted,
                    ..
                },
                TileGuard::Function(FunctionGuard::Domain(pred)),
            ) => {
                let ColumnValue::UInts(offset_vec) = &*offsets else {
                    panic!("CurriedFunction offsets must be UInts");
                };
                let offset_vec = offset_vec.clone();
                let n = domain1.len();
                let domain2_total = domain2.len();
                for i in 0..n {
                    if pred.contains(&domain1.index_at(i)) {
                        let start = offset_vec[i];
                        let end = if i + 1 < n {
                            offset_vec[i + 1]
                        } else {
                            domain2_total
                        };
                        for j in start..end {
                            deleted.insert(j);
                        }
                    }
                }
            }
            // CurriedFunction + Codomain(Domain(pred)): mark flat rows whose domain2 value matches.
            (
                Tile::CurriedFunction {
                    domain2, deleted, ..
                },
                TileGuard::Function(FunctionGuard::Codomain(inner)),
            ) => {
                let TileGuard::Function(FunctionGuard::Domain(pred)) = *inner else {
                    unimplemented!(
                        "CurriedFunction remove_guarded only supports Codomain(Domain(pred))"
                    )
                };
                for j in 0..domain2.len() {
                    if pred.contains(&domain2.index_at(j)) {
                        deleted.insert(j);
                    }
                }
            }
            // A store release names a prefix of decided commit ticks the consumer
            // no longer needs to *read at*. Dropping those change cells here would
            // be unsound: under step interpolation a released tick's value may
            // still hold forward past the release watermark, so a fold
            // (`store_current` at the frontier) needs each key's latest write even
            // when it lies in the released prefix. The load-bearing GC is therefore
            // the engine's `gc_released_prefix` (keep-latest), which bounds the
            // *source*; the per-consumer `FanOut` view reaching here is a throwaway
            // per-pull clone the consumer folds whole, so removal is a no-op. This
            // is the release-path face of the `SealedFunction` overload the `Store`
            // variant exists to avoid — "release tick t" is not "delete position t".
            (Tile::Store { .. }, TileGuard::Function(FunctionGuard::Domain(_))) => {}
            (s, g) => panic!("Incompatible tile and guard in remove_guarded: {s:?} and {g:?}"),
        }
    }

    /// Whether this tile still carries live data inside `guard`.
    ///
    /// Defined as "removing the guarded region would change the tile", so it
    /// agrees with [`Self::remove_guarded`] by construction — including where
    /// that deliberately keeps data, as a [`Tile::Store`] does for a released
    /// tick prefix whose values still hold forward past the watermark. A row
    /// already marked deleted is not live, so re-marking it reports nothing.
    pub fn contains_guarded(&self, guard: &TileGuard) -> bool {
        if guard.is_empty() {
            return false;
        }
        let mut probe = self.clone();
        probe.remove_guarded(guard.clone());
        probe != *self
    }

    /// Creates a TileGuard representing the contents of this Tile.
    /// For Scalar: universal if the scalar is known and empty otherwise
    /// For Aggregation: universal if terminal and empty otherwise
    /// For SealedFunction: Domain predicate for all domain values
    /// For CurriedFunction, Codomain(Domain(predicate)) for all domain2 values (TODO for now we assume unique domain2)
    ///
    /// Important note around logical deletes: we don't release eagerly when logically deleting rows via the
    /// deleted bitsets, so `to_guard` includes logically-deleted rows when constructing the guards.
    /// Doing it this way significantly reduces the fragmentation of the obsolete guards, which lets them use
    /// smaller representations.
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
            } => {
                if domain_predicate.is_true() {
                    TileGuard::Function(FunctionGuard::Domain(Predicate::True))
                } else {
                    // TODO include domain_predicate in from_column_value to avoid unnecessary work.
                    TileGuard::Function(FunctionGuard::Domain(
                        Predicate::from_column_value(domain).union(domain_predicate),
                    ))
                }
            }
            Tile::CurriedFunction {
                domain2,
                domain_predicate,
                ..
            } => TileGuard::flatten_or(vec![
                TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Function(
                    FunctionGuard::Domain(Predicate::from_column_value(domain2)),
                )))),
                TileGuard::Function(FunctionGuard::Domain(domain_predicate.clone())),
            ]),
            // The store's guard is over its commit-time domain (the change
            // ticks), like a `SealedFunction` — consumers release a prefix of it.
            Tile::Store {
                changes,
                frontier,
                terminal,
                ..
            } => {
                if *terminal {
                    TileGuard::Function(FunctionGuard::Domain(Predicate::True))
                } else {
                    TileGuard::Function(FunctionGuard::Domain(
                        Predicate::from_column_value(changes).union(frontier),
                    ))
                }
            }
        }
    }

    /// Creates a `Tile::CurriedFunction` and does dev-build-only validation for correct structure.
    /// Pass `BitSet::new()` for `deleted` when no entries are logically removed.
    pub fn curried_function(
        domain1: ColumnValue,
        offsets: ColumnValue,
        domain2: ColumnValue,
        codomain: ColumnValue,
        domain_predicate: Predicate,
        deleted: BitSet,
    ) -> Tile {
        let result = Tile::CurriedFunction {
            domain1,
            offsets,
            domain2,
            codomain,
            domain_predicate,
            deleted,
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
            deleted: _,
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
        // A store's changelog is one delta per change tick, and the ticks are
        // strictly ascending — the fold ([`store_value_at`] et al.) and the
        // change-append `merge` both depend on it, and neither is type-enforced.
        Tile::Store {
            changes, deltas, ..
        } => {
            changes.len() == deltas.len()
                && matches!(deltas, ColumnValue::Variants(_))
                && (0..changes.len()).all(|i| {
                    i == 0
                        || matches!(
                            (changes.index_at(i - 1), changes.index_at(i)),
                            (Value::UInt(a), Value::UInt(b)) if a < b
                        )
                })
        }
        _ => true,
    }
}

#[cfg(test)]
mod tests {
    use bit_set::BitSet;
    use bit_vec::BitVec;

    use super::*;
    use crate::interpreter::{ColumnValue, FunctionGuard, Predicate, TileGuard, Value};

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
            deleted: BitSet::new(),
        };
        assert!(tile.is_terminal());
    }

    #[test]
    fn tile_sealed_function_false_predicate_not_terminal() {
        let tile = Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![]))),
            domain_predicate: Predicate::False,
            deleted: BitSet::new(),
        };
        assert!(!tile.is_terminal());
    }

    #[test]
    fn tile_lookup_function_true_predicate_is_terminal() {
        let tile = Tile::CurriedFunction {
            domain1: ColumnValue::UInts(vec![]),
            offsets: ColumnValue::UInts(vec![]),
            domain2: ColumnValue::UInts(vec![]),
            codomain: ColumnValue::UInts(vec![]),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        assert!(tile.is_terminal());
    }

    // ── helpers for merge / to_guard / remove_guarded tests ──────────────────

    /// A SealedFunction tile mapping `domain` ints to `codomain` ints.
    fn sf_int(domain: Vec<i64>, codomain: Vec<i64>, pred: Predicate) -> Tile {
        Tile::SealedFunction {
            domain: ColumnValue::Ints(domain),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(codomain))),
            domain_predicate: pred,
            deleted: BitSet::new(),
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
            BitSet::new(),
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
    fn to_guard_curried_function_nonempty_domain_predicate_produces_or() {
        // When domain_predicate is non-False it should appear as a second arm of an Or
        // alongside the domain2-derived codomain guard.
        let pred = Predicate::LessThanEq(Value::UInt(0));
        let tile = cf_uint_int(vec![0], vec![0], vec![10, 11], vec![100, 110], pred.clone());
        let guard = tile.to_guard();
        // Expect Or([Codomain(Domain(domain2_pred)), Domain(pred)])
        let TileGuard::Or(arms) = guard else {
            panic!("expected Or guard when domain_predicate is non-False, got {guard:?}");
        };
        assert_eq!(arms.len(), 2);
        // One arm covers domain1 (the released-region predicate).
        assert!(
            arms.iter()
                .any(|a| matches!(a, TileGuard::Function(FunctionGuard::Domain(_))))
        );
        // One arm covers domain2 (the codomain inner guard).
        assert!(
            arms.iter()
                .any(|a| matches!(a, TileGuard::Function(FunctionGuard::Codomain(_))))
        );
    }

    #[test]
    fn to_guard_curried_function_empty_domain2_filters_codomain_arm() {
        // When domain2 is empty its guard is Predicate::False (empty).  flatten_or must
        // filter it out, leaving only the domain1 predicate as a plain Domain guard — not
        // wrapped in an Or.
        let pred = Predicate::LessThanEq(Value::UInt(5));
        let tile = cf_uint_int(vec![], vec![], vec![], vec![], pred.clone());
        let guard = tile.to_guard();
        // The codomain arm is empty → filtered; only the domain arm remains.
        let TileGuard::Function(FunctionGuard::Domain(result_pred)) = guard else {
            panic!("expected a single Domain guard, got {guard:?}");
        };
        assert_eq!(result_pred, pred);
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
        // Logically removes domain value 1 (index 0); physical arrays are unchanged.
        let pred = Predicate::from_column_value(&ColumnValue::Ints(vec![1]));
        let mut tile = sf_int(vec![1, 2], vec![10, 20], Predicate::True);
        tile.remove_guarded(TileGuard::Function(FunctionGuard::Domain(pred)));
        // Logical length excludes deleted entries.
        assert_eq!(tile.len(), 1);
        let Tile::SealedFunction {
            domain,
            codomain,
            deleted,
            ..
        } = &tile
        else {
            panic!("expected SealedFunction");
        };
        // Physical arrays are unchanged.
        assert_eq!(*domain, ColumnValue::Ints(vec![1, 2]));
        assert_eq!(
            *codomain,
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20])))
        );
        // Index 0 (domain value 1) is logically deleted.
        assert!(deleted.contains(0), "index 0 should be deleted");
        assert!(!deleted.contains(1), "index 1 should not be deleted");
    }

    #[test]
    fn remove_guarded_sealed_function_full_release_clears() {
        let mut tile = sf_int(vec![1, 2], vec![10, 20], Predicate::True);
        let guard = tile.to_guard();
        tile.remove_guarded(guard);
        // Physical arrays are unchanged; logical length is 0.
        assert_eq!(tile.len(), 0);
    }

    #[test]
    fn remove_guarded_curried_function_removes_matching_domain2() {
        // d1=[0,1], offsets=[0,2], d2=[10,11,12], cod=[100,110,120]
        // Logically removes d2=11 (flat index 1); physical arrays are unchanged.
        let mut tile = cf_uint_int(
            vec![0, 1],
            vec![0, 2],
            vec![10, 11, 12],
            vec![100, 110, 120],
            Predicate::False,
        );
        let pred = Predicate::from_column_value(&ColumnValue::UInts(vec![11]));
        tile.remove_guarded(cf_release_guard(pred));
        let Tile::CurriedFunction {
            domain2,
            codomain,
            deleted,
            ..
        } = &tile
        else {
            panic!("expected CurriedFunction");
        };
        // Physical arrays unchanged.
        assert_eq!(*domain2, ColumnValue::UInts(vec![10, 11, 12]));
        assert_eq!(*codomain, ColumnValue::Ints(vec![100, 110, 120]));
        // Only flat index 1 (d2=11) is logically deleted.
        assert!(!deleted.contains(0));
        assert!(deleted.contains(1));
        assert!(!deleted.contains(2));
    }

    #[test]
    fn remove_guarded_curried_function_prunes_empty_group() {
        // d1=[0,1], offsets=[0,2], d2=[10,11,12], cod=[100,110,120]
        // Logically removes d2=10 (idx 0) and d2=11 (idx 1); physical arrays unchanged.
        let mut tile = cf_uint_int(
            vec![0, 1],
            vec![0, 2],
            vec![10, 11, 12],
            vec![100, 110, 120],
            Predicate::False,
        );
        let pred = Predicate::from_column_value(&ColumnValue::UInts(vec![10, 11]));
        tile.remove_guarded(cf_release_guard(pred));
        let Tile::CurriedFunction { deleted, .. } = &tile else {
            panic!("expected CurriedFunction");
        };
        assert!(deleted.contains(0));
        assert!(deleted.contains(1));
        assert!(!deleted.contains(2));
    }

    #[test]
    fn remove_guarded_curried_function_domain_removes_whole_group() {
        // d1=[0,1], offsets=[0,2], d2=[10,11,12], cod=[100,110,120]
        // Logically removes group 0 (flat indices 0,1) via domain guard on d1=0.
        let mut tile = cf_uint_int(
            vec![0, 1],
            vec![0, 2],
            vec![10, 11, 12],
            vec![100, 110, 120],
            Predicate::False,
        );
        let pred = Predicate::from_column_value(&ColumnValue::UInts(vec![0]));
        tile.remove_guarded(TileGuard::Function(FunctionGuard::Domain(pred)));
        let Tile::CurriedFunction { deleted, .. } = &tile else {
            panic!("expected CurriedFunction");
        };
        assert!(deleted.contains(0));
        assert!(deleted.contains(1));
        assert!(!deleted.contains(2));
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
        // After logical deletion, to_guard() still sees all physical entries, so
        // the guard is unchanged (including deleted entries for complete source releasing).
        let mut tile = cf_uint_int(
            vec![0, 1],
            vec![0, 2],
            vec![10, 11, 12],
            vec![100, 110, 120],
            Predicate::False,
        );
        let guard = tile.to_guard();
        tile.remove_guarded(guard.clone());
        assert_eq!(tile.to_guard(), guard);
        // All entries are logically deleted.
        assert_eq!(tile.len(), 0);
    }

    // ── Tile::retain (CurriedFunction) ────────────────────────────────────────

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
