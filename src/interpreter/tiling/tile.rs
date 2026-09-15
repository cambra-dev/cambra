//! The [`Tile`] type: the materialized data exchanged between operators, plus
//! [`validate_tile`] for dev-build structural checks.

use std::collections::{HashMap, HashSet};

use bit_set::BitSet;
use bit_vec::BitVec;

/// The logically removed elements of a curried tile, **one set per domain level**.
///
/// The level is part of the index. A bit in level `k` is a position in `domains[k]`, so a
/// removed group and a removed entry are different bits in different sets rather than two
/// readings of one — and a producer says which it holds at the point it builds one. Reading
/// the two as one index space is what put a group ordinal into the innermost set, twice, in
/// operators that had every other field right.
///
/// A level with nothing removed need not be stored, so a `Deleted` may be shorter than the
/// tile is deep and [`Deleted::none`] is the empty one.
#[derive(Clone, Debug, Default)]
pub struct Deleted {
    levels: Vec<BitSet>,
}

/// A level stored empty and a level not stored are the same statement, so equality reads the
/// levels rather than the vector. Deriving it would make [`Deleted::level_mut`] observable:
/// reaching for a level to insert nothing would leave a value that compares unequal to the
/// one it started as, and `Tile::contains_guarded` decides on exactly that comparison.
impl PartialEq for Deleted {
    fn eq(&self, other: &Self) -> bool {
        let depth = self.levels.len().max(other.levels.len());
        (0..depth).all(|k| self.level(k) == other.level(k))
    }
}

impl Eq for Deleted {}

impl Deleted {
    /// Nothing removed, at any level.
    pub fn none() -> Self {
        Self::default()
    }

    /// The positions removed at `level`, which is a position in that level's domain column.
    pub fn at_level(level: usize, removed: BitSet) -> Self {
        let mut levels = vec![BitSet::new(); level];
        levels.push(removed);
        Self { levels }
    }

    /// The set at `level`, empty where nothing there is removed.
    pub fn level(&self, level: usize) -> &BitSet {
        static EMPTY: std::sync::OnceLock<BitSet> = std::sync::OnceLock::new();
        self.levels
            .get(level)
            .unwrap_or_else(|| EMPTY.get_or_init(BitSet::new))
    }

    /// The set at `level`, growing to reach it.
    pub fn level_mut(&mut self, level: usize) -> &mut BitSet {
        if self.levels.len() <= level {
            self.levels.resize(level + 1, BitSet::new());
        }
        &mut self.levels[level]
    }

    /// Whether nothing is removed anywhere.
    pub fn is_empty(&self) -> bool {
        self.levels.iter().all(BitSet::is_empty)
    }

    /// The number of levels this stores, which may be fewer than the tile is deep.
    pub fn stored_levels(&self) -> usize {
        self.levels.len()
    }

    /// Remove everything, at every level.
    pub fn clear(&mut self) {
        self.levels.clear();
    }
}

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
        /// The region of the **domain** for which no new elements will ever be seen.
        /// Calls to `get` can still return tiles with data in this region, but such data is guaranteed to
        /// be the same as data already observed.
        domain_predicate: Predicate,
        /// Set of indices (into `domain`/`codomain`) that have been logically removed by
        /// filtering.  1 = deleted; an empty set means all entries are present.  The full
        /// physical arrays are preserved so that `to_guard` can report every domain value
        /// that has ever been seen—not just the survivors—enabling complete source releasing.
        deleted: BitSet,
    },
    /// A curried function of any depth, `D₀ → D₁ → … → Dₙ₋₁ → C`.
    ///
    /// Stored in a Compressed Sparse Row (CSR)-like layout, one offsets array per level
    /// above the innermost. `domains[0]` is sorted so lookups can be done in O(log n) via
    /// binary search; `offsets[k][i]` is the start index in `domains[k + 1]` for element
    /// `i` of `domains[k]`, and element `i`'s run ends where `i + 1`'s begins (at the end
    /// of the level, for the last element). `codomain` is the flattened sequence of
    /// codomain values across every innermost group, so vectorized transformations over
    /// the full codomain are straightforward.
    ///
    /// The offsets are what a [`Tile::SealedFunction`] codomain cannot supply: a codomain
    /// tile is vectorized one entry per domain position, which can express a nested
    /// function only when every parent holds the same inner domain. A per-parent inner
    /// domain is ragged, and ragged needs the offsets.
    CurriedFunction {
        /// Domain columns, outermost first. `domains[0]` is sorted and dense; each later
        /// one is flattened across its parent's groups. Always at least two.
        domains: Vec<ColumnValue>,
        /// One offsets column per level above the innermost, so
        /// `offsets.len() == domains.len() - 1`. Each is `ColumnValue::UInts`.
        offsets: Vec<ColumnValue>,
        /// The codomain, vectorized one entry per innermost domain element — the same
        /// convention [`Self::SealedFunction`]'s codomain follows, so a fold may leave a
        /// [`Self::Aggregation`] here.
        codomain: Box<Tile>,
        /// The region of `domains[0]` for which no new elements will ever be seen — the
        /// same statement [`Self::SealedFunction`]'s makes, and covering each key in the
        /// region together with every level below it.
        domain_predicate: Predicate,
        /// Logically removed elements, one set per domain level ([`Deleted`]). 1 = removed;
        /// empty means every element is present. Preserved for the same reason as
        /// [`Tile::SealedFunction::deleted`]: so `to_guard` can report every innermost
        /// domain value ever seen, enabling complete source releasing.
        ///
        /// Every producer today removes at the innermost level only, a group being removed
        /// by removing its entries. The level is stored rather than assumed because the two
        /// index spaces are otherwise the same type, which is how a group ordinal reached
        /// the innermost set.
        deleted: Deleted,
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
        /// Keys that will receive no further write, deduplicated and in no
        /// meaningful order — it is read as a set (`Value` is not `Ord`, and
        /// membership is the only question asked of it). A key closes once every writer
        /// whose write set contains it has finished, never later than the whole store
        /// and earlier whenever some other writer is still running: a store whose keys
        /// are written by different blocks closes each key as that block drains.
        ///
        /// **Neither axis derives from the other.** A key that is never written
        /// appears in no delta, so the tile does not know its own key universe and
        /// cannot read "every key listed here is closed" as "the store is closed".
        /// They close different things: `terminal` closes the commit-time
        /// *domain*, `closed_keys` closes a key's *write set*.
        ///
        /// Only a per-key **change** stream may reduce on this. A carry-forward
        /// projection gains a position at every tick, including ticks that wrote
        /// some other key, so it is closed by `terminal` alone — see
        /// [`StoreValueStream`](crate::interpreter::commit_operator::StoreValueStream).
        closed_keys: Vec<Value>,
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
                domains, deleted, ..
            } => {
                let innermost = domains.len() - 1;
                domains[innermost].len() - deleted.level(innermost).len()
            }
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
                    domains: s_domains,
                    offsets: s_offsets,
                    codomain: s_codomain,
                    domain_predicate: s_pred,
                    deleted: s_deleted,
                },
                Tile::CurriedFunction {
                    domains: o_domains,
                    offsets: o_offsets,
                    codomain: o_codomain,
                    domain_predicate: o_pred,
                    deleted: o_deleted,
                },
            ) => {
                assert_eq!(
                    s_domains.len(),
                    o_domains.len(),
                    "merging curried tiles of different depths"
                );
                // Each level concatenates, so o's offsets into the level below shift by
                // that level's current size in s, and a removal shifts by its own level's.
                // Read every length before appending.
                let level_lens: Vec<usize> = s_domains.iter().map(ColumnValue::len).collect();
                for (k, mut o_level) in o_offsets.into_iter().enumerate() {
                    o_level.for_each_uint(|u| *u += level_lens[k + 1]);
                    s_offsets[k].append(o_level);
                }
                for (s_level, o_level) in s_domains.iter_mut().zip(o_domains) {
                    s_level.append(o_level);
                }
                s_codomain.merge(*o_codomain);
                *s_pred = s_pred.union(&o_pred);
                for (k, shift) in level_lens
                    .iter()
                    .enumerate()
                    .take(o_deleted.stored_levels())
                {
                    let removed: Vec<usize> = o_deleted.level(k).iter().collect();
                    let s_level = s_deleted.level_mut(k);
                    for idx in removed {
                        s_level.insert(idx + shift);
                    }
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
            // it), and `closed_keys` unions for the same reason — closure is
            // monotone, so a key either side reports closed stays closed. Mirrors
            // the `SealedFunction` arm sans `deleted`: a store releases by
            // physically dropping a decided prefix (see `remove_guarded`), never by
            // logical tombstoning.
            (
                Tile::Store {
                    changes: s_changes,
                    deltas: s_deltas,
                    frontier: s_frontier,
                    terminal: s_terminal,
                    closed_keys: s_closed,
                },
                Tile::Store {
                    changes: o_changes,
                    deltas: o_deltas,
                    frontier: o_frontier,
                    terminal: o_terminal,
                    closed_keys: o_closed,
                },
            ) => {
                s_changes.append(o_changes);
                s_deltas.append(o_deltas);
                *s_frontier = s_frontier.union(&o_frontier);
                *s_terminal = *s_terminal || o_terminal;
                for k in o_closed {
                    if !s_closed.contains(&k) {
                        s_closed.push(k);
                    }
                }
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
                domains,
                offsets,
                codomain,
                deleted,
                ..
            } => {
                // The mask is over the flat innermost rows.
                let inner = domains.last().expect("a curried tile has levels");
                assert_eq!(
                    mask.len(),
                    inner.len(),
                    "retain mask length must equal the innermost domain length"
                );
                // Combine the caller's mask with the logical-deletion bits, as the sealed
                // case does: keep row j only if the mask says so and it is not deleted.
                let innermost_removed = deleted.level(domains.len() - 1);
                let keep: BitVec = mask
                    .iter()
                    .enumerate()
                    .map(|(j, keep)| keep && !innermost_removed.contains(j))
                    .collect();
                retain_levels(domains, offsets, codomain, &keep);
                deleted.clear();
            }
            // An aggregation is flat columns over the same positions its function's
            // innermost level has, so it filters position-wise like a scalar does. A
            // per-level fold leaves one under a curried tile, which is what reaches here.
            Tile::Aggregation {
                accumulator,
                terminal,
                ..
            } => {
                accumulator.retain(mask);
                terminal.retain(mask);
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
            Tile::SealedFunction { deleted, .. } => {
                for (i, keep) in mask.iter().enumerate() {
                    if !keep {
                        deleted.insert(i);
                    }
                }
            }
            // The mask is over the innermost level, which is where the codomain is
            // vectorized and so where a caller's per-entry decision lands.
            Tile::CurriedFunction {
                domains, deleted, ..
            } => {
                let innermost = domains.len() - 1;
                let level = deleted.level_mut(innermost);
                for (i, keep) in mask.iter().enumerate() {
                    if !keep {
                        level.insert(i);
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
                deleted, domains, ..
            } => {
                if deleted.is_empty() {
                    return;
                }
                domains[domains.len() - 1].len()
            }
            _ => return,
        };
        // Build the keep-mask from the deleted set, then let retain() do the work
        // (retain also clears deleted).
        let deleted_clone = match self {
            Tile::SealedFunction { deleted, .. } => deleted.clone(),
            Tile::CurriedFunction {
                domains, deleted, ..
            } => deleted.level(domains.len() - 1).clone(),
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
            // **A guard nests as deeply as the type does.** `Domain(p)` names the
            // outermost level; each `Codomain` wrapper steps one level in, so
            // `Codomain(Domain(p))` names level 1 and `Codomain(Codomain(Domain(p)))`
            // level 2. Marking is always over the innermost rows, so a named element
            // takes its whole subtree with it.
            (
                Tile::CurriedFunction {
                    domains,
                    offsets,
                    deleted,
                    ..
                },
                guard @ TileGuard::Function(_),
            ) => {
                let Some((level, pred)) = guard_level(&guard) else {
                    unimplemented!(
                        "CurriedFunction remove_guarded only supports a Domain under some \
                         number of Codomains, got {guard:?}"
                    )
                };
                assert!(
                    level < domains.len(),
                    "a release guard names level {level} of a {}-level curried tile",
                    domains.len()
                );
                let owner = ancestor_at(domains, offsets, level);
                let named = domains[level].clone();
                let innermost = domains.len() - 1;
                let removed = deleted.level_mut(innermost);
                for (row, &ancestor) in owner.iter().enumerate() {
                    if pred.contains(&named.index_at(ancestor)) {
                        removed.insert(row);
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
    /// For CurriedFunction, `Domain` over the groups the predicate calls whole, plus
    /// `Codomain(Domain(...))` over the keys of the groups it does not
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
            // **A key is released by its group where the group is whole.** A codomain guard
            // names keys and says nothing about which group they sit in, so releasing one
            // releases it in *every* group — sound only while no key repeats across groups,
            // which a curried-function tile permits (`validate_tile` asks for uniqueness
            // within a group and no more) and a collection held per row routinely does. The
            // `domain_predicate` is what separates the two cases: it names the groups that
            // will see no new elements, each together with its whole list, so `Domain` over
            // that region releases those groups outright and their keys need no naming. A
            // group outside it may still grow, so its keys are named the only way the
            // vocabulary allows.
            Tile::CurriedFunction {
                domains,
                offsets,
                domain_predicate,
                ..
            } => {
                let open_keys = Predicate::from_column_value(&keys_of_open_groups(
                    domains,
                    offsets,
                    domain_predicate,
                ));
                // Those keys are the innermost level's, so the guard names that level: one
                // `Codomain` per level in ([`guard_level`]). Two levels make that one
                // wrapper, and deeper it is more — a single wrapper would name level 1 with
                // the innermost level's keys.
                TileGuard::flatten_or(vec![
                    guard_at_level(domains.len() - 1, open_keys),
                    TileGuard::Function(FunctionGuard::Domain(domain_predicate.clone())),
                ])
            }
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
    /// Pass [`Deleted::none`] when nothing is logically removed.
    pub fn curried_function(
        domains: Vec<ColumnValue>,
        offsets: Vec<ColumnValue>,
        codomain: Box<Tile>,
        domain_predicate: Predicate,
        deleted: Deleted,
    ) -> Tile {
        let result = Tile::CurriedFunction {
            domains,
            offsets,
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

    /// For each element of `level`, the values of its ancestors from the outermost level
    /// down to and including itself.
    ///
    /// A key repeats across its siblings' groups, so an element deeper than the outermost
    /// is identified by its path and not by its own value — which is what a per-level fold
    /// has to key its accumulators on.
    pub fn curried_paths_at(&self, level: usize) -> Vec<Vec<Value>> {
        let Tile::CurriedFunction {
            domains, offsets, ..
        } = self
        else {
            panic!("curried_paths_at expects a curried tile, got {self:?}")
        };
        let mut paths: Vec<Vec<Value>> = (0..domains[0].len())
            .map(|i| vec![domains[0].index_at(i)])
            .collect();
        for k in 0..level {
            let starts = level_offsets(&offsets[k]);
            let below_len = domains[k + 1].len();
            let mut next = vec![Vec::new(); below_len];
            for (i, parent) in paths.iter().enumerate() {
                let (start, end) = level_run(starts, i, below_len);
                for (j, slot) in next.iter_mut().enumerate().take(end).skip(start) {
                    let mut path = parent.clone();
                    path.push(domains[k + 1].index_at(j));
                    *slot = path;
                }
            }
            paths = next;
        }
        paths
    }
}

/// The offsets column at one level, as the `usize` run-starts it is required to be.
fn level_offsets(offsets: &ColumnValue) -> &[usize] {
    match offsets {
        ColumnValue::UInts(v) => v,
        other => panic!("CurriedFunction offsets must be UInts, got {other:?}"),
    }
}

/// The half-open run of level-below indices belonging to element `i`.
///
/// The last element runs to the end of the level, which is why the level's length is
/// needed: the offsets column stores starts only.
fn level_run(offsets: &[usize], i: usize, below_len: usize) -> (usize, usize) {
    let start = offsets[i];
    let end = if i + 1 < offsets.len() {
        offsets[i + 1]
    } else {
        below_len
    };
    (start, end)
}

/// Which elements of each level have at least one surviving descendant, innermost first.
///
/// A curried tile's offsets are strictly ascending, so a group holding nothing cannot be
/// represented at all ([`validate_tile`]). Pruning therefore has to propagate upward: an
/// element whose whole run below is gone goes with it, and so on to the outermost level.
fn alive_levels(
    domains: &[ColumnValue],
    offsets: &[ColumnValue],
    keep_inner: &BitVec,
) -> Vec<BitVec> {
    let depth = domains.len();
    let mut alive: Vec<BitVec> = domains
        .iter()
        .map(|d| BitVec::from_elem(d.len(), false))
        .collect();
    for j in 0..domains[depth - 1].len() {
        alive[depth - 1].set(j, keep_inner[j]);
    }
    for k in (0..depth - 1).rev() {
        let below_len = domains[k + 1].len();
        let run_starts = level_offsets(&offsets[k]);
        for i in 0..domains[k].len() {
            let (start, end) = level_run(run_starts, i, below_len);
            let any = (start..end).any(|j| alive[k + 1][j]);
            alive[k].set(i, any);
        }
    }
    alive
}

/// Rebuild every level, keeping the innermost rows `keep_inner` selects and dropping each
/// ancestor left with none.
///
/// The kept children of a surviving parent stay contiguous, because the kept indices at a
/// level preserve their original order and the runs they came from were disjoint and
/// ordered — which is what lets a parent's new offset be the rank of its first kept child.
fn retain_levels(
    domains: &mut [ColumnValue],
    offsets: &mut Vec<ColumnValue>,
    codomain: &mut Tile,
    keep_inner: &BitVec,
) {
    let depth = domains.len();
    let alive = alive_levels(domains, offsets, keep_inner);
    let kept: Vec<Vec<usize>> = (0..depth)
        .map(|k| (0..domains[k].len()).filter(|&i| alive[k][i]).collect())
        .collect();

    let mut new_offsets = Vec::with_capacity(depth - 1);
    for k in 0..depth - 1 {
        let below_len = domains[k + 1].len();
        let run_starts = level_offsets(&offsets[k]);
        let mut rank_of = vec![usize::MAX; below_len];
        for (rank, &j) in kept[k + 1].iter().enumerate() {
            rank_of[j] = rank;
        }
        let mut starts = Vec::with_capacity(kept[k].len());
        for &i in &kept[k] {
            let (start, end) = level_run(run_starts, i, below_len);
            let first = (start..end)
                .find(|&j| alive[k + 1][j])
                .expect("a level element survives only when a descendant does");
            starts.push(rank_of[first]);
        }
        new_offsets.push(ColumnValue::UInts(starts));
    }

    for k in 0..depth {
        domains[k] = domains[k].select_indices(kept[k].iter().copied(), kept[k].len());
    }
    // The codomain is vectorized over the innermost level, so it keeps exactly the rows
    // that level kept.
    let mut inner_mask = BitVec::from_elem(alive[depth - 1].len(), false);
    for &row in &kept[depth - 1] {
        inner_mask.set(row, true);
    }
    codomain.retain(&inner_mask);
    *offsets = new_offsets;
}

/// The keys of the groups `domain_predicate` does **not** call whole.
///
/// A group inside the predicate is released by its own `domain1` value, so naming its keys
/// would release them in every other group too ([`Tile::to_guard`]).
fn keys_of_open_groups(
    domains: &[ColumnValue],
    offsets: &[ColumnValue],
    domain_predicate: &Predicate,
) -> ColumnValue {
    let inner = &domains[domains.len() - 1];
    if domain_predicate.is_false() {
        return inner.clone();
    }
    let outer = &domains[0];
    let owner = ancestor_at(domains, offsets, 0);
    let open: Vec<usize> = (0..inner.len())
        .filter(|&row| !domain_predicate.contains(&outer.index_at(owner[row])))
        .collect();
    let kept = open.len();
    inner.select_indices(open.into_iter(), kept)
}

/// The guard naming `level` with `pred`: the inverse of [`guard_level`].
fn guard_at_level(level: usize, pred: Predicate) -> TileGuard {
    (0..level).fold(
        TileGuard::Function(FunctionGuard::Domain(pred)),
        |inner, _| TileGuard::Function(FunctionGuard::Codomain(Box::new(inner))),
    )
}

/// The level a release guard names, and the predicate it names it with.
///
/// `Domain(p)` is level 0 and each enclosing `Codomain` steps one level in, mirroring how
/// the curried type nests. Any other shape is not a level reference.
fn guard_level(guard: &TileGuard) -> Option<(usize, Predicate)> {
    let mut level = 0;
    let mut current = guard;
    loop {
        match current {
            TileGuard::Function(FunctionGuard::Domain(pred)) => {
                return Some((level, pred.clone()));
            }
            TileGuard::Function(FunctionGuard::Codomain(inner)) => {
                level += 1;
                current = inner;
            }
            _ => return None,
        }
    }
}

/// For each innermost row, the index of the element at `level` that owns it.
fn ancestor_at(domains: &[ColumnValue], offsets: &[ColumnValue], level: usize) -> Vec<usize> {
    let depth = domains.len();
    let mut owner: Vec<usize> = (0..domains[level].len()).collect();
    for k in level..depth - 1 {
        let starts = level_offsets(&offsets[k]);
        let below_len = domains[k + 1].len();
        let mut next = vec![0usize; below_len];
        for (i, &parent) in owner.iter().enumerate() {
            let (start, end) = level_run(starts, i, below_len);
            for row in next.iter_mut().take(end).skip(start) {
                *row = parent;
            }
        }
        owner = next;
    }
    owner
}

pub fn validate_tile(tile: &Tile) -> bool {
    match tile {
        Tile::CurriedFunction {
            domains,
            offsets,
            codomain,
            domain_predicate: _,
            deleted,
        } => {
            // At least two levels, one offsets column between each adjacent pair, and a
            // codomain value per innermost element.
            if domains.len() < 2
                || offsets.len() + 1 != domains.len()
                || domains[domains.len() - 1].len() != codomain.len()
            {
                return false;
            }
            // Each stored level is bounded by that level's own domain column. The level
            // is part of the index ([`Deleted`]), so a group and an entry are no longer the
            // same bit read two ways, and this bound checks each for what it is.
            if deleted.stored_levels() > domains.len()
                || (0..deleted.stored_levels())
                    .any(|k| deleted.level(k).iter().any(|i| i >= domains[k].len()))
            {
                return false;
            }
            // The outermost keys are unique; a deeper level is unique only *within* a
            // group, since a key may repeat across its siblings' groups.
            let outer: Vec<Value> = domains[0].clone().drain_to_value_iter().collect();
            if HashSet::<Value>::from_iter(outer.iter().cloned()).len() != domains[0].len() {
                return false;
            }
            (0..offsets.len()).all(|k| {
                let ColumnValue::UInts(starts) = &offsets[k] else {
                    return false;
                };
                let below_len = domains[k + 1].len();
                let below: Vec<Value> = domains[k + 1].clone().drain_to_value_iter().collect();
                starts.len() == domains[k].len()
                    && starts.windows(2).all(|w| w[0] < w[1])
                    && starts.last().is_none_or(|o| *o < below_len)
                    && (0..starts.len()).all(|i| {
                        let (start, end) = level_run(starts, i, below_len);
                        end - start
                            == HashSet::<Value>::from_iter(below[start..end].iter().cloned()).len()
                    })
            })
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
            domains: vec![ColumnValue::UInts(vec![]), ColumnValue::UInts(vec![])],
            offsets: vec![ColumnValue::UInts(vec![])],
            codomain: Box::new(Tile::Scalar(ColumnValue::UInts(vec![]))),
            domain_predicate: Predicate::True,
            deleted: Deleted::none(),
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
            vec![ColumnValue::UInts(d1), ColumnValue::UInts(d2)],
            vec![ColumnValue::UInts(offsets)],
            Box::new(Tile::Scalar(ColumnValue::Ints(cod))),
            pred,
            Deleted::none(),
        )
    }

    /// The codomain arm names the level its keys came from, which at three levels is not
    /// level 1. `keys_of_open_groups` answers the innermost domain, and [`guard_level`]
    /// reads one `Codomain` wrapper as level 1 — so a single wrapper would hand a consumer
    /// the innermost keys against the middle level's domain.
    #[test]
    fn to_guard_curried_function_names_the_innermost_level_at_depth_three() {
        let tile = Tile::curried_function(
            vec![
                ColumnValue::UInts(vec![0]),
                ColumnValue::UInts(vec![10, 11]),
                ColumnValue::UInts(vec![100, 101, 102, 103]),
            ],
            vec![ColumnValue::UInts(vec![0]), ColumnValue::UInts(vec![0, 2])],
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3, 4]))),
            // Every group open, so every innermost key is named.
            Predicate::False,
            Deleted::none(),
        );
        let guard = tile.to_guard();
        let (level, pred) = guard_level(&guard).expect("a level reference, got {guard:?}");
        assert_eq!(level, 2, "the innermost level of a three-level tile");
        assert!(
            pred.contains(&Value::UInt(100)) && pred.contains(&Value::UInt(103)),
            "the arm carries the innermost keys, got {pred:?}"
        );
    }

    /// A level stored empty is the level absent, which is what keeps [`Deleted::level_mut`]
    /// from being observable — `Tile::contains_guarded` decides by comparing a probe against
    /// the tile it was cloned from.
    #[test]
    fn deleted_compares_by_level_not_by_storage() {
        let mut reached = Deleted::none();
        let _ = reached.level_mut(3);
        assert_eq!(reached, Deleted::none(), "reaching a level removes nothing");
        assert!(reached.is_empty());

        let mut one = BitSet::new();
        one.insert(1);
        let marked = Deleted::at_level(2, one.clone());
        assert_eq!(
            marked.level(2),
            &one,
            "the bit is at the level it was given"
        );
        assert!(
            marked.level(1).is_empty() && marked.level(9).is_empty(),
            "every other level, stored or not, is empty"
        );
        assert_ne!(
            marked,
            Deleted::at_level(1, one),
            "the level is part of the index"
        );
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

    /// `⊕` rejects a position the tile already holds, whatever value arrives
    /// with it.
    ///
    /// `docs/operational-semantics/semantics.md`, "Integrity properties" makes
    /// compatibility a requirement rather than a consequence: `⊕` is partial, and
    /// a second claim on one position is a combination it does not define. Same
    /// value or not makes no difference — the domain column carries the duplicate
    /// either way, so [`validate_tile`] rejects it and `merge`'s closing
    /// `debug_assert!` fires. Pinned because the alternative reading, that an
    /// identical re-merge is a harmless no-op, holds for no tile shape here: a
    /// `Sum` accumulator would double, and a `Scalar` would grow a second entry.
    #[test]
    #[cfg_attr(
        not(debug_assertions),
        ignore = "the tile check `merge` closes with is a `debug_assert!`"
    )]
    #[should_panic(expected = "Invalid tile")]
    fn merge_rejects_a_repeated_position_carrying_the_same_value() {
        let mut tile = sf_int(vec![1], vec![10], Predicate::False);
        tile.merge(sf_int(vec![1], vec![10], Predicate::False));
    }

    /// A store's changelog rejects a tick it already holds, for the same reason.
    ///
    /// The ticks are strictly ascending, so a repeat is not merely redundant: the
    /// fold that reads the changelog resolves a tick to the latest change at or
    /// below it, and two changes at one tick leave that undefined.
    #[test]
    #[cfg_attr(
        not(debug_assertions),
        ignore = "the tile check `merge` closes with is a `debug_assert!`"
    )]
    #[should_panic(expected = "Invalid tile")]
    fn merge_rejects_a_repeated_commit_tick() {
        let store = || Tile::Store {
            changes: ColumnValue::from_uints(vec![0]),
            deltas: ColumnValue::Variants(vec![Value::UInt(1)]),
            frontier: Predicate::False,
            terminal: false,
            closed_keys: Vec::new(),
        };
        let mut tile = store();
        tile.merge(store());
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

    /// A group the predicate calls whole is released by its own key; only the groups it
    /// leaves open contribute a codomain arm. Keys repeat across groups here, which is what
    /// makes the distinction observable: naming a whole group's keys would release them in
    /// the open group too.
    #[test]
    fn to_guard_curried_function_names_only_the_open_groups_keys() {
        // Groups 0 and 1, both keyed 10 and 11; the predicate calls group 0 whole.
        let tile = cf_uint_int(
            vec![0, 1],
            vec![0, 2],
            vec![10, 11, 10, 11],
            vec![100, 110, 200, 210],
            Predicate::LessThanEq(Value::UInt(0)),
        );
        let TileGuard::Or(arms) = tile.to_guard() else {
            panic!("expected an Or over the two halves")
        };
        let codomain = arms
            .iter()
            .find_map(|a| match a {
                TileGuard::Function(FunctionGuard::Codomain(inner)) => Some(inner.as_ref()),
                _ => None,
            })
            .expect("the open group contributes a codomain arm");
        let TileGuard::Function(FunctionGuard::Domain(keys)) = codomain else {
            panic!("a codomain arm guards the inner domain, got {codomain:?}")
        };
        // Group 1's keys, named once each rather than twice.
        assert!(keys.contains(&Value::UInt(10)));
        assert!(keys.contains(&Value::UInt(11)));
        assert!(
            arms.iter()
                .any(|a| matches!(a, TileGuard::Function(FunctionGuard::Domain(_)))),
            "the whole group is released by its own key"
        );
    }

    /// With every group whole there is nothing left for a codomain arm to name, so the
    /// guard is the domain half alone — which is what lets a consumer recognise it as
    /// universal where the predicate is.
    #[test]
    fn to_guard_curried_function_whole_groups_name_no_keys() {
        let tile = cf_uint_int(
            vec![0],
            vec![0],
            vec![10, 11],
            vec![100, 110],
            Predicate::True,
        );
        let guard = tile.to_guard();
        assert!(
            matches!(
                guard,
                TileGuard::Function(FunctionGuard::Domain(Predicate::True))
            ),
            "expected the domain half alone, got {guard:?}"
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
            domains,
            codomain,
            deleted,
            ..
        } = &tile
        else {
            panic!("expected CurriedFunction");
        };
        // Physical arrays unchanged.
        assert_eq!(domains[1], ColumnValue::UInts(vec![10, 11, 12]));
        assert_eq!(
            **codomain,
            Tile::Scalar(ColumnValue::Ints(vec![100, 110, 120]))
        );
        // Only flat index 1 (d2=11) is logically deleted.
        assert!(!deleted.level(1).contains(0));
        assert!(deleted.level(1).contains(1));
        assert!(!deleted.level(1).contains(2));
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
        assert!(deleted.level(1).contains(0));
        assert!(deleted.level(1).contains(1));
        assert!(!deleted.level(1).contains(2));
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
        assert!(deleted.level(1).contains(0));
        assert!(deleted.level(1).contains(1));
        assert!(!deleted.level(1).contains(2));
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
