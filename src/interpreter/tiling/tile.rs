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
    /// A collection, `keys ⤇ values` — one new dimension over the rows it sits in.
    ///
    /// **A tile is a value of its type vectorized over `R` rows**, and `R` is set by
    /// position: 1 at the top level, and inside a collection's `values`, that collection's
    /// key count. A [`Self::Scalar`] is one entry per row and a [`Self::Record`] is one
    /// sub-tile per field at the same `R`; a collection groups instead of pairing, which is
    /// what `row_starts` records.
    ///
    /// Stored Compressed-Sparse-Row-wise: `keys` is every row's keys run together, and
    /// `values` is a tile over those keys. A chain of collections nests one node per level,
    /// holding the same columns a flat level list would — and unlike a flat list it can say
    /// where a record sits between two levels, which is what lets records and collections
    /// nest freely.
    Function {
        /// Where each row's run of keys begins in `keys`, one entry per row. **Non-decreasing**:
        /// two equal starts are a row whose group holds nothing. A key with an empty group is
        /// a collection that is empty, which an aggregate folds to its identity; a key that is
        /// gone is absent from `keys` instead.
        ///
        /// At the top level this is `[0]` — the one row, whose group is the whole collection.
        row_starts: ColumnValue,
        /// Every row's keys, run together. Sorted within a row, so a lookup inside one is a
        /// binary search.
        keys: ColumnValue,
        /// The values, a tile over `keys` — so a fold may leave an [`Self::Aggregation`] here.
        values: Box<Tile>,
        /// The region of `keys` whose values are complete: no new element will be seen under
        /// them, at any depth. Covering every key says the key set itself is closed, which is
        /// what makes [`Tile::is_terminal`] read this as one flag.
        domain_predicate: Predicate,
        /// Logically removed keys. 1 = removed; empty means every key is present. `keys` is
        /// preserved so `to_guard` can report every key ever seen, enabling complete source
        /// releasing.
        deleted: BitSet,
    },
    /// A Tile representing the state of a scalar aggregation.
    Aggregation {
        /// The type of aggregate
        kind: AggregateKind,
        /// The accumulator state of the specific aggregate, one value per row. A tile
        /// rather than a column because a fold may yield an *element*: `Sole` holds
        /// whatever shape the element has, levels included.
        accumulator: Box<Tile>,
        /// Boolean representing whether the aggregate is complete
        terminal: ColumnValue,
    },
    /// A **transactional store**: a right-continuous step function
    /// `Txn ⇒ {key: value}` over the commit-time domain, materialized as one
    /// **changelog per key** — the ticks at which that key was written, against
    /// the values written there.
    ///
    /// This is not a [`Tile::Function`] and must not be treated as one:
    /// in a collection a key absent from a changelog is
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
        /// One changelog per store key: a [`Tile::Record`] whose fields are the key
        /// space, each field a [`Tile::Function`] over one row — the commit ticks at
        /// which that key was written, ascending, against the values written there.
        /// A tick a key's changelog omits did not write it, so its value holds.
        ///
        /// A key's values are a tile, so a collection-valued key carries its elements
        /// as a level rather than as one materialized cell; and a write set spanning
        /// several keys lands as one tick in each of their changelogs, which is what
        /// replaces a per-tick heterogeneous map.
        state: Box<Tile>,
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
        /// **Neither axis derives from the other**, because they close different
        /// things: `terminal` closes the commit-time *domain*, `closed_keys` closes a
        /// key's *write set*. A store whose every key is closed still decides further
        /// ticks, each carrying every key's value forward.
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

    /// Whether this tile carries no data.
    ///
    /// There is no single *length* of a tile to compare against zero: a record's fields are
    /// columns of one entry per row under a codomain but independent collections in a
    /// product value, and a store counts decided positions rather than stored ones. Empty,
    /// though, means the same everywhere — nothing has arrived.
    pub fn is_empty(&self) -> bool {
        match self {
            Tile::Scalar(cv) => cv.is_empty(),
            // A product value is empty when every component is; a struct-of-arrays record
            // fills its fields together, so either reading agrees there.
            Tile::Record(m) => m.values().all(Tile::is_empty),
            // A collection with no live key holds nothing, and so does one whose values
            // hold nothing however many keys stand over them — which is what a full release
            // of a nested collection leaves behind.
            Tile::Function {
                keys,
                values,
                deleted,
                ..
            } => keys.len() == deleted.len() || values.is_empty(),
            Tile::Aggregation { accumulator, .. } => accumulator.is_empty(),
            // A `Store` is a right-continuous *step function* over its decided prefix, not a
            // list of change events: a tick absent from a key's changelog but at or below
            // the frontier is *decided*, its value holding from the latest earlier change.
            // So it is empty when nothing is decided, which an undecided (`False`) frontier
            // says and a `LessThanEq` watermark never does.
            Tile::Store { frontier, .. } => {
                !matches!(frontier, Predicate::LessThanEq(Value::UInt(_)))
            }
        }
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
                Tile::Function {
                    keys: key_column,
                    values: value_tile,
                    ..
                },
                Tiling::Function { keys, values },
            ) => key_column.is_compatible_with_extent(keys) && value_tile.check_from(values),
            (Tile::Aggregation { .. }, Tiling::Aggregation { .. }) => true,
            // The state is a changelog per key, which is what the tiling's own
            // `store_state` spells out; checking against that checks each key's change
            // ticks against the commit domain and its values against that key's tiling.
            (Tile::Store { state, .. }, tiling @ Tiling::Store { .. }) => {
                state.check_from(&tiling.store_state())
            }
            _ => false,
        }
    }

    pub fn is_terminal(&self) -> bool {
        match self {
            Tile::Scalar(cv) => !cv.is_empty(),
            Tile::Record(m) => m.values().all(Tile::is_terminal),
            Tile::Function {
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

    /// Merge the contents of `other` into `self`. Requires the two tiles to be compatible
    /// (i.e. non-overlapping).
    ///
    /// A merge extends a value with a part of it that arrived later. At the top level that
    /// means new **keys** of the outermost collection; everything beneath is then new
    /// **rows**, because a key of the level above is a row of the level below.
    pub fn merge(&mut self, other: Tile) {
        self.merge_part(other, true);
    }

    /// Append `other`'s rows after this tile's, rather than merging both into one row.
    ///
    /// The distinction [`Self::merge`] makes at the top level and carries down: a whole
    /// value's two halves describe the same one row, so its keys run together, while rows
    /// under a collection follow one another and a run shifts past the keys already there.
    /// An operator that concatenates collections — rather than reconciling two views of one
    /// — wants this.
    pub fn merge_rows(&mut self, other: Tile) {
        self.merge_part(other, false);
    }

    /// `merge`, knowing whether this tile is the whole value or sits under one.
    fn merge_part(&mut self, other: Tile, whole: bool) {
        match (&mut *self, other) {
            // Append: handles both "unknown → known" (empty + non-empty) and the vectorized
            // case where a scalar holds one value per row.
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
                s_kind.accumulate(s_acc, &o_acc, 0, o_acc.rows());
                let taken = std::mem::replace(s_term, ColumnValue::Units(0));
                *s_term = apply_binop_column(BinOpKind::BoolLogic(LogicKind::Or), taken, &o_term);
            }
            (
                Tile::Function {
                    row_starts: s_starts,
                    keys: s_keys,
                    values: s_values,
                    domain_predicate: s_pred,
                    deleted: s_deleted,
                },
                Tile::Function {
                    row_starts: o_starts,
                    keys: o_keys,
                    values: o_values,
                    domain_predicate: o_pred,
                    deleted: o_deleted,
                },
            ) => {
                let seen = s_keys.len();
                if whole {
                    // One row, and both describe it: the keys run together.
                    assert_eq!(
                        s_starts.len(),
                        1,
                        "a whole collection is its one row's group"
                    );
                } else {
                    // New rows, each starting past the keys already here.
                    let mut shifted = o_starts;
                    shifted.for_each_uint(|u| *u += seen);
                    s_starts.append(shifted);
                }
                s_keys.append(o_keys);
                s_values.merge_part(*o_values, false);
                *s_pred = s_pred.union(&o_pred);
                for key in o_deleted.iter() {
                    s_deleted.insert(key + seen);
                }
                collapse_grown_groups(s_starts, s_keys, s_values, s_deleted);
            }
            // A record's fields are whole exactly when the record is: a record of whole
            // values merges field by whole field, and one sitting under a collection merges
            // each field the way that collection's rows merge.
            (Tile::Record(s_fields), Tile::Record(ref mut o_fields)) => {
                assert_eq!(s_fields.len(), o_fields.len());
                s_fields.iter_mut().for_each(|(f, t)| {
                    t.merge_part(
                        o_fields
                            .remove(f)
                            .unwrap_or_else(|| panic!("Record missing field {f}")),
                        whole,
                    )
                })
            }
            // Change-append: `other`'s new commit ticks are strictly greater than any
            // already present (a changelog only grows forward in commit time), so
            // appending preserves the ascending order the fold relies on. Each key's
            // changelog is one row's collection, so the state merges as the whole value it
            // is. The frontier advances to the union — for the watermark `LessThanEq(w)`
            // this is `LessThanEq(max(w_self, w_other))`; the `terminal` flag ORs (either
            // side declaring the frontier closed closes it), and `closed_keys` unions for
            // the same reason — closure is monotone, so a key either side reports closed
            // stays closed. A store releases by physically dropping a decided prefix (see
            // `remove_guarded`), never by logical tombstoning, which is why it carries no
            // `deleted`.
            (
                Tile::Store {
                    state: s_state,
                    frontier: s_frontier,
                    terminal: s_terminal,
                    closed_keys: s_closed,
                },
                Tile::Store {
                    state: o_state,
                    frontier: o_frontier,
                    terminal: o_terminal,
                    closed_keys: o_closed,
                },
            ) => {
                s_state.merge_part(*o_state, true);
                *s_frontier = s_frontier.union(&o_frontier);
                *s_terminal = *s_terminal || o_terminal;
                s_closed.extend(o_closed);
            }
            (s, o) => panic!("Incompatible tiles {s:?} and {o:?}"),
        };
        debug_assert!(
            !whole || validate_tile(self),
            "Invalid tile after merge: {self:?}"
        );
    }

    /// Keep the rows `mask` names, dropping the rest.
    ///
    /// The mask is over this tile's own rows, so a scalar keeps the entries it names, a
    /// record keeps them in every field, and a collection keeps those rows' whole groups.
    pub fn retain(&mut self, mask: &BitVec) {
        match self {
            Tile::Scalar(cv) => cv.retain(mask),
            Tile::Record(fields) => fields.values_mut().for_each(|t| t.retain(mask)),
            // A kept row brings its whole run of keys, so keeping a row is gathering it:
            // one group per survivor, in order, which is what [`Tile::regroup_rows`] does.
            Tile::Function { .. } => {
                let kept: Vec<Vec<usize>> = mask
                    .iter()
                    .enumerate()
                    .filter(|(_, keep)| *keep)
                    .map(|(row, _)| vec![row])
                    .collect();
                *self = self.regroup_rows(&kept);
            }
            // An aggregation is flat columns over the same rows, so it filters position-wise
            // like a scalar does.
            Tile::Aggregation {
                accumulator,
                terminal,
                ..
            } => {
                accumulator.retain(mask);
                terminal.retain(mask);
            }
            other => panic!("retain not supported for {other:?}"),
        }
    }

    /// This tile's rows in the order `rows` names them, each as many times as it appears.
    ///
    /// A gather rather than a filter: [`Tile::retain`] is the case where every row goes to a
    /// row of its own or to none, and this is what an operator uses when it rebuilds a
    /// collection by looking rows up.
    pub fn select_rows(&self, rows: &[usize]) -> Tile {
        match self {
            Tile::Scalar(cv) => Tile::Scalar(cv.select_indices(rows.iter().copied(), rows.len())),
            Tile::Record(fields) => Tile::Record(
                fields
                    .iter()
                    .map(|(k, t)| (k.clone(), t.select_rows(rows)))
                    .collect(),
            ),
            Tile::Function { .. } => {
                self.regroup_rows(&rows.iter().map(|r| vec![*r]).collect::<Vec<_>>())
            }
            Tile::Aggregation {
                kind,
                accumulator,
                terminal,
            } => Tile::Aggregation {
                kind: *kind,
                accumulator: Box::new(accumulator.select_rows(rows)),
                terminal: terminal.select_indices(rows.iter().copied(), rows.len()),
            },
            other => panic!("select_rows is not defined for {other:?}"),
        }
    }

    /// This collection re-grouped: one row per group, holding the runs of the rows that
    /// group names, in the order it names them.
    ///
    /// A row may land in several groups, or in none. That is what a lookup does — it reads
    /// a key's group once per row that asks for it — and what collapsing a family of groups
    /// into one does, which is the whole of applying a keyed collection at a single key.
    pub fn regroup_rows(&self, groups: &[Vec<usize>]) -> Tile {
        let Tile::Function {
            keys,
            values,
            domain_predicate,
            deleted,
            ..
        } = self
        else {
            panic!("regroup_rows is a collection's: {self:?}")
        };
        let mut starts = Vec::with_capacity(groups.len());
        let mut picked: Vec<usize> = Vec::new();
        for group in groups {
            starts.push(picked.len());
            for &row in group {
                let (from, to) = self.row_run(row);
                picked.extend(from..to);
            }
        }
        let mut moved = BitSet::new();
        for (to, from) in picked.iter().enumerate() {
            if deleted.contains(*from) {
                moved.insert(to);
            }
        }
        Tile::grouped(
            ColumnValue::UInts(starts),
            keys.select_indices(picked.iter().copied(), picked.len()),
            Box::new(values.select_rows(&picked)),
            domain_predicate.clone(),
            moved,
        )
    }

    /// Keep the keys `mask` names, dropping the rest — a filter *within* each row.
    ///
    /// The mask is over this collection's keys, which is what a predicate over its elements
    /// produces. Rows keep their identity; only their groups shrink.
    pub fn retain_keys(&mut self, mask: &BitVec) {
        let Tile::Function {
            row_starts,
            keys,
            values,
            deleted,
            ..
        } = self
        else {
            panic!("retain_keys is a collection's: {self:?}")
        };
        let starts = level_offsets(row_starts).to_vec();
        let mut new_starts = Vec::with_capacity(starts.len());
        let mut kept = 0usize;
        for row in 0..starts.len() {
            new_starts.push(kept);
            let (from, to) = level_run(&starts, row, keys.len());
            kept += (from..to).filter(|&k| mask[k]).count();
        }
        let survivors: Vec<usize> = (0..keys.len()).filter(|&k| mask[k]).collect();
        let mut moved = BitSet::new();
        for (to, from) in survivors.iter().enumerate() {
            if deleted.contains(*from) {
                moved.insert(to);
            }
        }
        *keys = keys.select_indices(survivors.iter().copied(), survivors.len());
        *deleted = moved;
        *row_starts = ColumnValue::UInts(new_starts);
        values.retain(mask);
    }

    /// Logically remove the keys `mask` does **not** name, by setting bits in `deleted`.
    ///
    /// Physical arrays are untouched, so `to_guard` still reports every key that was ever
    /// present. Call [`Tile::compact`] to drop them for real.
    pub fn mark_deleted(&mut self, mask: &BitVec) {
        let Tile::Function { deleted, .. } = self else {
            panic!("mark_deleted is a collection's: {self:?}")
        };
        for (key, keep) in mask.iter().enumerate() {
            if !keep {
                deleted.insert(key);
            }
        }
    }

    /// Physically remove every logically-deleted key and clear `deleted`.
    ///
    /// After this the collection is compact: every key is live. A removed key takes its
    /// whole group with it, which a filter over the level below cannot say.
    pub fn compact(&mut self) {
        if let Tile::Function { keys, deleted, .. } = self
            && !deleted.is_empty()
        {
            let removed = std::mem::take(deleted);
            let keep: BitVec = (0..keys.len()).map(|k| !removed.contains(k)).collect();
            self.retain_keys(&keep);
        }
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
                **accumulator = accumulator.select_rows(&[]);
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
            // **A guard nests as deeply as the value does.** `Domain(p)` names this
            // collection's own keys; a `Codomain` wrapper steps into its values, where the
            // guard is read against whatever sits there. The named key is marked here and
            // [`Tile::compact`] takes its group with it — marking the keys beneath instead
            // would make a released group indistinguishable from one a filter emptied.
            (
                Tile::Function { keys, deleted, .. },
                TileGuard::Function(FunctionGuard::Domain(pred)),
            ) => {
                for key in 0..keys.len() {
                    if pred.contains(&keys.index_at(key)) {
                        deleted.insert(key);
                    }
                }
            }
            (
                Tile::Function { values, .. },
                TileGuard::Function(FunctionGuard::Codomain(inner)),
            ) => values.remove_guarded(*inner),
            // A store release names a prefix of decided commit ticks the consumer
            // no longer needs to *read at*. Dropping those change cells here would
            // be unsound: under step interpolation a released tick's value may
            // still hold forward past the release watermark, so a fold
            // (`store_current` at the frontier) needs each key's latest write even
            // when it lies in the released prefix. The load-bearing GC is therefore
            // the engine's `gc_released_prefix` (keep-latest), which bounds the
            // *source*; the per-consumer `FanOut` view reaching here is a throwaway
            // per-pull clone the consumer folds whole, so removal is a no-op. This
            // is the release-path face of the function overload the `Store` variant
            // exists to avoid — "release tick t" is not "delete position t".
            (Tile::Store { .. }, TileGuard::Function(FunctionGuard::Domain(_))) => {}
            (s, g) => panic!("Incompatible tile and guard in remove_guarded: {s:?} and {g:?}"),
        }
    }

    /// Whether this tile holds anything the guard names.
    pub fn contains_guarded(&self, guard: &TileGuard) -> bool {
        let mut probe = self.clone();
        probe.remove_guarded(guard.clone());
        probe != *self
    }

    /// Creates a TileGuard representing the contents of this Tile.
    ///
    /// For Scalar: universal if the scalar is known and empty otherwise.
    /// For Aggregation: universal if terminal and empty otherwise.
    /// For Collection: `Domain` over the keys whose groups are whole, plus
    /// `Codomain(...)` over what the values hold under the keys that are not.
    ///
    /// Important note around logical deletes: we don't release eagerly when logically
    /// deleting keys via `deleted`, so `to_guard` includes logically-deleted keys when
    /// constructing the guards. Doing it this way significantly reduces the fragmentation of
    /// the obsolete guards, which lets them use smaller representations.
    pub fn to_guard(&self) -> TileGuard {
        match self {
            Tile::Scalar(cv) => TileGuard::Scalar(!cv.is_empty()),
            Tile::Aggregation { terminal, .. } => {
                TileGuard::Aggregation(terminal.as_single().map(|t| t.as_bool()).unwrap_or(false))
            }
            Tile::Record(m) => {
                TileGuard::Record(m.iter().map(|(k, t)| (k.clone(), t.to_guard())).collect())
            }
            // **A key is released once what it holds is complete.** A scalar under a key is
            // complete as soon as it is there, so every key present is releasable. A
            // collection under a key may still grow, and only `domain_predicate` says which
            // keys it will not; what an open key holds is named one step in, which is where
            // a `Codomain` guard reads.
            Tile::Function {
                keys,
                values,
                domain_predicate,
                ..
            } => {
                if domain_predicate.is_true() {
                    return TileGuard::Function(FunctionGuard::Domain(Predicate::True));
                }
                if !values.is_function() {
                    return TileGuard::Function(FunctionGuard::Domain(
                        Predicate::from_column_value(keys).union(domain_predicate),
                    ));
                }
                // The codomain arm names what the **open** keys hold. A key the predicate
                // calls whole is released by its own key, and a codomain guard is read
                // against every row of the values it wraps — so naming a whole group's
                // keys would release the same key value under a sibling still growing.
                let open = BitVec::from_fn(keys.len(), |key| {
                    !domain_predicate.contains(&keys.index_at(key))
                });
                if !open.any() {
                    return TileGuard::Function(FunctionGuard::Domain(domain_predicate.clone()));
                }
                let mut open_values = (**values).clone();
                open_values.retain(&open);
                TileGuard::flatten_or(vec![
                    TileGuard::Function(FunctionGuard::Domain(domain_predicate.clone())),
                    TileGuard::Function(FunctionGuard::Codomain(Box::new(
                        open_values.held_guard(),
                    ))),
                ])
            }
            // The store's guard is over its commit-time domain (the change ticks), like a
            // collection's — consumers release a prefix of it. A tick naming any key is a
            // change of the store, so the ticks are the union over the key changelogs.
            Tile::Store {
                state,
                frontier,
                terminal,
                ..
            } => {
                if *terminal {
                    TileGuard::Function(FunctionGuard::Domain(Predicate::True))
                } else {
                    TileGuard::Function(FunctionGuard::Domain(
                        store_change_ticks(state).union(frontier),
                    ))
                }
            }
        }
    }

    /// A collection over one row — the whole value — with dev-build-only validation.
    pub fn function(
        keys: ColumnValue,
        values: Box<Tile>,
        domain_predicate: Predicate,
        deleted: BitSet,
    ) -> Tile {
        Tile::grouped(
            ColumnValue::UInts(vec![0]),
            keys,
            values,
            domain_predicate,
            deleted,
        )
    }

    /// A collection grouped under `row_starts`, with dev-build-only validation.
    pub fn grouped(
        row_starts: ColumnValue,
        keys: ColumnValue,
        values: Box<Tile>,
        domain_predicate: Predicate,
        deleted: BitSet,
    ) -> Tile {
        let result = Tile::Function {
            row_starts,
            keys,
            values,
            domain_predicate,
            deleted,
        };
        debug_assert!(
            valid_over(&result, level_offsets_of(&result).len()),
            "Invalid collection: {result:?}"
        );
        result
    }

    /// The tile sitting under every level of this collection chain — what an operator
    /// transforms when it changes a collection's values and nothing else.
    ///
    /// The runtime counterpart of what
    /// [`change_tiling_result`](crate::interpreter::tile_operators::change_tiling_result)
    /// does to a tiling. A tile that is not a collection is its own deepest values.
    pub fn deepest_values(&self) -> &Tile {
        match self {
            Tile::Function { values, .. } => values.deepest_values(),
            other => other,
        }
    }

    /// The tile `depth` levels in, which is `self` at depth 0.
    ///
    /// Where [`Self::deepest_values`] goes all the way down, this stops where an operator
    /// says to — at the levels its inputs share, below which each of them keeps its own.
    pub fn values_at(&self, depth: usize) -> &Tile {
        match (depth, self) {
            (0, _) => self,
            (_, Tile::Function { values, .. }) => values.values_at(depth - 1),
            (_, other) => panic!("no level {depth} in {other:?}"),
        }
    }

    /// [`Self::values_at`], to write through.
    pub fn values_at_mut(&mut self, depth: usize) -> &mut Tile {
        if depth == 0 {
            return self;
        }
        let Tile::Function { values, .. } = self else {
            panic!("no level {depth} in {self:?}")
        };
        values.values_at_mut(depth - 1)
    }

    /// [`Self::deepest_values`], to write through.
    pub fn deepest_values_mut(&mut self) -> &mut Tile {
        match self {
            Tile::Function { values, .. } => values.deepest_values_mut(),
            other => other,
        }
    }

    /// The innermost collection of this chain: the one whose values are not a collection.
    ///
    /// `None` where there is no collection at all. Paired with [`Self::key_paths`], this is
    /// where an operator that acts on a chain's elements does its work.
    pub fn innermost_level_mut(&mut self) -> Option<&mut Tile> {
        // The shape is read through a borrow that ends before the descent, which is what
        // lets the recursion hand back a reference into `self`.
        match self {
            Tile::Function { values, .. } if values.is_function() => {}
            Tile::Function { .. } => return Some(self),
            _ => return None,
        }
        let Tile::Function { values, .. } = self else {
            unreachable!("the shape was matched above")
        };
        values.innermost_level_mut()
    }

    /// Each level's `(row_starts, keys)`, outermost first: the chain's skeleton, without
    /// the values under it. Two collections carrying the same data over the same keys agree
    /// here whatever their predicates say.
    pub fn key_levels(&self) -> Vec<(&ColumnValue, &ColumnValue)> {
        let mut levels = Vec::new();
        let mut node = self;
        while let Tile::Function {
            row_starts,
            keys,
            values,
            ..
        } = node
        {
            levels.push((row_starts, keys));
            node = values;
        }
        levels
    }

    /// The rows this tile stands over, as it carries them.
    pub fn rows(&self) -> usize {
        match self {
            Tile::Scalar(cv) => cv.len(),
            Tile::Record(fields) => fields.values().map(Tile::rows).max().unwrap_or(0),
            Tile::Function { row_starts, .. } => row_starts.len(),
            Tile::Aggregation { accumulator, .. } => accumulator.rows(),
            Tile::Store { .. } => 1,
        }
    }

    /// A store key's changelog: the commit ticks that wrote it, ascending, against the
    /// values written there. `None` for a tile that is not a store, and for a key outside
    /// its key space.
    ///
    /// This and [`Self::store_keys`] are the only way into a store's state, so the record
    /// of collections it is encoded as stays this module's business — a reader folds the
    /// changelog ([`store_value_at`](crate::interpreter::commit_operator::store_value_at)
    /// and its neighbours) rather than indexing a tick.
    pub fn store_changelog(&self, key: &str) -> Option<(&ColumnValue, &Tile)> {
        match self.store_state().get(key)? {
            Tile::Function { keys, values, .. } => Some((keys, values)),
            other => unreachable!("a store key's changelog is a collection; got {other:?}"),
        }
    }

    /// A store's key space — the mutable variables and reply taps it holds, which is
    /// static and so complete whether or not a key has been written.
    pub fn store_keys(&self) -> impl Iterator<Item = &String> {
        self.store_state().keys()
    }

    /// The per-key changelogs of a store, empty for any other tile.
    fn store_state(&self) -> &HashMap<String, Tile> {
        static NONE: std::sync::LazyLock<HashMap<String, Tile>> =
            std::sync::LazyLock::new(HashMap::new);
        let Tile::Store { state, .. } = self else {
            return &NONE;
        };
        match &**state {
            Tile::Record(keys) => keys,
            other => {
                unreachable!("a store's state is a record of per-key changelogs; got {other:?}")
            }
        }
    }

    /// Whether this tile is the keyed-data representation, the test an operator makes when
    /// it walks a chain of levels.
    pub fn is_function(&self) -> bool {
        matches!(self, Tile::Function { .. })
    }

    /// The key path of every key of this collection, each extending its row's path.
    ///
    /// `row_paths` holds one path per row, so the result — one path per key — is the
    /// `row_paths` of whatever collection sits in `values`. A key repeats across its
    /// siblings' groups, so below the top level only the whole path identifies an element.
    pub fn key_paths(&self, row_paths: &[Vec<Value>]) -> Vec<Vec<Value>> {
        let Tile::Function { keys, .. } = self else {
            panic!("key_paths is a collection's: {self:?}")
        };
        let mut paths = Vec::with_capacity(keys.len());
        for (row, path) in row_paths.iter().enumerate() {
            let (start, end) = self.row_run(row);
            paths.extend((start..end).map(|key| {
                let mut extended = path.clone();
                extended.push(keys.index_at(key));
                extended
            }));
        }
        paths
    }

    /// The guard naming what this tile **holds**, with no allowance for what it has been
    /// promised.
    ///
    /// What [`Self::to_guard`] answers for a whole tile includes its `domain_predicate`:
    /// a key the producer promises is releasable even before it arrives. A
    /// [`FunctionGuard::Codomain`] arm cannot carry that, because it is read against every
    /// row of the values it wraps — a promised key would be released under a row that
    /// already holds it, and that row's value would go with it.
    fn held_guard(&self) -> TileGuard {
        match self {
            Tile::Function { keys, values, .. } => {
                let keys_guard =
                    TileGuard::Function(FunctionGuard::Domain(Predicate::from_column_value(keys)));
                if !values.is_function() {
                    return keys_guard;
                }
                TileGuard::flatten_or(vec![
                    keys_guard,
                    TileGuard::Function(FunctionGuard::Codomain(Box::new(values.held_guard()))),
                ])
            }
            other => other.to_guard(),
        }
    }

    /// The half-open run of `keys` belonging to row `row`.
    pub fn row_run(&self, row: usize) -> (usize, usize) {
        let Tile::Function {
            row_starts, keys, ..
        } = self
        else {
            panic!("row_run is a collection's: {self:?}")
        };
        level_run(level_offsets(row_starts), row, keys.len())
    }
}

/// A collection's own `row_starts`, for the validation a constructor does.
fn level_offsets_of(tile: &Tile) -> &[usize] {
    let Tile::Function { row_starts, .. } = tile else {
        unreachable!("only a collection is constructed this way")
    };
    level_offsets(row_starts)
}

fn level_offsets(offsets: &ColumnValue) -> &[usize] {
    match offsets {
        ColumnValue::UInts(v) => v,
        other => panic!("Function offsets must be UInts, got {other:?}"),
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

/// A chain of collections from flat level columns, outermost first.
///
/// `starts[k]` groups `levels[k + 1]` under `levels[k]`, so this is the nesting a flat CSR
/// level list describes. Building one is what an operator does when it has the columns in
/// hand rather than a tile to descend.
pub fn nest_levels(
    levels: Vec<ColumnValue>,
    starts: Vec<ColumnValue>,
    innermost: Box<Tile>,
    domain_predicate: Predicate,
) -> Tile {
    assert_eq!(
        starts.len() + 1,
        levels.len(),
        "one starts column between each adjacent pair of levels"
    );
    let mut built = *innermost;
    for (level, keys) in levels.into_iter().enumerate().rev() {
        built = if level == 0 {
            Tile::function(
                keys,
                Box::new(built),
                domain_predicate.clone(),
                BitSet::new(),
            )
        } else {
            Tile::grouped(
                starts[level - 1].clone(),
                keys,
                Box::new(built),
                Predicate::False,
                BitSet::new(),
            )
        };
    }
    built
}

/// Whether `tile` is well formed as a whole value.
///
/// Nothing pins the row count at the top level: a tile there carries its own rows, as a
/// `Scalar(Union)` stream does when its keys are the column's positions. Every depth below
/// is pinned — a collection's values stand at its key count, and a record's fields at the
/// rows the record does — and that pairing is what this checks.
pub fn validate_tile(tile: &Tile) -> bool {
    match tile {
        Tile::Scalar(_) => true,
        // A record at the top level is a record of whole values; only a collection's keys
        // pin its fields to one count.
        Tile::Record(fields) => fields.values().all(validate_tile),
        Tile::Aggregation {
            accumulator,
            terminal,
            ..
        } => accumulator.rows() == terminal.len(),
        Tile::Function { row_starts, .. } => valid_over(tile, row_starts.len()),
        Tile::Store { .. } => valid_over(tile, 1),
    }
}

/// Collapse a run of equal keys in one row into the single key it is.
///
/// A merge **extends** a collection, so a key it already holds is a group that grew
/// rather than a second key: a collection delivered a row at a time re-states the row it
/// is adding to, and the level below gains the new elements. Appending the key again
/// would leave the level with a repeated key, which no collection admits
/// ([`valid_over`]) and which a lookup inside the row would only find the first run of.
///
/// Only a level whose values are themselves a collection can grow this way. Where they
/// are not, a repeated key is one position delivered twice — a release-contract
/// violation rather than growth — and it is left alone so `valid_over` reports it.
///
/// The keys of one row run together and a row grows at its end, so a repeat is adjacent
/// to what it extends; a repeat that is not is a collection whose rows interleave, which
/// no producer emits.
fn collapse_grown_groups(
    row_starts: &mut ColumnValue,
    keys: &mut ColumnValue,
    values: &mut Tile,
    deleted: &mut BitSet,
) {
    if !values.is_function() {
        return;
    }
    let ColumnValue::UInts(starts) = row_starts else {
        return;
    };
    let boundaries: HashSet<usize> = starts.iter().copied().collect();
    let grown: Vec<usize> = (1..keys.len())
        .filter(|i| !boundaries.contains(i) && keys.index_at(*i) == keys.index_at(i - 1))
        .collect();
    if grown.is_empty() {
        return;
    }
    let dropped: HashSet<usize> = grown.iter().copied().collect();
    debug_assert!(
        (1..keys.len()).all(|i| dropped.contains(&i)
            || boundaries.contains(&i)
            || (0..i).all(|j| dropped.contains(&j) || keys.index_at(j) != keys.index_at(i))),
        "a key repeats a row's earlier key without extending it, so the rows interleave: \
         {keys:?}"
    );
    // Each dropped key's group joins the one before it, which is the row of `values` just
    // before: dropping that row's start is what joins the two runs, and the elements
    // themselves do not move.
    if let Tile::Function {
        row_starts: below, ..
    } = values
    {
        let keep: BitVec = (0..below.len()).map(|i| !dropped.contains(&i)).collect();
        below.retain(&keep);
    }
    let keep: BitVec = (0..keys.len()).map(|i| !dropped.contains(&i)).collect();
    keys.retain(&keep);
    // This level's own row starts count keys, so each one drops by the repeats before it.
    let ColumnValue::UInts(starts) = row_starts else {
        unreachable!("checked above")
    };
    for start in starts.iter_mut() {
        *start -= grown.iter().filter(|d| **d < *start).count();
    }
    let shifted: BitSet = deleted
        .iter()
        .filter(|k| !dropped.contains(k))
        .map(|k| k - grown.iter().filter(|d| **d < k).count())
        .collect();
    *deleted = shifted;
}

/// Every commit tick at which a store's state records a write, as the predicate naming
/// them: a tick is a change of the store when any one key's changelog carries it.
fn store_change_ticks(state: &Tile) -> Predicate {
    let Tile::Record(keys) = state else {
        unreachable!("a store's state is a record of per-key changelogs; got {state:?}")
    };
    keys.values().fold(Predicate::False, |acc, log| match log {
        Tile::Function { keys, .. } => acc.union(&Predicate::from_column_value(keys)),
        other => unreachable!("a store key's changelog is a collection; got {other:?}"),
    })
}

/// Whether `tile` is well formed as a value vectorized over `rows` rows.
///
/// The three rules, and nothing else: a scalar is one entry per row, a record is its fields
/// over the same rows, and a collection is one run of keys per row with its values over
/// those keys.
fn valid_over(tile: &Tile, rows: usize) -> bool {
    match tile {
        // A column that has not arrived is empty rather than `rows` long — what a producer
        // emits before it has an answer and a consumer reads as "not ready". It holds
        // wherever a column does, so a record field may be empty while its siblings are
        // full: a binop over a lagging operand builds the record before both columns are
        // in, and combines only the common prefix.
        Tile::Scalar(cv) => cv.is_empty() || cv.len() == rows,
        Tile::Record(fields) => fields.values().all(|t| valid_over(t, rows)),
        Tile::Function {
            row_starts,
            keys,
            values,
            domain_predicate: _,
            deleted,
        } => {
            let ColumnValue::UInts(starts) = row_starts else {
                return false;
            };
            // A run per row, beginning at 0 and never going backwards — two equal starts
            // are the row whose group holds nothing — and ending inside `keys`.
            if starts.len() != rows
                || starts.first().is_some_and(|s| *s != 0)
                || !starts.windows(2).all(|w| w[0] <= w[1])
                || starts.last().is_some_and(|s| *s > keys.len())
            {
                return false;
            }
            if deleted.iter().any(|i| i >= keys.len()) {
                return false;
            }
            // Keys are unique *within* a row; a key may repeat across rows, since each row
            // has a collection of its own.
            let all: Vec<Value> = keys.clone().drain_to_value_iter().collect();
            if !(0..rows).all(|r| {
                let (from, to) = level_run(starts, r, keys.len());
                to - from == HashSet::<Value>::from_iter(all[from..to].iter().cloned()).len()
            }) {
                return false;
            }
            valid_over(values, keys.len())
        }
        Tile::Aggregation {
            accumulator,
            terminal,
            ..
        } => {
            accumulator.rows() == terminal.len()
                && (accumulator.is_empty() || accumulator.rows() == rows)
        }
        // A store is a record of per-key changelogs, each a collection over the store's
        // one row, and each one's ticks are strictly ascending — the fold
        // ([`store_value_at`] et al.) and the change-append `merge` both depend on that,
        // and neither is type-enforced. It is a whole value rather than something
        // vectorized, so it stands at one row.
        Tile::Store { state, .. } => {
            let Tile::Record(keys) = &**state else {
                return false;
            };
            rows == 1
                && valid_over(state, 1)
                && keys.values().all(|log| {
                    let Tile::Function { keys, .. } = log else {
                        return false;
                    };
                    (1..keys.len()).all(|i| {
                        matches!(
                            (keys.index_at(i - 1), keys.index_at(i)),
                            (Value::UInt(a), Value::UInt(b)) if a < b
                        )
                    })
                })
        }
    }
}

#[cfg(test)]
mod tests {
    use bit_set::BitSet;
    use bit_vec::BitVec;

    use super::*;
    use crate::interpreter::{ColumnValue, FunctionGuard, Predicate, TileGuard, Value};

    // ── Merging a collection delivered row by row ─────────────────────────────

    /// One enclosing row's group, for a collection of collections.
    fn one_group(row: usize, inner: Vec<usize>, values: Vec<i64>) -> Tile {
        Tile::function(
            ColumnValue::from_uints(vec![row]),
            Box::new(Tile::grouped(
                ColumnValue::UInts(vec![0]),
                ColumnValue::from_uints(inner),
                Box::new(Tile::Scalar(ColumnValue::Ints(values))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        )
    }

    /// A merge **extends** a collection, so a key it already holds is that row's group
    /// growing rather than a second key. A collection delivered a row at a time re-states
    /// the row it is adding to, which is the only way a level gains elements under a key
    /// it already has.
    #[test]
    fn merging_a_row_that_grew_extends_its_group() {
        let mut tile = one_group(0, vec![0], vec![10]);
        tile.merge(one_group(0, vec![1], vec![20]));

        let Tile::Function { keys, values, .. } = &tile else {
            panic!("expected a collection, got {tile:?}");
        };
        assert_eq!(keys.len(), 1, "row 0 is one key, not two: {tile:?}");
        assert_eq!(values.row_run(0), (0, 2), "its group holds both elements");
        assert!(
            validate_tile(&tile),
            "and the tile is well formed: {tile:?}"
        );
    }

    /// A different key is a new row, which is what the merge did before any row could
    /// grow — so the collapse must not fold two rows that merely sit next to each other.
    #[test]
    fn merging_a_new_row_keeps_it_apart() {
        let mut tile = one_group(0, vec![0, 1], vec![10, 20]);
        tile.merge(one_group(1, vec![0], vec![30]));

        let Tile::Function { keys, values, .. } = &tile else {
            panic!("expected a collection, got {tile:?}");
        };
        assert_eq!(keys.len(), 2, "two enclosing rows: {tile:?}");
        assert_eq!(values.row_run(0), (0, 2));
        assert_eq!(values.row_run(1), (2, 3));
        assert!(
            validate_tile(&tile),
            "and the tile is well formed: {tile:?}"
        );
    }

    /// A row that grows twice collapses each time, so a collection delivered one element
    /// per pull ends with one key and the whole run under it.
    #[test]
    fn a_row_that_grows_repeatedly_stays_one_key() {
        let mut tile = one_group(0, vec![0], vec![10]);
        tile.merge(one_group(0, vec![1], vec![20]));
        tile.merge(one_group(0, vec![2], vec![30]));

        let Tile::Function { keys, values, .. } = &tile else {
            panic!("expected a collection, got {tile:?}");
        };
        assert_eq!(keys.len(), 1);
        assert_eq!(values.row_run(0), (0, 3));
        assert!(
            validate_tile(&tile),
            "and the tile is well formed: {tile:?}"
        );
    }

    /// A **scalar** codomain cannot grow under a key: a repeated key there is one
    /// position delivered twice, which is a release-contract violation rather than
    /// growth. It is left for the merge's own check to report rather than folded away,
    /// because folding it would turn a duplicate delivery into a silently lost value.
    #[test]
    #[should_panic(expected = "Invalid tile after merge")]
    fn a_repeated_scalar_key_is_reported_not_folded() {
        let leaf = |v: i64| {
            Tile::function(
                ColumnValue::from_uints(vec![0]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![v]))),
                Predicate::False,
                BitSet::new(),
            )
        };
        let mut tile = leaf(10);
        tile.merge(leaf(20));
    }

    // ── Tile::is_terminal ─────────────────────────────────────────────────────

    #[test]
    fn tile_scalar_non_empty_is_terminal() {
        let tile = Tile::Scalar(ColumnValue::Ints(vec![42]));
        assert!(tile.is_terminal());
    }

    #[test]
    fn tile_sealed_function_true_predicate_is_terminal() {
        let tile = Tile::function(
            ColumnValue::Ints(vec![1]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![2]))),
            Predicate::True,
            BitSet::new(),
        );
        assert!(tile.is_terminal());
    }

    #[test]
    fn tile_sealed_function_false_predicate_not_terminal() {
        let tile = Tile::function(
            ColumnValue::Ints(vec![]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![]))),
            Predicate::False,
            BitSet::new(),
        );
        assert!(!tile.is_terminal());
    }

    #[test]
    fn tile_lookup_function_true_predicate_is_terminal() {
        let tile = Tile::function(
            ColumnValue::UInts(vec![]),
            Box::new(Tile::grouped(
                ColumnValue::UInts(vec![]),
                ColumnValue::UInts(vec![]),
                Box::new(Tile::Scalar(ColumnValue::UInts(vec![]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        assert!(tile.is_terminal());
    }

    // ── helpers for merge / to_guard / remove_guarded tests ──────────────────

    /// A one-level function tile mapping `domain` ints to `codomain` ints.
    fn fn_int(domain: Vec<i64>, codomain: Vec<i64>, pred: Predicate) -> Tile {
        Tile::function(
            ColumnValue::Ints(domain),
            Box::new(Tile::Scalar(ColumnValue::Ints(codomain))),
            pred,
            BitSet::new(),
        )
    }

    /// Two nested collections: usize keys over usize keys over an int value.
    fn cf_uint_int(
        d1: Vec<usize>,
        offsets: Vec<usize>,
        d2: Vec<usize>,
        cod: Vec<i64>,
        pred: Predicate,
    ) -> Tile {
        Tile::function(
            ColumnValue::UInts(d1),
            Box::new(Tile::grouped(
                ColumnValue::UInts(offsets),
                ColumnValue::UInts(d2),
                Box::new(Tile::Scalar(ColumnValue::Ints(cod))),
                Predicate::False,
                BitSet::new(),
            )),
            pred,
            BitSet::new(),
        )
    }

    /// A record component may hold **a collection per row** rather than a value per row.
    ///
    /// The component restates the rows it sits under as its own outermost level, so each row
    /// keys a group of its own. That is the shape a product value takes inside a codomain,
    /// and the alternative — one boxed map per cell — is what it exists to avoid.
    fn rows_with_a_collection_component() -> Tile {
        Tile::function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::Record(HashMap::from([
                ("n".to_string(), Tile::Scalar(ColumnValue::Ints(vec![5, 7]))),
                (
                    "xs".to_string(),
                    // Row 0 holds [1, 2]; row 1 holds [3].
                    Tile::grouped(
                        ColumnValue::UInts(vec![0, 2]),
                        ColumnValue::UInts(vec![0, 1, 0]),
                        Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
                        Predicate::False,
                        BitSet::new(),
                    ),
                ),
            ]))),
            Predicate::True,
            BitSet::new(),
        )
    }

    /// The codomain's row count is what the innermost domain must match, and a component
    /// holding a collection counts the rows it covers rather than the entries it holds.
    #[test]
    fn a_collection_component_counts_its_rows_not_its_entries() {
        let tile = rows_with_a_collection_component();
        assert!(validate_tile(&tile), "{tile:?}");
    }

    /// A component whose rows disagree with the level above it is not a codomain.
    #[test]
    fn a_collection_component_at_the_wrong_row_count_is_rejected() {
        let Tile::Function {
            values: codomain, ..
        } = rows_with_a_collection_component()
        else {
            unreachable!()
        };
        // Built as a literal: the constructor's own check is what this is about.
        let mismatched = Tile::Function {
            // One row above, two rows inside the component.
            row_starts: ColumnValue::UInts(vec![0]),
            keys: ColumnValue::UInts(vec![0]),
            values: codomain,
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        assert!(!validate_tile(&mismatched));
    }

    /// Retaining a row takes that row's whole group out of a collection component, rather
    /// than reading the row mask as a mask over the component's entries.
    #[test]
    fn retaining_a_row_takes_its_group_from_a_collection_component() {
        let mut tile = rows_with_a_collection_component();
        // Keep row 0, drop row 1 — the rows the component sits over are this collection's
        // own keys.
        tile.retain_keys(&BitVec::from_fn(2, |i| i == 0));
        let Tile::Function {
            values: codomain, ..
        } = &tile
        else {
            unreachable!()
        };
        let Tile::Record(fields) = codomain.as_ref() else {
            unreachable!()
        };
        assert_eq!(
            fields["n"],
            Tile::Scalar(ColumnValue::Ints(vec![5])),
            "a column keeps the entry the mask names"
        );
        let Tile::Function {
            row_starts,
            keys,
            values: inner,
            ..
        } = &fields["xs"]
        else {
            panic!("the component holds a collection per row")
        };
        assert_eq!(*row_starts, ColumnValue::UInts(vec![0]), "one row survives");
        assert_eq!(
            *keys,
            ColumnValue::UInts(vec![0, 1]),
            "with its whole group, and row 1's element gone"
        );
        assert_eq!(**inner, Tile::Scalar(ColumnValue::Ints(vec![1, 2])));
        assert!(validate_tile(&tile), "{tile:?}");
    }

    /// A first start above 0 leaves the elements before it under no parent.
    ///
    /// `level_run` reads a run as `[starts[i], starts[i + 1])`, so nothing reaches them:
    /// they are neither an empty group, which two equal starts say, nor a removal, which a
    /// `deleted` bit says.
    #[test]
    #[cfg_attr(
        not(debug_assertions),
        ignore = "the constructor's tile check is a `debug_assert!`"
    )]
    #[should_panic(expected = "Invalid collection")]
    fn a_first_start_above_zero_orphans_the_entries_before_it() {
        cf_uint_int(
            vec![0, 1],
            vec![1, 2],
            vec![10, 11, 12],
            vec![100, 110, 120],
            Predicate::True,
        );
    }

    /// The `Codomain` arm the keys sit under is one wrapper per level, so the innermost
    /// keys of a three-level tile are named two wrappers in. Fewer would hand a consumer
    /// those keys against the middle level's own keys.
    #[test]
    fn to_guard_names_the_innermost_keys_one_codomain_per_level() {
        let tile = Tile::function(
            ColumnValue::UInts(vec![0]),
            Box::new(Tile::grouped(
                ColumnValue::UInts(vec![0]),
                ColumnValue::UInts(vec![10, 11]),
                Box::new(Tile::grouped(
                    ColumnValue::UInts(vec![0, 2]),
                    ColumnValue::UInts(vec![100, 101, 102, 103]),
                    Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3, 4]))),
                    // Every group open, so every innermost key is named.
                    Predicate::False,
                    BitSet::new(),
                )),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );
        let guard = tile.to_guard();
        let mut at = &guard;
        for level in 0..2 {
            at = codomain_arm(at)
                .unwrap_or_else(|| panic!("level {level} carries a codomain arm, got {at:?}"));
        }
        let pred = domain_arm(at).expect("the innermost level names its keys");
        assert!(
            pred.contains(&Value::UInt(100)) && pred.contains(&Value::UInt(103)),
            "the arm carries the innermost keys, got {pred:?}"
        );
    }

    /// The `Domain` predicate of a guard, through an `Or` if it is one.
    fn domain_arm(guard: &TileGuard) -> Option<&Predicate> {
        match guard {
            TileGuard::Function(FunctionGuard::Domain(p)) => Some(p),
            TileGuard::Or(arms) => arms.iter().find_map(domain_arm),
            _ => None,
        }
    }

    /// The `Codomain` arm of a guard, through an `Or` if it is one.
    fn codomain_arm(guard: &TileGuard) -> Option<&TileGuard> {
        match guard {
            TileGuard::Function(FunctionGuard::Codomain(inner)) => Some(inner),
            TileGuard::Or(arms) => arms.iter().find_map(codomain_arm),
            _ => None,
        }
    }

    /// Build a TileGuard for releasing domain2 values described by `pred` from a Function.
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
    fn merge_function_appends_domain_and_codomain() {
        let mut tile = fn_int(vec![1], vec![10], Predicate::False);
        tile.merge(fn_int(vec![2], vec![20], Predicate::False));
        let Tile::Function { keys, values, .. } = &tile else {
            panic!("expected a function tile");
        };
        assert_eq!(*keys, ColumnValue::Ints(vec![1, 2]));
        assert_eq!(
            *values,
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20])))
        );
    }

    #[test]
    fn merge_function_unions_predicates() {
        let p1 = Predicate::from_column_value(&ColumnValue::Ints(vec![1]));
        let p2 = Predicate::from_column_value(&ColumnValue::Ints(vec![2]));
        let mut tile = fn_int(vec![1], vec![10], p1.clone());
        tile.merge(fn_int(vec![2], vec![20], p2.clone()));
        let Tile::Function {
            domain_predicate, ..
        } = &tile
        else {
            panic!("expected a function tile");
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
        let mut tile = fn_int(vec![1], vec![10], Predicate::False);
        tile.merge(fn_int(vec![1], vec![10], Predicate::False));
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
            state: Box::new(Tile::Record(HashMap::from([(
                "acc".to_string(),
                Tile::function(
                    ColumnValue::UInts(vec![0]),
                    Box::new(Tile::Scalar(ColumnValue::Ints(vec![1]))),
                    Predicate::False,
                    BitSet::new(),
                ),
            )]))),
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
        let tile = fn_int(vec![1, 2], vec![10, 20], pred.clone());
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
        let mut tile = fn_int(vec![1, 2], vec![10, 20], Predicate::True);
        tile.remove_guarded(TileGuard::Function(FunctionGuard::Domain(pred)));
        let Tile::Function {
            keys,
            values,
            deleted,
            ..
        } = &tile
        else {
            panic!("expected a collection tile");
        };
        // Physical arrays are unchanged.
        assert_eq!(*keys, ColumnValue::Ints(vec![1, 2]));
        assert_eq!(
            *values,
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20])))
        );
        // Index 0 (key 1) is logically deleted.
        assert!(deleted.contains(0), "index 0 should be deleted");
        assert!(!deleted.contains(1), "index 1 should not be deleted");
    }

    #[test]
    fn remove_guarded_sealed_function_full_release_clears() {
        let mut tile = fn_int(vec![1, 2], vec![10, 20], Predicate::True);
        let guard = tile.to_guard();
        tile.remove_guarded(guard);
        // Physical arrays are unchanged; logical length is 0.
        assert!(tile.is_empty());
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
        let Tile::Function { values: groups, .. } = &tile else {
            panic!("expected a collection");
        };
        let Tile::Function {
            keys,
            values,
            deleted,
            ..
        } = groups.as_ref()
        else {
            panic!("expected a collection of collections");
        };
        // Physical arrays unchanged.
        assert_eq!(*keys, ColumnValue::UInts(vec![10, 11, 12]));
        assert_eq!(
            **values,
            Tile::Scalar(ColumnValue::Ints(vec![100, 110, 120]))
        );
        // Only key 11 is logically deleted.
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
        let Tile::Function { values: groups, .. } = &tile else {
            panic!("expected a collection");
        };
        let Tile::Function { deleted, .. } = groups.as_ref() else {
            panic!("expected a collection of collections");
        };
        assert!(deleted.contains(0));
        assert!(deleted.contains(1));
        assert!(!deleted.contains(2));
    }

    /// A release marks the element the guard names, **at that element's own level**, and
    /// `compact` is what takes its group with it. Marking the entries beneath it instead
    /// would leave a released group and a filtered-empty one the same shape.
    #[test]
    fn remove_guarded_curried_function_domain_marks_the_named_group() {
        // d1=[0,1], offsets=[0,2], d2=[10,11,12], cod=[100,110,120]
        let mut tile = cf_uint_int(
            vec![0, 1],
            vec![0, 2],
            vec![10, 11, 12],
            vec![100, 110, 120],
            Predicate::False,
        );
        let pred = Predicate::from_column_value(&ColumnValue::UInts(vec![0]));
        tile.remove_guarded(TileGuard::Function(FunctionGuard::Domain(pred)));
        let Tile::Function {
            deleted,
            values: groups,
            ..
        } = &tile
        else {
            panic!("expected a collection");
        };
        assert!(deleted.contains(0), "the named group is marked");
        assert!(!deleted.contains(1), "its sibling is not");
        let Tile::Function { deleted: inner, .. } = groups.as_ref() else {
            panic!("expected a collection of collections");
        };
        assert!(
            inner.is_empty(),
            "the entries beneath it are not marked; `compact` takes them"
        );

        tile.compact();
        let Tile::Function {
            keys,
            values: groups,
            ..
        } = &tile
        else {
            panic!("expected a collection");
        };
        assert_eq!(*keys, ColumnValue::UInts(vec![1]), "group 0 is gone");
        let Tile::Function {
            row_starts,
            keys: inner_keys,
            ..
        } = groups.as_ref()
        else {
            panic!("expected a collection of collections");
        };
        assert_eq!(
            *inner_keys,
            ColumnValue::UInts(vec![12]),
            "with its entries"
        );
        assert_eq!(*row_starts, ColumnValue::UInts(vec![0]));
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
        let mut tile = fn_int(vec![1, 2, 3], vec![10, 20, 30], Predicate::True);
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
        assert!(tile.is_empty());
    }

    // ── Tile::retain_keys ─────────────────────────────────────────────────────

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
    fn retain_keys_keep_all_is_noop() {
        let mut tile = cf_three_groups();
        let Tile::Function { values, .. } = &mut tile else {
            unreachable!("cf_three_groups is a collection of collections")
        };
        values.retain_keys(&BitVec::from_elem(6, true));
        assert_eq!(tile, cf_three_groups());
    }

    #[test]
    fn retain_keys_keep_none_leaves_every_group_empty() {
        let mut tile = cf_three_groups();
        let Tile::Function { values, .. } = &mut tile else {
            unreachable!("cf_three_groups is a collection of collections")
        };
        values.retain_keys(&BitVec::from_elem(6, false));
        assert_eq!(
            tile,
            cf_uint_int(
                vec![10, 20, 30],
                vec![0, 0, 0],
                vec![],
                vec![],
                Predicate::False
            )
        );
    }

    #[test]
    fn retain_keys_keep_entire_first_group() {
        let mut tile = cf_three_groups();
        // Keep positions 0,1 (group 10); groups 20 and 30 are left empty.
        let Tile::Function { values, .. } = &mut tile else {
            unreachable!("cf_three_groups is a collection of collections")
        };
        values.retain_keys(&BitVec::from_fn(6, |i| i < 2));
        assert_eq!(
            tile,
            cf_uint_int(
                vec![10, 20, 30],
                vec![0, 2, 2],
                vec![0, 1],
                vec![100, 110],
                Predicate::False
            )
        );
    }

    #[test]
    fn retain_keys_keep_entire_middle_group() {
        let mut tile = cf_three_groups();
        let Tile::Function { values, .. } = &mut tile else {
            unreachable!("cf_three_groups is a collection of collections")
        };
        values.retain_keys(&BitVec::from_fn(6, |i| (2..5).contains(&i)));
        assert_eq!(
            tile,
            cf_uint_int(
                vec![10, 20, 30],
                vec![0, 0, 3],
                vec![2, 3, 4],
                vec![200, 210, 220],
                Predicate::False
            )
        );
    }

    #[test]
    fn retain_keys_keep_entire_last_group() {
        let mut tile = cf_three_groups();
        let Tile::Function { values, .. } = &mut tile else {
            unreachable!("cf_three_groups is a collection of collections")
        };
        values.retain_keys(&BitVec::from_fn(6, |i| i == 5));
        assert_eq!(
            tile,
            cf_uint_int(
                vec![10, 20, 30],
                vec![0, 0, 0],
                vec![5],
                vec![300],
                Predicate::False
            )
        );
    }

    #[test]
    fn retain_keys_drop_entire_middle_group() {
        let mut tile = cf_three_groups();
        let Tile::Function { values, .. } = &mut tile else {
            unreachable!("cf_three_groups is a collection of collections")
        };
        values.retain_keys(&BitVec::from_fn(6, |i| !(2..5).contains(&i)));
        assert_eq!(
            tile,
            cf_uint_int(
                vec![10, 20, 30],
                vec![0, 2, 2],
                vec![0, 1, 5],
                vec![100, 110, 300],
                Predicate::False
            )
        );
    }

    #[test]
    fn retain_keys_partial_mask_within_group() {
        let mut tile = cf_three_groups();
        // One survivor in each of groups 10 and 20; group 30 keeps nothing.
        let Tile::Function { values, .. } = &mut tile else {
            unreachable!("cf_three_groups is a collection of collections")
        };
        values.retain_keys(&BitVec::from_fn(6, |i| i == 1 || i == 3));
        assert_eq!(
            tile,
            cf_uint_int(
                vec![10, 20, 30],
                vec![0, 1, 2],
                vec![1, 3],
                vec![110, 210],
                Predicate::False
            )
        );
    }

    #[test]
    fn retain_keys_partial_mask_empties_the_groups_it_clears() {
        let mut tile = cf_three_groups();
        // Keep d2[2] and d2[4] (both in group 20); groups 10 and 30 are left empty.
        let Tile::Function { values, .. } = &mut tile else {
            unreachable!("cf_three_groups is a collection of collections")
        };
        values.retain_keys(&BitVec::from_fn(6, |i| i == 2 || i == 4));
        assert_eq!(
            tile,
            cf_uint_int(
                vec![10, 20, 30],
                vec![0, 0, 2],
                vec![2, 4],
                vec![200, 220],
                Predicate::False
            )
        );
    }
}
