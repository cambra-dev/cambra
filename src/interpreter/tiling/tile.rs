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
    /// position: 1 at the top level, and inside a collection's `codomain`, that collection's
    /// key count. A [`Self::Scalar`] is one entry per row and a [`Self::Record`] is one
    /// sub-tile per field at the same `R`; a collection groups instead of pairing, which is
    /// what `row_starts` records.
    ///
    /// Stored Compressed-Sparse-Row-wise: `domain` is every row's keys run together, and
    /// `codomain` is a tile over those keys. A chain of collections nests one node per level,
    /// holding the same columns a flat level list would — and unlike a flat list it can say
    /// where a record sits between two levels, which is what lets records and collections
    /// nest freely.
    DataFunction {
        /// Where each row's run of keys begins in `domain`, one entry per row. **Non-decreasing**:
        /// two equal starts are a row whose group holds nothing. A key with an empty group is
        /// a collection that is empty, which an aggregate folds to its identity; a key that is
        /// gone is absent from `domain` instead.
        ///
        /// At the top level this is `[0]` — the one row, whose group is the whole collection.
        row_starts: ColumnValue,
        /// Every row's keys, run together. Unique within a row and otherwise in the order
        /// they were delivered, which is what [`valid_over`] checks and all a lookup
        /// inside a row assumes.
        domain: ColumnValue,
        /// The values, a tile over `domain` — so a fold may leave an [`Self::Aggregation`] here.
        codomain: Box<Tile>,
        /// The region of `domain` whose values are complete: no new element will be seen under
        /// them, at any depth. Covering every key says the key set itself is closed, which is
        /// what makes [`Tile::is_terminal`] read this as one flag.
        domain_predicate: Predicate,
        /// Logically removed keys. 1 = removed; empty means every key is present. `domain` is
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
    /// `Txn ⇒ {key: value}` over the commit-time domain, materialized as its
    /// **changelog** — the ticks that committed a write, each carrying that
    /// tick's write-set *delta*.
    ///
    /// This is not a [`Tile::DataFunction`] and must not be treated as one:
    /// in a collection a key absent from `changes` is
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
            // A collection holds something as soon as one key is live. A key is data: a
            // consumer that broadcasts over the keys, or releases them, has an answer
            // before any value lands. Values that hold nothing is the level below being
            // empty, which is that level's own answer and not this one's — a full release
            // of what a nested collection holds leaves its keys standing, and they are
            // still what it knows.
            Tile::DataFunction {
                domain, deleted, ..
            } => domain.len() == deleted.len(),
            Tile::Aggregation { accumulator, .. } => accumulator.is_empty(),
            // A `Store` is a right-continuous *step function* over its decided prefix, not a
            // list of change events: a tick absent from `changes` but at or below the
            // frontier is *decided*, its value holding from the latest earlier change. So it
            // is empty when nothing is decided, which an undecided (`False`) frontier says
            // and a `LessThanEq` watermark never does.
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
                Tile::DataFunction {
                    domain: key_column,
                    codomain: value_tile,
                    ..
                },
                Tiling::DataFunction { domain, codomain },
            ) => key_column.is_compatible_with_extent(domain) && value_tile.check_from(codomain),
            (Tile::Aggregation { .. }, Tiling::Aggregation { .. }) => true,
            // The change ticks must lie in the commit domain; the per-tick delta
            // encoding is trusted (like `DataFunction`).
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
            Tile::DataFunction {
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

    /// Merge the contents of `other` into `self`: extend a value with a part of it that
    /// arrived later. The two must not both hold one position.
    ///
    /// A collection merges by key. A key both sides hold is one key whose group is the two
    /// groups merged, so a collection delivered a part at a time re-states the key it adds
    /// to. A key matches only where what it holds can grow ([`Self::holds_a_level`]). Under a
    /// scalar a repeated key is one position delivered twice, and the two stay apart for
    /// [`validate_tile`] to report, since matching them would lose one of the values
    /// silently. At the top level the parts are keys of the outermost collection; beneath it
    /// they are rows, because a key of the level above is a row of the level below.
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

    /// Append `other`'s keys after this collection's, in place, matching none of them.
    ///
    /// For a whole value the keys join its one row's run. Otherwise `other`'s rows follow
    /// this tile's, each run shifted past the keys already here.
    fn append_keys(&mut self, other: Tile, whole: bool) {
        let (
            Tile::DataFunction {
                row_starts: s_starts,
                domain: s_domain,
                codomain: s_codomain,
                domain_predicate: s_pred,
                deleted: s_deleted,
            },
            Tile::DataFunction {
                row_starts: o_starts,
                domain: o_domain,
                codomain: o_codomain,
                domain_predicate: o_pred,
                deleted: o_deleted,
            },
        ) = (&mut *self, other)
        else {
            panic!("append_keys appends one collection to another")
        };
        let shift = s_domain.len();
        if whole {
            assert_eq!(
                s_starts.len(),
                1,
                "a whole collection is its one row's group"
            );
            assert_eq!(
                o_starts.len(),
                1,
                "a whole collection is its one row's group"
            );
        } else {
            let (ColumnValue::UInts(s), ColumnValue::UInts(o)) = (&mut *s_starts, o_starts) else {
                panic!("row_starts is a column of positions")
            };
            s.extend(o.into_iter().map(|start| start + shift));
        }
        s_domain.append(o_domain);
        s_codomain.merge_part(*o_codomain, false);
        *s_pred = s_pred.union(&o_pred);
        s_deleted.extend(o_deleted.iter().map(|i| i + shift));
    }

    /// `merge`, knowing whether this tile is the whole value or sits under one.
    fn merge_part(&mut self, other: Tile, whole: bool) {
        if self.is_data_function() && other.is_data_function() {
            // Where no key can match, the merge is a concatenation, done in place so a
            // collection delivered a part at a time costs the part and not what is already
            // held. Rows under a collection never match, and a whole value's keys match only
            // where what they hold can grow.
            let Tile::DataFunction { codomain, .. } = &*self else {
                unreachable!("checked above")
            };
            if !whole || !codomain.holds_a_level() {
                self.append_keys(other, whole);
                debug_assert!(
                    !whole || validate_tile(self),
                    "Invalid tile after merge: {self:?}"
                );
                return;
            }
            // One row, and both describe it.
            assert_eq!(self.rows(), 1, "a whole collection is its one row's group");
            assert_eq!(other.rows(), 1, "a whole collection is its one row's group");
            *self = merged_rows(self, &other, &[RowSource::Both(0, 0)]);
            debug_assert!(validate_tile(self), "Invalid tile after merge: {self:?}");
            return;
        }
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
                // A whole aggregation is one row, and `other` is a later contribution to it,
                // folded in by the aggregate's own law. Under a collection the two sides are
                // different rows, each its own accumulator, so they follow one another.
                if whole {
                    s_kind.accumulate(s_acc, &o_acc, 0, o_acc.rows());
                    let taken = std::mem::replace(s_term, ColumnValue::Units(0));
                    *s_term =
                        apply_binop_column(BinOpKind::BoolLogic(LogicKind::Or), taken, &o_term);
                } else {
                    s_acc.merge_part(*o_acc, false);
                    s_term.append(o_term);
                }
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
            // already present (the changelog only grows forward in commit time), so
            // appending preserves the ascending order the fold relies on. The frontier
            // advances to the union — for the watermark `LessThanEq(w)` this is
            // `LessThanEq(max(w_self, w_other))`; the `terminal` flag ORs (either side
            // declaring the frontier closed closes it), and `closed_keys` unions for the
            // same reason — closure is monotone, so a key either side reports closed stays
            // closed. A store releases by physically dropping a decided prefix (see
            // `remove_guarded`), never by logical tombstoning, which is why it carries no
            // `deleted`.
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
                s_closed.extend(o_closed);
            }
            (s, o) => panic!("Incompatible tiles {s:?} and {o:?}"),
        };
        debug_assert!(
            !whole || validate_tile(self),
            "Invalid tile after merge: {self:?}"
        );
    }

    /// Keep the rows `mask` names, dropping the rest — a filter along the *row* axis.
    ///
    /// The mask is over this tile's own rows, so a scalar keeps the entries it names, a
    /// record keeps them in every field, and a collection keeps those rows' whole groups.
    pub fn retain_rows(&mut self, mask: &BitVec) {
        match self {
            // A column that carries no row has nothing to filter, and a mask over the rows
            // names nothing in it. A record's fields stand over the same rows without being
            // filled together: a store's tap carries no value forward, and a scalar beside a
            // growing collection may not have arrived, so either is empty at rows the
            // others hold.
            Tile::Scalar(cv) if cv.is_empty() => {}
            Tile::Scalar(cv) => cv.retain(mask),
            Tile::Record(fields) => fields.values_mut().for_each(|t| t.retain_rows(mask)),
            // A kept row brings its whole run of keys, so keeping a row is gathering it:
            // one group per survivor, in order, which is what [`Tile::regroup_rows`] does.
            Tile::DataFunction { .. } => {
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
                accumulator.retain_rows(mask);
                terminal.retain(mask);
            }
            other => panic!("retain not supported for {other:?}"),
        }
    }

    /// This tile's rows in the order `rows` names them, each as many times as it appears.
    ///
    /// A gather rather than a filter: [`Tile::retain_rows`] is the case where every row goes to a
    /// row of its own or to none, and this is what an operator uses when it rebuilds a
    /// collection by looking rows up.
    pub fn select_rows(&self, rows: &[usize]) -> Tile {
        match self {
            // An empty column has no rows to gather. A record whose fields all hold
            // scalars fills them together, but one holding a level does not: the scalar
            // beside a collection that already has rows may still be unfilled.
            Tile::Scalar(cv) if cv.is_empty() => Tile::Scalar(cv.clone()),
            Tile::Scalar(cv) => Tile::Scalar(cv.select_indices(rows.iter().copied(), rows.len())),
            Tile::Record(fields) => Tile::Record(
                fields
                    .iter()
                    .map(|(k, t)| (k.clone(), t.select_rows(rows)))
                    .collect(),
            ),
            Tile::DataFunction { .. } => {
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
        let Tile::DataFunction {
            domain,
            codomain,
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
            domain.select_indices(picked.iter().copied(), picked.len()),
            Box::new(codomain.select_rows(&picked)),
            domain_predicate.clone(),
            moved,
        )
    }

    /// Keep the keys `mask` names, dropping the rest — a filter along the *key* axis,
    /// which is within each row rather than across rows ([`Self::retain_rows`]).
    ///
    /// The mask is over this collection's keys, which is what a predicate over its elements
    /// produces. A key goes with the value under it, as a row goes with its group; what
    /// differs is the axis, so rows keep their identity and only their groups shrink.
    pub fn retain_keys(&mut self, mask: &BitVec) {
        let Tile::DataFunction {
            row_starts,
            domain,
            codomain,
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
            let (from, to) = level_run(&starts, row, domain.len());
            kept += (from..to).filter(|&k| mask[k]).count();
        }
        let survivors: Vec<usize> = (0..domain.len()).filter(|&k| mask[k]).collect();
        let mut moved = BitSet::new();
        for (to, from) in survivors.iter().enumerate() {
            if deleted.contains(*from) {
                moved.insert(to);
            }
        }
        *domain = domain.select_indices(survivors.iter().copied(), survivors.len());
        *deleted = moved;
        *row_starts = ColumnValue::UInts(new_starts);
        codomain.retain_rows(mask);
    }

    /// Logically remove the keys `mask` does **not** name, by setting bits in `deleted`.
    ///
    /// Physical arrays are untouched, so `to_guard` still reports every key that was ever
    /// present. Call [`Tile::compact`] to drop them for real.
    pub fn mark_deleted(&mut self, mask: &BitVec) {
        let Tile::DataFunction { deleted, .. } = self else {
            panic!("mark_deleted is a collection's: {self:?}")
        };
        for (key, keep) in mask.iter().enumerate() {
            if !keep {
                deleted.insert(key);
            }
        }
    }

    /// Physically remove every logically-deleted key and clear `deleted`, at **every**
    /// level.
    ///
    /// After this the whole value is compact: every key of every level is live. A removed
    /// key takes its whole group with it, which a filter over the level below cannot say.
    ///
    /// Every level, because a release names the level it is about. Releasing a flat
    /// collection's keys names the top, and releasing what a nested one holds under a row
    /// names the level below. Compacting only the top leaves an inner key present but
    /// deleted, and the next delivery of that key lands beside it rather than replacing
    /// it — a row holding one key twice, which no collection admits ([`valid_over`]).
    pub fn compact(&mut self) {
        match self {
            Tile::DataFunction {
                domain, deleted, ..
            } => {
                if !deleted.is_empty() {
                    let removed = std::mem::take(deleted);
                    let keep: BitVec = (0..domain.len()).map(|k| !removed.contains(k)).collect();
                    self.retain_keys(&keep);
                }
                let Tile::DataFunction { codomain, .. } = self else {
                    unreachable!("retaining keys leaves a collection a collection")
                };
                codomain.compact();
            }
            Tile::Record(fields) => fields.values_mut().for_each(Tile::compact),
            // A fold holds an element, and `Sole`'s is whatever shape the element has, so
            // an accumulator can carry levels with released keys of their own. Compacting
            // it keeps the row count: a collection's rows are its `row_starts`, which
            // dropping keys rebuilds at the same length, so `accumulator.rows()` still
            // matches `terminal`.
            Tile::Aggregation { accumulator, .. } => accumulator.compact(),
            Tile::Scalar(_) | Tile::Store { .. } => {}
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
                Tile::DataFunction {
                    domain, deleted, ..
                },
                TileGuard::Function(FunctionGuard::Domain(pred)),
            ) => {
                for key in 0..domain.len() {
                    if pred.contains(&domain.index_at(key)) {
                        deleted.insert(key);
                    }
                }
            }
            (
                Tile::DataFunction { codomain, .. },
                TileGuard::Function(FunctionGuard::Codomain(inner)),
            ) => codomain.remove_guarded(*inner),
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
    /// For DataFunction: `Domain` over the keys whose groups are whole, plus
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
            // a `Codomain` guard reads. A collection in a record's field is a level under the
            // key like any other ([`Tile::holds_a_level`]).
            Tile::DataFunction {
                domain,
                codomain,
                domain_predicate,
                ..
            } => {
                if domain_predicate.is_true() {
                    return TileGuard::Function(FunctionGuard::Domain(Predicate::True));
                }
                if !codomain.holds_a_level() {
                    return TileGuard::Function(FunctionGuard::Domain(
                        Predicate::from_column_value(domain).union(domain_predicate),
                    ));
                }
                // The codomain arm names what the **open** keys hold. A key the predicate
                // calls whole is released by its own key, and a codomain guard is read
                // against every row of the values it wraps — so naming a whole group's
                // keys would release the same key value under a sibling still growing.
                let open = BitVec::from_fn(domain.len(), |key| {
                    !domain_predicate.contains(&domain.index_at(key))
                });
                if !open.any() {
                    return TileGuard::Function(FunctionGuard::Domain(domain_predicate.clone()));
                }
                let mut open_values = (**codomain).clone();
                open_values.retain_rows(&open);
                TileGuard::flatten_or(vec![
                    TileGuard::Function(FunctionGuard::Domain(domain_predicate.clone())),
                    TileGuard::Function(FunctionGuard::Codomain(Box::new(
                        open_values.held_guard(),
                    ))),
                ])
            }
            // The store's guard is over its commit-time domain (the change ticks), like a
            // collection's — consumers release a prefix of it.
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

    /// A collection over one row — the whole value — with dev-build-only validation.
    pub fn data_function(
        domain: ColumnValue,
        codomain: Box<Tile>,
        domain_predicate: Predicate,
        deleted: BitSet,
    ) -> Tile {
        Tile::grouped(
            ColumnValue::UInts(vec![0]),
            domain,
            codomain,
            domain_predicate,
            deleted,
        )
    }

    /// A collection grouped under `row_starts`, with dev-build-only validation.
    pub fn grouped(
        row_starts: ColumnValue,
        domain: ColumnValue,
        codomain: Box<Tile>,
        domain_predicate: Predicate,
        deleted: BitSet,
    ) -> Tile {
        let result = Tile::DataFunction {
            row_starts,
            domain,
            codomain,
            domain_predicate,
            deleted,
        };
        debug_assert!(
            valid_over(&result, level_offsets_of(&result).len()),
            "Invalid collection: {result:?}"
        );
        result
    }

    /// The tile sitting under this collection chain — what an operator transforms when it
    /// changes a collection's values and nothing else.
    ///
    /// A record ends the chain and is itself the answer ([`Self::holds_a_level`]).
    ///
    /// The runtime counterpart of what
    /// [`change_tiling_result`](crate::interpreter::tile_operators::change_tiling_result)
    /// does to a tiling. A tile that is not a collection is its own deepest values.
    pub fn deepest_values(&self) -> &Tile {
        match self {
            Tile::DataFunction { codomain, .. } => codomain.deepest_values(),
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
            (_, Tile::DataFunction { codomain, .. }) => codomain.values_at(depth - 1),
            (_, other) => panic!("no level {depth} in {other:?}"),
        }
    }

    /// [`Self::values_at`], to write through.
    pub fn values_at_mut(&mut self, depth: usize) -> &mut Tile {
        if depth == 0 {
            return self;
        }
        let Tile::DataFunction { codomain, .. } = self else {
            panic!("no level {depth} in {self:?}")
        };
        codomain.values_at_mut(depth - 1)
    }

    /// [`Self::deepest_values`], to write through.
    pub fn deepest_values_mut(&mut self) -> &mut Tile {
        match self {
            Tile::DataFunction { codomain, .. } => codomain.deepest_values_mut(),
            other => other,
        }
    }

    /// The depth of this chain's innermost collection: the last before its elements.
    ///
    /// `None` where there is no collection at all. [`Self::values_at`] takes this depth and
    /// [`Self::row_paths_at`] the key path of every row that level stands over, which is
    /// how an operator acting on a chain's elements finds its work.
    ///
    /// A record ends the chain ([`Self::holds_a_level`]).
    pub fn innermost_depth(&self) -> Option<usize> {
        let Tile::DataFunction { codomain, .. } = self else {
            return None;
        };
        Some(codomain.innermost_depth().map_or(0, |below| below + 1))
    }

    /// The innermost collection of this chain, to write through
    /// ([`Self::innermost_depth`]).
    pub fn innermost_level_mut(&mut self) -> Option<&mut Tile> {
        let depth = self.innermost_depth()?;
        Some(self.values_at_mut(depth))
    }

    /// The key path of every row at `depth`, outermost key first.
    ///
    /// Depth 0 is the whole value: one row, whose path is empty. Each level down extends
    /// its row's path by that level's key, so the rows at `depth` are the keys at
    /// `depth - 1` and an element's path names it uniquely.
    pub fn row_paths_at(&self, depth: usize) -> Vec<Vec<Value>> {
        let mut paths = vec![Vec::new()];
        let mut node = self;
        for _ in 0..depth {
            paths = node.key_paths(&paths);
            let Tile::DataFunction { codomain, .. } = node else {
                panic!("no level {depth} in {self:?}")
            };
            node = codomain;
        }
        paths
    }

    /// Each level's `(row_starts, domain)`, outermost first: the chain's skeleton, without
    /// the values under it. Two collections carrying the same data over the same keys agree
    /// here whatever their predicates say.
    ///
    /// A record ends the chain ([`Self::holds_a_level`]), so a caller comparing skeletons
    /// compares the levels the two tiles share above their values.
    pub fn key_levels(&self) -> Vec<(&ColumnValue, &ColumnValue)> {
        let mut levels = Vec::new();
        let mut node = self;
        while let Tile::DataFunction {
            row_starts,
            domain,
            codomain,
            ..
        } = node
        {
            levels.push((row_starts, domain));
            node = codomain;
        }
        levels
    }

    /// The rows this tile stands over, as it carries them.
    pub fn rows(&self) -> usize {
        match self {
            Tile::Scalar(cv) => cv.len(),
            Tile::Record(fields) => fields.values().map(Tile::rows).max().unwrap_or(0),
            Tile::DataFunction { row_starts, .. } => row_starts.len(),
            Tile::Aggregation { accumulator, .. } => accumulator.rows(),
            Tile::Store { .. } => 1,
        }
    }

    /// Whether this tile is the keyed-data representation, the test an operator makes when
    /// it walks a chain of levels.
    pub fn is_data_function(&self) -> bool {
        matches!(self, Tile::DataFunction { .. })
    }

    /// Whether a level sits here, or inside a record here.
    ///
    /// A [`Self::Record`] is one sub-tile per field over the *same* rows, so it introduces
    /// no dimension of its own and a collection inside one is a level of whatever holds the
    /// record. A [`Self::Aggregation`] and a [`Self::Store`] carry their own completeness,
    /// so what they hold is answered by their own guard rather than by descending into it.
    ///
    /// Two questions about a codomain read alike and differ at a record. Whether the chain
    /// continues is [`Self::is_data_function`], which a record answers no to: the record is the
    /// element the chain ends at, so `MapAggregate` over `𝐾 ⤇ 𝐽 ⤇ {a: Int, b: (𝐿 ⤇ Int)}`
    /// folds `𝐽`'s records and `𝐿` sits inside the element it folds. Whether what this holds
    /// can still grow is this one, and a record answers yes for its fields. Guards, the
    /// merge's key matching, and an operator putting a value into a column ask this one, a
    /// column having nowhere to put a level. The chain walks ([`Self::deepest_values`],
    /// [`Self::innermost_depth`], [`Self::key_levels`]) ask the first.
    pub fn holds_a_level(&self) -> bool {
        match self {
            Tile::DataFunction { .. } => true,
            Tile::Record(fields) => fields.values().any(Tile::holds_a_level),
            Tile::Scalar(_) | Tile::Aggregation { .. } | Tile::Store { .. } => false,
        }
    }

    /// The key path of every key of this collection, each extending its row's path.
    ///
    /// `row_paths` holds one path per row, so the result — one path per key — is the
    /// `row_paths` of whatever collection sits in `codomain`. A key repeats across its
    /// siblings' groups, so below the top level only the whole path identifies an element.
    pub fn key_paths(&self, row_paths: &[Vec<Value>]) -> Vec<Vec<Value>> {
        let Tile::DataFunction { domain, .. } = self else {
            panic!("key_paths is a collection's: {self:?}")
        };
        let mut paths = Vec::with_capacity(domain.len());
        for (row, path) in row_paths.iter().enumerate() {
            let (start, end) = self.row_run(row);
            paths.extend((start..end).map(|key| {
                let mut extended = path.clone();
                extended.push(domain.index_at(key));
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
            // A record's fields stand over the rows the record does, so what it holds is
            // what its fields hold — each read the same way, because a `Codomain` arm is
            // read against every row whatever sits at it.
            Tile::Record(fields) => TileGuard::Record(
                fields
                    .iter()
                    .map(|(name, field)| (name.clone(), field.held_guard()))
                    .collect(),
            ),
            Tile::DataFunction {
                domain, codomain, ..
            } => {
                let keys_guard = TileGuard::Function(FunctionGuard::Domain(
                    Predicate::from_column_value(domain),
                ));
                if !codomain.holds_a_level() {
                    return keys_guard;
                }
                TileGuard::flatten_or(vec![
                    keys_guard,
                    TileGuard::Function(FunctionGuard::Codomain(Box::new(codomain.held_guard()))),
                ])
            }
            other => other.to_guard(),
        }
    }

    /// The half-open run of `domain` belonging to row `row`.
    pub fn row_run(&self, row: usize) -> (usize, usize) {
        let Tile::DataFunction {
            row_starts, domain, ..
        } = self
        else {
            panic!("row_run is a collection's: {self:?}")
        };
        level_run(level_offsets(row_starts), row, domain.len())
    }
}

/// A collection's own `row_starts`, for the validation a constructor does.
fn level_offsets_of(tile: &Tile) -> &[usize] {
    let Tile::DataFunction { row_starts, .. } = tile else {
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
            Tile::data_function(
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

/// Where one row of a merge's result comes from.
///
/// A merge reconciles two views of one value, so a row of the result is a row of the left
/// view, a row of the right, or one row both of them delivered. That last case is what
/// makes a merge more than a concatenation: the two contributions join.
#[derive(Clone, Copy, Debug)]
enum RowSource {
    Left(usize),
    Right(usize),
    Both(usize, usize),
}

/// `left` and `right` standing over the rows `order` names, each row taking its content
/// from whichever side delivered it.
///
/// A collection matches its two key runs per row and recurses into the matched groups
/// ([`Tile::merge`]), so no level of the result holds a key twice.
fn merged_rows(left: &Tile, right: &Tile, order: &[RowSource]) -> Tile {
    match (left, right) {
        (Tile::Scalar(l), Tile::Scalar(r)) => Tile::Scalar(merged_column(l, r, order)),
        (Tile::Record(l), Tile::Record(r)) => {
            assert_eq!(l.len(), r.len(), "a record merges with its own shape");
            Tile::Record(
                l.iter()
                    .map(|(field, tile)| {
                        let other = r
                            .get(field)
                            .unwrap_or_else(|| panic!("Record missing field {field}"));
                        (field.clone(), merged_rows(tile, other, order))
                    })
                    .collect(),
            )
        }
        (
            Tile::DataFunction {
                row_starts: l_starts,
                domain: l_domain,
                codomain: l_codomain,
                domain_predicate: l_pred,
                deleted: l_deleted,
            },
            Tile::DataFunction {
                row_starts: r_starts,
                domain: r_domain,
                codomain: r_codomain,
                domain_predicate: r_pred,
                deleted: r_deleted,
            },
        ) => {
            let l_offsets = level_offsets(l_starts);
            let r_offsets = level_offsets(r_starts);
            // One entry per key of the result, naming which side's key column holds it.
            // The rows of the level below are this level's keys, so the same list is what
            // merges them.
            let mut starts = Vec::with_capacity(order.len());
            let mut keys: Vec<RowSource> = Vec::new();
            for source in order {
                starts.push(keys.len());
                match source {
                    RowSource::Left(row) => {
                        let (from, to) = level_run(l_offsets, *row, l_domain.len());
                        keys.extend((from..to).map(RowSource::Left));
                    }
                    RowSource::Right(row) => {
                        let (from, to) = level_run(r_offsets, *row, r_domain.len());
                        keys.extend((from..to).map(RowSource::Right));
                    }
                    RowSource::Both(l_row, r_row) => {
                        let (l_from, l_to) = level_run(l_offsets, *l_row, l_domain.len());
                        let (r_from, r_to) = level_run(r_offsets, *r_row, r_domain.len());
                        // A key matches only where what it holds can grow ([`Tile::merge`]).
                        if l_codomain.holds_a_level() {
                            keys.extend(matched_keys(
                                l_domain,
                                l_from..l_to,
                                r_domain,
                                r_from..r_to,
                            ));
                        } else {
                            keys.extend((l_from..l_to).map(RowSource::Left));
                            keys.extend((r_from..r_to).map(RowSource::Right));
                        }
                    }
                }
            }
            // A key a merge names sits in one of the two key columns, so picking it is a
            // gather out of the two run together. A key both sides delivered is one key,
            // and the two spellings are equal, so either serves.
            let mut combined = l_domain.clone();
            combined.append(r_domain.clone());
            let offset = l_domain.len();
            let picked: Vec<usize> = keys
                .iter()
                .map(|key| match key {
                    RowSource::Left(i) | RowSource::Both(i, _) => *i,
                    RowSource::Right(j) => offset + j,
                })
                .collect();
            // A key is removed when every side that delivered it had removed it: one side
            // still holding it is a key the consumer has not taken.
            let deleted: BitSet = keys
                .iter()
                .enumerate()
                .filter(|(_, key)| match key {
                    RowSource::Left(i) => l_deleted.contains(*i),
                    RowSource::Right(j) => r_deleted.contains(*j),
                    RowSource::Both(i, j) => l_deleted.contains(*i) && r_deleted.contains(*j),
                })
                .map(|(at, _)| at)
                .collect();
            Tile::DataFunction {
                row_starts: ColumnValue::UInts(starts),
                domain: combined.select_indices(picked.iter().copied(), picked.len()),
                codomain: Box::new(merged_rows(l_codomain, r_codomain, &keys)),
                domain_predicate: l_pred.union(r_pred),
                deleted,
            }
        }
        // An aggregation stands over rows without keys of its own. A row one side delivered
        // is picked, and a row both sides delivered is that row's two contributions folded
        // by the aggregate's own law, as a whole aggregation's two halves are
        // ([`Tile::merge`]). A key reaches here from both sides when a record holds the
        // aggregation beside a level the delivery grew.
        (Tile::Aggregation { .. }, Tile::Aggregation { .. }) => {
            if !order
                .iter()
                .any(|source| matches!(source, RowSource::Both(..)))
            {
                return gathered_rows(left, right, order);
            }
            let mut rows = order.iter().map(|source| match *source {
                RowSource::Left(i) => left.select_rows(&[i]),
                RowSource::Right(j) => right.select_rows(&[j]),
                RowSource::Both(i, j) => {
                    let mut row = left.select_rows(&[i]);
                    row.merge_part(right.select_rows(&[j]), true);
                    row
                }
            });
            let mut out = rows.next().expect("a `Both` row is one of the rows");
            rows.for_each(|row| out.merge_part(row, false));
            out
        }
        // A store carries its own completeness rather than standing over keys, so a row both
        // sides deliver would have to be combined by the store's merge, which is not written
        // for a store under a collection because no producer grows a key over one.
        (Tile::Store { .. }, Tile::Store { .. }) => {
            if !order
                .iter()
                .any(|source| matches!(source, RowSource::Both(..)))
            {
                return gathered_rows(left, right, order);
            }
            assert_eq!(
                order.len(),
                1,
                "a store row both sides deliver is combined by the store's merge, which is \
                 written for the whole store only"
            );
            let mut taken = left.clone();
            taken.merge_part(right.clone(), true);
            taken
        }
        (l, r) => panic!("Incompatible tiles {l:?} and {r:?}"),
    }
}

/// The rows `order` names, taken from whichever side holds each, with no combining — for
/// the tiles whose rows are picked rather than merged.
///
/// The picks are read out of the two sides' rows run together, so the result follows
/// `order` even where it interleaves the sides.
fn gathered_rows(left: &Tile, right: &Tile, order: &[RowSource]) -> Tile {
    let offset = left.rows();
    let picked: Vec<usize> = order
        .iter()
        .map(|source| match *source {
            RowSource::Left(i) => i,
            RowSource::Right(j) => offset + j,
            RowSource::Both(..) => unreachable!("a row both sides deliver is combined, not picked"),
        })
        .collect();
    let mut combined = left.clone();
    combined.merge_part(right.clone(), false);
    combined.select_rows(&picked)
}

/// One column over the rows `order` names.
///
/// A column is empty or holds one value per row ([`valid_over`]), so a row both sides name
/// is carried by at most one of them: the other delivered that row to grow what sits beside
/// it in the record and left this column alone. Both carrying it is one position delivered
/// twice, which the release contract forbids and for which there is no answer.
fn merged_column(left: &ColumnValue, right: &ColumnValue, order: &[RowSource]) -> ColumnValue {
    if left.is_empty() && right.is_empty() {
        return left.clone();
    }
    let mut combined = left.clone();
    combined.append(right.clone());
    let offset = left.len();
    // A row whose side carries no column contributes no value, which leaves the result
    // short — the state `valid_over` reports rather than one this can repair.
    let picked: Vec<usize> = order
        .iter()
        .filter_map(|source| match source {
            RowSource::Left(i) => (!left.is_empty()).then_some(*i),
            RowSource::Right(j) => (!right.is_empty()).then_some(offset + j),
            RowSource::Both(i, j) => match (left.is_empty(), right.is_empty()) {
                (false, true) => Some(*i),
                (true, false) => Some(offset + j),
                (true, true) => None,
                (false, false) => panic!(
                    "a regrown key restates a scalar beside it, which the release contract \
                     forbids: {left:?} and {right:?}"
                ),
            },
        })
        .collect();
    combined.select_indices(picked.iter().copied(), picked.len())
}

/// Two rows' key runs matched into the one run they describe.
///
/// The left run's order is kept and the right run's new keys follow ([`Tile::merge`]). Keys are
/// unique within a row ([`valid_over`]), so each matches at most one key on the other side
/// and no ordering between the two runs is assumed — a producer that re-states an enclosing
/// key delivers its runs interleaved rather than abutting.
fn matched_keys(
    l_domain: &ColumnValue,
    l_run: std::ops::Range<usize>,
    r_domain: &ColumnValue,
    r_run: std::ops::Range<usize>,
) -> Vec<RowSource> {
    let right: HashMap<Value, usize> = r_run.clone().map(|j| (r_domain.index_at(j), j)).collect();
    let mut matched: HashSet<usize> = HashSet::new();
    let mut out = Vec::with_capacity(l_run.len() + r_run.len());
    for i in l_run {
        match right.get(&l_domain.index_at(i)) {
            Some(j) => {
                matched.insert(*j);
                out.push(RowSource::Both(i, *j));
            }
            None => out.push(RowSource::Left(i)),
        }
    }
    out.extend(r_run.filter(|j| !matched.contains(j)).map(RowSource::Right));
    out
}

/// Whether `tile` is well formed as a whole value.
///
/// Nothing pins the row count at the top level: a tile there carries its own rows, as a
/// `Scalar(Union)` stream does when its keys are the column's positions. Every depth below
/// is pinned by the row count [`Tile::DataFunction`] states, which is what this checks.
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
        Tile::DataFunction { row_starts, .. } => valid_over(tile, row_starts.len()),
        Tile::Store { .. } => valid_over(tile, 1),
    }
}

/// Whether `tile` is well formed as a value vectorized over `rows` rows.
///
/// Checks the row counts [`Tile::DataFunction`] states, and nothing else.
fn valid_over(tile: &Tile, rows: usize) -> bool {
    match tile {
        // A column that has not arrived is empty rather than `rows` long — what a producer
        // emits before it has an answer and a consumer reads as "not ready". It holds
        // wherever a column does, so a record field may be empty while its siblings are
        // full: a binop over a lagging operand builds the record before both columns are
        // in, and combines only the common prefix.
        Tile::Scalar(cv) => cv.is_empty() || cv.len() == rows,
        Tile::Record(fields) => fields.values().all(|t| valid_over(t, rows)),
        Tile::DataFunction {
            row_starts,
            domain,
            codomain,
            domain_predicate: _,
            deleted,
        } => {
            let ColumnValue::UInts(starts) = row_starts else {
                return false;
            };
            // A run per row, beginning at 0, non-decreasing, and ending inside `domain`.
            if starts.len() != rows
                || starts.first().is_some_and(|s| *s != 0)
                || !starts.windows(2).all(|w| w[0] <= w[1])
                || starts.last().is_some_and(|s| *s > domain.len())
            {
                return false;
            }
            if deleted.iter().any(|i| i >= domain.len()) {
                return false;
            }
            // Keys are unique *within* a row; a key may repeat across rows, since each row
            // has a collection of its own.
            let all: Vec<Value> = domain.clone().drain_to_value_iter().collect();
            if !(0..rows).all(|r| {
                let (from, to) = level_run(starts, r, domain.len());
                to - from == HashSet::<Value>::from_iter(all[from..to].iter().cloned()).len()
            }) {
                return false;
            }
            valid_over(codomain, domain.len())
        }
        Tile::Aggregation {
            accumulator,
            terminal,
            ..
        } => {
            accumulator.rows() == terminal.len()
                && (accumulator.is_empty() || accumulator.rows() == rows)
        }
        // A store's changelog is one delta per change tick, and the ticks are strictly
        // ascending — the fold ([`store_value_at`] et al.) and the change-append `merge`
        // both depend on it, and neither is type-enforced. It is a whole value rather than
        // something vectorized, so it stands at one row.
        Tile::Store {
            changes, deltas, ..
        } => {
            rows == 1
                && changes.len() == deltas.len()
                && matches!(deltas, ColumnValue::Variants(_))
                && (0..changes.len()).all(|i| {
                    i == 0
                        || matches!(
                            (changes.index_at(i - 1), changes.index_at(i)),
                            (Value::UInt(a), Value::UInt(b)) if a < b
                        )
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
        Tile::data_function(
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

    // ── Three collection levels ───────────────────────────────────────────────

    /// One `A` key's contribution: the key, then its `B` keys, each with its `C` entries.
    type ThreeLevelGroup<'a> = (usize, &'a [(usize, &'a [(usize, i64)])]);

    /// `A ⤇ B ⤇ C ⤇ Int`, every group named.
    ///
    /// The chain the one-node-per-level representation exists for: each level's
    /// `row_starts` counts the level above's keys, so the pairing is checked three deep.
    fn three_levels(groups: &[ThreeLevelGroup<'_>], outer_pred: Predicate) -> Tile {
        let (mut b_starts, mut b_keys) = (Vec::new(), Vec::new());
        let (mut c_starts, mut c_keys, mut values) = (Vec::new(), Vec::new(), Vec::new());
        for (_, bs) in groups {
            b_starts.push(b_keys.len());
            for (bk, cs) in *bs {
                b_keys.push(*bk);
                c_starts.push(c_keys.len());
                for (ck, v) in *cs {
                    c_keys.push(*ck);
                    values.push(*v);
                }
            }
        }
        let c = Tile::grouped(
            ColumnValue::UInts(c_starts),
            ColumnValue::from_uints(c_keys),
            Box::new(Tile::Scalar(ColumnValue::Ints(values))),
            Predicate::False,
            BitSet::new(),
        );
        let b = Tile::grouped(
            ColumnValue::UInts(b_starts),
            ColumnValue::from_uints(b_keys),
            Box::new(c),
            Predicate::False,
            BitSet::new(),
        );
        Tile::data_function(
            ColumnValue::from_uints(groups.iter().map(|(k, _)| *k).collect()),
            Box::new(b),
            outer_pred,
            BitSet::new(),
        )
    }

    /// A three-level fixture: `A=10` over `B=1,2`, `A=20` over `B=3`.
    fn abc() -> Tile {
        three_levels(
            &[
                (10, &[(1, &[(100, 1)]), (2, &[(200, 2), (201, 3)])]),
                (20, &[(3, &[(300, 4)])]),
            ],
            Predicate::False,
        )
    }

    /// The pairing rule holds at every level, not just the outermost: each level is one run
    /// of keys per row of the level above, and the values are one entry per innermost key.
    #[test]
    fn three_levels_pair_at_every_level() {
        assert!(validate_tile(&abc()));
    }

    /// The check reaches the third level: a `C` run count that disagrees with `B`'s key
    /// count is rejected even though the two levels above it agree.
    #[test]
    fn a_third_level_at_the_wrong_row_count_is_rejected() {
        let Tile::DataFunction { codomain, .. } = abc() else {
            unreachable!()
        };
        let Tile::DataFunction {
            row_starts,
            domain,
            codomain: c,
            ..
        } = *codomain
        else {
            unreachable!()
        };
        // `B` keeps its three keys; `C` is rebuilt over two rows instead of three.
        let Tile::DataFunction {
            domain: c_domain,
            codomain: c_values,
            ..
        } = *c
        else {
            unreachable!()
        };
        let short = Tile::DataFunction {
            row_starts: ColumnValue::UInts(vec![0, 1]),
            domain: c_domain,
            codomain: c_values,
            domain_predicate: Predicate::False,
            deleted: BitSet::new(),
        };
        let b = Tile::DataFunction {
            row_starts,
            domain,
            codomain: Box::new(short),
            domain_predicate: Predicate::False,
            deleted: BitSet::new(),
        };
        assert!(
            !valid_over(&b, 1),
            "C stands over two rows, B has three keys"
        );
    }

    /// An element three levels down is named by its whole path, and the chain walk reports
    /// the level it lives on.
    #[test]
    fn three_levels_name_each_element_by_its_path() {
        let tile = abc();
        assert_eq!(tile.innermost_depth(), Some(2), "C is two levels in from A");
        assert_eq!(
            tile.row_paths_at(3),
            vec![
                vec![Value::UInt(10), Value::UInt(1), Value::UInt(100)],
                vec![Value::UInt(10), Value::UInt(2), Value::UInt(200)],
                vec![Value::UInt(10), Value::UInt(2), Value::UInt(201)],
                vec![Value::UInt(20), Value::UInt(3), Value::UInt(300)],
            ],
            "each `C` key extends its `B` key's path, which extends its `A` key's"
        );
        assert_eq!(
            tile.values_at(2).rows(),
            3,
            "`C` stands over `B`'s three keys"
        );
    }

    /// A delivery that re-states a key two levels down grows the innermost group, and the
    /// levels above it keep their keys: the merge matches keys at each level down to the one
    /// that repeated.
    #[test]
    fn merging_three_levels_grows_the_innermost_group() {
        let mut tile = three_levels(&[(10, &[(1, &[(100, 1)])])], Predicate::False);
        tile.merge(three_levels(&[(10, &[(1, &[(200, 2)])])], Predicate::False));

        assert_eq!(
            tile.row_paths_at(3),
            vec![
                vec![Value::UInt(10), Value::UInt(1), Value::UInt(100)],
                vec![Value::UInt(10), Value::UInt(1), Value::UInt(200)],
            ],
            "one `A` key over one `B` key over both deliveries' `C` entries"
        );
        assert!(validate_tile(&tile));
    }

    /// The same delivery shape one level up: a re-stated `A` key carrying a new `B` key
    /// grows the middle level rather than repeating `A`.
    #[test]
    fn merging_three_levels_grows_a_middle_group() {
        let mut tile = three_levels(&[(10, &[(1, &[(100, 1)])])], Predicate::False);
        tile.merge(three_levels(&[(10, &[(2, &[(200, 2)])])], Predicate::False));

        let Tile::DataFunction { domain, .. } = &tile else {
            unreachable!()
        };
        assert_eq!(
            domain.len(),
            1,
            "`A` grew rather than repeating: {domain:?}"
        );
        assert_eq!(
            tile.row_paths_at(2),
            vec![
                vec![Value::UInt(10), Value::UInt(1)],
                vec![Value::UInt(10), Value::UInt(2)],
            ],
            "both `B` keys sit under the one `A` key"
        );
        assert!(validate_tile(&tile));
    }

    /// Matching keys joins a group that grew; it does not absorb a position delivered
    /// twice. Two deliveries naming the same innermost key are one position claimed twice,
    /// which the release contract forbids, and the recursion stops at the level whose
    /// values hold none so `valid_over` still sees the repeat.
    #[test]
    #[cfg_attr(
        not(debug_assertions),
        ignore = "pins the merge's `debug_assert!` on `validate_tile`"
    )]
    #[should_panic(expected = "Invalid tile after merge")]
    fn merging_three_levels_still_rejects_a_repeated_element() {
        let mut tile = three_levels(&[(10, &[(1, &[(100, 1)])])], Predicate::False);
        tile.merge(three_levels(&[(10, &[(1, &[(100, 2)])])], Predicate::False));
    }

    /// A release names a level by its depth, and compaction reaches it. Releasing a `C`
    /// key is two `Codomain` steps in, and the key is physically gone afterwards.
    #[test]
    fn compacting_reaches_the_third_level() {
        let mut tile = abc();
        tile.remove_guarded(TileGuard::Function(FunctionGuard::Codomain(Box::new(
            TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Function(
                FunctionGuard::Domain(Predicate::LessThanEq(Value::UInt(200))),
            )))),
        ))));
        tile.compact();

        assert_eq!(
            tile.row_paths_at(3),
            vec![
                vec![Value::UInt(10), Value::UInt(2), Value::UInt(201)],
                vec![Value::UInt(20), Value::UInt(3), Value::UInt(300)],
            ],
            "the `C` keys at or below 200 are gone, and `B=1` is left holding nothing"
        );
        assert!(
            validate_tile(&tile),
            "an emptied group is still a key: {tile:?}"
        );
    }

    /// Filtering the innermost level of three keeps every key above it, so a `B` key whose
    /// `C` entries all go keeps its identity and holds an empty group.
    #[test]
    fn retaining_innermost_keys_of_three_empties_rather_than_removes() {
        let mut tile = abc();
        let innermost = tile
            .innermost_depth()
            .unwrap_or_else(|| unreachable!("three levels"));
        // Keep only `C` keys 201 and 300 — `B=1`'s only entry goes.
        tile.values_at_mut(innermost)
            .retain_keys(&BitVec::from_fn(4, |k| k >= 2));

        assert_eq!(
            tile.row_paths_at(2),
            vec![
                vec![Value::UInt(10), Value::UInt(1)],
                vec![Value::UInt(10), Value::UInt(2)],
                vec![Value::UInt(20), Value::UInt(3)],
            ],
            "every `B` key survives the filter that emptied one of them"
        );
        assert_eq!(tile.values_at(2).row_run(0), (0, 0), "`B=1` holds nothing");
        assert!(validate_tile(&tile));
    }

    /// Releasing exactly what a three-level tile's guard names leaves nothing live.
    #[test]
    fn releasing_a_three_level_guard_round_trips() {
        let mut tile = abc();
        let guard = tile.to_guard();
        tile.remove_guarded(guard);
        tile.compact();

        assert!(
            tile.row_paths_at(3).is_empty(),
            "every element the guard named is gone: {tile:?}"
        );
        assert!(validate_tile(&tile));
    }

    // ── A record between two collection levels ────────────────────────────

    /// One `K` key's contribution: the key, the `n` value this delivery carries for it,
    /// and the `xs` entries under it.
    type RecordGroup<'a> = (usize, Option<i64>, &'a [(usize, i64)]);

    /// `K ⤇ {n: Int, xs: (J ⤇ Int)}`, one `K` key per group.
    ///
    /// A record component may hold **a collection per row** rather than a value per row:
    /// `xs` restates the rows it sits under as its own outermost level, so each row keys a
    /// group of its own. That is the shape a product value takes inside a codomain, and the
    /// alternative — one boxed map per cell — is what it exists to avoid.
    ///
    /// `n` is the record's scalar field, one value per `K` key. `None` is a delivery that
    /// does not carry it, which is what a repeat of a key it already stated must do.
    fn record_between_levels(
        groups: &[RecordGroup<'_>],
        outer_pred: Predicate,
        inner_pred: Predicate,
    ) -> Tile {
        let mut starts = Vec::new();
        let mut inner_keys = Vec::new();
        let mut inner_values = Vec::new();
        for (_, _, entries) in groups {
            starts.push(inner_keys.len());
            inner_keys.extend(entries.iter().map(|(k, _)| *k));
            inner_values.extend(entries.iter().map(|(_, v)| *v));
        }
        let b = Tile::grouped(
            ColumnValue::UInts(starts),
            ColumnValue::from_uints(inner_keys),
            Box::new(Tile::Scalar(ColumnValue::Ints(inner_values))),
            inner_pred,
            BitSet::new(),
        );
        Tile::data_function(
            ColumnValue::from_uints(groups.iter().map(|(k, _, _)| *k).collect()),
            Box::new(Tile::Record(HashMap::from([
                (
                    "n".to_string(),
                    Tile::Scalar(ColumnValue::Ints(
                        groups.iter().filter_map(|(_, n, _)| *n).collect(),
                    )),
                ),
                ("xs".to_string(), b),
            ]))),
            outer_pred,
            BitSet::new(),
        )
    }

    /// The record's two fields, as the `n` column and `xs`'s `(domain, codomain)`.
    fn record_fields(tile: &Tile) -> (Vec<Value>, Vec<Value>, Vec<Value>) {
        let Tile::DataFunction { codomain, .. } = tile else {
            panic!("expected a collection, got {tile:?}");
        };
        let Tile::Record(fields) = codomain.as_ref() else {
            panic!("expected a record codomain, got {codomain:?}");
        };
        let Tile::Scalar(n) = &fields["n"] else {
            panic!("expected a scalar at `n`, got {:?}", fields["n"]);
        };
        let Tile::DataFunction {
            domain, codomain, ..
        } = &fields["xs"]
        else {
            panic!("expected a collection at `xs`, got {:?}", fields["xs"]);
        };
        let Tile::Scalar(values) = codomain.as_ref() else {
            panic!("expected scalar values under `xs`, got {codomain:?}");
        };
        let column = |c: &ColumnValue| (0..c.len()).map(|i| c.index_at(i)).collect::<Vec<_>>();
        (column(n), column(domain), column(values))
    }

    /// A collection under a record's field is a level under the key the record stands on,
    /// so the key is complete only when every field is. Reading the codomain's node type
    /// alone calls the record a leaf and releases every `K` key, taking the still-growing
    /// `J` groups with it.
    #[test]
    fn a_record_between_two_levels_holds_its_keys() {
        let tile = record_between_levels(
            &[(0, Some(1), &[(100, 10)]), (1, Some(2), &[(200, 20)])],
            Predicate::False,
            Predicate::False,
        );

        // No `K` key is settled, so the domain arm names nothing and drops out of the
        // union: what is left is the level the record holds, one step in.
        let TileGuard::Function(FunctionGuard::Codomain(held)) = tile.to_guard() else {
            panic!(
                "a still-growing collection under the record holds every key back, so no \
                 key is named: {:?}",
                tile.to_guard()
            );
        };
        let TileGuard::Record(fields) = held.as_ref() else {
            panic!("a record codomain is guarded field-wise, got {held:?}");
        };
        assert_eq!(
            fields.get("n"),
            Some(&TileGuard::Scalar(true)),
            "a scalar field is complete as soon as it is there: {fields:?}"
        );
        assert_eq!(
            fields.get("xs"),
            Some(&TileGuard::Function(FunctionGuard::Domain(
                Predicate::from_column_value(&ColumnValue::from_uints(vec![100, 200]))
            ))),
            "the collection field names the inner keys it holds: {fields:?}"
        );
    }

    /// Releasing exactly what the guard named empties what sat under the keys and leaves
    /// the keys themselves, which are not complete and were never named.
    #[test]
    fn releasing_a_record_codomain_keeps_the_keys_above_it() {
        let mut tile = record_between_levels(
            &[(0, Some(1), &[(100, 10)]), (1, Some(2), &[(200, 20)])],
            Predicate::False,
            Predicate::False,
        );
        let guard = tile.to_guard();
        tile.remove_guarded(guard);
        tile.compact();

        let Tile::DataFunction { domain, .. } = &tile else {
            panic!("expected a collection, got {tile:?}");
        };
        assert_eq!(domain.len(), 2, "the unsettled keys stay: {domain:?}");
        assert_eq!(
            record_fields(&tile),
            (vec![], vec![], vec![]),
            "everything the guard named is gone"
        );
    }

    /// A key re-stated to extend the collection under its record grows that collection,
    /// exactly as it would with no record in the way. The record's scalar field stands one
    /// value per key and has nothing to join, so the repeat leaves it alone.
    #[test]
    fn a_regrown_key_joins_the_collection_inside_its_record() {
        let mut tile = record_between_levels(
            &[(0, Some(7), &[(100, 10)])],
            Predicate::False,
            Predicate::False,
        );
        tile.merge(record_between_levels(
            &[(0, None, &[(200, 20)])],
            Predicate::False,
            Predicate::False,
        ));

        let Tile::DataFunction { domain, .. } = &tile else {
            panic!("expected a collection, got {tile:?}");
        };
        assert_eq!(
            domain.len(),
            1,
            "the repeat is one key that grew: {domain:?}"
        );
        assert_eq!(
            record_fields(&tile),
            (
                vec![Value::Int(7)],
                vec![Value::UInt(100), Value::UInt(200)],
                vec![Value::Int(10), Value::Int(20)]
            ),
            "both deliveries' entries sit in the one group, over the one scalar value"
        );
    }

    /// The other half of that rule: a repeat that re-states the scalar beside the grown
    /// collection has delivered one position twice, and there is no answer for which value
    /// stands. `merged_column` says so rather than picking.
    #[test]
    #[should_panic(expected = "restates a scalar beside it")]
    fn a_regrown_key_may_not_restate_the_scalar_beside_it() {
        let mut tile = record_between_levels(
            &[(0, Some(7), &[(100, 10)])],
            Predicate::False,
            Predicate::False,
        );
        tile.merge(record_between_levels(
            &[(0, Some(9), &[(200, 20)])],
            Predicate::False,
            Predicate::False,
        ));
    }

    /// Compaction reaches a level held inside a record: a key released there is gone
    /// afterwards, so the next delivery of it replaces the group rather than landing
    /// beside it.
    #[test]
    fn compacting_reaches_a_level_inside_a_record() {
        let mut tile = record_between_levels(
            &[(0, Some(7), &[(100, 10), (200, 20)])],
            Predicate::False,
            Predicate::True,
        );
        tile.remove_guarded(TileGuard::Function(FunctionGuard::Codomain(Box::new(
            TileGuard::Record(HashMap::from([
                ("n".to_string(), TileGuard::Scalar(false)),
                (
                    "xs".to_string(),
                    TileGuard::Function(FunctionGuard::Domain(Predicate::LessThanEq(Value::UInt(
                        100,
                    )))),
                ),
            ])),
        ))));
        tile.compact();

        assert_eq!(
            record_fields(&tile),
            (
                vec![Value::Int(7)],
                vec![Value::UInt(200)],
                vec![Value::Int(20)]
            ),
            "the released inner key is physically gone"
        );
    }

    /// The innermost level is the one a record sits under, not a collection in one of its
    /// fields ([`Tile::holds_a_level`]).
    #[test]
    fn a_record_ends_the_chain_and_is_the_element() {
        assert_eq!(
            record_between_levels(
                &[(0, Some(1), &[(100, 10)])],
                Predicate::False,
                Predicate::False
            )
            .innermost_depth(),
            Some(0),
            "the record is `K`'s element, so `K` is the innermost level"
        );
        let nested = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(record_between_levels(
                &[(0, Some(1), &[(100, 10)])],
                Predicate::False,
                Predicate::False,
            )),
            Predicate::False,
            BitSet::new(),
        );
        assert_eq!(
            nested.innermost_depth(),
            Some(1),
            "a level above it makes that level the innermost, not the record's field"
        );
    }

    /// What can still grow looks through a record and stops at an aggregation
    /// ([`Tile::holds_a_level`]).
    #[test]
    fn holds_a_level_looks_through_a_record_and_stops_at_an_aggregation() {
        let collection = Tile::data_function(
            ColumnValue::from_uints(vec![100]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10]))),
            Predicate::False,
            BitSet::new(),
        );
        assert!(
            Tile::Record(HashMap::from([
                ("a".to_string(), Tile::Scalar(ColumnValue::Ints(vec![1]))),
                ("b".to_string(), collection.clone()),
            ]))
            .holds_a_level(),
            "a collection in a record's field is a level under the record"
        );
        assert!(
            !Tile::Record(HashMap::from([(
                "a".to_string(),
                Tile::Scalar(ColumnValue::Ints(vec![1]))
            )]))
            .holds_a_level(),
            "a record of scalars holds nothing that grows"
        );
        assert!(
            !Tile::Aggregation {
                kind: AggregateKind::Sole,
                accumulator: Box::new(collection),
                terminal: ColumnValue::Bools(BitVec::from_elem(1, false)),
            }
            .holds_a_level(),
            "an aggregation carries its own completeness, so it answers for what it holds"
        );
    }
    /// A release names the level it is about, and what it names is physically gone after
    /// a compaction. For a nested collection that level is **below** the top, so
    /// compacting has to reach it — otherwise the key stays present-but-deleted, and the
    /// next delivery of that key lands beside it instead of replacing it.
    #[test]
    fn compacting_reaches_an_inner_level() {
        let mut tile = one_group(0, vec![0, 1], vec![10, 20]);
        tile.remove_guarded(TileGuard::Function(FunctionGuard::Codomain(Box::new(
            TileGuard::Function(FunctionGuard::Domain(Predicate::LessThanEq(Value::UInt(0)))),
        ))));
        tile.compact();

        let Tile::DataFunction { codomain, .. } = &tile else {
            panic!("expected a collection, got {tile:?}");
        };
        let Tile::DataFunction {
            domain, deleted, ..
        } = codomain.as_ref()
        else {
            panic!("expected a group under the row, got {codomain:?}");
        };
        assert!(deleted.is_empty(), "the released key is gone, not deleted");
        assert_eq!(domain.len(), 1, "only the unreleased position is left");
        assert_eq!(domain.index_at(0), Value::UInt(1));
    }

    /// A record sits between two levels, so a compaction reaches its fields as well: the
    /// collection under a field is as much a level as one under a key.
    #[test]
    fn compacting_reaches_a_record_field() {
        let mut field = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20]))),
            Predicate::False,
            BitSet::new(),
        );
        field.remove_guarded(TileGuard::Function(FunctionGuard::Domain(
            Predicate::LessThanEq(Value::UInt(0)),
        )));
        let mut tile = Tile::Record(HashMap::from([("a".to_string(), field)]));
        tile.compact();

        let Tile::Record(fields) = &tile else {
            panic!("expected a record, got {tile:?}");
        };
        let Tile::DataFunction {
            domain, deleted, ..
        } = &fields["a"]
        else {
            panic!("expected a collection in the field, got {:?}", fields["a"]);
        };
        assert!(deleted.is_empty(), "the field's released key is gone");
        assert_eq!(domain.len(), 1);
        assert_eq!(domain.index_at(0), Value::UInt(1));
    }

    /// A `Sole` accumulator holds an *element*, so it carries whatever levels the element
    /// has and a compaction has to reach them. The row count is what makes this more than
    /// one more recursion: `terminal` has one bit per row, and a collection's rows are its
    /// `row_starts`, which dropping keys rebuilds at the same length — so the accumulator
    /// still stands over as many rows as there are bits, which is what [`validate_tile`]
    /// asks of an aggregation.
    #[test]
    fn compacting_reaches_a_sole_accumulator() {
        let mut accumulator = Tile::grouped(
            ColumnValue::UInts(vec![0, 2]),
            ColumnValue::from_uints(vec![100, 101, 200]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
            Predicate::False,
            BitSet::new(),
        );
        accumulator.remove_guarded(TileGuard::Function(FunctionGuard::Domain(
            Predicate::LessThanEq(Value::UInt(100)),
        )));
        let mut tile = Tile::Aggregation {
            kind: AggregateKind::Sole,
            accumulator: Box::new(accumulator),
            terminal: ColumnValue::Bools(BitVec::from_elem(2, false)),
        };
        tile.compact();

        let Tile::Aggregation { accumulator, .. } = &tile else {
            panic!("expected an aggregation, got {tile:?}");
        };
        let Tile::DataFunction {
            row_starts,
            domain,
            deleted,
            ..
        } = accumulator.as_ref()
        else {
            panic!("expected a collection in the accumulator, got {accumulator:?}");
        };
        assert!(deleted.is_empty(), "the released key is gone, not deleted");
        assert_eq!(
            domain.clone().drain_to_value_iter().collect::<Vec<_>>(),
            vec![Value::UInt(101), Value::UInt(200)],
            "only the unreleased keys are left"
        );
        assert_eq!(
            row_starts,
            &ColumnValue::UInts(vec![0, 1]),
            "the first row lost a key, so the second row's run now begins one earlier"
        );
        assert!(
            validate_tile(&tile),
            "the accumulator still stands over as many rows as `terminal` has bits"
        );
    }

    /// A re-stated key grows its group rather than repeating ([`Tile::merge`]).
    #[test]
    fn merging_a_row_that_grew_extends_its_group() {
        let mut tile = one_group(0, vec![0], vec![10]);
        tile.merge(one_group(0, vec![1], vec![20]));

        let Tile::DataFunction {
            domain, codomain, ..
        } = &tile
        else {
            panic!("expected a collection, got {tile:?}");
        };
        assert_eq!(domain.len(), 1, "row 0 is one key, not two: {tile:?}");
        assert_eq!(codomain.row_run(0), (0, 2), "its group holds both elements");
        assert!(
            validate_tile(&tile),
            "and the tile is well formed: {tile:?}"
        );
    }

    /// A different key is a new row, so the merge keeps two rows that sit next to each other
    /// apart.
    #[test]
    fn merging_a_new_row_keeps_it_apart() {
        let mut tile = one_group(0, vec![0, 1], vec![10, 20]);
        tile.merge(one_group(1, vec![0], vec![30]));

        let Tile::DataFunction {
            domain, codomain, ..
        } = &tile
        else {
            panic!("expected a collection, got {tile:?}");
        };
        assert_eq!(domain.len(), 2, "two enclosing rows: {tile:?}");
        assert_eq!(codomain.row_run(0), (0, 2));
        assert_eq!(codomain.row_run(1), (2, 3));
        assert!(
            validate_tile(&tile),
            "and the tile is well formed: {tile:?}"
        );
    }

    /// A row that grows twice matches its key each time, so a collection delivered one
    /// element per pull ends with one key and the whole run under it.
    #[test]
    fn a_row_that_grows_repeatedly_stays_one_key() {
        let mut tile = one_group(0, vec![0], vec![10]);
        tile.merge(one_group(0, vec![1], vec![20]));
        tile.merge(one_group(0, vec![2], vec![30]));

        let Tile::DataFunction {
            domain, codomain, ..
        } = &tile
        else {
            panic!("expected a collection, got {tile:?}");
        };
        assert_eq!(domain.len(), 1);
        assert_eq!(codomain.row_run(0), (0, 3));
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
    #[cfg_attr(
        not(debug_assertions),
        ignore = "pins the merge's `debug_assert!` on `validate_tile`"
    )]
    #[should_panic(expected = "Invalid tile after merge")]
    fn a_repeated_scalar_key_is_reported_not_folded() {
        let leaf = |v: i64| {
            Tile::data_function(
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
    fn tile_function_true_predicate_is_terminal() {
        let tile = Tile::data_function(
            ColumnValue::Ints(vec![1]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![2]))),
            Predicate::True,
            BitSet::new(),
        );
        assert!(tile.is_terminal());
    }

    #[test]
    fn tile_function_false_predicate_not_terminal() {
        let tile = Tile::data_function(
            ColumnValue::Ints(vec![]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![]))),
            Predicate::False,
            BitSet::new(),
        );
        assert!(!tile.is_terminal());
    }

    #[test]
    fn tile_lookup_function_true_predicate_is_terminal() {
        let tile = Tile::data_function(
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
        Tile::data_function(
            ColumnValue::Ints(domain),
            Box::new(Tile::Scalar(ColumnValue::Ints(codomain))),
            pred,
            BitSet::new(),
        )
    }

    /// Two nested collections: usize keys over usize keys over an int value.
    fn two_level_uint_int(
        d1: Vec<usize>,
        offsets: Vec<usize>,
        d2: Vec<usize>,
        cod: Vec<i64>,
        pred: Predicate,
    ) -> Tile {
        Tile::data_function(
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

    /// The two-row case of [`record_between_levels`], named for what it is about: a
    /// component holding a collection per row. Row 0 holds `[1, 2]`, row 1 holds `[3]`,
    /// and the inner keys repeat across rows because each row keys a group of its own.
    fn rows_with_a_collection_component() -> Tile {
        record_between_levels(
            &[(0, Some(5), &[(0, 1), (1, 2)]), (1, Some(7), &[(0, 3)])],
            Predicate::True,
            Predicate::False,
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
        let Tile::DataFunction { codomain, .. } = rows_with_a_collection_component() else {
            unreachable!()
        };
        // Built as a literal: the constructor's own check is what this is about.
        let mismatched = Tile::DataFunction {
            // One row above, two rows inside the component.
            row_starts: ColumnValue::UInts(vec![0]),
            domain: ColumnValue::UInts(vec![0]),
            codomain,
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        assert!(!validate_tile(&mismatched));
    }

    /// Retaining a key takes that key's whole group out of a collection component, rather
    /// than reading the key mask as a mask over the component's entries. The rows the
    /// component sits over are this collection's own keys, which is why a key mask reaches
    /// it at all.
    #[test]
    fn retaining_a_key_takes_its_group_from_a_collection_component() {
        let mut tile = rows_with_a_collection_component();
        tile.retain_keys(&BitVec::from_fn(2, |i| i == 0));
        let Tile::DataFunction { codomain, .. } = &tile else {
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
        let Tile::DataFunction {
            row_starts,
            domain,
            codomain: inner,
            ..
        } = &fields["xs"]
        else {
            panic!("the component holds a collection per row")
        };
        assert_eq!(*row_starts, ColumnValue::UInts(vec![0]), "one row survives");
        assert_eq!(
            *domain,
            ColumnValue::UInts(vec![0, 1]),
            "with its whole group, and row 1's element gone"
        );
        assert_eq!(**inner, Tile::Scalar(ColumnValue::Ints(vec![1, 2])));
        assert!(validate_tile(&tile), "{tile:?}");
    }

    /// A first start above 0 leaves the elements before it under no parent.
    ///
    /// `level_run` reads a run as `[starts[i], starts[i + 1])`, so nothing reaches them,
    /// and they are neither an empty group nor a removed key ([`Tile::DataFunction`]'s
    /// `row_starts`).
    #[test]
    #[cfg_attr(
        not(debug_assertions),
        ignore = "the constructor's tile check is a `debug_assert!`"
    )]
    #[should_panic(expected = "Invalid collection")]
    fn a_first_start_above_zero_orphans_the_entries_before_it() {
        two_level_uint_int(
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
        let tile = Tile::data_function(
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

    /// Build a TileGuard for releasing the inner keys described by `pred` from a collection.
    fn inner_release_guard(pred: Predicate) -> TileGuard {
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
        let Tile::DataFunction {
            domain, codomain, ..
        } = &tile
        else {
            panic!("expected a function tile");
        };
        assert_eq!(*domain, ColumnValue::Ints(vec![1, 2]));
        assert_eq!(
            *codomain,
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20])))
        );
    }

    #[test]
    fn merge_function_unions_predicates() {
        let p1 = Predicate::from_column_value(&ColumnValue::Ints(vec![1]));
        let p2 = Predicate::from_column_value(&ColumnValue::Ints(vec![2]));
        let mut tile = fn_int(vec![1], vec![10], p1.clone());
        tile.merge(fn_int(vec![2], vec![20], p2.clone()));
        let Tile::DataFunction {
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
    fn merging_two_levels_with_disjoint_keys_runs_the_groups_together() {
        // Group 0 (d1=0): d2=[10, 11], cod=[100, 110]
        // Group 1 (d1=1): d2=[12],     cod=[120]
        let mut tile = two_level_uint_int(
            vec![0],
            vec![0],
            vec![10, 11],
            vec![100, 110],
            Predicate::False,
        );
        tile.merge(two_level_uint_int(
            vec![1],
            vec![0],
            vec![12],
            vec![120],
            Predicate::False,
        ));
        assert_eq!(
            tile,
            two_level_uint_int(
                vec![0, 1],
                vec![0, 2], // the second key's group starts at index 2 of the joined keys
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
    fn to_guard_one_level_wraps_domain_predicate() {
        let pred = Predicate::from_column_value(&ColumnValue::Ints(vec![1, 2]));
        let tile = fn_int(vec![1, 2], vec![10, 20], pred.clone());
        assert_eq!(
            tile.to_guard(),
            TileGuard::Function(FunctionGuard::Domain(pred))
        );
    }

    #[test]
    fn to_guard_two_levels_uses_the_inner_keys() {
        let tile = two_level_uint_int(
            vec![0],
            vec![0],
            vec![10, 11],
            vec![100, 110],
            Predicate::False,
        );
        let guard = tile.to_guard();
        // The guard should cover inner keys 10 and 11.
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
    fn to_guard_two_levels_names_only_the_open_groups_keys() {
        // Groups 0 and 1, both keyed 10 and 11; the predicate calls group 0 whole.
        let tile = two_level_uint_int(
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
    fn to_guard_two_levels_whole_groups_name_no_keys() {
        let tile = two_level_uint_int(
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
    fn to_guard_two_levels_empty_inner_filters_codomain_arm() {
        // When the inner level is empty its guard is Predicate::False (empty).  flatten_or
        // must filter it out, leaving only the outer predicate as a plain Domain guard — not
        // wrapped in an Or.
        let pred = Predicate::LessThanEq(Value::UInt(5));
        let tile = two_level_uint_int(vec![], vec![], vec![], vec![], pred.clone());
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
    fn remove_guarded_one_level_removes_matching_entries() {
        // Logically removes domain value 1 (index 0); physical arrays are unchanged.
        let pred = Predicate::from_column_value(&ColumnValue::Ints(vec![1]));
        let mut tile = fn_int(vec![1, 2], vec![10, 20], Predicate::True);
        tile.remove_guarded(TileGuard::Function(FunctionGuard::Domain(pred)));
        let Tile::DataFunction {
            domain,
            codomain,
            deleted,
            ..
        } = &tile
        else {
            panic!("expected a collection tile");
        };
        // Physical arrays are unchanged.
        assert_eq!(*domain, ColumnValue::Ints(vec![1, 2]));
        assert_eq!(
            *codomain,
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20])))
        );
        // Index 0 (key 1) is logically deleted.
        assert!(deleted.contains(0), "index 0 should be deleted");
        assert!(!deleted.contains(1), "index 1 should not be deleted");
    }

    #[test]
    fn remove_guarded_one_level_full_release_clears() {
        let mut tile = fn_int(vec![1, 2], vec![10, 20], Predicate::True);
        let guard = tile.to_guard();
        tile.remove_guarded(guard);
        // Physical arrays are unchanged; logical length is 0.
        assert!(tile.is_empty());
    }

    #[test]
    fn remove_guarded_two_levels_removes_matching_inner_keys() {
        // d1=[0,1], offsets=[0,2], d2=[10,11,12], cod=[100,110,120]
        // Logically removes d2=11 (flat index 1); physical arrays are unchanged.
        let mut tile = two_level_uint_int(
            vec![0, 1],
            vec![0, 2],
            vec![10, 11, 12],
            vec![100, 110, 120],
            Predicate::False,
        );
        let pred = Predicate::from_column_value(&ColumnValue::UInts(vec![11]));
        tile.remove_guarded(inner_release_guard(pred));
        let Tile::DataFunction {
            codomain: groups, ..
        } = &tile
        else {
            panic!("expected a collection");
        };
        let Tile::DataFunction {
            domain,
            codomain,
            deleted,
            ..
        } = groups.as_ref()
        else {
            panic!("expected a collection of collections");
        };
        // Physical arrays unchanged.
        assert_eq!(*domain, ColumnValue::UInts(vec![10, 11, 12]));
        assert_eq!(
            **codomain,
            Tile::Scalar(ColumnValue::Ints(vec![100, 110, 120]))
        );
        // Only key 11 is logically deleted.
        assert!(!deleted.contains(0));
        assert!(deleted.contains(1));
        assert!(!deleted.contains(2));
    }

    #[test]
    fn remove_guarded_two_levels_prunes_empty_group() {
        // d1=[0,1], offsets=[0,2], d2=[10,11,12], cod=[100,110,120]
        // Logically removes d2=10 (idx 0) and d2=11 (idx 1); physical arrays unchanged.
        let mut tile = two_level_uint_int(
            vec![0, 1],
            vec![0, 2],
            vec![10, 11, 12],
            vec![100, 110, 120],
            Predicate::False,
        );
        let pred = Predicate::from_column_value(&ColumnValue::UInts(vec![10, 11]));
        tile.remove_guarded(inner_release_guard(pred));
        let Tile::DataFunction {
            codomain: groups, ..
        } = &tile
        else {
            panic!("expected a collection");
        };
        let Tile::DataFunction { deleted, .. } = groups.as_ref() else {
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
    fn remove_guarded_two_levels_domain_marks_the_named_group() {
        // d1=[0,1], offsets=[0,2], d2=[10,11,12], cod=[100,110,120]
        let mut tile = two_level_uint_int(
            vec![0, 1],
            vec![0, 2],
            vec![10, 11, 12],
            vec![100, 110, 120],
            Predicate::False,
        );
        let pred = Predicate::from_column_value(&ColumnValue::UInts(vec![0]));
        tile.remove_guarded(TileGuard::Function(FunctionGuard::Domain(pred)));
        let Tile::DataFunction {
            deleted,
            codomain: groups,
            ..
        } = &tile
        else {
            panic!("expected a collection");
        };
        assert!(deleted.contains(0), "the named group is marked");
        assert!(!deleted.contains(1), "its sibling is not");
        let Tile::DataFunction { deleted: inner, .. } = groups.as_ref() else {
            panic!("expected a collection of collections");
        };
        assert!(
            inner.is_empty(),
            "the entries beneath it are not marked; `compact` takes them"
        );

        tile.compact();
        let Tile::DataFunction {
            domain,
            codomain: groups,
            ..
        } = &tile
        else {
            panic!("expected a collection");
        };
        assert_eq!(*domain, ColumnValue::UInts(vec![1]), "group 0 is gone");
        let Tile::DataFunction {
            row_starts,
            domain: inner_keys,
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
    fn round_trip_one_level_full_release() {
        let mut tile = fn_int(vec![1, 2, 3], vec![10, 20, 30], Predicate::True);
        let guard = tile.to_guard();
        tile.remove_guarded(guard);
        assert_eq!(
            tile.to_guard(),
            TileGuard::Function(FunctionGuard::Domain(Predicate::True))
        );
    }

    #[test]
    fn round_trip_two_levels_full_release() {
        // After logical deletion, to_guard() still sees all physical entries, so
        // the guard is unchanged (including deleted entries for complete source releasing).
        let mut tile = two_level_uint_int(
            vec![0, 1],
            vec![0, 2],
            vec![10, 11, 12],
            vec![100, 110, 120],
            Predicate::False,
        );
        let guard = tile.to_guard();
        tile.remove_guarded(guard.clone());
        assert_eq!(tile.to_guard(), guard);
        // Emptiness is per level, which is the distinction a collection's own keys make.
        // The inner level is empty: every entry it holds is logically deleted. The outer
        // is not: the guard never named its keys, because nothing says their groups are
        // complete, and a collection that still knows its keys still knows something.
        let Tile::DataFunction { codomain, .. } = &tile else {
            unreachable!("a collection stays a collection")
        };
        assert!(
            codomain.is_empty(),
            "every entry is logically deleted: {codomain:?}"
        );
        assert!(!tile.is_empty(), "the outer keys are still data: {tile:?}");
    }

    // ── Tile::retain_keys ─────────────────────────────────────────────────────

    fn three_groups() -> Tile {
        two_level_uint_int(
            vec![10, 20, 30],
            vec![0, 2, 5],
            vec![0, 1, 2, 3, 4, 5],
            vec![100, 110, 200, 210, 220, 300],
            Predicate::False,
        )
    }

    #[test]
    fn retain_keys_keep_all_is_noop() {
        let mut tile = three_groups();
        let Tile::DataFunction { codomain, .. } = &mut tile else {
            unreachable!("three_groups is a collection of collections")
        };
        codomain.retain_keys(&BitVec::from_elem(6, true));
        assert_eq!(tile, three_groups());
    }

    #[test]
    fn retain_keys_keep_none_leaves_every_group_empty() {
        let mut tile = three_groups();
        let Tile::DataFunction { codomain, .. } = &mut tile else {
            unreachable!("three_groups is a collection of collections")
        };
        codomain.retain_keys(&BitVec::from_elem(6, false));
        assert_eq!(
            tile,
            two_level_uint_int(
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
        let mut tile = three_groups();
        // Keep positions 0,1 (group 10); groups 20 and 30 are left empty.
        let Tile::DataFunction { codomain, .. } = &mut tile else {
            unreachable!("three_groups is a collection of collections")
        };
        codomain.retain_keys(&BitVec::from_fn(6, |i| i < 2));
        assert_eq!(
            tile,
            two_level_uint_int(
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
        let mut tile = three_groups();
        let Tile::DataFunction { codomain, .. } = &mut tile else {
            unreachable!("three_groups is a collection of collections")
        };
        codomain.retain_keys(&BitVec::from_fn(6, |i| (2..5).contains(&i)));
        assert_eq!(
            tile,
            two_level_uint_int(
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
        let mut tile = three_groups();
        let Tile::DataFunction { codomain, .. } = &mut tile else {
            unreachable!("three_groups is a collection of collections")
        };
        codomain.retain_keys(&BitVec::from_fn(6, |i| i == 5));
        assert_eq!(
            tile,
            two_level_uint_int(
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
        let mut tile = three_groups();
        let Tile::DataFunction { codomain, .. } = &mut tile else {
            unreachable!("three_groups is a collection of collections")
        };
        codomain.retain_keys(&BitVec::from_fn(6, |i| !(2..5).contains(&i)));
        assert_eq!(
            tile,
            two_level_uint_int(
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
        let mut tile = three_groups();
        // One survivor in each of groups 10 and 20; group 30 keeps nothing.
        let Tile::DataFunction { codomain, .. } = &mut tile else {
            unreachable!("three_groups is a collection of collections")
        };
        codomain.retain_keys(&BitVec::from_fn(6, |i| i == 1 || i == 3));
        assert_eq!(
            tile,
            two_level_uint_int(
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
        let mut tile = three_groups();
        // Keep d2[2] and d2[4] (both in group 20); groups 10 and 30 are left empty.
        let Tile::DataFunction { codomain, .. } = &mut tile else {
            unreachable!("three_groups is a collection of collections")
        };
        codomain.retain_keys(&BitVec::from_fn(6, |i| i == 2 || i == 4));
        assert_eq!(
            tile,
            two_level_uint_int(
                vec![10, 20, 30],
                vec![0, 0, 2],
                vec![2, 4],
                vec![200, 220],
                Predicate::False
            )
        );
    }

    /// `Sum` accumulators, one row per key, each row already terminal.
    fn sums(acc: Vec<i64>) -> Tile {
        let rows = acc.len();
        Tile::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tile::Scalar(ColumnValue::Ints(acc))),
            terminal: ColumnValue::Bools(BitVec::from_elem(rows, true)),
        }
    }

    /// The accumulator column of the aggregation at `level`.
    fn accumulated(tile: &Tile, level: usize) -> ColumnValue {
        let Tile::Aggregation { accumulator, .. } = tile.values_at(level) else {
            panic!("expected an aggregation at level {level}: {tile:?}");
        };
        let Tile::Scalar(column) = accumulator.as_ref() else {
            panic!("expected a column accumulator: {accumulator:?}");
        };
        column.clone()
    }

    /// A delivery of new keys over aggregations appends one accumulator per key, and
    /// folds none of them into another.
    #[test]
    fn merging_new_keys_over_aggregations_keeps_one_accumulator_each() {
        let mut tile = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1]),
            Box::new(sums(vec![10, 20])),
            Predicate::False,
            BitSet::new(),
        );
        tile.merge(Tile::data_function(
            ColumnValue::from_uints(vec![2]),
            Box::new(sums(vec![30])),
            Predicate::False,
            BitSet::new(),
        ));
        assert!(validate_tile(&tile), "{tile:?}");
        assert_eq!(accumulated(&tile, 1), ColumnValue::Ints(vec![10, 20, 30]));
    }

    /// Two outer keys both grown: the inner keys interleave the two sides, `0`'s old and
    /// new keys and then `1`'s, and each aggregation follows its own key.
    #[test]
    fn merging_interleaved_rows_over_aggregations_keeps_each_with_its_key() {
        let two_groups = |inner: usize, acc: Vec<i64>| {
            Tile::data_function(
                ColumnValue::from_uints(vec![0, 1]),
                Box::new(Tile::grouped(
                    ColumnValue::UInts(vec![0, 1]),
                    ColumnValue::from_uints(vec![inner, inner]),
                    Box::new(sums(acc)),
                    Predicate::False,
                    BitSet::new(),
                )),
                Predicate::False,
                BitSet::new(),
            )
        };
        let mut tile = two_groups(100, vec![1, 3]);
        tile.merge(two_groups(200, vec![2, 4]));
        assert!(validate_tile(&tile), "{tile:?}");
        assert_eq!(
            tile.values_at(1)
                .key_paths(&[vec![Value::UInt(0)], vec![Value::UInt(1)]]),
            vec![
                vec![Value::UInt(0), Value::UInt(100)],
                vec![Value::UInt(0), Value::UInt(200)],
                vec![Value::UInt(1), Value::UInt(100)],
                vec![Value::UInt(1), Value::UInt(200)],
            ]
        );
        assert_eq!(accumulated(&tile, 2), ColumnValue::Ints(vec![1, 2, 3, 4]));
    }

    /// An aggregation beside a level the delivery grew is one row both sides delivered, at
    /// every key they share, and folds its two contributions by the aggregate's law.
    #[test]
    fn a_regrown_key_folds_the_aggregation_beside_it() {
        let keyed = |xs: usize, acc: Vec<i64>| {
            Tile::data_function(
                ColumnValue::from_uints(vec![0, 1]),
                Box::new(Tile::Record(HashMap::from([
                    ("agg".to_string(), sums(acc)),
                    (
                        "xs".to_string(),
                        Tile::grouped(
                            ColumnValue::UInts(vec![0, 1]),
                            ColumnValue::from_uints(vec![xs, xs]),
                            Box::new(Tile::Scalar(ColumnValue::Ints(vec![7, 8]))),
                            Predicate::False,
                            BitSet::new(),
                        ),
                    ),
                ]))),
                Predicate::False,
                BitSet::new(),
            )
        };
        let mut tile = keyed(100, vec![1, 10]);
        tile.merge(keyed(200, vec![2, 20]));
        assert!(validate_tile(&tile), "{tile:?}");
        let Tile::DataFunction { codomain, .. } = &tile else {
            panic!("expected a collection: {tile:?}");
        };
        let Tile::Record(fields) = codomain.as_ref() else {
            panic!("expected a record: {codomain:?}");
        };
        let Tile::Aggregation { accumulator, .. } = &fields["agg"] else {
            panic!("expected an aggregation: {fields:?}");
        };
        assert_eq!(
            accumulator.as_ref(),
            &Tile::Scalar(ColumnValue::Ints(vec![3, 30]))
        );
    }
}
