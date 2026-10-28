//! The projection guards a producer restates: [`Projection`].
//! See `src/interpreter/design-operators.md`, "Projection guards".

use std::{collections::BTreeMap, sync::Arc};

use smol_str::SmolStr;

use crate::interpreter::{FunctionGuard, Predicate, Tile, TileGuard, Tiling};

/// The part of a producer's tile that a `get` asks for.
///
/// A projection guard is any [`TileGuard`], and a producer restates exactly the three shapes a
/// pipeline cuts a tile with: everything, nothing, and the keys of the outermost collection
/// that a predicate admits. Anything else is a gap the producer reports rather than answers
/// with a smaller region (`src/interpreter/design-operators.md`, "Guard operations are
/// exact").
#[derive(Clone, Debug, PartialEq)]
pub enum Projection {
    /// The producer's whole tile.
    Everything,
    /// No part of it.
    Nothing,
    /// The outermost collection's keys that the predicate admits, each with the value under
    /// it. The predicate is neither `True` nor `False`, and names no enclosing path.
    Keys(Predicate),
    /// A record's regions by field, each a region of that field's tile, for a notification from
    /// a producer whose tile is a record. A field the map omits is [`Nothing`](Self::Nothing).
    /// Built by [`Projection::fields`], which names no `Nothing` field and no empty map, and is
    /// everything where every field's region is.
    ///
    /// A region of fields names where a notification's change is and nothing a read can ask
    /// for, so it is a notification region only: every use of a projection as a pull
    /// (`guard`, `restrict_to`, `within`) fails on it with the region in the message.
    Fields(FieldRegions),
}

/// The regions of the fields of one record, which knows every field's name, so that a region of
/// everything in each is [`Projection::Everything`] without a caller's help.
///
/// Two regions of fields of one record share its names. The algebra asserts that in debug builds.
#[derive(Clone, Debug, PartialEq)]
pub struct FieldRegions {
    names: Arc<[SmolStr]>,
    regions: BTreeMap<SmolStr, Projection>,
}

impl FieldRegions {
    /// The region of the field `name`, if it names one.
    pub fn get(&self, name: &str) -> Option<&Projection> {
        self.regions.get(name)
    }

    fn same_record(&self, other: &FieldRegions) -> bool {
        self.names == other.names
    }
}

impl Projection {
    /// The projection `guard` names, or why the guard is not one a producer restates.
    pub fn of(guard: &TileGuard) -> Result<Self, String> {
        if guard.is_universal() {
            return Ok(Projection::Everything);
        }
        if guard.is_empty() {
            return Ok(Projection::Nothing);
        }
        match guard {
            TileGuard::Function(FunctionGuard::Domain(keys)) if keys.qualifies() => Err(format!(
                "a projection guard names keys under enclosing paths, which only a release does: \
                 {guard:?}"
            )),
            TileGuard::Function(FunctionGuard::Domain(keys)) => Ok(Projection::Keys(keys.clone())),
            other => Err(format!(
                "a projection guard is everything, nothing or the keys of the outermost \
                 collection, got {other:?}"
            )),
        }
    }

    /// The guard this projection names for a producer with `tiling`.
    pub fn guard(&self, tiling: &Tiling) -> TileGuard {
        match self {
            Projection::Everything => tiling.universal_guard(),
            Projection::Nothing => tiling.empty_guard(),
            Projection::Keys(keys) => TileGuard::Function(FunctionGuard::Domain(keys.clone())),
            Projection::Fields(_) => panic!(
                "a region of fields is a notification's and names no guard to read: {self:?}"
            ),
        }
    }

    /// The projection of `self` within `other`: what both name.
    ///
    /// # Panics
    ///
    /// For a region of fields, whose intersection is not spelled.
    pub fn intersect(&self, other: &Projection) -> Projection {
        match (self, other) {
            (Projection::Nothing, _) | (_, Projection::Nothing) => Projection::Nothing,
            (Projection::Everything, kept) | (kept, Projection::Everything) => kept.clone(),
            (Projection::Keys(a), Projection::Keys(b)) => Projection::admitting(a.intersect(b)),
            (a, b) => panic!("the intersection of regions of fields is not spelled: {a:?}, {b:?}"),
        }
    }

    /// What `self` names that `other` does not: the region still unread after a read at `other`.
    ///
    /// # Panics
    ///
    /// For a region of fields against anything but `Nothing` and `Everything`: the remainder of
    /// a region of fields is not spelled.
    pub fn minus(&self, other: &Projection) -> Projection {
        let region = |projection: &Projection| match projection {
            Projection::Everything => Predicate::True,
            Projection::Nothing => Predicate::False,
            Projection::Keys(keys) => keys.clone(),
            Projection::Fields(_) => panic!(
                "the remainder of a region of fields is not spelled: {self:?} minus {other:?}"
            ),
        };
        match (self, other) {
            (Projection::Nothing, _) => Projection::Nothing,
            (_, Projection::Nothing) => self.clone(),
            (Projection::Fields(_), Projection::Everything) => Projection::Nothing,
            _ => Projection::admitting(region(self).minus(&region(other))),
        }
    }

    /// The projection naming what either names: the region a memo has read or must read again, or
    /// a notification that coalesces others.
    ///
    /// A region of fields and a region of keys name different things, and the union that is
    /// larger than both is [`Everything`](Self::Everything), which a notification may widen to.
    pub fn union(&self, other: &Projection) -> Projection {
        match (self, other) {
            (Projection::Everything, _) | (_, Projection::Everything) => Projection::Everything,
            (Projection::Nothing, kept) | (kept, Projection::Nothing) => kept.clone(),
            (Projection::Keys(a), Projection::Keys(b)) => Projection::admitting(a.union(b)),
            (Projection::Fields(a), Projection::Fields(b)) => {
                debug_assert!(
                    a.same_record(b),
                    "regions of different records: {a:?}, {b:?}"
                );
                let mut merged = a.regions.clone();
                for (name, region) in &b.regions {
                    let united = match merged.get(name) {
                        Some(held) => held.union(region),
                        None => region.clone(),
                    };
                    merged.insert(name.clone(), united);
                }
                Projection::fields(a.names.clone(), merged)
            }
            (Projection::Fields(_), Projection::Keys(_))
            | (Projection::Keys(_), Projection::Fields(_)) => Projection::Everything,
        }
    }

    /// Whether everything `self` names is inside `other`. Regions of a different kind (keys and
    /// fields) are not contained in one another, short of `Everything`.
    pub fn contained_in(&self, other: &Projection) -> bool {
        match (self, other) {
            (Projection::Nothing, _) | (_, Projection::Everything) => true,
            (Projection::Everything, _) | (_, Projection::Nothing) => false,
            (Projection::Keys(a), Projection::Keys(b)) => a.minus(b).is_false(),
            (Projection::Fields(a), Projection::Fields(b)) => {
                debug_assert!(
                    a.same_record(b),
                    "regions of different records: {a:?}, {b:?}"
                );
                a.regions
                    .iter()
                    .all(|(name, region)| b.get(name).is_some_and(|held| region.contained_in(held)))
            }
            (Projection::Keys(_), Projection::Fields(_))
            | (Projection::Fields(_), Projection::Keys(_)) => false,
        }
    }

    /// What `self` and `other` name together, for a gate recording what it passed: the union,
    /// except that regions of different kinds keep `other` alone, which is less than their
    /// union and so only ever passes a later notification that was suppressible.
    pub fn passed_with(&self, other: &Projection) -> Projection {
        match (self, other) {
            (Projection::Keys(_), Projection::Fields(_))
            | (Projection::Fields(_), Projection::Keys(_)) => other.clone(),
            _ => self.union(other),
        }
    }

    /// This region for an operator that keeps its input's keys: a region of fields, which names
    /// a change inside a record, becomes [`Everything`](Self::Everything).
    pub fn keys_only(&self) -> Projection {
        match self {
            Projection::Fields(_) => Projection::Everything,
            other => other.clone(),
        }
    }

    /// The regions of the fields `entries` name of the record whose fields are `names`, sorted: a
    /// `Nothing` region is dropped, no entry at all is `Nothing`, and every field's region being
    /// [`Everything`](Self::Everything) is `Everything`.
    pub fn fields(
        names: Arc<[SmolStr]>,
        entries: impl IntoIterator<Item = (SmolStr, Projection)>,
    ) -> Projection {
        // Names compare in order, so a record's are sorted by whoever builds them, once.
        debug_assert!(names.is_sorted(), "a record's names are sorted: {names:?}");
        let regions: BTreeMap<SmolStr, Projection> = entries
            .into_iter()
            .filter(|(_, region)| *region != Projection::Nothing)
            .collect();
        debug_assert!(
            regions.is_empty() || !names.is_empty(),
            "a region of fields of a record with no fields: {regions:?}"
        );
        debug_assert!(
            regions.keys().all(|name| names.contains(name)),
            "a region names a field the record lacks: {regions:?} of {names:?}"
        );
        let everything = !names.is_empty()
            && names
                .iter()
                .all(|name| regions.get(name) == Some(&Projection::Everything));
        match (regions.is_empty(), everything) {
            (true, _) => Projection::Nothing,
            (_, true) => Projection::Everything,
            _ => Projection::Fields(FieldRegions { names, regions }),
        }
    }

    /// The region of the field `name` of a record whose fields are `all`, for tests.
    #[cfg(test)]
    pub(crate) fn field_of(all: &[&str], name: &str, region: Projection) -> Projection {
        Projection::fields(
            {
                let mut names: Vec<SmolStr> = all.iter().copied().map(SmolStr::new).collect();
                names.sort();
                names.into()
            },
            [(SmolStr::new(name), region)],
        )
    }

    /// The projection naming the keys `keys` admits, normalized to
    /// [`Everything`](Self::Everything) or [`Nothing`](Self::Nothing) where it admits all or
    /// none.
    pub fn admitting(keys: Predicate) -> Projection {
        match () {
            () if keys.is_true() => Projection::Everything,
            () if keys.is_false() => Projection::Nothing,
            () => Projection::Keys(keys),
        }
    }
}

/// `stated`, a statement about the keys `depth` levels in, cut to the paths whose outermost key
/// `keys` admits.
///
/// At the outermost level that is the intersection. Beneath it a statement names its groups by
/// the paths that reach them, so it is qualified by the keys: one made of every group, the
/// unqualified kind, is about the groups of the keys kept and no others.
fn within_keys(stated: &Predicate, keys: &Predicate, depth: usize) -> Predicate {
    match stated {
        Predicate::False => Predicate::False,
        Predicate::Or(arms) => arms
            .iter()
            .map(|arm| within_keys(arm, keys, depth))
            .fold(Predicate::False, |all, arm| all.union(&arm)),
        Predicate::Qualified { enclosing, here } => {
            assert!(
                depth > 0,
                "the outermost level names no enclosing path: {stated:?}"
            );
            Predicate::qualified(within_keys(enclosing, keys, depth - 1), (**here).clone())
        }
        unqualified if depth == 0 => unqualified.intersect(keys),
        unqualified => Predicate::qualified(
            within_keys(&Predicate::True, keys, depth - 1),
            unqualified.clone(),
        ),
    }
}

impl TileGuard {
    /// The projection this guard names, or a panic naming `producer` and the guard: a consumer
    /// that sends a shape no producer restates has a bug, and answering a smaller region would
    /// hide it.
    pub fn projection(&self, producer: &str) -> Projection {
        Projection::of(self).unwrap_or_else(|why| panic!("{producer}: {why}"))
    }
}

impl Tile {
    /// Keep the outermost collection's keys that `keys` admits, each with the value under it,
    /// and state complete only the region the predicate names.
    ///
    /// The tile is the producer's answer to the universal projection, so every key it holds is
    /// one the producer has answered. A key outside `keys` is dropped with its value, and the
    /// completeness the tile states is cut to the admitted region at every level: a producer
    /// asked for part of its keys says nothing about the rest, and a statement about the
    /// groups beneath the keys is about the groups of the keys kept.
    ///
    /// # Panics
    ///
    /// For a tile with no outermost collection, which has no keys to cut at.
    pub fn restrict_to_keys(&mut self, keys: &Predicate) {
        let Tile::DataFunction { domain, .. } = &*self else {
            panic!("only a collection has keys to restrict, got {self:?}")
        };
        let mask: Vec<bool> = (0..domain.len())
            .map(|key| keys.contains(&domain.index_at(key)))
            .collect();
        if !mask.iter().all(|kept| *kept) {
            self.retain_keys(&mask);
        }
        self.map_level_predicates(&mut |depth, stated| within_keys(stated, keys, depth));
    }

    /// Whether this tile holds only what `projection` names, or why it does not.
    ///
    /// A producer answers a pull with a tile inside the projection, so a cell outside it is a
    /// producer that ignored the guard. Rows deleted but not yet compacted are released, so
    /// they are not part of the answer. The check reads keys and cells and does not read the
    /// completeness the tile states.
    pub fn within(&self, projection: &Projection) -> Result<(), String> {
        match projection {
            Projection::Everything => Ok(()),
            Projection::Nothing => {
                let mut live = self.clone();
                live.compact();
                match live.cell_count() {
                    0 => Ok(()),
                    _ => Err("it holds cells, and the projection names none".into()),
                }
            }
            Projection::Fields(_) => Err(format!(
                "a region of fields is a notification's, and no tile is within it: {projection:?}"
            )),
            Projection::Keys(keys) => {
                let Tile::DataFunction {
                    domain, deleted, ..
                } = self
                else {
                    return Err("it is not a collection, so it has no keys to project".into());
                };
                match (0..domain.len())
                    .filter(|row| !deleted.contains(*row))
                    .map(|row| domain.index_at(row))
                    .find(|key| !keys.contains(key))
                {
                    None => Ok(()),
                    Some(key) => Err(format!("it holds the key {key:?}, which {keys:?} omits")),
                }
            }
        }
    }

    /// Cut this tile to `projection`.
    ///
    /// `Nothing` empties it at `tiling`, the tiling of the producer that made it.
    pub fn restrict_to(&mut self, projection: &Projection, tiling: &Tiling) {
        match projection {
            Projection::Everything => {}
            Projection::Nothing => *self = tiling.empty_tile(),
            Projection::Keys(keys) => self.restrict_to_keys(keys),
            Projection::Fields(_) => {
                panic!("a region of fields is a notification's and cuts no tile: {projection:?}")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::LockNow;
    use crate::interpreter::tile_operators::TileProducer;
    use crate::interpreter::tile_operators::test_helpers::{
        ProjectionSpy, int_entries, ints_by_position, keys_between,
    };
    use crate::interpreter::{BaseType, ColumnValue, Extent, Value};
    use bit_set::BitSet;
    use intervalsets::{Interval, IntervalSet};

    fn positions(first: u64, last: u64) -> Predicate {
        Predicate::intervals(IntervalSet::from(Interval::closed(
            Value::UInt(first),
            Value::UInt(last),
        )))
    }

    fn ints_tiling(rows: u64) -> Tiling {
        Tiling::data_function(
            Extent::uint_range(rows),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        )
    }

    #[test]
    fn a_guard_names_everything_nothing_or_the_outermost_keys() {
        let tiling = ints_tiling(4);
        assert_eq!(
            Projection::of(&tiling.universal_guard()),
            Ok(Projection::Everything)
        );
        assert_eq!(
            Projection::of(&tiling.empty_guard()),
            Ok(Projection::Nothing)
        );
        assert_eq!(
            Projection::of(&keys_between(1, 2)),
            Ok(Projection::Keys(positions(1, 2)))
        );
        // `Domain(True)` is the universal guard however it is spelled.
        assert_eq!(
            Projection::of(&TileGuard::Function(FunctionGuard::Domain(Predicate::True))),
            Ok(Projection::Everything)
        );
    }

    #[test]
    fn a_guard_that_names_a_path_or_a_codomain_is_not_a_projection() {
        let one = Predicate::point(Value::UInt(0));
        let qualified = Predicate::qualified(one.clone(), one.clone());
        let named_path = TileGuard::Function(FunctionGuard::Domain(qualified));
        let error = Projection::of(&named_path).expect_err("a path is a release's");
        assert!(error.contains("enclosing paths"), "{error}");
        let within_values = TileGuard::Function(FunctionGuard::Codomain(Box::new(
            TileGuard::Function(FunctionGuard::Domain(one)),
        )));
        assert!(Projection::of(&within_values).is_err());
    }

    #[test]
    #[should_panic(expected = "Producer: a projection guard is everything, nothing")]
    fn a_producer_reports_a_guard_it_cannot_restate() {
        let beneath = TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Function(
            FunctionGuard::Domain(positions(0, 0)),
        ))));
        beneath.projection("Producer");
    }

    #[test]
    fn projections_intersect_and_normalize() {
        let (low, high) = (
            Projection::Keys(positions(0, 5)),
            Projection::Keys(positions(3, 9)),
        );
        assert_eq!(
            low.intersect(&high),
            Projection::Keys(positions(3, 5)),
            "both name keys 3 to 5"
        );
        assert_eq!(
            low.intersect(&Projection::Keys(positions(7, 9))),
            Projection::Nothing,
            "disjoint regions name nothing"
        );
        assert_eq!(low.intersect(&Projection::Everything), low);
        assert_eq!(Projection::Nothing.intersect(&high), Projection::Nothing);
        assert_eq!(
            Projection::admitting(Predicate::True),
            Projection::Everything
        );
        assert_eq!(
            low.minus(&Projection::Keys(positions(3, 9))),
            Projection::Keys(positions(0, 2).union(&Predicate::False)),
            "keys 0 to 5 less 3 to 9 leave 0 to 2"
        );
        assert_eq!(low.minus(&Projection::Everything), Projection::Nothing);
        assert_eq!(low.minus(&Projection::Nothing), low);
    }

    #[test]
    fn a_union_names_the_region_a_memo_has_read_or_must_read_again() {
        let (low, high) = (
            Projection::Keys(positions(0, 2)),
            Projection::Keys(positions(5, 7)),
        );
        assert_eq!(
            low.union(&high),
            Projection::Keys(positions(0, 2).union(&positions(5, 7)))
        );
        assert_eq!(low.union(&Projection::Nothing), low);
        assert_eq!(
            Projection::Nothing.union(&Projection::Nothing),
            Projection::Nothing
        );
        assert_eq!(low.union(&Projection::Everything), Projection::Everything);
    }

    #[test]
    fn restricting_keeps_the_admitted_keys_and_cuts_the_completeness() {
        let mut complete = ints_by_position(&[10, 20, 30, 40], true);
        complete.restrict_to_keys(&positions(1, 2));
        assert_eq!(int_entries(&complete), [(1, 20), (2, 30)]);
        let Tile::DataFunction {
            domain_predicate, ..
        } = &complete
        else {
            panic!("a collection")
        };
        assert_eq!(
            *domain_predicate,
            positions(1, 2),
            "only the admitted region is stated complete"
        );

        // A tile that has delivered positions 0 to 3 and nothing more says nothing of 4 and
        // above, in or out of the projection.
        let mut partial = ints_by_position(&[10, 20, 30, 40], false);
        partial.restrict_to_keys(&positions(2, 9));
        assert_eq!(int_entries(&partial), [(2, 30), (3, 40)]);
        let Tile::DataFunction {
            domain_predicate, ..
        } = &partial
        else {
            panic!("a collection")
        };
        assert_eq!(*domain_predicate, positions(2, 3));
    }

    /// A group stays whole under its key: the projection cuts the outermost keys, and what a
    /// key holds is the key's. What the tile states of the groups is cut with the keys, so the
    /// groups of the keys dropped are not stated complete.
    #[test]
    fn restricting_a_nested_collection_keeps_each_kept_group_whole() {
        // Keys 1, 2 and 3 hold {0 ↦ 10, 2 ↦ 11}, {1 ↦ 20} and nothing.
        let nested = |keys: Vec<i64>,
                      starts: Vec<usize>,
                      members: Vec<u64>,
                      values: Vec<i64>,
                      groups_stated: Predicate,
                      outer: Predicate| {
            Tile::data_function(
                ColumnValue::Ints(keys),
                Box::new(Tile::grouped(
                    starts,
                    ColumnValue::UInts(members),
                    Box::new(Tile::Scalar(ColumnValue::Ints(values))),
                    groups_stated,
                    BitSet::new(),
                )),
                outer,
                BitSet::new(),
            )
        };
        let mut tile = nested(
            vec![1, 2, 3],
            vec![0, 2, 3],
            vec![0, 2, 1],
            vec![10, 11, 20],
            Predicate::True,
            Predicate::True,
        );
        let kept = Predicate::point(Value::Int(1)).union(&Predicate::point(Value::Int(3)));
        tile.restrict_to_keys(&kept);
        assert_eq!(
            tile,
            nested(
                vec![1, 3],
                vec![0, 2],
                vec![0, 2],
                vec![10, 11],
                Predicate::qualified(kept.clone(), Predicate::True),
                kept,
            ),
            "keys 1 and 3 with their groups, key 2 and its group gone, and the groups stated \
             complete only under the keys kept"
        );
    }

    #[test]
    fn nothing_empties_the_tile_at_its_producer_s_tiling() {
        let tiling = ints_tiling(4);
        let mut tile = ints_by_position(&[10, 20], true);
        tile.restrict_to(&Projection::Nothing, &tiling);
        assert_eq!(tile, tiling.empty_tile());
    }

    /// The double a test pulls an operator over answers the projection it is asked for, and
    /// logs the guards it received.
    #[test]
    fn the_projection_spy_answers_the_region_it_is_pulled_at_and_logs_it() {
        let tiling = ints_tiling(4);
        let (mut spy, pulled, released) =
            ProjectionSpy::new(ints_by_position(&[10, 20, 30, 40], true), tiling.clone());
        let middle = spy.get(keys_between(1, 2));
        assert_eq!(int_entries(&middle), [(1, 20), (2, 30)]);
        spy.release(keys_between(1, 2));
        let rest = spy.get(tiling.universal_guard());
        assert_eq!(int_entries(&rest), [(0, 10), (3, 40)]);
        assert_eq!(
            *pulled.lock_now(),
            [keys_between(1, 2), tiling.universal_guard()]
        );
        assert_eq!(*released.lock_now(), [keys_between(1, 2)]);
        // A pull that names nothing states nothing complete, which is withdrawal unless
        // the consumer released what it took.
        spy.release(tiling.universal_guard());
        assert_eq!(spy.get(tiling.empty_guard()), tiling.empty_tile());
    }

    #[test]
    fn a_tile_is_within_the_keys_it_holds_and_not_beyond() {
        let tile = ints_by_position(&[10, 20, 30, 40], true);
        let admitting = |first, last| Projection::admitting(positions(first, last));
        assert_eq!(tile.within(&admitting(0, 3)), Ok(()));
        assert_eq!(tile.within(&Projection::Everything), Ok(()));
        assert!(tile.within(&admitting(1, 2)).unwrap_err().contains("omits"));
        assert!(tile.within(&Projection::Nothing).is_err());
        assert_eq!(
            ints_tiling(4).empty_tile().within(&Projection::Nothing),
            Ok(())
        );
        let mut released = ints_by_position(&[10, 20], true);
        released.remove_guarded(keys_between(0, 1));
        assert_eq!(released.within(&Projection::Nothing), Ok(()));
        assert_eq!(released.within(&admitting(5, 6)), Ok(()));
        let scalar = Tile::Scalar(ColumnValue::Ints(vec![1]));
        assert!(scalar.within(&admitting(0, 3)).is_err());
    }

    /// A producer that ignores the guard is caught by the `get` wrapper in a debug build, where
    /// a pull for a morsel returns the whole tile.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "answered a pull at")]
    fn get_rejects_an_answer_beyond_the_projection() {
        use crate::interpreter::tile_operators::test_helpers::TestTileProducer;
        let mut ignoring =
            TestTileProducer::new(ints_by_position(&[10, 20, 30, 40], true), ints_tiling(4));
        ignoring.get(keys_between(1, 2));
    }
}

#[cfg(test)]
mod fields_tests {
    use super::*;
    use crate::interpreter::Value;

    fn name(field: &str) -> SmolStr {
        SmolStr::new(field)
    }

    fn keys(first: u64, last: u64) -> Projection {
        Projection::admitting(Predicate::intervals(intervalsets::IntervalSet::from(
            intervalsets::Interval::closed(Value::UInt(first), Value::UInt(last)),
        )))
    }

    /// The regions `entries` of a record whose fields are `a` to `d`.
    fn fields(entries: &[(&str, Projection)]) -> Projection {
        fields_of(&["a", "b", "c", "d"], entries)
    }

    fn fields_of(all: &[&str], entries: &[(&str, Projection)]) -> Projection {
        let mut names: Vec<SmolStr> = all.iter().map(|field| name(field)).collect();
        names.sort();
        Projection::fields(
            names.into(),
            entries
                .iter()
                .map(|(field, region)| (name(field), region.clone())),
        )
    }

    #[test]
    fn fields_drops_a_nothing_field_and_an_empty_map_is_nothing() {
        assert_eq!(
            fields(&[("a", keys(1, 2)), ("b", Projection::Nothing)]),
            fields(&[("a", keys(1, 2))])
        );
        assert_eq!(
            fields(&[("a", Projection::Nothing), ("b", Projection::Nothing)]),
            Projection::Nothing
        );
        assert_eq!(fields(&[]), Projection::Nothing);
    }

    #[test]
    fn a_region_of_every_field_everything_is_everything() {
        let both = |entries: &[(&str, Projection)]| fields_of(&["a", "b"], entries);
        assert_eq!(
            both(&[("a", Projection::Everything), ("b", Projection::Everything)]),
            Projection::Everything
        );
        let one = both(&[("a", Projection::Everything)]);
        assert!(matches!(one, Projection::Fields(_)));
        let narrow = both(&[("a", Projection::Everything), ("b", keys(1, 2))]);
        assert!(matches!(narrow, Projection::Fields(_)));
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "names are sorted")]
    fn unsorted_names_are_a_bug_in_debug_builds() {
        Projection::fields(vec![name("b"), name("a")].into(), [(name("a"), keys(1, 2))]);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "names a field the record lacks")]
    fn a_region_of_a_field_the_record_lacks_is_a_bug_in_debug_builds() {
        Projection::fields(vec![name("a")].into(), [(name("z"), keys(1, 2))]);
    }

    #[test]
    fn the_union_of_two_fields_that_are_everything_is_everything() {
        let both = ["a", "b"];
        let a = fields_of(&both, &[("a", Projection::Everything)]);
        let b = fields_of(&both, &[("b", Projection::Everything)]);
        assert_eq!(a.union(&b), Projection::Everything);
    }

    #[test]
    fn the_union_of_fields_unites_each_field_and_keeps_an_absent_one() {
        let a = fields(&[("a", keys(1, 2)), ("b", keys(5, 6))]);
        let b = fields(&[("a", keys(2, 4)), ("c", Projection::Everything)]);
        assert_eq!(
            a.union(&b),
            fields(&[
                ("a", keys(1, 4)),
                ("b", keys(5, 6)),
                ("c", Projection::Everything)
            ])
        );
        assert_eq!(a.union(&Projection::Nothing), a);
        assert_eq!(a.union(&Projection::Everything), Projection::Everything);
    }

    #[test]
    fn the_union_of_fields_and_keys_is_everything() {
        let record = fields(&[("a", keys(1, 2))]);
        assert_eq!(record.union(&keys(1, 2)), Projection::Everything);
        assert_eq!(keys(1, 2).union(&record), Projection::Everything);
    }

    #[test]
    fn nested_fields_unite_beneath_their_field() {
        let inner = |a: Projection| fields_of(&["x"], &[("x", a)]);
        let left = fields(&[("a", inner(keys(1, 2)))]);
        let right = fields(&[("a", inner(keys(3, 4)))]);
        assert_eq!(left.union(&right), fields(&[("a", inner(keys(1, 4)))]));
    }

    #[test]
    fn subtraction_is_total_where_fields_meet_nothing_or_everything() {
        let a = fields(&[("a", keys(1, 2))]);
        assert_eq!(a.minus(&Projection::Nothing), a);
        assert_eq!(Projection::Nothing.minus(&a), Projection::Nothing);
        assert_eq!(a.minus(&Projection::Everything), Projection::Nothing);
    }

    #[test]
    #[should_panic(expected = "intersection of regions of fields is not spelled")]
    fn the_intersection_of_regions_of_fields_is_not_spelled() {
        fields(&[("a", keys(1, 2))]).intersect(&fields(&[("a", keys(1, 2))]));
    }

    #[test]
    #[should_panic(expected = "remainder of a region of fields is not spelled")]
    fn the_remainder_of_a_region_of_fields_is_not_spelled() {
        keys(1, 2).minus(&fields(&[("a", keys(1, 2))]));
    }

    #[test]
    #[should_panic(expected = "notification's and names no guard")]
    fn a_region_of_fields_names_no_guard() {
        let tiling = Tiling::Scalar(crate::interpreter::Extent::Base(
            crate::interpreter::BaseType::Int,
        ));
        fields(&[("a", keys(1, 2))]).guard(&tiling);
    }

    #[test]
    #[should_panic(expected = "cuts no tile")]
    fn a_region_of_fields_cuts_no_tile() {
        let tiling = Tiling::Scalar(crate::interpreter::Extent::Base(
            crate::interpreter::BaseType::Int,
        ));
        let mut tile = tiling.empty_tile();
        tile.restrict_to(&fields(&[("a", keys(1, 2))]), &tiling);
    }

    #[test]
    fn no_tile_is_within_a_region_of_fields() {
        let tiling = Tiling::Scalar(crate::interpreter::Extent::Base(
            crate::interpreter::BaseType::Int,
        ));
        let region = fields(&[("a", keys(1, 2))]);
        let error = tiling.empty_tile().within(&region).expect_err("not within");
        assert!(error.contains("notification's"), "{error}");
    }
}

#[cfg(test)]
mod containment_tests {
    use super::*;
    use crate::interpreter::Value;

    fn keys(first: u64, last: u64) -> Projection {
        Projection::admitting(Predicate::intervals(intervalsets::IntervalSet::from(
            intervalsets::Interval::closed(Value::UInt(first), Value::UInt(last)),
        )))
    }

    fn field(name: &str, region: Projection) -> Projection {
        Projection::field_of(&["a", "b", "c"], name, region)
    }

    #[test]
    fn everything_contains_all_and_nothing_is_in_all() {
        assert!(keys(1, 2).contained_in(&Projection::Everything));
        assert!(Projection::Nothing.contained_in(&keys(1, 2)));
        assert!(!Projection::Everything.contained_in(&keys(1, 2)));
        assert!(!keys(1, 2).contained_in(&Projection::Nothing));
    }

    #[test]
    fn keys_are_contained_when_their_difference_is_empty() {
        assert!(keys(2, 3).contained_in(&keys(1, 4)));
        assert!(!keys(3, 6).contained_in(&keys(1, 4)));
    }

    #[test]
    fn fields_are_contained_field_by_field_and_a_missing_field_holds_nothing() {
        let held = field("a", keys(1, 4)).union(&field("b", Projection::Everything));
        assert!(field("a", keys(2, 3)).contained_in(&held));
        assert!(field("b", keys(0, 9)).contained_in(&held));
        assert!(!field("c", keys(2, 3)).contained_in(&held));
        assert!(!field("a", keys(2, 9)).contained_in(&held));
    }

    #[test]
    fn keys_and_fields_are_in_each_other_only_through_everything() {
        assert!(!keys(1, 2).contained_in(&field("a", keys(1, 2))));
        assert!(!field("a", keys(1, 2)).contained_in(&keys(1, 2)));
    }

    #[test]
    fn what_a_gate_passed_is_the_union_or_the_latest_of_different_kinds() {
        assert_eq!(
            keys(1, 2).passed_with(&keys(5, 6)),
            keys(1, 2).union(&keys(5, 6))
        );
        assert_eq!(
            keys(1, 2).passed_with(&field("a", keys(1, 2))),
            field("a", keys(1, 2))
        );
        assert_eq!(field("a", keys(1, 2)).passed_with(&keys(5, 6)), keys(5, 6));
        assert_eq!(
            field("a", keys(1, 2)).passed_with(&field("b", keys(1, 2))),
            field("a", keys(1, 2)).union(&field("b", keys(1, 2)))
        );
    }
}
