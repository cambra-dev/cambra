//! The projection guards a producer restates: [`Projection`].
//! See `src/interpreter/design-operators.md`, "Projection guards".

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
        }
    }

    /// The projection of `self` within `other`: what both name.
    pub fn intersect(&self, other: &Projection) -> Projection {
        match (self, other) {
            (Projection::Nothing, _) | (_, Projection::Nothing) => Projection::Nothing,
            (Projection::Everything, kept) | (kept, Projection::Everything) => kept.clone(),
            (Projection::Keys(a), Projection::Keys(b)) => Projection::admitting(a.intersect(b)),
        }
    }

    /// What `self` names that `other` does not: the region still unread after a read at `other`.
    pub fn minus(&self, other: &Projection) -> Projection {
        let region = |projection: &Projection| match projection {
            Projection::Everything => Predicate::True,
            Projection::Nothing => Predicate::False,
            Projection::Keys(keys) => keys.clone(),
        };
        Projection::admitting(region(self).minus(&region(other)))
    }

    /// The projection naming what either names: the region a producer shared by several
    /// readers is asked for once each has asked.
    pub fn union(&self, other: &Projection) -> Projection {
        match (self, other) {
            (Projection::Everything, _) | (_, Projection::Everything) => Projection::Everything,
            (Projection::Nothing, kept) | (kept, Projection::Nothing) => kept.clone(),
            (Projection::Keys(a), Projection::Keys(b)) => Projection::admitting(a.union(b)),
        }
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
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
    fn projections_unite_to_the_region_a_shared_producer_is_asked_for() {
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
            *pulled.borrow(),
            [keys_between(1, 2), tiling.universal_guard()]
        );
        assert_eq!(*released.borrow(), [keys_between(1, 2)]);
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
