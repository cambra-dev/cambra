//! The projection guards a producer restates: [`Projection`].
//! See `src/interpreter/design-operators.md`, "Projection guards".

use crate::interpreter::{CurryLevel, FunctionGuard, Predicate, Tile, TileGuard, Tiling, Value};

/// The part of a producer's tile that a `get` asks for.
///
/// A projection guard is any [`TileGuard`], and a projection is the three shapes a pipeline
/// cuts a tile with: everything, nothing, and the keys of one collection level that a predicate
/// admits. Anything else is a gap the producer reports rather than answers with a smaller region
/// (`src/interpreter/design-operators.md`, "Guard operations are exact").
#[derive(Clone, Debug, PartialEq)]
pub enum Projection {
    /// The producer's whole tile.
    Everything,
    /// No part of it.
    Nothing,
    /// The keys of `level` that `keys` admits, each with the value under it, and the keys above
    /// them that an admitted path runs through.
    ///
    /// At the outermost level `keys` names no enclosing path. Beneath it, `keys` admits whole
    /// paths ([`Predicate::contains_path`]), and an unqualified arm admits its keys under every
    /// path. `keys` is neither `True` nor `False`, and is not every key beneath some keys of the
    /// level above, which that level spells ([`Projection::keys_at`]).
    Keys { level: CurryLevel, keys: Predicate },
}

impl Projection {
    /// The projection `guard` names, or why the guard is not one.
    ///
    /// A domain guard names the keys of the outermost collection, and one inside `𝑛` codomain
    /// guards the keys of level `𝑛` ([`CurryLevel::wrap_guard`]). An `Or` of such arms names
    /// their union at the deepest of their levels.
    pub fn of(guard: &TileGuard) -> Result<Self, String> {
        if guard.is_universal() {
            return Ok(Projection::Everything);
        }
        if guard.is_empty() {
            return Ok(Projection::Nothing);
        }
        let arms = match guard {
            TileGuard::Or(arms) => arms.as_slice(),
            single => std::slice::from_ref(single),
        };
        arms.iter().try_fold(Projection::Nothing, |all, arm| {
            Ok(all.union(&Projection::of_arm(arm, guard)?))
        })
    }

    /// The projection one arm of `guard` names: a domain guard, at the level the codomain guards
    /// around it step to.
    fn of_arm(arm: &TileGuard, guard: &TileGuard) -> Result<Self, String> {
        let mut level = 0;
        let mut node = arm;
        while let TileGuard::Function(FunctionGuard::Codomain(inner)) = node {
            level += 1;
            node = inner;
        }
        match node {
            TileGuard::Function(FunctionGuard::Domain(keys)) if qualifying_levels(keys) > level => {
                Err(format!(
                    "a projection guard names keys under enclosing paths only as many levels \
                     deep as it steps into, got {guard:?}"
                ))
            }
            TileGuard::Function(FunctionGuard::Domain(keys)) => {
                Ok(Projection::keys_at(CurryLevel::new(level), keys.clone()))
            }
            _ => Err(format!(
                "a projection guard is everything, nothing or the keys of a collection level, \
                 got {guard:?}"
            )),
        }
    }

    /// The guard this projection names for a producer with `tiling`.
    ///
    /// Each arm of the keys is spelled at the shallowest level it is every key beneath, one
    /// domain guard inside a codomain guard per level above it, as `domain_prefix` spells a
    /// release.
    pub fn guard(&self, tiling: &Tiling) -> TileGuard {
        match self {
            Projection::Everything => tiling.universal_guard(),
            Projection::Nothing => tiling.empty_guard(),
            Projection::Keys { level, keys } => spell(*level, keys),
        }
    }

    /// The level whose keys this projection names, `None` for everything and nothing.
    pub fn level(&self) -> Option<CurryLevel> {
        match self {
            Projection::Keys { level, .. } => Some(*level),
            _ => None,
        }
    }

    /// The projection of `self` within `other`: what both name.
    pub fn intersect(&self, other: &Projection) -> Projection {
        let level = self.deepest(other);
        Projection::keys_at(level, self.at(level).intersect(&other.at(level)))
    }

    /// What `self` names that `other` does not: the region still unread after a read at `other`.
    pub fn minus(&self, other: &Projection) -> Projection {
        let level = self.deepest(other);
        Projection::keys_at(level, self.at(level).minus(&other.at(level)))
    }

    /// The projection naming what either names.
    pub fn union(&self, other: &Projection) -> Projection {
        let level = self.deepest(other);
        Projection::keys_at(level, self.at(level).union(&other.at(level)))
    }

    /// The deeper of the levels `self` and `other` name keys of, the outermost where neither
    /// names keys.
    fn deepest(&self, other: &Projection) -> CurryLevel {
        [self.level(), other.level()]
            .into_iter()
            .flatten()
            .max()
            .unwrap_or(CurryLevel::OUTERMOST)
    }

    /// This projection as the paths of `level` it names, `level` being at or beneath its own:
    /// a key of a level above names every path beneath it.
    fn at(&self, level: CurryLevel) -> Predicate {
        match self {
            Projection::Everything => Predicate::True,
            Projection::Nothing => Predicate::False,
            Projection::Keys { level: own, keys } => {
                let beneath = level
                    .index()
                    .checked_sub(own.index())
                    .unwrap_or_else(|| panic!("{self:?} is read at {level}, above its own level"));
                keys.descend(beneath)
            }
        }
    }

    /// The projection naming the outermost keys `keys` admits ([`keys_at`](Self::keys_at) at the
    /// outermost level).
    pub fn admitting(keys: Predicate) -> Projection {
        Projection::keys_at(CurryLevel::OUTERMOST, keys)
    }

    /// The projection naming the keys of `level` that `keys` admits, normalized: to
    /// [`Everything`](Self::Everything) or [`Nothing`](Self::Nothing) where it admits all or
    /// none, and to the level above where it is every key beneath keys of that level.
    ///
    /// # Panics
    ///
    /// For keys that name a path through more levels than lie above `level`.
    pub fn keys_at(level: CurryLevel, keys: Predicate) -> Projection {
        assert!(
            qualifying_levels(&keys) <= level.index(),
            "keys at {level} name a path through at most {} levels above: {keys:?}",
            level.index()
        );
        let (mut level, mut keys) = (level, keys);
        loop {
            if keys.is_true() {
                return Projection::Everything;
            }
            if keys.is_false() {
                return Projection::Nothing;
            }
            match (level.enclosing(), every_key_beneath(&keys)) {
                (Some(above), Some(whole)) => (level, keys) = (above, whole),
                _ => break,
            }
        }
        Projection::Keys { level, keys }
    }
}

/// The collection levels whose keys a producer restates: the levels at which a projection guard
/// sent to its `get` may name keys ([`TileProducer::restates`]).
///
/// [`TileProducer::restates`]: crate::interpreter::tile_operators::TileProducer::restates
pub enum Restates {
    /// The outermost collection's keys only.
    Outermost,
    /// The outermost collection's keys and the keys of every level above the given one. A
    /// producer that keeps its input's keys above its own level and computes the values beneath
    /// them declares its own level, since the keys at and beneath it are inside those values.
    Above(CurryLevel),
    /// The keys of every level.
    Every,
}

impl Restates {
    /// Whether a projection of the keys of `level` names keys this declaration excludes.
    pub fn refuses(&self, level: CurryLevel) -> bool {
        match self {
            Restates::Outermost => level != CurryLevel::OUTERMOST,
            Restates::Above(own) => level != CurryLevel::OUTERMOST && level >= *own,
            Restates::Every => false,
        }
    }
}

impl std::fmt::Display for Restates {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Restates::Outermost => write!(f, "the outermost keys only"),
            Restates::Above(own) => write!(f, "the outermost keys and the keys above {own}"),
            Restates::Every => write!(f, "the keys of every level"),
        }
    }
}

/// How many levels above its own `keys` names a path through: the length of its longest
/// qualification chain.
fn qualifying_levels(keys: &Predicate) -> usize {
    match keys {
        Predicate::Qualified { enclosing, .. } => 1 + qualifying_levels(enclosing),
        Predicate::Or(arms) => arms.iter().map(qualifying_levels).max().unwrap_or(0),
        _ => 0,
    }
}

/// The arms of `keys`, which an `Or` holds and any other predicate is one of.
fn arms_of(keys: &Predicate) -> &[Predicate] {
    match keys {
        Predicate::Or(arms) => arms,
        single => std::slice::from_ref(single),
    }
}

/// The keys of the level above that `keys`, a region of paths, is every key beneath, where each
/// of its arms is: `Qualified { enclosing, here: True }`, every key under the paths `enclosing`
/// admits.
fn every_key_beneath(keys: &Predicate) -> Option<Predicate> {
    arms_of(keys)
        .iter()
        .map(|arm| match arm {
            Predicate::Qualified { enclosing, here } if here.is_true() => {
                Some((**enclosing).clone())
            }
            _ => None,
        })
        .try_fold(Predicate::False, |all, arm| Some(all.union(&arm?)))
}

/// The guard naming the keys of `level` that `keys` admits, in the spelling
/// `TileGuard::flatten_or` gives every guard: each arm at the shallowest level it is every key
/// beneath, inside a codomain guard per level above that one.
fn spell(level: CurryLevel, keys: &Predicate) -> TileGuard {
    TileGuard::flatten_or(vec![
        level.wrap_guard(TileGuard::Function(FunctionGuard::Domain(keys.clone()))),
    ])
}

/// The keys of level `to` that some path `keys` admits runs through. `keys` is a region of paths
/// at level `from`, beneath `to`; an unqualified arm runs through every key above it.
fn through_at(keys: &Predicate, from: CurryLevel, to: CurryLevel) -> Predicate {
    fn up(keys: &Predicate, levels: usize) -> Predicate {
        match levels {
            0 => keys.clone(),
            _ => arms_of(keys)
                .iter()
                .map(|arm| up(arm.split_qualification().0, levels - 1))
                .fold(Predicate::False, |all, arm| all.union(&arm)),
        }
    }
    up(keys, from.index() - to.index())
}

/// Per level above `level`, the keys every path beneath which `keys` admits. Each arm of the
/// guard [`spell`] gives `keys` that sits above `level` names such keys at its own level, and the
/// paths beneath them at every level down to `level`.
fn whole_above(level: CurryLevel, keys: &Predicate) -> Vec<Predicate> {
    let mut whole = vec![Predicate::False; level.index()];
    let guard = spell(level, keys);
    let arms = match &guard {
        TileGuard::Or(arms) => arms.as_slice(),
        single => std::slice::from_ref(single),
    };
    for arm in arms {
        let mut depth = 0;
        let mut node = arm;
        while let TileGuard::Function(FunctionGuard::Codomain(inner)) = node {
            depth += 1;
            node = inner;
        }
        let TileGuard::Function(FunctionGuard::Domain(region)) = node else {
            unreachable!("a projection's guard is domain guards beneath codomain guards: {guard:?}")
        };
        for (at, whole) in whole.iter_mut().enumerate().skip(depth) {
            *whole = whole.union(&region.descend(at - depth));
        }
    }
    whole
}

/// `stated`, a statement about the keys `depth` levels in, cut to the paths of `level` that
/// `keys` admits, `depth` being at or beneath `level`.
///
/// At `level` that is the intersection. Beneath it a statement names its groups by the paths
/// that reach them, so it is qualified by the keys: one made of every group, the unqualified
/// kind, is about the groups of the paths kept and no others.
fn within_paths(stated: &Predicate, keys: &Predicate, level: usize, depth: usize) -> Predicate {
    match stated {
        Predicate::False => Predicate::False,
        Predicate::Or(arms) => arms
            .iter()
            .map(|arm| within_paths(arm, keys, level, depth))
            .fold(Predicate::False, |all, arm| all.union(&arm)),
        at_level if depth == level => {
            assert!(
                depth > 0 || !at_level.qualifies(),
                "the outermost level names no enclosing path: {stated:?}"
            );
            at_level.intersect(keys)
        }
        Predicate::Qualified { enclosing, here } => Predicate::qualified(
            within_paths(enclosing, keys, level, depth - 1),
            (**here).clone(),
        ),
        unqualified => Predicate::qualified(
            within_paths(&Predicate::True, keys, level, depth - 1),
            unqualified.clone(),
        ),
    }
}

impl TileGuard {
    /// The projection this guard names, for a producer that restates the outermost keys only
    /// ([`Restates::Outermost`]), or a panic naming `producer` and the guard.
    pub fn projection(&self, producer: &str) -> Projection {
        self.projection_restating(&Restates::Outermost, || producer.to_owned())
    }

    /// The projection this guard names, for `producer`, at the levels its
    /// [`restates`](crate::interpreter::tile_operators::TileProducer::restates) declares, or a
    /// panic naming `producer` and the guard.
    pub fn projection_for(
        &self,
        producer: &(impl crate::interpreter::tile_operators::TileProducer + ?Sized),
    ) -> Projection {
        self.projection_restating(&producer.restates(), || producer.name())
    }

    /// The projection this guard names, or a panic naming the producer and the guard where the
    /// guard names no projection or names keys at a level `restates` refuses: a consumer that
    /// sends a shape the producer does not restate has a bug, and answering a smaller region
    /// would hide it.
    fn projection_restating(
        &self,
        restates: &Restates,
        producer: impl Fn() -> String,
    ) -> Projection {
        let projection = Projection::of(self).unwrap_or_else(|why| panic!("{}: {why}", producer()));
        if let Some(level) = projection.level()
            && restates.refuses(level)
        {
            let producer = producer();
            panic!(
                "{producer}: a projection guard names keys at {level}, and {producer} restates \
                 {restates}: {self:?}"
            );
        }
        projection
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
        self.restrict_to_paths(CurryLevel::OUTERMOST, keys);
    }

    /// Keep the keys of `level` whose path `keys` admits, each with the value under it, and the
    /// keys above them that an admitted path runs through; and state complete only the region
    /// the predicate names.
    ///
    /// A statement beneath `level` is cut to the paths kept. A statement above it keeps the keys
    /// every path beneath which `keys` admits, and the rest of what it said is stated at
    /// `level`, cut to `keys`: completeness closes downward, so a key stated complete states
    /// every path beneath it.
    ///
    /// # Panics
    ///
    /// For a tile with no collection at `level`.
    pub fn restrict_to_paths(&mut self, level: CurryLevel, keys: &Predicate) {
        let Tile::DataFunction { domain, .. } = self.values_at_level_above(level) else {
            panic!("only a collection has keys to restrict at {level}, got {self:?}")
        };
        if level == CurryLevel::OUTERMOST {
            let mask: Vec<bool> = (0..domain.len())
                .map(|key| keys.contains(&domain.index_at(key)))
                .collect();
            if !mask.iter().all(|kept| *kept) {
                self.retain_keys(&mask);
            }
            cut_statements(self, 0, 0, keys, &[], Predicate::False);
            return;
        }
        let through: Vec<Predicate> = (0..level.index())
            .map(|above| through_at(keys, level, CurryLevel::new(above)))
            .collect();
        let whole = whole_above(level, keys);
        let admitted = |path: &[Value]| match path.len() - 1 {
            at if at == level.index() => keys.contains_path(path),
            above => through[above].contains_path(path),
        };
        let mut all_kept = true;
        for depth in 0..=level.index() {
            let paths = self.paths_at(CurryLevel::new(depth));
            all_kept &= paths.iter().all(|path| admitted(path));
        }
        if !all_kept {
            self.retain_paths(level, &admitted);
        }
        cut_statements(self, 0, level.index(), keys, &whole, Predicate::False);
    }

    /// The tile holding `level`'s keys: this one at the outermost level, and the values of the
    /// level above beneath it.
    fn values_at_level_above(&self, level: CurryLevel) -> &Tile {
        match level.enclosing() {
            None => self,
            Some(above) => self.values_at(above),
        }
    }

    /// Cut this tile to `projection`.
    ///
    /// `Nothing` empties it at `tiling`, the tiling of the producer that made it.
    pub fn restrict_to(&mut self, projection: &Projection, tiling: &Tiling) {
        match projection {
            Projection::Everything => {}
            Projection::Nothing => *self = tiling.empty_tile(),
            Projection::Keys { level, keys } => self.restrict_to_paths(*level, keys),
        }
    }
}

/// Cut what `tile` and the levels beneath it state to the paths of `level` that `keys` admits
/// ([`Tile::restrict_to_paths`]). `tile` is `depth` levels in. `whole` holds, per level above
/// `level`, the keys every path beneath which `keys` admits ([`whole_above`]). `beneath` is what
/// the levels above `tile` stated of paths at `level`, cut to `keys`.
fn cut_statements(
    tile: &mut Tile,
    depth: usize,
    level: usize,
    keys: &Predicate,
    whole: &[Predicate],
    beneath: Predicate,
) {
    match tile {
        Tile::DataFunction {
            codomain,
            domain_predicate,
            ..
        } => {
            let (stated, below) = match depth.cmp(&level) {
                std::cmp::Ordering::Less => {
                    let partly = domain_predicate
                        .minus(&whole[depth])
                        .descend(level - depth)
                        .intersect(keys);
                    (
                        domain_predicate.intersect(&whole[depth]),
                        beneath.union(&partly),
                    )
                }
                std::cmp::Ordering::Equal => (
                    within_paths(domain_predicate, keys, level, depth).union(&beneath),
                    Predicate::False,
                ),
                std::cmp::Ordering::Greater => (
                    within_paths(domain_predicate, keys, level, depth),
                    Predicate::False,
                ),
            };
            *domain_predicate = stated;
            cut_statements(codomain, depth + 1, level, keys, whole, below);
        }
        // A record of tiles stands over the same rows, so a collection in one of its fields is a
        // level at the same depth as the record.
        Tile::Record { fields, .. } => {
            for field in fields.values_mut() {
                cut_statements(field, depth, level, keys, whole, beneath.clone());
            }
        }
        _ => {}
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
            Ok(Projection::admitting(positions(1, 2)))
        );
        // `Domain(True)` is the universal guard however it is spelled.
        assert_eq!(
            Projection::of(&TileGuard::Function(FunctionGuard::Domain(Predicate::True))),
            Ok(Projection::Everything)
        );
    }

    /// A domain guard inside a codomain guard names keys of the level it steps to, under the
    /// paths its predicate qualifies them by, and names no more enclosing levels than it steps
    /// into.
    #[test]
    fn a_guard_inside_a_codomain_names_keys_of_its_level() {
        let one = Predicate::point(Value::UInt(0));
        let qualified = Predicate::qualified(one.clone(), one.clone());
        let named_path = TileGuard::Function(FunctionGuard::Domain(qualified.clone()));
        let error = Projection::of(&named_path).expect_err("the outermost keys have no path");
        assert!(error.contains("enclosing paths"), "{error}");
        assert_eq!(
            Projection::of(&codomain(domain(one.clone()))),
            Ok(Projection::Keys {
                level: CurryLevel::new(1),
                keys: one.clone()
            }),
            "the key 0 beneath every outermost key"
        );
        assert_eq!(
            Projection::of(&codomain(domain(qualified.clone()))),
            Ok(Projection::Keys {
                level: CurryLevel::new(1),
                keys: qualified.clone()
            })
        );
        let two_up = Predicate::qualified(qualified, one);
        assert!(Projection::of(&codomain(domain(two_up))).is_err());
        let scalar = codomain(TileGuard::Scalar(under(key(0), Predicate::True)));
        assert!(Projection::of(&scalar).is_err());
    }

    /// `Above` admits the outermost keys and the levels above its own, and refuses its own level
    /// and every level beneath it.
    #[test]
    fn a_declaration_above_a_level_refuses_that_level_and_beneath() {
        let [outermost, one, two] = [0, 1, 2].map(CurryLevel::new);
        assert!(!Restates::Outermost.refuses(outermost));
        assert!(Restates::Outermost.refuses(one));
        assert!(!Restates::Above(outermost).refuses(outermost));
        assert!(Restates::Above(outermost).refuses(one));
        assert!(!Restates::Above(two).refuses(outermost));
        assert!(!Restates::Above(two).refuses(one));
        assert!(Restates::Above(two).refuses(two));
        assert!(Restates::Above(one).refuses(two));
        assert!(!Restates::Every.refuses(two));
    }

    /// A producer that reads a projection with `TileGuard::projection` restates the outermost
    /// keys only, and reports keys beneath them.
    #[test]
    #[should_panic(expected = "Producer: a projection guard names keys at level 1")]
    fn a_producer_reports_keys_beneath_the_outermost_collection() {
        codomain(domain(positions(0, 0))).projection("Producer");
    }

    fn domain(keys: Predicate) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(keys))
    }

    fn codomain(inner: TileGuard) -> TileGuard {
        TileGuard::Function(FunctionGuard::Codomain(Box::new(inner)))
    }

    /// The paths `(𝑘, 𝑗)` of the outer keys `outer`, `𝑗` in `inner`.
    fn under(outer: Predicate, inner: Predicate) -> Predicate {
        Predicate::qualified(outer, inner)
    }

    fn key(k: u64) -> Predicate {
        Predicate::point(Value::UInt(k))
    }

    fn level_one(keys: Predicate) -> Projection {
        Projection::Keys {
            level: CurryLevel::new(1),
            keys,
        }
    }

    /// Every key beneath an outermost key is that key, so the level above spells it.
    #[test]
    fn every_key_beneath_keys_is_those_keys() {
        assert_eq!(
            Projection::keys_at(CurryLevel::new(1), under(key(2), Predicate::True)),
            Projection::admitting(key(2))
        );
        assert_eq!(
            Projection::keys_at(CurryLevel::new(2), Predicate::True),
            Projection::Everything
        );
        let mixed = under(key(2), Predicate::True).union(&under(key(0), positions(2, 9)));
        assert_eq!(
            Projection::keys_at(CurryLevel::new(1), mixed.clone()).level(),
            Some(CurryLevel::new(1)),
            "a region partly beneath key 0 stays at level 1"
        );
        // Its guard spells key 2 at the outermost level and key 0's paths beneath it, and reads
        // back as the same projection.
        let tiling = nested_tiling();
        let spelled = level_one(mixed.clone()).guard(&tiling);
        assert_eq!(
            spelled,
            TileGuard::flatten_or(vec![
                domain(key(2)),
                codomain(domain(under(key(0), positions(2, 9)))),
            ])
        );
        assert_eq!(Projection::of(&spelled), Ok(level_one(mixed)));
    }

    /// `0 ↦ {0 ↦ 10, 1 ↦ 11, 2 ↦ 12}`, `1 ↦ {0 ↦ 20}`, `2 ↦ {0 ↦ 30}`: every key and every group
    /// stated complete.
    fn three_rows() -> Tile {
        Tile::data_function(
            ColumnValue::UInts(vec![0, 1, 2]),
            Box::new(Tile::grouped(
                vec![0, 3, 4],
                ColumnValue::UInts(vec![0, 1, 2, 0, 0]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 11, 12, 20, 30]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        )
    }

    fn nested_tiling() -> Tiling {
        Tiling::data_function(
            Extent::uint_range(3),
            Tiling::data_function(
                Extent::uint_range(3),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        )
    }

    /// The `(path, value)` cells of a two-level tile.
    fn cells(tile: &Tile) -> Vec<(Vec<Value>, i64)> {
        let mut live = tile.clone();
        live.compact();
        let paths = live.paths_at(CurryLevel::new(1));
        let Tile::Scalar(ColumnValue::Ints(values)) = live.values_at(CurryLevel::new(2)) else {
            panic!("ints beneath two levels: {live:?}")
        };
        paths.into_iter().zip(values.iter().copied()).collect()
    }

    /// A tile cut to a projection at level 1 and the same tile cut to the rest merge back into
    /// the tile.
    #[test]
    fn a_cut_and_its_complement_merge_back_into_the_tile() {
        let projection =
            level_one(under(key(0), positions(1, 2)).union(&under(key(1), Predicate::True)));
        let tiling = nested_tiling();
        let mut inside = three_rows();
        inside.restrict_to(&projection, &tiling);
        let mut outside = three_rows();
        outside.restrict_to(&Projection::Everything.minus(&projection), &tiling);
        outside.merge(inside);
        let mut merged = cells(&outside);
        merged.sort_by(|a, b| a.0.partial_cmp(&b.0).expect("positions are ordered"));
        assert_eq!(
            merged,
            cells(&three_rows()),
            "a merge appends the keys it adds"
        );
        for (k, j) in [(0, 0), (0, 2), (1, 0), (2, 0)] {
            let path = [Value::UInt(k), Value::UInt(j)];
            assert!(
                outside
                    .completion_at(CurryLevel::new(1))
                    .contains_path(&path),
                "({k}, {j}) is stated complete again"
            );
        }
    }

    /// Every key beneath an outermost key reads as that key, so a producer restating the
    /// outermost keys reads it.
    #[test]
    fn every_key_beneath_a_key_is_a_projection_of_the_outermost_keys() {
        assert_eq!(
            codomain(domain(under(key(2), Predicate::True))).projection("Producer"),
            Projection::admitting(key(2))
        );
    }

    #[test]
    fn projections_intersect_and_normalize() {
        let (low, high) = (
            Projection::admitting(positions(0, 5)),
            Projection::admitting(positions(3, 9)),
        );
        assert_eq!(
            low.intersect(&high),
            Projection::admitting(positions(3, 5)),
            "both name keys 3 to 5"
        );
        assert_eq!(
            low.intersect(&Projection::admitting(positions(7, 9))),
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
            low.minus(&Projection::admitting(positions(3, 9))),
            Projection::admitting(positions(0, 2).union(&Predicate::False)),
            "keys 0 to 5 less 3 to 9 leave 0 to 2"
        );
        assert_eq!(low.minus(&Projection::Everything), Projection::Nothing);
        assert_eq!(low.minus(&Projection::Nothing), low);
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
}
