//! The projection guards a producer restates: [`Projection`].
//! See `src/interpreter/design-operators.md`, "Projection guards".

use std::collections::BTreeMap;

use smol_str::SmolStr;

use crate::ccl::{FieldKey, TagMap};
#[cfg(test)]
use crate::interpreter::tile_operators::test_helpers::ReadInPipeline as _;
use crate::interpreter::{
    CurryLevel, Extent, FunctionGuard, Predicate, Tile, TileGuard, Tiling, Value,
};
#[cfg(test)]
use std::sync::PoisonError;

/// The part of a producer's tile that a `get` asks for.
///
/// A projection guard is any [`TileGuard`], and a projection is the shapes a pipeline cuts a
/// tile with: everything, nothing, the keys of one collection level that a predicate admits, and
/// a projection per field of a record of values. Anything else is a gap the producer reports
/// rather than answers with a smaller region (`src/interpreter/design-operators.md`, "Guard
/// operations are exact").
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
    /// A record of values, each field's part named by its own projection: `fields` for the fields
    /// it lists, and `rest` for every field it does not. A record has no keys, so this is how a
    /// region of a record names part of it.
    ///
    /// Construct through [`Projection::fields`]: no listed field's projection equals `rest`, and
    /// at least one field is listed.
    Fields {
        fields: BTreeMap<SmolStr, Projection>,
        rest: Box<Projection>,
    },
    /// The keys of `level` that `keys` admits, and of the value under each the part `values`
    /// names, `values` being a projection of the values at `level`'s keys: a record whose
    /// collection field is complete through some rows names the record's fields this way.
    ///
    /// Construct through [`Projection::within`]: `values` is neither everything, which is
    /// [`Keys`](Self::Keys), nor nothing.
    Within {
        level: CurryLevel,
        keys: Predicate,
        values: Box<Projection>,
    },
    /// The union of regions no one projection names, as keys of one level with different parts of
    /// their values. Construct through [`Projection::any_of`]: two or more arms, none an `Or`,
    /// everything or nothing, and no two arms one projection names.
    Or(Vec<Projection>),
}

/// `keys`, admitting paths whose last key stands at `depth` beneath an arm of a tagged union, as
/// paths of the union: each path's outermost key under `tag`. A part unqualified below the
/// outermost level stands under every enclosing path of the arm, which is every path headed by a
/// key under `tag`. The outermost keys are tagged whole, so they stay one union predicate, the
/// shape a tagged union reads its outermost keys in.
fn tagged_at(keys: &Predicate, depth: usize, tag: &FieldKey) -> Predicate {
    match keys {
        _ if keys.is_false() => Predicate::False,
        Predicate::Or(arms) if depth > 0 => arms
            .iter()
            .map(|arm| tagged_at(arm, depth, tag))
            .fold(Predicate::False, |all, arm| all.union(&arm)),
        Predicate::Qualified { enclosing, here } if depth > 0 => {
            Predicate::qualified(tagged_at(enclosing, depth - 1, tag), (**here).clone())
        }
        unqualified if depth > 0 => Predicate::qualified(
            tagged_at(&Predicate::True, depth - 1, tag),
            unqualified.clone(),
        ),
        outermost => Predicate::tagged(
            TagMap::from_arms(vec![(tag.clone(), outermost.clone())]),
            false,
        ),
    }
}

impl Projection {
    /// Panic for `reader`, which answers whole values at keys, given `part`: a
    /// [`Within`](Projection::Within) or an [`Or`](Projection::Or), which names part of some values.
    /// A reader that only a projection of keys reaches states that no such projection reaches it.
    #[track_caller]
    pub(crate) fn refuse_part_of_values(reader: &str, part: &Projection) -> ! {
        panic!(
            "{reader} answers whole values at keys, and {part:?} names part of some values: a \
             projection within values or an `Or` reaches it"
        )
    }

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
        if let TileGuard::Record(fields) = arm {
            let fields = fields
                .iter()
                .map(|(name, field)| Ok((name.clone(), Projection::of(field)?)))
                .collect::<Result<BTreeMap<_, _>, String>>()?;
            return Ok(Projection::fields(fields, Projection::Nothing));
        }
        let mut level = 0;
        let mut node = arm;
        while let TileGuard::Function(FunctionGuard::Codomain(inner)) = node {
            level += 1;
            node = inner;
        }
        // Cells beneath keys, as a record whose collection field is complete through some rows:
        // the keys of the level above, each within the part of its values the cells name.
        if level > 0 && matches!(node, TileGuard::Record(_) | TileGuard::Scalar(_)) {
            return within_of_cells(node, CurryLevel::new(level - 1))
                .ok_or_else(|| format!("{guard:?} names cells this projection has no part for"));
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
                "a projection guard is everything, nothing, the keys of a collection level or a \
                 projection per field of a record of values, got {guard:?}"
            )),
        }
    }

    /// The guard this projection names for a producer with `tiling`.
    ///
    /// Each arm of the keys is spelled at the shallowest level it is every key beneath, one
    /// domain guard inside a codomain guard per level above it, as `domain_prefix` spells a
    /// release.
    ///
    /// # Panics
    ///
    /// Where a [`Within`](Projection::Within) names a part of the values at its keys that
    /// `tiling` has no spelling of.
    pub fn guard(&self, tiling: &Tiling) -> TileGuard {
        match self {
            Projection::Everything => tiling.universal_guard(),
            Projection::Nothing => tiling.empty_guard(),
            Projection::Keys { level, keys } => spell(*level, keys),
            Projection::Within {
                level,
                keys,
                values,
            } => {
                let Tiling::DataFunction { codomain, .. } = tiling.values_at(*level) else {
                    panic!("{self:?} names keys of {level}, and {tiling} has no collection there")
                };
                assert!(
                    values.fits(codomain),
                    "{self:?} names a part of the values at its keys that {codomain} has no \
                     spelling of, and a guard names exactly its region"
                );
                let inner = guard_beneath_keys(&values.guard(codomain), keys, 0);
                CurryLevel::new(level.index() + 1).wrap_guard(inner)
            }
            Projection::Or(arms) => {
                TileGuard::flatten_or(arms.iter().map(|arm| arm.guard(tiling)).collect())
            }
            Projection::Fields { fields: listed, .. } => {
                let Tiling::Record(fields) = tiling else {
                    panic!("{self:?} names the fields of a record, and {tiling} is none")
                };
                debug_assert!(
                    listed.keys().all(|name| fields.contains_key(name)),
                    "{self:?} names only fields of {tiling}"
                );
                TileGuard::Record(
                    fields
                        .iter()
                        .map(|(name, field)| (name.clone(), self.field(name).guard(field)))
                        .collect(),
                )
            }
        }
    }

    /// The guard this projection names for a collection, whose universal guard is the domain
    /// guard admitting every key ([`guard`](Self::guard) where no tiling is at hand).
    pub(crate) fn collection_guard(&self) -> TileGuard {
        match self {
            Projection::Everything => TileGuard::Function(FunctionGuard::Domain(Predicate::True)),
            Projection::Nothing => TileGuard::Function(FunctionGuard::Domain(Predicate::False)),
            Projection::Keys { level, keys } => spell(*level, keys),
            Projection::Or(arms) => {
                TileGuard::flatten_or(arms.iter().map(Projection::collection_guard).collect())
            }
            Projection::Within { .. } => {
                panic!(
                    "{self:?} names part of some values, which no guard spells without their tiling"
                )
            }
            Projection::Fields { .. } => {
                panic!("{self:?} names the fields of a record, which is no collection")
            }
        }
    }

    /// The projection of a record of values naming `fields` per listed field and `rest` for every
    /// other field, normalized: a listed field whose projection is `rest` is dropped, and with no
    /// field listed it is `rest`. It knows no field list, so a projection naming every field of the
    /// record whole is not [`Everything`](Self::Everything); [`over_fields`](Self::over_fields)
    /// normalizes against the record's fields.
    pub(crate) fn fields(fields: BTreeMap<SmolStr, Projection>, rest: Projection) -> Projection {
        let fields: BTreeMap<_, _> = fields
            .into_iter()
            .filter(|(_, field)| *field != rest)
            .collect();
        match fields.is_empty() {
            true => rest,
            false => Projection::Fields {
                fields,
                rest: Box::new(rest),
            },
        }
    }

    /// The projection of a record of values naming `field` of the field `name` and nothing of
    /// any other field.
    pub(crate) fn of_field(name: &str, field: Projection) -> Projection {
        Projection::fields(BTreeMap::from([(name.into(), field)]), Projection::Nothing)
    }

    /// This projection of a record of values whose fields are `names`, normalized against them:
    /// [`Everything`](Self::Everything) where it names every field whole and
    /// [`Nothing`](Self::Nothing) where it names none of any.
    pub(crate) fn over_fields<'a>(
        self,
        names: impl IntoIterator<Item = &'a SmolStr>,
    ) -> Projection {
        let Projection::Fields { .. } = self else {
            return self;
        };
        let parts: Vec<Projection> = names.into_iter().map(|name| self.field(name)).collect();
        if parts.iter().all(|part| *part == Projection::Everything) {
            Projection::Everything
        } else if parts.iter().all(|part| *part == Projection::Nothing) {
            Projection::Nothing
        } else {
            self
        }
    }

    /// The part of the field `name` this projection of a record of values names.
    ///
    /// # Panics
    ///
    /// For a projection of keys, which no record of values is pulled at, and for a
    /// [`Within`](Projection::Within) or an [`Or`](Projection::Or).
    pub(crate) fn field(&self, name: &str) -> Projection {
        match self {
            part @ (Projection::Within { .. } | Projection::Or(_)) => {
                Projection::refuse_part_of_values("Projection::field", part)
            }
            Projection::Everything | Projection::Nothing => self.clone(),
            Projection::Fields { fields, rest } => fields
                .get(name)
                .cloned()
                .unwrap_or_else(|| (**rest).clone()),
            Projection::Keys { .. } => {
                panic!("{self:?} names keys, and a record of values has none")
            }
        }
    }

    /// `op` applied field by field to two projections of one record of values, either of which
    /// may be everything or nothing.
    fn field_by_field(
        &self,
        other: &Projection,
        op: impl Fn(&Projection, &Projection) -> Projection,
    ) -> Projection {
        let rest = |projection: &Projection| match projection {
            Projection::Fields { rest, .. } => (**rest).clone(),
            whole => whole.clone(),
        };
        let listed = |projection: &Projection| match projection {
            Projection::Fields { fields, .. } => fields.keys().cloned().collect(),
            _ => Vec::new(),
        };
        let mut names = listed(self);
        names.extend(listed(other));
        let fields = names
            .into_iter()
            .map(|name| {
                let field = op(&self.field(&name), &other.field(&name));
                (name, field)
            })
            .collect();
        Projection::fields(fields, op(&rest(self), &rest(other)))
    }

    /// Whether either of `self` and `other` names fields of a record of values: their union,
    /// intersection and difference then go field by field.
    fn either_names_fields(&self, other: &Projection) -> bool {
        matches!(self, Projection::Fields { .. }) || matches!(other, Projection::Fields { .. })
    }

    /// The keys above `level` that this projection names, for an operator whose input lacks
    /// `level`: itself where it names keys above `level`, and otherwise the keys of the level just
    /// above that its paths run through, or everything where `level` is the outermost.
    ///
    /// The operator pulls its input there and cuts its answer to this projection after; pulling
    /// more is sound for a `get`.
    pub fn above(&self, level: CurryLevel) -> Projection {
        match self {
            Projection::Or(arms) => Projection::any_of(arms.iter().map(|arm| arm.above(level))),
            Projection::Keys { level: own, keys }
            | Projection::Within {
                level: own, keys, ..
            } if *own >= level => match level.enclosing() {
                None => Projection::Everything,
                Some(enclosing) => {
                    Projection::keys_at(enclosing, through_at(keys, *own, enclosing))
                }
            },
            // A part of the values at `level`, which the operator computes anew from them, names
            // the whole value at its keys.
            Projection::Within {
                level: own, keys, ..
            } if own.index() + 1 >= level.index() => Projection::keys_at(*own, keys.clone()),
            other => other.clone(),
        }
    }

    /// This projection where `restates` does not refuse the level it names, and otherwise the
    /// keys its paths run through at the nearest level above that `restates` does not refuse
    /// ([`above`](Self::above)); everything where an arm names its keys under every key of
    /// that level.
    ///
    /// An operator whose input does not restate the level this projection names pulls the
    /// input there and cuts its answer after; pulling more is sound for a `get`.
    pub fn restated_by(&self, restates: &Restates) -> Projection {
        let Some(own) = self.level() else {
            return self.clone();
        };
        let restated = restates.nearest(own);
        let mut pulled = self.clone();
        while let Some(level) = pulled.level()
            && level > restated
        {
            pulled = pulled.above(level);
        }
        pulled
    }

    /// The level whose keys this projection names, `None` for everything and nothing.
    pub fn level(&self) -> Option<CurryLevel> {
        match self {
            Projection::Keys { level, .. } | Projection::Within { level, .. } => Some(*level),
            Projection::Or(arms) => arms.iter().filter_map(Projection::level).max(),
            _ => None,
        }
    }

    /// The projection of `self` within `other`: what both name.
    pub fn intersect(&self, other: &Projection) -> Projection {
        if self.names_part_of_values()
            || other.names_part_of_values()
            || matches!(self, Projection::Or(_))
            || matches!(other, Projection::Or(_))
        {
            return self.intersect_parts(other);
        }
        if self.either_names_fields(other) {
            return self.field_by_field(other, Projection::intersect);
        }
        let level = self.deepest(other);
        Projection::keys_at(level, self.at(level).intersect(&other.at(level)))
    }

    /// What `self` names that `other` does not: the region still unread after a read at `other`.
    pub fn minus(&self, other: &Projection) -> Projection {
        if self.names_part_of_values()
            || other.names_part_of_values()
            || matches!(self, Projection::Or(_))
            || matches!(other, Projection::Or(_))
        {
            return self.minus_parts(other);
        }
        if self.either_names_fields(other) {
            return self.field_by_field(other, Projection::minus);
        }
        let level = self.deepest(other);
        Projection::keys_at(level, self.at(level).minus(&other.at(level)))
    }

    /// The projection naming what either names: the region a memo has read or must read
    /// again.
    pub fn union(&self, other: &Projection) -> Projection {
        if self.names_part_of_values()
            || other.names_part_of_values()
            || matches!(self, Projection::Or(_))
            || matches!(other, Projection::Or(_))
        {
            return Projection::any_of([self.clone(), other.clone()]);
        }
        if self.either_names_fields(other) {
            return self.field_by_field(other, Projection::union);
        }
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
            part @ (Projection::Within { .. } | Projection::Or(_)) => {
                Projection::refuse_part_of_values("Projection::at", part)
            }
            Projection::Everything => Predicate::True,
            Projection::Nothing => Predicate::False,
            Projection::Keys { level: own, keys } => {
                let beneath = level
                    .index()
                    .checked_sub(own.index())
                    .unwrap_or_else(|| panic!("{self:?} is read at {level}, above its own level"));
                keys.descend(beneath)
            }
            Projection::Fields { .. } => {
                panic!("{self:?} names the fields of a record, which has no level of keys")
            }
        }
    }

    /// The region of a tagged union that `self`, a region of the union's arm under `tag`, names:
    /// the same paths with their outermost key under the tag. The arm's
    /// [`Everything`](Self::Everything) is every key under the tag, and no key under another.
    pub fn tagged(&self, tag: &FieldKey) -> Projection {
        match self {
            Projection::Or(arms) => Projection::any_of(arms.iter().map(|arm| arm.tagged(tag))),
            // The tag stands on the keys, so the part of the values beneath them is unchanged.
            Projection::Within {
                level,
                keys,
                values,
            } => Projection::within(
                *level,
                tagged_at(keys, level.index(), tag),
                (**values).clone(),
            ),
            Projection::Nothing => Projection::Nothing,
            Projection::Everything => Projection::admitting(tagged_at(&Predicate::True, 0, tag)),
            Projection::Keys { level, keys } => {
                Projection::keys_at(*level, tagged_at(keys, level.index(), tag))
            }
            Projection::Fields { .. } => {
                panic!("{self:?} names the fields of a record, which is no arm of a tagged union")
            }
        }
    }

    /// The projection naming the outermost keys `keys` admits ([`keys_at`](Self::keys_at) at the
    /// outermost level).
    pub fn admitting(keys: Predicate) -> Projection {
        Projection::keys_at(CurryLevel::OUTERMOST, keys)
    }

    /// The projection of the one path `path`, a key per level from the outermost: the key of its
    /// last level under the keys above it.
    ///
    /// # Panics
    ///
    /// For an empty path, which names no level.
    pub fn of_path(path: &[Value]) -> Projection {
        let (last, above) = path.split_last().expect("a path names a key at its level");
        let enclosing = above.iter().fold(Predicate::True, |enclosing, key| {
            Predicate::qualified(enclosing, Predicate::point(key.clone()))
        });
        Projection::keys_at(
            CurryLevel::new(above.len()),
            Predicate::qualified(enclosing, Predicate::point(last.clone())),
        )
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

impl Projection {
    /// The keys of `level` that `keys` admits with the part `values` names of each one's value,
    /// normalized: nothing where either names nothing, and [`keys_at`](Self::keys_at) where
    /// `values` is everything.
    pub fn within(level: CurryLevel, keys: Predicate, values: Projection) -> Projection {
        match values {
            _ if keys.is_false() => Projection::Nothing,
            Projection::Nothing => Projection::Nothing,
            Projection::Everything => Projection::keys_at(level, keys),
            values => Projection::Within {
                level,
                keys,
                values: Box::new(values),
            },
        }
    }

    /// The union of `arms`, normalized: an `Or` is flattened, nothing dropped, everything absorbs
    /// the rest, arms of keys at one level merged and arms within the same values at one level
    /// merged, and a single arm is itself.
    pub fn any_of(arms: impl IntoIterator<Item = Projection>) -> Projection {
        let mut flat = Vec::new();
        for arm in arms {
            match arm {
                Projection::Or(inner) => flat.extend(inner),
                Projection::Nothing => {}
                Projection::Everything => return Projection::Everything,
                other => flat.push(other),
            }
        }
        let mut merged: Vec<Projection> = Vec::new();
        for arm in flat {
            let joined = merged.iter().position(|other| match (other, &arm) {
                (Projection::Keys { level: a, .. }, Projection::Keys { level: b, .. }) => a == b,
                (
                    Projection::Within {
                        level: a,
                        values: va,
                        ..
                    },
                    Projection::Within {
                        level: b,
                        values: vb,
                        ..
                    },
                ) => a == b && va == vb,
                _ => false,
            });
            match joined {
                Some(at) => {
                    let other = merged.remove(at);
                    merged.push(match (other, arm) {
                        (Projection::Keys { level, keys: a }, Projection::Keys { keys: b, .. }) => {
                            Projection::keys_at(level, a.union(&b))
                        }
                        (
                            Projection::Within {
                                level,
                                keys: a,
                                values,
                            },
                            Projection::Within { keys: b, .. },
                        ) => Projection::within(level, a.union(&b), *values),
                        _ => unreachable!("only like arms merge"),
                    });
                }
                None => merged.push(arm),
            }
        }
        match merged.len() {
            0 => Projection::Nothing,
            1 => merged.pop().expect("one arm"),
            _ => Projection::Or(merged),
        }
    }

    /// Whether this projection of some values names only parts `tiling` has: fields of a record it
    /// is, and keys of a collection it is.
    fn fits(&self, tiling: &Tiling) -> bool {
        match (self, tiling) {
            (Projection::Everything | Projection::Nothing, _) => true,
            (Projection::Fields { fields, .. }, Tiling::Record(record)) => fields
                .iter()
                .all(|(name, part)| record.get(name).is_some_and(|field| part.fits(field))),
            (Projection::Fields { .. }, _) => false,
            (Projection::Keys { .. }, Tiling::DataFunction { .. }) => true,
            (Projection::Within { level, values, .. }, Tiling::DataFunction { .. }) => {
                match tiling.values_at(*level) {
                    Tiling::DataFunction { codomain, .. } => values.fits(codomain),
                    _ => false,
                }
            }
            (Projection::Or(arms), _) => arms.iter().all(|arm| arm.fits(tiling)),
            _ => false,
        }
    }

    /// The arms of this projection, which an `Or` holds and any other is one of.
    fn arms(&self) -> Vec<Projection> {
        match self {
            Projection::Or(arms) => arms.clone(),
            single => vec![single.clone()],
        }
    }

    /// Whether this projection names part of some value: a [`Within`](Self::Within) or an `Or`
    /// with one.
    pub fn names_part_of_values(&self) -> bool {
        match self {
            Projection::Within { .. } => true,
            Projection::Or(arms) => arms.iter().any(Projection::names_part_of_values),
            _ => false,
        }
    }

    /// The keys holding what this projection names: each arm within some values as its keys
    /// whole. A pull of part of some values pulls these keys and is answered with more than it
    /// names, which is sound for a `get`.
    pub fn rows(&self) -> Projection {
        Projection::any_of(self.arms().into_iter().map(|arm| match arm {
            Projection::Within { level, keys, .. } => Projection::keys_at(level, keys),
            other => other,
        }))
    }

    /// One arm, never an `Or`, at `level` beneath its own where it names whole keys: the same
    /// paths as keys of the deeper level. `None` for an arm within some values, which names part
    /// of the values beneath its keys.
    fn whole_at(&self, level: CurryLevel) -> Option<Projection> {
        match self {
            Projection::Everything => Some(Projection::Everything),
            Projection::Nothing => Some(Projection::Nothing),
            Projection::Keys { level: own, keys } if *own <= level => Some(Projection::Keys {
                level,
                keys: keys.descend(level.index() - own.index()),
            }),
            _ => None,
        }
    }

    /// `op` on two arms of keys or within values, neither an `Or` nor a record of values, at the
    /// deeper of their levels: `keys` combines the keys, `values` the parts of the values.
    ///
    /// # Panics
    ///
    /// Where one arm names part of the values at a level above the other's keys: the deeper keys
    /// stand inside those values, and this algebra has no spelling for keys inside a part.
    fn arm_op(
        a: &Projection,
        b: &Projection,
        keys: impl Fn(&Predicate, &Predicate) -> Predicate,
        values: impl Fn(&Projection, &Projection) -> Projection,
    ) -> (CurryLevel, Predicate, Projection) {
        let level = [a.level(), b.level()]
            .into_iter()
            .flatten()
            .max()
            .unwrap_or(CurryLevel::OUTERMOST);
        let at = |arm: &Projection| -> (Predicate, Projection) {
            match arm {
                Projection::Within {
                    level: own,
                    keys,
                    values,
                } if *own == level => (keys.clone(), (**values).clone()),
                Projection::Within { .. } => panic!(
                    "the projection algebra has no region of {a:?} and {b:?}: keys at {level} stand \
                     inside part of the values above them"
                ),
                whole => match whole.whole_at(level).expect("an arm of whole keys") {
                    Projection::Everything => (Predicate::True, Projection::Everything),
                    Projection::Nothing => (Predicate::False, Projection::Everything),
                    Projection::Keys { keys, .. } => (keys, Projection::Everything),
                    _ => unreachable!("whole_at answers whole keys"),
                },
            }
        };
        let ((ka, va), (kb, vb)) = (at(a), at(b));
        (level, keys(&ka, &kb), values(&va, &vb))
    }

    /// The intersection of two projections, either of which may name part of some values.
    fn intersect_parts(&self, other: &Projection) -> Projection {
        Projection::any_of(self.arms().iter().flat_map(|a| {
            other.arms().into_iter().map(move |b| {
                let (level, keys, values) =
                    Projection::arm_op(a, &b, Predicate::intersect, Projection::intersect);
                Projection::within(level, keys, values)
            })
        }))
    }

    /// What `self` names that `other` does not, either of which may name part of some values: of
    /// the keys both name, the part of the values `self` names and `other` does not.
    fn minus_parts(&self, other: &Projection) -> Projection {
        Projection::any_of(self.arms().into_iter().map(|a| {
            other.arms().iter().fold(a, |left, b| {
                Projection::any_of(left.arms().into_iter().map(|arm| {
                    let (level, only, _) =
                        Projection::arm_op(&arm, b, Predicate::minus, |va, _| va.clone());
                    let (_, both, values) =
                        Projection::arm_op(&arm, b, Predicate::intersect, Projection::minus);
                    Projection::any_of([
                        Projection::within(level, only, arm_values(&arm, level)),
                        Projection::within(level, both, values),
                    ])
                }))
            })
        }))
    }
}

/// The part of the values beneath `level`'s keys `arm` names: everything for whole keys.
fn arm_values(arm: &Projection, level: CurryLevel) -> Projection {
    match arm {
        Projection::Within {
            level: own, values, ..
        } if *own == level => (**values).clone(),
        _ => Projection::Everything,
    }
}

/// The pairs of keys and paths beneath them `paths` admits, `paths` being over paths `relative`
/// levels beneath keys of some level: each arm split into the keys above and the paths beneath
/// them, the inverse of [`beneath_keys`]. An unqualified arm stands beneath every key.
fn split_beneath_keys(paths: &Predicate, relative: usize) -> Vec<(Predicate, Predicate)> {
    match paths {
        Predicate::False => Vec::new(),
        Predicate::Or(arms) => arms
            .iter()
            .flat_map(|arm| split_beneath_keys(arm, relative))
            .collect(),
        Predicate::Qualified { enclosing, here } if relative == 0 => {
            vec![((**enclosing).clone(), (**here).clone())]
        }
        Predicate::Qualified { enclosing, here } => split_beneath_keys(enclosing, relative - 1)
            .into_iter()
            .map(|(keys, above)| (keys, Predicate::qualified(above, (**here).clone())))
            .collect(),
        unqualified => vec![(Predicate::True, unqualified.clone())],
    }
}

/// The projection a guard of cells beneath keys of `level` names, `node` being the record or
/// scalar guard of the values at those keys: per region of the keys whose cells the guard names
/// alike, those keys within the part of their values it names. `None` where a field holds more
/// than a scalar or one collection level, which this reading has no part for.
fn within_of_cells(node: &TileGuard, level: CurryLevel) -> Option<Projection> {
    // Per leaf of the values, its field path from the values (empty for the values themselves),
    // whether it is a collection's keys, and the pairs of keys and the part beneath them it names.
    type Leaf = (Vec<SmolStr>, bool, Vec<(Predicate, Predicate)>);
    fn read(path: Vec<SmolStr>, guard: &TileGuard, leaves: &mut Vec<Leaf>) -> Option<()> {
        match guard {
            TileGuard::Scalar(paths) => leaves.push((path, false, split_beneath_keys(paths, 0))),
            TileGuard::Function(FunctionGuard::Domain(paths)) => {
                leaves.push((path, true, split_beneath_keys(paths, 0)))
            }
            TileGuard::Record(fields) => {
                for (name, field) in fields {
                    let mut deeper = path.clone();
                    deeper.push(name.clone());
                    read(deeper, field, leaves)?;
                }
            }
            _ => return None,
        }
        Some(())
    }
    let mut leaves: Vec<Leaf> = Vec::new();
    read(Vec::new(), node, &mut leaves)?;
    // The regions of keys every leaf names alike: refine by each leaf's keys in turn.
    let mut regions: Vec<(Predicate, Vec<Projection>)> =
        vec![(Predicate::True, vec![Projection::Nothing; leaves.len()])];
    for (at, (_, collection, pairs)) in leaves.iter().enumerate() {
        for (keys, part) in pairs {
            let part = match collection {
                true => Projection::admitting(part.clone()),
                false => match part.is_true() {
                    true => Projection::Everything,
                    false => return None,
                },
            };
            regions = regions
                .into_iter()
                .flat_map(|(region, parts)| {
                    let inside = region.intersect(keys);
                    let outside = region.minus(keys);
                    let mut with = parts.clone();
                    with[at] = with[at].union(&part);
                    [(inside, with), (outside, parts)]
                })
                .filter(|(region, _)| !region.is_false())
                .collect();
        }
    }
    /// The projection of the values the leaves under `prefix` name, field by field.
    fn values(leaves: &[Leaf], parts: &[Projection], prefix: &[SmolStr]) -> Projection {
        let under: Vec<usize> = (0..leaves.len())
            .filter(|&at| leaves[at].0.starts_with(prefix))
            .collect();
        if let [at] = under.as_slice()
            && leaves[*at].0.len() == prefix.len()
        {
            return parts[*at].clone();
        }
        let mut names: Vec<SmolStr> = under
            .iter()
            .filter_map(|&at| leaves[at].0.get(prefix.len()).cloned())
            .collect();
        names.sort();
        names.dedup();
        Projection::fields(
            names
                .into_iter()
                .map(|name| {
                    let mut deeper = prefix.to_vec();
                    deeper.push(name.clone());
                    let part = values(leaves, parts, &deeper);
                    (name, part)
                })
                .collect(),
            Projection::Nothing,
        )
    }
    Some(Projection::any_of(regions.into_iter().map(
        |(keys, parts)| Projection::within(level, keys, values(&leaves, &parts, &[])),
    )))
}

/// `paths`, a predicate over paths `relative` levels beneath keys of some level, read beneath the
/// keys `keys` admits: the same paths with those keys above them.
pub(crate) fn beneath_keys(paths: &Predicate, keys: &Predicate, relative: usize) -> Predicate {
    match paths {
        Predicate::False => Predicate::False,
        Predicate::Or(arms) => arms
            .iter()
            .map(|arm| beneath_keys(arm, keys, relative))
            .fold(Predicate::False, |all, arm| all.union(&arm)),
        _ if relative == 0 => Predicate::qualified(keys.clone(), paths.clone()),
        Predicate::Qualified { enclosing, here } => Predicate::qualified(
            beneath_keys(enclosing, keys, relative - 1),
            (**here).clone(),
        ),
        unqualified => Predicate::qualified(
            beneath_keys(&Predicate::True, keys, relative - 1),
            unqualified.clone(),
        ),
    }
}

/// `guard`, a guard of some values, with each predicate it holds read beneath the keys `keys`
/// admits ([`beneath_keys`]), `depth` codomain guards deep within the values.
fn guard_beneath_keys(guard: &TileGuard, keys: &Predicate, depth: usize) -> TileGuard {
    match guard {
        TileGuard::Or(arms) => TileGuard::flatten_or(
            arms.iter()
                .map(|arm| guard_beneath_keys(arm, keys, depth))
                .collect(),
        ),
        TileGuard::Function(FunctionGuard::Codomain(inner)) => TileGuard::Function(
            FunctionGuard::Codomain(Box::new(guard_beneath_keys(inner, keys, depth + 1))),
        ),
        TileGuard::Function(FunctionGuard::Domain(paths)) => {
            TileGuard::Function(FunctionGuard::Domain(beneath_keys(paths, keys, depth)))
        }
        TileGuard::Record(fields) => TileGuard::Record(
            fields
                .iter()
                .map(|(name, field)| (name.clone(), guard_beneath_keys(field, keys, depth)))
                .collect(),
        ),
        TileGuard::Scalar(paths) => TileGuard::Scalar(beneath_keys(paths, keys, depth)),
        TileGuard::Aggregation(paths) => TileGuard::Aggregation(beneath_keys(paths, keys, depth)),
    }
}

/// The shape of the collection levels and record fields `guards` name, as a tiling whose extents
/// are placeholders, for a difference that reads leaves ([`Leaves`]) where no tiling is at hand. A
/// record guard closed over its tiling lists every field, so the fields read off one are the
/// record's. `None` where two guards disagree on the shape at some step.
pub(crate) fn skeleton(guards: &[&TileGuard]) -> Option<Tiling> {
    fn placeholder() -> Tiling {
        Tiling::Scalar(Extent::Base(crate::interpreter::BaseType::Int))
    }
    fn merge(shape: Option<Tiling>, guard: &TileGuard) -> Option<Option<Tiling>> {
        Some(match guard {
            TileGuard::Or(arms) => {
                let mut shape = shape;
                for arm in arms {
                    shape = merge(shape, arm)?;
                }
                shape
            }
            TileGuard::Function(FunctionGuard::Domain(_)) => match shape {
                None => Some(Tiling::DataFunction {
                    domain: Extent::Base(crate::interpreter::BaseType::UInt),
                    codomain: Box::new(placeholder()),
                }),
                Some(Tiling::DataFunction { .. }) => shape,
                Some(_) => return None,
            },
            TileGuard::Function(FunctionGuard::Codomain(inner)) => match shape {
                None => Some(Tiling::DataFunction {
                    domain: Extent::Base(crate::interpreter::BaseType::UInt),
                    codomain: Box::new(merge(None, inner)?.unwrap_or_else(placeholder)),
                }),
                Some(Tiling::DataFunction { domain, codomain }) => {
                    let known = match *codomain {
                        Tiling::Scalar(_) => None,
                        other => Some(other),
                    };
                    Some(Tiling::DataFunction {
                        domain,
                        codomain: Box::new(merge(known, inner)?.unwrap_or_else(placeholder)),
                    })
                }
                Some(_) => return None,
            },
            TileGuard::Record(parts) => {
                let mut fields = match shape {
                    None => std::collections::HashMap::new(),
                    Some(Tiling::Record(fields)) => fields,
                    Some(_) => return None,
                };
                for (name, part) in parts {
                    let known = fields.remove(name);
                    let known = match known {
                        Some(Tiling::Scalar(_)) => None,
                        other => other,
                    };
                    fields.insert(
                        name.clone(),
                        merge(known, part)?.unwrap_or_else(placeholder),
                    );
                }
                Some(Tiling::Record(fields))
            }
            TileGuard::Scalar(_) => Some(shape.unwrap_or_else(placeholder)),
            TileGuard::Aggregation(_) => return None,
        })
    }
    let mut shape = None;
    for guard in guards {
        shape = merge(shape, guard)?;
    }
    shape
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

    /// The deepest level at or above `level` this declaration does not refuse: the level
    /// [`Projection::restated_by`] pulls a projection of `level`'s keys at. Every declaration
    /// restates the outermost keys, and one that refuses a level refuses every level beneath it,
    /// so every level beneath the answer down to `level` is refused.
    pub fn nearest(&self, level: CurryLevel) -> CurryLevel {
        let mut nearest = level;
        while self.refuses(nearest) {
            nearest = nearest
                .enclosing()
                .unwrap_or_else(|| unreachable!("every declaration restates the outermost keys"));
        }
        nearest
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
pub(super) fn qualifying_levels(keys: &Predicate) -> usize {
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

    /// Whether this tile holds only what `projection` names, or why it does not.
    ///
    /// A producer answers a pull with a tile inside the projection, so a cell outside it is a
    /// producer that ignored the guard. Rows deleted but not yet compacted are released, so
    /// they are not part of the answer.
    ///
    /// The completeness the tile states is bounded the same way: at each level it lies within what
    /// [`restrict_to`](Self::restrict_to) would leave stated there. A statement that a key outside
    /// the projection is complete, or absent, is one the pull did not ask for, and a consumer that
    /// merges answers would take it as settling a key it has not read.
    pub fn within(&self, projection: &Projection) -> Result<(), String> {
        self.cells_within(projection)?;
        self.statements_within(projection, None)
    }

    /// [`within`](Self::within) for a tile of a producer with `tiling`, whose outermost keys the
    /// tiling bounds: a statement of the outermost level outside the projection lies outside it
    /// only where it names a key of the tiling's domain. A union's domain carries its tags, so a
    /// statement of the arms past them names no key.
    pub fn within_over(&self, projection: &Projection, tiling: &Tiling) -> Result<(), String> {
        self.cells_within(projection)?;
        self.statements_within(projection, Some(tiling))
    }

    /// [`within`](Self::within) for the keys and cells the tile holds.
    fn cells_within(&self, projection: &Projection) -> Result<(), String> {
        match projection {
            part @ (Projection::Within { .. } | Projection::Or(_)) => {
                Projection::refuse_part_of_values("Tile::cells_within", part)
            }
            Projection::Everything => Ok(()),
            Projection::Fields { .. } => self.each_field_within(projection, Tile::cells_within),
            Projection::Nothing => {
                let mut live = self.clone();
                live.compact();
                match live.cell_count() {
                    0 => Ok(()),
                    _ => Err("it holds cells, and the projection names none".into()),
                }
            }
            Projection::Keys { level, keys } if *level == CurryLevel::OUTERMOST => {
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
            Projection::Keys { level, keys } => {
                if self.levels_held() <= level.index() {
                    return Err(format!(
                        "it has no collection at {level}, so it has no keys to project there"
                    ));
                }
                let mut live = self.clone();
                live.compact();
                for depth in 0..=level.index() {
                    let at = CurryLevel::new(depth);
                    let admits = match at == *level {
                        true => keys.clone(),
                        false => through_at(keys, *level, at),
                    };
                    if let Some(path) = live
                        .paths_at(at)
                        .into_iter()
                        .find(|path| !admits.contains_path(path))
                    {
                        return Err(format!(
                            "it holds the path {path:?}, which {admits:?} omits"
                        ));
                    }
                }
                Ok(())
            }
        }
    }

    /// [`within`](Self::within) for the completeness the tile states, closing the outermost
    /// level's over `tiling` where one is given ([`within_over`](Self::within_over)).
    fn statements_within(
        &self,
        projection: &Projection,
        tiling: Option<&Tiling>,
    ) -> Result<(), String> {
        if let Projection::Fields { .. } = projection {
            return self.each_field_within(projection, |field, projection| {
                field.statements_within(projection, None)
            });
        }
        let stated = self.stated_completeness();
        let allowed = match projection {
            part @ (Projection::Within { .. } | Projection::Or(_)) => {
                Projection::refuse_part_of_values("Tile::statements_within", part)
            }
            Projection::Everything => return Ok(()),
            Projection::Fields { .. } => unreachable!("a projection of fields returned above"),
            Projection::Nothing => vec![Predicate::False; stated.len()],
            Projection::Keys { level, keys } => {
                let mut cut = self.clone();
                cut.restrict_to_paths(*level, keys);
                cut.stated_completeness()
            }
        };
        debug_assert_eq!(
            stated.len(),
            allowed.len(),
            "a restriction keeps every collection level of the tile"
        );
        let outside = stated
            .iter()
            .zip(&allowed)
            .enumerate()
            .filter(|(_, (stated, allowed))| !allowed.subsumes(stated))
            .map(|(at, (stated, allowed))| (at, stated.minus(allowed)))
            .find(|(at, outside)| match (at, tiling) {
                (0, Some(tiling)) => names_a_key_of(outside, tiling),
                _ => true,
            });
        match outside {
            None => Ok(()),
            Some((_, outside)) => Err(format!(
                "it states {outside:?} complete, which the projection omits"
            )),
        }
    }

    /// `check` of each field of this record of values against the part of it `projection` names.
    fn each_field_within(
        &self,
        projection: &Projection,
        check: impl Fn(&Tile, &Projection) -> Result<(), String>,
    ) -> Result<(), String> {
        let Tile::Record { fields, .. } = self else {
            return Err("it is not a record, so it has no fields to project".into());
        };
        fields.iter().try_for_each(|(name, field)| {
            check(field, &projection.field(name)).map_err(|why| format!("its field {name}: {why}"))
        })
    }

    /// The completeness each collection level of this tile states, outermost first and a record's
    /// fields in name order.
    fn stated_completeness(&self) -> Vec<Predicate> {
        fn walk(tile: &Tile, out: &mut Vec<Predicate>) {
            match tile {
                Tile::DataFunction {
                    domain_predicate,
                    codomain,
                    ..
                } => {
                    out.push(domain_predicate.clone());
                    walk(codomain, out);
                }
                Tile::Record { fields, .. } => {
                    let mut names: Vec<_> = fields.keys().collect();
                    names.sort();
                    for name in names {
                        walk(&fields[name], out);
                    }
                }
                _ => {}
            }
        }
        let mut out = Vec::new();
        walk(self, &mut out);
        out
    }

    /// How many collection levels this tile holds from its root down.
    fn levels_held(&self) -> usize {
        match self {
            Tile::DataFunction { codomain, .. } => 1 + codomain.levels_held(),
            _ => 0,
        }
    }

    /// Cut this tile to `projection`.
    ///
    /// `Nothing` empties it at `tiling`, the tiling of the producer that made it.
    pub fn restrict_to(&mut self, projection: &Projection, tiling: &Tiling) {
        match projection {
            part @ (Projection::Within { .. } | Projection::Or(_)) => {
                Projection::refuse_part_of_values("Tile::restrict_to", part)
            }
            Projection::Everything => {}
            Projection::Nothing => *self = tiling.empty_tile(),
            Projection::Keys { level, keys } => self.restrict_to_paths(*level, keys),
            Projection::Fields { .. } => {
                let (Tile::Record { fields, .. }, Tiling::Record(tilings)) = (&mut *self, tiling)
                else {
                    panic!("{projection:?} cuts a record of values, got {tiling}")
                };
                for (name, field) in fields.iter_mut() {
                    field.restrict_to(&projection.field(name), &tilings[name]);
                }
            }
        }
    }
}

/// Whether `keys`, a region of the outermost keys of a producer with `tiling`, names a key its
/// domain has: under a union domain, a key of one of the tags it carries.
fn names_a_key_of(keys: &Predicate, tiling: &Tiling) -> bool {
    match (keys, tiling.domain_extent()) {
        (Predicate::Union { .. }, Some(Extent::Union(arms))) => arms
            .keys()
            .any(|tag| keys.under_tag(tag).is_none_or(|under| !under.is_false())),
        _ => !keys.is_false(),
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
        assert_eq!(
            Projection::of(&scalar),
            Ok(Projection::admitting(key(0))),
            "a scalar beneath a key is that key's whole value"
        );
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

    /// Whether `projection` names the path `path`.
    fn names(projection: &Projection, path: &[u64]) -> bool {
        let path: Vec<Value> = path.iter().map(|k| Value::UInt(*k)).collect();
        match projection {
            part @ (Projection::Within { .. } | Projection::Or(_)) => {
                Projection::refuse_part_of_values("names", part)
            }
            Projection::Everything => true,
            Projection::Nothing => false,
            Projection::Keys { level, keys } => {
                let deeper = path.len() - 1 - level.index();
                keys.descend(deeper).contains_path(&path)
            }
            Projection::Fields { .. } => unreachable!("a path of keys is no record's field"),
        }
    }

    fn field_of_keys(name: &str, k: u64) -> Projection {
        Projection::of_field(name, Projection::admitting(key(k)))
    }

    /// The union, intersection and difference of projections of a record of values go field by
    /// field, every field a projection does not list standing as its `rest`.
    #[test]
    fn projections_of_fields_combine_field_by_field() {
        let a = field_of_keys("a", 1);
        let b = field_of_keys("b", 2);
        let both = a.union(&b);
        assert_eq!(both.field("a"), Projection::admitting(key(1)));
        assert_eq!(both.field("b"), Projection::admitting(key(2)));
        assert_eq!(both.field("c"), Projection::Nothing);
        assert_eq!(both.intersect(&a), a);
        assert_eq!(both.minus(&a), b);
        assert_eq!(a.intersect(&b), Projection::Nothing);
        let rest = Projection::Everything.minus(&a);
        assert_eq!(
            rest.field("a"),
            Projection::Everything.minus(&Projection::admitting(key(1)))
        );
        assert_eq!(rest.field("b"), Projection::Everything);
        assert_eq!(rest.union(&a), Projection::Everything);
    }

    /// The algebra knows no field list, so a projection naming every field whole, or none of any,
    /// is normalized against the record's fields.
    #[test]
    fn a_projection_naming_every_field_is_normalized_against_the_fields() {
        let names = [SmolStr::new("a"), SmolStr::new("b")];
        let every = Projection::of_field("a", Projection::Everything)
            .union(&Projection::of_field("b", Projection::Everything));
        assert_ne!(every, Projection::Everything);
        assert_eq!(every.clone().over_fields(&names), Projection::Everything);
        let none = Projection::Everything.minus(&every);
        assert_eq!(none.over_fields(&names), Projection::Nothing);
        let one = field_of_keys("a", 1);
        assert_eq!(one.clone().over_fields(&names), one);
    }

    /// A projection of fields spells a record guard naming each field of the tiling, and that
    /// guard names it back.
    #[test]
    fn a_projection_of_fields_round_trips_through_its_record_guard() {
        let ints = Tiling::data_function(
            Extent::uint_range(8),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let tiling = Tiling::Record(
            [(SmolStr::new("a"), ints.clone()), (SmolStr::new("b"), ints)]
                .into_iter()
                .collect(),
        );
        let projection = field_of_keys("a", 1);
        let guard = projection.guard(&tiling);
        let TileGuard::Record(fields) = &guard else {
            panic!("a record's guard names its fields: {guard:?}")
        };
        assert!(fields["b"].is_empty(), "{guard:?}");
        assert_eq!(Projection::of(&guard), Ok(projection));
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

    /// Two projections meet at the deeper level, where a key of the level above is every path
    /// beneath it.
    #[test]
    fn projections_at_two_levels_meet_at_the_deeper() {
        let keys_0_and_1 = Projection::admitting(positions(0, 1));
        let row_0_to_1 = level_one(under(key(0), positions(0, 1)));
        let left = keys_0_and_1.minus(&row_0_to_1);
        for (path, named) in [
            ([0, 0], false),
            ([0, 1], false),
            ([0, 2], true),
            ([1, 0], true),
            ([2, 0], false),
        ] {
            assert_eq!(names(&left, &path), named, "{path:?} in {left:?}");
        }
        assert_eq!(keys_0_and_1.intersect(&row_0_to_1), row_0_to_1);
        assert_eq!(left.union(&row_0_to_1), keys_0_and_1);
        assert_eq!(row_0_to_1.minus(&keys_0_and_1), Projection::Nothing);
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

    /// A cut at level 1 keeps the admitted paths and the keys they run through. What a level
    /// above stated of a key partly cut is stated of its paths kept, at level 1.
    #[test]
    fn restricting_at_a_level_keeps_the_paths_admitted() {
        let paths = under(key(0), positions(1, 2)).union(&under(key(1), Predicate::True));
        let projection = level_one(paths.clone());
        let mut tile = three_rows();
        tile.restrict_to(&projection, &nested_tiling());
        let path = |k: u64, j: u64| vec![Value::UInt(k), Value::UInt(j)];
        assert_eq!(
            cells(&tile),
            [(path(0, 1), 11), (path(0, 2), 12), (path(1, 0), 20)]
        );
        assert_eq!(tile.within(&projection), Ok(()));
        let Tile::DataFunction {
            domain_predicate,
            codomain,
            ..
        } = &tile
        else {
            panic!("a collection")
        };
        assert_eq!(
            *domain_predicate,
            key(1),
            "key 1 alone is stated whole, every path beneath it being admitted"
        );
        let Tile::DataFunction {
            domain_predicate: rows_stated,
            ..
        } = &**codomain
        else {
            panic!("a nested collection")
        };
        for (k, j, stated) in [(0, 0, false), (0, 1, true), (0, 2, true), (2, 0, false)] {
            assert_eq!(
                rows_stated.contains_path(&path(k, j)),
                stated,
                "({k}, {j}) in {rows_stated:?}"
            );
        }
        assert!(
            three_rows()
                .within(&projection)
                .unwrap_err()
                .contains("[u2]"),
            "key 2 is on no admitted path"
        );
        let mut rows_0_and_1 = three_rows();
        rows_0_and_1.restrict_to_keys(&positions(0, 1));
        assert!(
            rows_0_and_1
                .within(&projection)
                .unwrap_err()
                .contains("[u0, u0]"),
            "the path (0, 0) is not admitted"
        );
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

    /// An operator that keeps the keys above its level pulls its input, for a projection of
    /// paths at or beneath that level, at the rows above it the paths run through, and at the
    /// projection itself otherwise.
    #[test]
    fn a_projection_beneath_an_operator_s_level_is_pulled_at_the_rows_above_it() {
        let paths =
            level_one(under(key(0), positions(1, 2)).union(&under(key(1), Predicate::True)));
        let rows = paths.above(CurryLevel::new(1));
        let both = Projection::admitting(positions(0, 1));
        assert_eq!(
            (rows.minus(&both), both.minus(&rows)),
            (Projection::Nothing, Projection::Nothing),
            "rows 0 and 1, which the paths run through: {rows:?}"
        );
        assert_eq!(paths.above(CurryLevel::new(2)), paths);
        assert_eq!(paths.above(CurryLevel::OUTERMOST), Projection::Everything);
        let keys = Projection::admitting(key(0));
        assert_eq!(keys.above(CurryLevel::new(1)), keys);
        assert_eq!(keys.above(CurryLevel::OUTERMOST), Projection::Everything);
    }

    /// A producer that refuses the level a projection names is pulled at the nearest level above
    /// that it restates: the paths `(0, 1, 0)` and `(1, 0, 0)` climb to the groups `(0, 1)` and
    /// `(1, 0)` past a producer that restates above level 2, and to the rows 0 and 1 past one
    /// that restates above level 1 or the outermost keys only.
    #[test]
    fn a_refused_projection_climbs_to_the_nearest_level_restated() {
        let [one, two] = [1, 2].map(CurryLevel::new);
        let paths = Projection::keys_at(
            two,
            under(under(key(0), key(1)), key(0)).union(&under(under(key(1), key(0)), key(0))),
        );
        let groups = level_one(under(key(0), key(1)).union(&under(key(1), key(0))));
        let rows = Projection::admitting(key(0).union(&key(1)));
        assert_eq!(paths.restated_by(&Restates::Every), paths);
        assert_eq!(paths.restated_by(&Restates::Above(two)), groups);
        assert_eq!(paths.restated_by(&Restates::Above(one)), rows);
        assert_eq!(paths.restated_by(&Restates::Outermost), rows);
        assert_eq!(groups.restated_by(&Restates::Above(two)), groups);
        // The level each declaration answers for level 2 is the level of the projection it
        // pulls (`Restates::nearest`).
        for (restates, level) in [
            (Restates::Every, two),
            (Restates::Above(two), one),
            (Restates::Above(one), CurryLevel::OUTERMOST),
            (Restates::Outermost, CurryLevel::OUTERMOST),
        ] {
            assert_eq!(restates.nearest(two), level, "{restates}");
            assert_eq!(
                paths.restated_by(&restates).level(),
                Some(level),
                "{restates}"
            );
        }
        // Every declaration restates the outermost keys, and a declaration above the outermost
        // level is the outermost keys only.
        for restates in [
            Restates::Every,
            Restates::Above(two),
            Restates::Above(CurryLevel::OUTERMOST),
            Restates::Outermost,
        ] {
            assert_eq!(
                restates.nearest(CurryLevel::OUTERMOST),
                CurryLevel::OUTERMOST,
                "{restates}"
            );
        }
        assert_eq!(
            Restates::Above(CurryLevel::OUTERMOST).nearest(two),
            CurryLevel::OUTERMOST
        );
        // A key named under every row leaves no keys above to climb to.
        assert_eq!(
            level_one(key(0)).restated_by(&Restates::Outermost),
            Projection::Everything
        );
        for whole in [Projection::Everything, Projection::Nothing] {
            assert_eq!(whole.restated_by(&Restates::Outermost), whole);
        }
    }

    /// A key every path beneath which a projection at level 2 admits keeps the outermost
    /// statement of it, though the region reaches it through an `Or` of enclosing paths only some
    /// of which are whole.
    #[test]
    fn a_key_whole_through_an_or_enclosing_keeps_its_statement() {
        // 0 ↦ {0 ↦ {0 ↦ 100}, 1 ↦ {0 ↦ 110}}, 1 ↦ {0 ↦ {0 ↦ 200}}, every level stated complete.
        let tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 2],
                ColumnValue::UInts(vec![0, 1, 0]),
                Box::new(Tile::grouped(
                    vec![0, 1, 2],
                    ColumnValue::UInts(vec![0, 0, 0]),
                    Box::new(Tile::Scalar(ColumnValue::Ints(vec![100, 110, 200]))),
                    Predicate::True,
                    BitSet::new(),
                )),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::data_function(
                Extent::uint_range(2),
                Tiling::data_function(
                    Extent::uint_range(1),
                    Tiling::Scalar(Extent::Base(BaseType::Int)),
                ),
            ),
        );
        let one_path = Projection::Keys {
            level: CurryLevel::new(2),
            keys: under(under(key(0), key(1)), key(0)),
        };
        let rest = Projection::Everything.minus(&one_path);
        let mut cut = tile;
        cut.restrict_to(&rest, &tiling);
        let Tile::DataFunction {
            domain_predicate, ..
        } = &cut
        else {
            panic!("a collection")
        };
        assert!(
            domain_predicate.contains(&Value::UInt(1)),
            "key 1 is whole in {rest:?}, and level 0 states {domain_predicate:?}"
        );
        assert_eq!(cut.within(&rest), Ok(()));
    }

    /// An unqualified region beneath the outermost keys names its keys under every key above,
    /// so a cut keeps every outermost key and the rows it admits.
    #[test]
    fn an_unqualified_region_beneath_the_outermost_keys_keeps_every_key_above() {
        let projection = level_one(key(0));
        let mut tile = three_rows();
        tile.restrict_to(&projection, &nested_tiling());
        let path = |k: u64, j: u64| vec![Value::UInt(k), Value::UInt(j)];
        assert_eq!(
            cells(&tile),
            [(path(0, 0), 10), (path(1, 0), 20), (path(2, 0), 30)]
        );
        assert_eq!(tile.within(&projection), Ok(()));
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

    /// A region beneath the outermost keys keeps its path, with the outermost key under the tag;
    /// keys under every outer key stand under every key of the arm.
    #[test]
    fn a_region_beneath_the_outermost_keys_is_tagged_at_its_outermost_key() {
        let tag = FieldKey::Index(0);
        let under_tag = |keys: Predicate| {
            Predicate::tagged(TagMap::from_arms(vec![(tag.clone(), keys)]), false)
        };
        assert_eq!(
            level_one(under(key(0), key(1))).tagged(&tag),
            level_one(under(under_tag(key(0)), key(1)))
        );
        assert_eq!(
            level_one(key(1)).tagged(&tag),
            level_one(under(under_tag(Predicate::True), key(1)))
        );
    }

    /// Closing drops an arm only where its level's extent is a finite range of positions none of
    /// which the arm names, and keeps the others as they are.
    #[test]
    fn closing_drops_only_the_arms_naming_no_key_of_their_level() {
        let ints = || Tiling::Scalar(Extent::Base(BaseType::Int));
        let finite = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::data_function(
                Extent::uint_range(2),
                Tiling::data_function(Extent::uint_range(1), ints()),
            ),
        );
        let open = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::data_function(
                Extent::uint_range(2),
                Tiling::data_function(Extent::Base(BaseType::UInt), ints()),
            ),
        );
        let past_the_end =
            CurryLevel::new(2).wrap_guard(domain(under(under(key(0), key(1)), positions(1, 5))));
        let inside = codomain(domain(under(key(1), key(0))));
        let both = TileGuard::flatten_or(vec![past_the_end.clone(), inside.clone()]);
        assert_eq!(both.clone().closed_over(&finite), inside);
        assert_eq!(both.clone().closed_over(&open), both);
        assert!(past_the_end.closed_over(&finite).is_empty());
    }

    /// A difference of a collection's keys and a scalar's names no region, though each reads as
    /// a projection where it is universal or empty.
    #[test]
    #[should_panic(expected = "the guard algebra has no difference")]
    fn a_difference_of_keys_and_a_scalar_panics() {
        crate::interpreter::tile_operators::guard_minus(
            &TileGuard::Scalar(Predicate::True),
            &domain(key(1)),
        );
    }

    /// The design's example: a breaker holding the keys 0 and 1 and released up to the path
    /// `(0, 1)` holds key 1 and row 0's paths past 1, and row 0 has none past 1 where its
    /// positions are `0..2`.
    #[test]
    fn a_difference_of_nested_guards_closes_over_the_row_s_extent() {
        use crate::interpreter::tile_operators::guard_minus;
        let held = domain(positions(0, 1));
        let released = codomain(domain(under(key(0), positions(0, 1))));
        let left = guard_minus(&held, &released);
        let region = Projection::of(&left).expect("a difference of keys is keys");
        for (path, named) in [
            ([0, 1], false),
            ([0, 2], true),
            ([1, 0], true),
            ([2, 0], false),
        ] {
            assert_eq!(names(&region, &path), named, "{path:?} in {left:?}");
        }
        let two_positions = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::data_function(
                Extent::uint_range(2),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        assert_eq!(left.clone().closed_over(&two_positions), domain(key(1)));
        assert_eq!(
            left.clone().closed_over(&nested_tiling()),
            left,
            "row 0 of positions 0..3 has the path (0, 2) left"
        );
        assert!(
            guard_minus(&codomain(domain(under(key(0), key(1)))), &released).is_empty(),
            "a released position is held no more"
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
    fn a_union_names_the_region_a_memo_has_read_or_must_read_again() {
        let (low, high) = (
            Projection::admitting(positions(0, 2)),
            Projection::admitting(positions(5, 7)),
        );
        assert_eq!(
            low.union(&high),
            Projection::admitting(positions(0, 2).union(&positions(5, 7)))
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

    /// A pull at keys drops the rows released before it from the record a debug build keeps of
    /// what each region last stated: a stream pulled and released one morsel at a time leaves
    /// the record holding the morsel last answered.
    #[test]
    #[cfg(debug_assertions)]
    fn a_pull_at_keys_drops_released_rows_from_the_completeness_record() {
        const ROWS: u64 = 16;
        const MORSEL: u64 = 4;
        let values: Vec<i64> = (0..ROWS as i64).collect();
        let (mut spy, _, _) =
            ProjectionSpy::new(ints_by_position(&values, true), ints_tiling(ROWS));
        for first in (0..ROWS).step_by(MORSEL as usize) {
            let morsel = keys_between(first, first + MORSEL - 1);
            assert_eq!(int_entries(&spy.get(morsel.clone())).len(), MORSEL as usize);
            spy.release(morsel);
            let Some(Tile::DataFunction { domain, .. }) = &*spy
                .base
                .last_output
                .read()
                .unwrap_or_else(PoisonError::into_inner)
            else {
                panic!("a pull records the collection it answered")
            };
            assert_eq!(
                domain.len(),
                MORSEL as usize,
                "the record holds the rows of the morsel just answered"
            );
        }
    }

    /// The double a test pulls an operator over answers the projection it is asked for, and
    /// logs the guards it received.
    #[test]
    fn the_projection_spy_answers_the_region_it_is_pulled_at_and_logs_it() {
        let tiling = ints_tiling(4);
        let (mut spy, pulled, released) =
            ProjectionSpy::new(ints_by_position(&[10, 20, 30, 40], true), tiling.clone());
        let middle = spy.read_in_pipeline(keys_between(1, 2));
        assert_eq!(int_entries(&middle), [(1, 20), (2, 30)]);
        spy.release(keys_between(1, 2));
        let rest = spy.read_in_pipeline(tiling.universal_guard());
        assert_eq!(int_entries(&rest), [(0, 10), (3, 40)]);
        assert_eq!(
            *pulled.read().unwrap_or_else(PoisonError::into_inner),
            [keys_between(1, 2), tiling.universal_guard()]
        );
        assert_eq!(
            *released.read().unwrap_or_else(PoisonError::into_inner),
            [keys_between(1, 2)]
        );
        // A pull that names nothing states nothing complete, which is withdrawal unless
        // the consumer released what it took.
        spy.release(tiling.universal_guard());
        assert_eq!(
            spy.read_in_pipeline(tiling.empty_guard()),
            tiling.empty_tile()
        );
    }

    #[test]
    fn a_tile_is_within_the_keys_it_holds_and_not_beyond() {
        let tile = ints_by_position(&[10, 20, 30, 40], false);
        let admitting = |first, last| Projection::admitting(positions(first, last));
        assert_eq!(tile.within(&admitting(0, 3)), Ok(()));
        assert_eq!(tile.within(&Projection::Everything), Ok(()));
        assert!(tile.within(&admitting(1, 2)).unwrap_err().contains("omits"));
        assert!(tile.within(&Projection::Nothing).is_err());
        assert_eq!(
            ints_tiling(4).empty_tile().within(&Projection::Nothing),
            Ok(())
        );
        // Released rows are no part of the answer, so their cells lie within any projection. What
        // the tile still states complete of them lies within a projection that names them only.
        let mut released = ints_by_position(&[10, 20], false);
        released.remove_guarded(keys_between(0, 1));
        assert_eq!(released.within(&admitting(0, 1)), Ok(()));
        assert!(released.within(&Projection::Nothing).is_err());
        assert!(released.within(&admitting(5, 6)).is_err());
        let scalar = Tile::Scalar(ColumnValue::Ints(vec![1]));
        assert!(scalar.within(&admitting(0, 3)).is_err());
    }

    /// A tile whose cells lie within the projection still answers outside it where it states keys
    /// beyond the projection complete: a key stated complete with no row is stated absent, which
    /// the pull did not ask about.
    #[test]
    fn a_tile_states_completeness_only_within_the_projection() {
        let admitting = |first, last| Projection::admitting(positions(first, last));
        let mut one = ints_by_position(&[10, 20, 30], true);
        assert!(
            one.within(&admitting(1, 1)).unwrap_err().contains("omits"),
            "its cells lie outside too"
        );
        one.restrict_to(&admitting(1, 1), &ints_tiling(3));
        assert_eq!(one.within(&admitting(1, 1)), Ok(()));
        // Only the completeness lies outside: no cells, and every key stated complete.
        let mut closed = ints_tiling(3).empty_tile();
        let Tile::DataFunction {
            domain_predicate, ..
        } = &mut closed
        else {
            panic!("a collection's empty tile is a collection")
        };
        *domain_predicate = Predicate::True;
        let outside = closed.within(&admitting(1, 1)).unwrap_err();
        assert!(outside.contains("complete"), "{outside}");
        assert!(closed.within(&Projection::Nothing).is_err());
        assert_eq!(closed.within(&Projection::Everything), Ok(()));
    }

    /// A producer that restates no projection beneath its outermost keys is caught by the `get`
    /// wrapper in a debug build when it is pulled at one (`TileProducer::restates`).
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "restates the outermost keys only")]
    fn get_rejects_a_pull_beneath_the_outermost_keys_of_a_producer_that_restates_none() {
        use crate::interpreter::tile_operators::test_helpers::TestTileProducer;
        let producer = TestTileProducer::new(three_rows(), nested_tiling());
        producer.get(codomain(domain(under(key(0), key(1)))));
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
        ignoring.read_in_pipeline(keys_between(1, 2));
    }
}
