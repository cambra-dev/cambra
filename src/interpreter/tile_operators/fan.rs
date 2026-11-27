#[cfg(test)]
use crate::interpreter::tile_operators::test_helpers::ReadInPipeline as _;
use smol_str::SmolStr;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex, PoisonError};

use crate::interpreter::tiling::KeysFollow;

use bit_set::BitSet;

use super::*;
use crate::interpreter::operator_graph::{value, value_at};
use crate::interpreter::{
    Consumer, Projection, RowIndex, SubscribeContext, Value, shared_consumer, tuple_field,
};

/// Pairs its operands at `level`, producing a collection carrying the levels standing above it
/// whose values are a record of what each operand holds there.
///
/// The standing levels are the ones every operand was applied over. That is a property of what
/// they were applied to and not of their own shapes, so the caller states `level`
/// ([`zip_arms_at`]). Beneath the standing levels the operands may differ, which is what lets
/// one of them hold a collection while its sibling holds a column.
///
/// Output fields are named `_0`, `_1`, … matching the input order.
pub struct Zip {
    /// Output tiling: the standing levels, with a `Record` where the operands' values sat.
    base: OperatorBase,
    /// Field names in input order, used when producing the output Record tile.
    names: Vec<SmolStr>,
    /// The input collections to pair.
    inputs: Vec<Arc<dyn TileOperator>>,
    /// The level the record sits at — the values every standing level is over.
    level: CurryLevel,
}

/// `tiling`'s levels above `level`, with `inner` at it.
pub fn with_values_at(tiling: &Tiling, level: CurryLevel, inner: Tiling) -> Tiling {
    if level == CurryLevel::OUTERMOST {
        return inner;
    }
    let Tiling::DataFunction { domain, codomain } = tiling else {
        unreachable!("{level} was counted off this tiling")
    };
    Tiling::DataFunction {
        domain: domain.clone(),
        codomain: Box::new(with_values_at(codomain, level.in_codomain(), inner)),
    }
}

impl Zip {
    /// Create a `Zip` pairing its operands at `level`, beneath the levels standing above it.
    ///
    /// `level` is the caller's to state, not something the operands say: the standing levels
    /// are the ones the operands were applied over. Two arms that agree beneath them (two
    /// projections of one grouped row, say) look pairable all the way down, and two that
    /// differ there are the collection-valued component case.
    pub fn new_at(names: Vec<SmolStr>, ops: Vec<Arc<dyn TileOperator>>, level: CurryLevel) -> Self {
        assert!(!ops.is_empty(), "Zip requires at least one input");
        assert!(
            level != CurryLevel::OUTERMOST,
            "Zip pairs under at least one standing level"
        );
        // The operands agree on the standing levels — they were applied over them — and may
        // differ below, which is what lets one hold a collection while its sibling holds a
        // column. Their runtime *presence* may still differ (one branch has emitted 0..3
        // while another has 0..2), which `ZipProducer::get_impl` intersects.
        for op in ops.iter() {
            for d in (0..level.index()).map(CurryLevel::new) {
                let (
                    Tiling::DataFunction { domain, .. },
                    Tiling::DataFunction { domain: other, .. },
                ) = (ops[0].tiling().values_at(d), op.tiling().values_at(d))
                else {
                    panic!(
                        "Zip pairs collections over the {} levels above it, got {} and {}",
                        level.index(),
                        ops[0].tiling(),
                        op.tiling()
                    )
                };
                assert_eq!(
                    domain, other,
                    "Zip's operands were applied over the same standing levels, so they agree \
                     on their keys at every one"
                );
            }
        }
        let record = Tiling::Record(
            names
                .iter()
                .zip(ops.iter())
                .map(|(name, op)| (name.clone(), op.tiling().values_at(level).clone()))
                .collect(),
        );
        let tiling = with_values_at(ops[0].tiling(), level, record);
        Self {
            base: OperatorBase::new(tiling),
            names,
            inputs: ops,
            level,
        }
    }
}

/// Build the right product combinator for the compiled arms, pairing at `level`, over the
/// levels standing above it.
///
/// A scalar-only product is a record of values ([`MakeRecord`]); anything with a collection
/// among its arms is a pointwise pairing over the levels the arms were applied over
/// ([`Zip`]). `level` is where the record lands, which the caller knows because it applied
/// them. See the "CCL types vs. tilings" section of
/// [`design-operators.md`](./design-operators.md) for why the same CCL-level `zip` compiles
/// to two different tile operators.
pub fn zip_arms_at(inputs: Vec<Arc<dyn TileOperator>>, level: CurryLevel) -> Arc<dyn TileOperator> {
    if inputs.iter().all(|op| op.tiling().is_scalar()) {
        return Arc::new(MakeRecord::new(inputs));
    }
    let names = (0..inputs.len()).map(tuple_field).collect();
    Arc::new(Zip::new_at(names, inputs, level))
}

/// Named-field variant of [`zip_arms_at`], for record literals.
pub fn zip_arms_named_at(
    inputs: Vec<(SmolStr, Arc<dyn TileOperator>)>,
    level: CurryLevel,
) -> Arc<dyn TileOperator> {
    if inputs.iter().all(|(_, op)| op.tiling().is_scalar()) {
        return Arc::new(MakeRecord::new_named(inputs));
    }
    // A lone arm over a collection has nothing to pair with, so its values are wrapped in place.
    let inputs = match <[_; 1]>::try_from(inputs) {
        Ok([(name, input)]) => return Arc::new(RecordWrap::new_at(name, input, level)),
        Err(inputs) => inputs,
    };
    let (names, ops) = inputs.into_iter().unzip();
    Arc::new(Zip::new_at(names, ops, level))
}

/// The values at `level` of its input, wrapped in a one-field record, under the levels
/// standing above it: [`Zip`] with one arm.
///
/// A zip pairs its arms by key. One arm is paired with nothing, so the keys pass through and
/// only the values change. Rows the input marks deleted pass through as they are, as they do
/// through [`VariantWrap`].
///
/// An input that is a bare value, with no collection above `level`, is a [`MakeRecord`]'s to
/// wrap, which [`zip_arms_named_at`] checks first.
pub struct RecordWrap {
    /// Output tiling: the standing levels, with a one-field `Record` where the values sat.
    base: OperatorBase,
    name: SmolStr,
    input: Arc<dyn TileOperator>,
    /// The level the record sits at — the values every standing level is over.
    level: CurryLevel,
}

impl RecordWrap {
    /// Wrap the values `input` holds at `level` as the field `name`.
    pub fn new_at(name: SmolStr, input: Arc<dyn TileOperator>, level: CurryLevel) -> Self {
        assert!(
            level != CurryLevel::OUTERMOST,
            "RecordWrap wraps the values of a collection, beneath at least one standing level"
        );
        let record = Tiling::Record(
            [(name.clone(), input.tiling().values_at(level).clone())]
                .into_iter()
                .collect(),
        );
        let tiling = with_values_at(input.tiling(), level, record);
        Self {
            base: OperatorBase::new(tiling),
            name,
            input,
            level,
        }
    }
}

impl TileOperator for RecordWrap {
    impl_operator_base!();

    fn inspect_annotation(&self) -> Option<String> {
        Some(format!("field {}", self.name))
    }

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
    }

    fn subscribe(
        self: Arc<Self>,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        let consumer = crate::interpreter::notifications::through_values(self.level, consumer);
        let input =
            self.input
                .clone()
                .subscribe(self.input.tiling().universal_guard(), consumer, cx);
        Box::new(RecordWrapProducer {
            base: ProducerBase::new(
                RecordWrapProducer::alloc_id(),
                self.tiling(),
                self.clone(),
                cx,
            ),
            name: self.name.clone(),
            level: self.level,
            input,
        })
    }
}

struct RecordWrapProducer {
    base: ProducerBase,
    name: SmolStr,
    level: CurryLevel,
    input: Box<dyn TileProducer>,
}

impl TileProducer for RecordWrapProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit("input", &mut *self.input);
    }

    /// It keeps its input's keys above its level and computes the values beneath it.
    fn restates(&self) -> Restates {
        Restates::Above(self.level)
    }

    /// Wrapping keeps the input's keys, so the input is pulled at the projection.
    fn get_impl(&self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection_for(self);
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let mut tile = self.input.get(projection.guard(self.input.tiling()));
        assert!(
            tile.is_data_function(),
            "RecordWrap: the input must be a function tile, got {tile:?}"
        );
        // Lift the values out, as `Zip` does, and put them back as the one field.
        let slot = tile.values_at_mut(self.level);
        let values = std::mem::replace(slot, Tile::record(HashMap::new()));
        *slot = Tile::record(HashMap::from([(self.name.clone(), values)]));
        tile
    }

    fn release_impl(&self, obsolete_guard: TileGuard) {
        let guard = match &obsolete_guard {
            g if g.is_universal() => self.input.tiling().universal_guard(),
            g if g.is_empty() => self.input.tiling().empty_guard(),
            // The standing levels name the same keys of the input; at `level` the input is the
            // one field of the record and takes that field's part.
            g => crate::interpreter::tiling::onto_record_field(
                g.clone(),
                self.level.index(),
                &self.name,
                self.input.tiling(),
            ),
        };
        self.input.release(guard);
    }
}

impl TileOperator for Zip {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        for (i, input) in self.inputs.iter().enumerate() {
            visit(value_at(i, &**input));
        }
    }

    fn subscribe(
        self: Arc<Self>,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        // Beneath rows each arm is one field of the pair, so a region of an arm names that field
        // of the rows it reaches and nothing of another arm's. At the
        // outermost level the pair is one record, whose regions widen.
        let beneath_rows = self.level != CurryLevel::OUTERMOST;
        let shared = shared_consumer(match beneath_rows {
            true => consumer,
            false => crate::interpreter::notifications::through_values(self.level, consumer),
        });
        // The arms share the rows' keys, beneath rows and at the outermost level alike, and a
        // row exists once every arm has delivered it (`AlignedInputs`).
        let rows = self
            .level
            .enclosing()
            .filter(|_| beneath_rows)
            .unwrap_or(CurryLevel::OUTERMOST);
        let aligned = crate::interpreter::notifications::AlignedInputs::new(rows, &self.inputs);
        let keys = crate::interpreter::notifications::InputRows::Keys;
        let inputs = self
            .inputs
            .iter()
            .zip(&self.names)
            .enumerate()
            // Every arm is pulled at the projection: the arms share the pair's keys.
            .map(|(arm, (input, name))| {
                let forward = forwarding_consumer_keeping_keys(&shared);
                let notifications = if beneath_rows {
                    aligned.zip_field(arm, name.clone(), forward)
                } else {
                    aligned.consumer(arm, keys, forward)
                };
                input
                    .clone()
                    .subscribe(input.tiling().universal_guard(), notifications, cx)
            })
            .collect();
        Box::new(ZipProducer {
            base: ProducerBase::new(ZipProducer::alloc_id(), self.tiling(), self.clone(), cx),
            names: self.names.clone(),
            level: self.level,
            state: Mutex::new(ZipState::new(self.inputs.len())),
            inputs,
        })
    }
}

/// `tile`, which stands beneath the rows `rows` admits, with each collection level in it
/// complete only beneath those rows.
fn qualify_beneath(tile: &mut Tile, rows: &Predicate) {
    match tile {
        Tile::Record { fields, .. } => fields.values_mut().for_each(|f| qualify_beneath(f, rows)),
        Tile::DataFunction {
            domain_predicate,
            codomain,
            ..
        } => {
            let beneath = Predicate::qualified(rows.clone(), Predicate::True);
            *domain_predicate = domain_predicate.intersect(&beneath);
            qualify_beneath(codomain, &beneath);
        }
        _ => {}
    }
}

/// Producer for [`Zip`]: pulls each input and assembles a record-codomain tile.
struct ZipProducer {
    base: ProducerBase,
    /// Field names in input order, used when producing the output Record tile.
    names: Vec<SmolStr>,
    /// Live input producers, in field order.
    inputs: Vec<Box<dyn TileProducer>>,
    /// The level the record sits at ([`Zip`]).
    level: CurryLevel,
    /// What a pull and a release both change, under one lock.
    // shared-state-ok: this producer's own state, which `get` and `release` change through `&self`
    // while several workers pull its pipeline; no other operator holds it.
    state: Mutex<ZipState>,
}

struct ZipState {
    /// The paths of the rows each arm has held at the pair's enclosing level, on any pull: an
    /// arm gives back only a row it held.
    held: Vec<HashSet<Vec<Value>>>,
    /// The keys of the pairs a flat zip has emitted, whose cells a consumer may give back
    /// field by field ([`ZipProducer::release_impl`]).
    emitted: Predicate,
    /// Per arm, the rows it deleted, which no consumer releases, so the next release gives them
    /// back.
    dropped_rows: HashMap<usize, TileGuard>,
}

impl ZipState {
    fn new(arms: usize) -> Self {
        Self {
            held: vec![HashSet::new(); arms],
            emitted: Predicate::False,
            dropped_rows: HashMap::new(),
        }
    }

    fn remember_dropped(&mut self, arm: usize, dropped: TileGuard) {
        self.held[arm].retain(|path| !dropped.covers_path(path));
        let released = match self.dropped_rows.remove(&arm) {
            Some(before) => before.union(&dropped),
            None => dropped,
        };
        self.dropped_rows.insert(arm, released);
    }
}

impl ZipProducer {
    /// Only a pair seen on a previous read can answer without consulting the other arms.
    fn matched_field(&self, projection: &Projection) -> Option<(usize, &SmolStr)> {
        let Projection::Within {
            level,
            keys,
            values,
        } = projection
        else {
            return None;
        };
        let Projection::Fields { fields, rest } = values.as_ref() else {
            return None;
        };
        if self.level.index() != 1
            || *level != CurryLevel::OUTERMOST
            || **rest != Projection::Nothing
            || fields.len() != 1
        {
            return None;
        }
        let matched = self
            .state
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .emitted
            .subsumes(keys);
        if !matched {
            return None;
        }
        self.names
            .iter()
            .enumerate()
            .find(|(_, name)| fields.contains_key(*name))
    }

    fn read_field(&self, guard: TileGuard, arm: usize, name: &SmolStr) -> Tile {
        let input = &self.inputs[arm];
        let part = crate::interpreter::tiling::onto_record_field(
            guard,
            self.level.index(),
            name,
            input.tiling(),
        );
        let mut answer = input.get(TileGuard::flatten_or(vec![part]));
        if let Some(dropped) = answer.deleted_keys_guard() {
            self.state
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .remember_dropped(arm, dropped);
        }
        answer.compact();
        answer.unfollow_values_at(self.level);
        let Tile::DataFunction { domain, .. } = &answer else {
            unreachable!("zip arm is keyed")
        };
        let record = self
            .tiling()
            .values_at(self.level)
            .empty_at_rows(domain.len());
        let slot = answer.values_at_mut(self.level);
        let field = std::mem::replace(slot, record);
        let Tile::Record { fields, .. } = slot else {
            unreachable!("zip values are records")
        };
        fields.insert(name.clone(), field);
        answer
    }
}

impl TileProducer for ZipProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        for (i, input) in self.inputs.iter().enumerate() {
            visit(&format!("_{i}"), &**input);
        }
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        for (i, input) in self.inputs.iter_mut().enumerate() {
            visit(&format!("_{i}"), &mut **input);
        }
    }

    /// It keeps its input's keys above its level and computes the values beneath it.
    fn restates(&self) -> Restates {
        Restates::Above(self.level)
    }

    fn input_level(&self, role: &str, level: CurryLevel) -> Option<CurryLevel> {
        // An exact field read can descend through the collection levels of its input.
        let arm: usize = role.strip_prefix('_')?.parse().ok()?;
        Some(if self.level.index() == 1 {
            level.max(CurryLevel::new(
                self.inputs[arm].tiling().levels().saturating_sub(1),
            ))
        } else {
            level
        })
    }

    fn get(&self, guard: TileGuard) -> Tile {
        self.checked_get(guard, &|guard| {
            let Some(rows) = guard.enclosing_rows() else {
                return self.get_impl(guard);
            };
            let projection = guard.projection_for(self);
            let mut answer = match self.matched_field(&projection) {
                Some((arm, name)) => self.read_field(guard, arm, name),
                None => self.get_impl(rows),
            };
            answer.restrict_to(&projection, self.tiling());
            answer
        })
    }

    /// The arms share the pair's keys, so each arm is pulled at the projection.
    fn get_impl(&self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection_for(self);
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        // The presence intersection below runs on every pull, inputs that already agree
        // included: N predicate intersections, N `to_remove` minuses and one `remove_guarded`
        // per input.
        //
        // An input's own deleted rows are dropped here and reach no consumer, so each input is
        // released through its own (below); a row only absent from another input may still
        // arrive there, so it is not.
        let (mut tiles, dropped): (Vec<Tile>, Vec<Option<TileGuard>>) = self
            .inputs
            .iter()
            .map(|i| {
                let mut tile = i.get(projection.guard(i.tiling()));
                let dropped = tile.deleted_keys_guard();
                // Presence is read off the key columns, so a key an arm has dropped is gone
                // from them first.
                tile.compact();
                (tile, dropped)
            })
            .unzip();
        // A scalar arm gives back each row's value once its consumer has taken it, while a
        // sibling holding a level keeps the row open (`src/interpreter/design-operators.md`,
        // "The release contract"). Such a row stays, holding no cell of that field; only a
        // row an arm lacks without having released it is one the arms disagree on.
        let released: Vec<Option<TileGuard>> = self
            .names
            .iter()
            .zip(self.inputs.iter())
            .map(|(name, input)| {
                // In canonical form, where a release of every cell under a key names the
                // key, which is what a path is read against.
                (!input.tiling().values_at(self.level).holds_a_level()).then(|| {
                    TileGuard::flatten_or(vec![crate::interpreter::tiling::onto_record_field(
                        self.obsolete_guard().clone(),
                        self.level.index(),
                        name,
                        input.tiling(),
                    )])
                })
            })
            .collect();
        // A release covering a row the arm never held, one its input never had, gives
        // nothing back: the row is absent from that arm, and so from the pair.
        // Held across the merge below, which reads no input: a pull on another thread waits
        // for the rows this one adds and the pairs it emits, and a release for the rows it gives
        // back.
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        if let Some(rows_level) = self.level.enclosing() {
            for (arm, tile) in tiles.iter().enumerate() {
                if tile.is_data_function() {
                    state.held[arm].extend(tile.paths_at(rows_level));
                }
            }
        }
        // A path above the rows was given back where the arm held a row beneath it.
        let gave_back = |arm: usize, path: &[Value]| {
            released[arm]
                .as_ref()
                .is_some_and(|guard| guard.covers_path(path))
                && state.held[arm].iter().any(|row| row.starts_with(path))
        };

        // Every level above the pair has to agree before anything pairs beneath it. The
        // arms are pulled from their own branches, so one may already hold a row under a
        // key the other has not reached, and beneath a standing level a key alone does not
        // name that row — it repeats across its siblings' groups. So the arms are aligned
        // over whole paths, level by level: each keeps the paths every arm holds or has given
        // back.
        //
        // Level by level rather than by extension, because a group may legitimately be
        // empty. A key holding nothing extends to no path of the level below, and reading
        // the levels above off the deepest one's paths would take that key away — where
        // what every arm agrees on is that the key is there and holds nothing.
        // Only where something stands above the pair's own enclosing level. One level up is
        // the flat case, which the presence intersection below already aligns over the
        // outermost keys; the paths each arm holds are recorded for every zip above, flat or
        // not, for what a release gives back.
        if let Some(above) = self.level.enclosing()
            && above.index() >= 1
            && tiles[0].is_data_function()
        {
            let present: Vec<HashSet<Vec<Value>>> = (0..=above.index())
                .map(|depth| {
                    let level = CurryLevel::new(depth);
                    let held: Vec<HashSet<Vec<Value>>> = tiles
                        .iter()
                        .map(|tile| tile.paths_at(level).into_iter().collect())
                        .collect();
                    held.iter()
                        .flatten()
                        .filter(|path| {
                            held.iter()
                                .enumerate()
                                .all(|(arm, paths)| paths.contains(*path) || gave_back(arm, path))
                        })
                        .cloned()
                        .collect()
                })
                .collect();
            let keep = |path: &[Value]| present[path.len() - 1].contains(path);
            for tile in tiles.iter_mut() {
                tile.retain_paths(above, &keep);
            }
        }

        match &tiles[0] {
            Tile::DataFunction { .. } => {
                // All inputs are DataFunction tiles, but they may differ in
                // which *actual rows* are present — one branch may have
                // emitted positions 0..3 while another has only 0..2 (or one
                // input's upstream release shrank its known region).  We
                // compute the intersection of every input's actually-present
                // positions (a `Predicate` built from each tile's `domain`
                // column), filter every tile down to it, and only then build
                // the combined codomain record.
                //
                // We separately intersect the inputs' `domain_predicate`s for
                // the *output* tile's predicate — that's purely forward-
                // looking finality, not what governs which rows to keep,
                // because a non-terminal input (e.g. an incremental data
                // source) carries `domain_predicate: False` alongside
                // fully-valid concrete rows.
                let mut presence: Option<Predicate> = None;
                let mut domain_pred: Option<Predicate> = None;
                // An outermost key an arm has given back stays where another arm holds it, at a
                // flat pair and beneath a standing level alike. Beneath a standing level the
                // alignment above has already kept the key's paths in the arms that hold it.
                let outermost: Vec<Value> = tiles
                    .iter()
                    .flat_map(|t| match t {
                        Tile::DataFunction { domain, .. } => {
                            (0..domain.len()).map(|k| domain.index_at(k)).collect()
                        }
                        _ => Vec::new(),
                    })
                    .collect();
                for (arm, t) in tiles.iter().enumerate() {
                    let Tile::DataFunction { domain, .. } = t else {
                        panic!("Zip: cannot mix function and non-function tiles")
                    };
                    let mut p = Predicate::from_column_value(domain);
                    if released[arm].is_some() {
                        let given: Vec<Predicate> = outermost
                            .iter()
                            .filter(|key| gave_back(arm, std::slice::from_ref(*key)))
                            .map(|key| Predicate::exactly(std::slice::from_ref(key)))
                            .collect();
                        if !given.is_empty() {
                            p = p.union(&Predicate::union_all(given));
                        }
                    }
                    presence = Some(match presence {
                        None => p,
                        Some(prev) => prev.intersect(&p),
                    });
                    let complete = if t.values_at(CurryLevel::new(1)).holds_a_level() {
                        t.complete_keys()
                    } else {
                        t.level_statement()
                    };
                    domain_pred = Some(match domain_pred {
                        None => complete.clone(),
                        Some(prev) => prev.intersect(&complete),
                    });
                }
                let presence = presence.unwrap();
                let intersect_pred = domain_pred.unwrap();

                // Filter each tile to the intersection of present positions
                // (compute "to_remove" as that tile's domain minus the
                // intersection, then drop those rows).
                let rows_level = self.level.enclosing().expect("a pair stands beneath a row");
                let mut filtered_tiles: Vec<Tile> = Vec::with_capacity(tiles.len());
                // A pair is complete where every arm's key is: each level above the pair
                // states the meet of the arms' statements, not the skeleton arm's alone,
                // which calls a row complete that another arm is still filling.
                let mut standing: Vec<Predicate> = Vec::new();
                for mut filtered in tiles.into_iter() {
                    for depth in 1..self.level.index() {
                        let stated = filtered.values_at(CurryLevel::new(depth)).level_statement();
                        match standing.get_mut(depth - 1) {
                            Some(meet) => *meet = meet.intersect(&stated),
                            None => standing.push(stated),
                        }
                    }
                    let Tile::DataFunction { domain, .. } = &filtered else {
                        unreachable!()
                    };
                    let to_remove = Predicate::from_column_value(domain).minus(&presence);
                    if to_remove.as_bool() != Some(false) {
                        filtered
                            .remove_guarded(TileGuard::Function(FunctionGuard::Domain(to_remove)));
                    }
                    filtered.compact();
                    filtered_tiles.push(filtered);
                }
                // The skeleton holds every row: an arm short of one has given it back.
                let skeleton_at = (0..filtered_tiles.len())
                    .max_by_key(|&arm| filtered_tiles[arm].paths_at(rows_level).len())
                    .expect("Zip has at least one input");
                let rows = filtered_tiles[skeleton_at].paths_at(rows_level);
                // An arm short of a row has given it back, and every other arm still holds it
                // or has given it back too; an arm holding a row the skeleton lacks would lose
                // that row's cells here.
                {
                    let held: HashSet<&Vec<Value>> = rows.iter().collect();
                    assert!(
                        filtered_tiles
                            .iter()
                            .all(|t| t.paths_at(rows_level).iter().all(|p| held.contains(p))),
                        "Zip: no arm holds every row the arms hold between them, so the rows \
                         two arms gave back separately have no skeleton to stand on"
                    );
                }
                let skeleton_levels: Vec<(Vec<RowIndex>, ColumnValue)> =
                    filtered_tiles[skeleton_at].key_levels()[..self.level.index()]
                        .iter()
                        .map(|(starts, keys)| (starts.to_vec(), (*keys).clone()))
                        .collect();
                let mut codomains: Vec<Tile> = Vec::with_capacity(filtered_tiles.len());
                let mut absent: HashMap<SmolStr, BitSet> = HashMap::new();
                // What a level inside a value states is the pair's to say only beneath the rows it
                // pairs: a row one arm states something about and the pair does not hold yet
                // arrives later.
                let paired =
                    Predicate::union_all(rows.iter().map(|p| Predicate::exactly(p)).collect());
                for (arm, filtered) in filtered_tiles.iter_mut().enumerate() {
                    let held = filtered.paths_at(rows_level);
                    // Lift the values out, leaving the chain of keys behind: what stays is
                    // the output's own shape, and every input has to agree on it.
                    let mut values = std::mem::replace(
                        filtered.values_at_mut(self.level),
                        Tile::record(HashMap::new()),
                    );
                    // A statement naming rows is narrowed to the paired ones; one naming none
                    // is about every row and says nothing a withheld row could contradict.
                    if values.holds_a_level() {
                        values.map_level_predicates(
                            &mut |depth, stated| match stated.qualifies() {
                                true => {
                                    stated.intersect(&Predicate::True.qualified_by(&paired, depth))
                                }
                                false => stated.clone(),
                            },
                        );
                    }
                    if held == rows {
                        // Presence is intersected over the outermost keys only, so arms that
                        // disagree beneath them would pair one arm's values under another's
                        // keys.
                        assert!(
                            filtered.key_levels()[..self.level.index()]
                                .iter()
                                .map(|(starts, keys)| (starts.to_vec(), (*keys).clone()))
                                .eq(skeleton_levels.iter().cloned()),
                            "Zip: inputs disagree on the {} levels above the pair, after \
                             aligning them: {skeleton_levels:?} against {filtered:?}",
                            self.level.index(),
                        );
                        codomains.push(values);
                        continue;
                    }
                    let at: HashMap<&Vec<Value>, usize> =
                        held.iter().enumerate().map(|(i, p)| (p, i)).collect();
                    let cells: Vec<Option<usize>> = rows
                        .iter()
                        .map(|path| {
                            let cell = at.get(path).copied();
                            assert!(
                                cell.is_some() || gave_back(arm, path),
                                "Zip: arm {arm} lacks row {path:?}, which it has not given back"
                            );
                            cell
                        })
                        .collect();
                    if let Some(order) = cells.iter().copied().collect::<Option<Vec<_>>>() {
                        codomains.push(values.select_rows(&order));
                        continue;
                    }
                    let (aligned, missing) = align_keyless(values, &cells);
                    if let Some(missing) = missing {
                        absent.insert(self.names[arm].clone(), missing);
                    }
                    codomains.push(aligned);
                }
                let skeleton = filtered_tiles.swap_remove(skeleton_at);

                let names = &self.names;
                let codomain_record = Tile::Record {
                    fields: codomains
                        .into_iter()
                        .enumerate()
                        .map(move |(i, cv)| (names[i].clone(), cv))
                        .collect(),
                    absent,
                };
                // A row an arm deleted reaches no consumer, so no consumer releases it: the arm
                // gives it back here and stops tracking it.
                for (arm, dropped) in dropped.into_iter().enumerate() {
                    if let Some(dropped) = dropped {
                        state.remember_dropped(arm, dropped);
                    }
                }
                let mut out = skeleton;
                *out.values_at_mut(self.level) = codomain_record;
                // The pair's enclosing level holds a record of the arms' values beneath it, which
                // no key of that level follows; the levels above it stand over the skeleton
                // arm's keys, stated as the arms' meet, and keep its flag.
                let enclosing = self.level.enclosing().expect("a pair stands beneath a row");
                if let Tile::DataFunction {
                    keys_follow_beneath,
                    ..
                } = out.values_at_mut(enclosing)
                {
                    *keys_follow_beneath = KeysFollow::DoesNot;
                }
                for (at, meet) in standing.into_iter().enumerate() {
                    let Tile::DataFunction {
                        domain_predicate, ..
                    } = out.values_at_mut(CurryLevel::new(at + 1))
                    else {
                        unreachable!("the levels above the pair are collections")
                    };
                    *domain_predicate = meet;
                }
                let Tile::DataFunction {
                    domain_predicate, ..
                } = &mut out
                else {
                    unreachable!("the skeleton is one of the collection inputs")
                };
                *domain_predicate = intersect_pred;
                // An arm's statement about the levels beneath the pair holds beneath the rows
                // that arm holds, and the pair holds only the rows every arm does: beneath a
                // row one arm has reached and another has not, the pair has promised nothing
                // yet (`src/interpreter/design-operators.md`, "The completeness contract").
                // So each level beneath the pair is complete only beneath the rows the pair
                // holds or calls complete.
                if self
                    .inputs
                    .iter()
                    .any(|i| i.tiling().values_at(self.level).holds_a_level())
                {
                    let Tile::DataFunction {
                        domain,
                        domain_predicate,
                        ..
                    } = out.values_at(rows_level)
                    else {
                        unreachable!("the pair stands beneath a collection")
                    };
                    let held = match rows_level.index() {
                        0 => Predicate::from_column_value(domain),
                        _ => Predicate::union_all(
                            out.paths_at(rows_level)
                                .iter()
                                .map(|path| Predicate::exactly(path))
                                .collect(),
                        ),
                    };
                    let vouched = held.union(domain_predicate);
                    qualify_beneath(out.values_at_mut(self.level), &vouched);
                }
                // The arms keep the rows a consumer released only a field of
                // ([`ZipProducer::release_impl`]), so those cells are taken back out here.
                if !self.obsolete_guard().is_empty() {
                    out.remove_guarded(self.obsolete_guard());
                }
                if let (1, Tile::DataFunction { domain, .. }) = (self.level.index(), &out) {
                    state.emitted = state.emitted.union(&Predicate::from_column_value(domain));
                }
                drop(state);
                // The completeness intersected above is each arm's, which an arm restating fewer
                // levels than the projection's states over the region it was pulled at, so it is
                // cut to the projection.
                out.restrict_to(&projection, self.tiling());
                out
            }
            other => panic!("Zip: every input must be a function tile, got {other:?}"),
        }
    }

    fn release_impl(&self, obsolete_guard: TileGuard) {
        let (dropped_rows, emitted) = {
            let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
            (
                std::mem::take(&mut state.dropped_rows),
                state.emitted.clone(),
            )
        };
        for (arm, dropped) in dropped_rows {
            self.inputs[arm].release(dropped);
        }

        let level = self.level.index();
        let pair = self.base.tiling.values_at(self.level).empty_guard();
        // An arm takes the pairs released whole, and a field of a pair it has emitted. A
        // consumer done with one field may be done with it at every row, the rows the pair
        // has not paired yet included, and an arm releasing a row's cells gives the row back:
        // the pair would lose a row it still pairs with the arms that have not reached it.
        // The released fields of the rest are taken out of the pair instead. Beneath standing
        // levels only whole pairs are passed on.
        let delivered = match level {
            1 => obsolete_guard.intersect(&TileGuard::Function(FunctionGuard::Domain(emitted))),
            _ => self.base.tiling.empty_guard(),
        };
        let whole = TileGuard::flatten_or(vec![whole_pair_rows(
            self.obsolete_guard().clone(),
            0,
            level,
            &pair,
        )]);
        let released = TileGuard::flatten_or(vec![whole.clone(), delivered]);
        for (name, input) in self.names.iter().zip(self.inputs.iter()) {
            let guard = match &released {
                g if g.is_universal() => input.tiling().universal_guard(),
                g if g.is_empty() => input.tiling().empty_guard(),
                // A zip pairs its arms at the same positions, so the levels above the pair
                // name the same keys of every arm; at the pair each arm is one field of the
                // record, and takes that field's part.
                //
                // An arm whose values hold a level gives up a key only where the zip gave it
                // up. A scalar arm gives back each row it was released, and the zip keeps the
                // row (`gave_back` in `get_impl`); an arm holding a level keeps its rows open
                // itself, so one whose whole value a consumer released (a field `SelectField`
                // does not read, say) still holds the keys later rows pair on. In canonical form
                // that whole value is the key, so it is kept back here.
                g => {
                    let field = crate::interpreter::tiling::onto_record_field(
                        g.clone(),
                        level,
                        name,
                        input.tiling(),
                    );
                    let holds_a_level = input.tiling().values_at(self.level).holds_a_level();
                    match level.checked_sub(1) {
                        Some(keys) if holds_a_level => limit_keys_at(
                            TileGuard::flatten_or(vec![field]),
                            keys,
                            &keys_at(&TileGuard::flatten_or(vec![g.clone()]), keys),
                        ),
                        _ => field,
                    }
                }
            };
            input.release(guard);
        }
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        for paths in &mut state.held {
            paths.retain(|path| !whole.covers_path(path));
        }
        if whole.is_universal() {
            state.emitted = Predicate::False;
        } else if let TileGuard::Function(FunctionGuard::Domain(keys)) = &whole {
            state.emitted = state.emitted.minus(keys);
        }
    }
}

/// The part of `guard`, a release of a [`Zip`]'s output, that covers whole pairs: the keys it
/// releases above the pair, and the pairs it releases in full, without the fields it releases
/// of a pair it keeps. `depth` counts the levels `guard` stands beneath, the pair standing
/// beneath `level`, and `empty` is the release of no pair.
fn whole_pair_rows(guard: TileGuard, depth: usize, level: usize, empty: &TileGuard) -> TileGuard {
    match guard {
        TileGuard::Or(arms) => TileGuard::flatten_or(
            arms.into_iter()
                .map(|arm| whole_pair_rows(arm, depth, level, empty))
                .collect(),
        ),
        g if depth == level => match g.is_universal() {
            true => g,
            false => empty.clone(),
        },
        TileGuard::Function(FunctionGuard::Codomain(inner)) => TileGuard::Function(
            FunctionGuard::Codomain(Box::new(whole_pair_rows(*inner, depth + 1, level, empty))),
        ),
        g => g,
    }
}

/// The keys `guard`, in canonical form, names at `depth` codomain steps.
fn keys_at(guard: &TileGuard, depth: usize) -> Predicate {
    match guard {
        TileGuard::Or(arms) => arms
            .iter()
            .fold(Predicate::False, |acc, arm| acc.union(&keys_at(arm, depth))),
        TileGuard::Function(FunctionGuard::Codomain(inner)) if depth > 0 => {
            keys_at(inner, depth - 1)
        }
        TileGuard::Function(FunctionGuard::Domain(pred)) => pred.descend(depth),
        _ => Predicate::False,
    }
}

/// `guard`, in canonical form, naming at `depth` codomain steps only the keys `released`
/// names; what it names beneath the keys is left as it is.
fn limit_keys_at(guard: TileGuard, depth: usize, released: &Predicate) -> TileGuard {
    match guard {
        TileGuard::Or(arms) => TileGuard::flatten_or(
            arms.into_iter()
                .map(|arm| limit_keys_at(arm, depth, released))
                .collect(),
        ),
        TileGuard::Function(FunctionGuard::Codomain(inner)) if depth > 0 => TileGuard::Function(
            FunctionGuard::Codomain(Box::new(limit_keys_at(*inner, depth - 1, released))),
        ),
        TileGuard::Function(FunctionGuard::Domain(pred)) => {
            CurryLevel::new(depth).wrap_guard(TileGuard::Function(FunctionGuard::Domain(
                pred.descend(depth).intersect(released),
            )))
        }
        other => other,
    }
}

/// A value with no level of its own, rearranged onto the rows `cells` names: row `r` takes
/// the value's cell `cells[r]`, and holds none where that is `None`. A scalar answers the
/// rows it holds none at, for the record it is a field of to state; a record states its own
/// fields'.
fn align_keyless(values: Tile, cells: &[Option<usize>]) -> (Tile, Option<BitSet>) {
    match values {
        Tile::Scalar(column) => {
            let picked: Vec<usize> = cells.iter().flatten().copied().collect();
            let missing: BitSet = (0..cells.len()).filter(|&r| cells[r].is_none()).collect();
            let n = picked.len();
            (
                Tile::Scalar(column.select_indices(picked.into_iter(), n)),
                (!missing.is_empty()).then_some(missing),
            )
        }
        Tile::Record { fields, absent } => {
            assert!(
                absent.is_empty(),
                "Zip: a record arm holding no cell of a field at a row is aligned field by \
                 field, which this one already is: {absent:?}"
            );
            let mut absent = HashMap::new();
            let fields = fields
                .into_iter()
                .map(|(name, field)| {
                    let (aligned, missing) = align_keyless(field, cells);
                    if let Some(missing) = missing {
                        absent.insert(name.clone(), missing);
                    }
                    (name, aligned)
                })
                .collect();
            (Tile::Record { fields, absent }, None)
        }
        other => panic!(
            "Zip: an arm short of rows the others hold gave them back, which only an arm \
             holding no level does: {other:?}"
        ),
    }
}

/// Build a product value from N components: a `Tile::Record` whose fields are `_0`, `_1`,
/// … for a tuple, or the source's own names for a record.
///
/// [`SelectField`] is the eliminator. See `src/interpreter/design-operators.md`, "A product
/// value is a record of tiles".
pub struct MakeRecord {
    base: OperatorBase,
    /// Field names in input order, used when producing `Tile::Record` tiles.
    names: Vec<SmolStr>,
    inputs: Vec<Arc<dyn TileOperator>>,
}

impl MakeRecord {
    /// Construct a `MakeRecord` whose fields are `inputs`, named `_0`, `_1`, … in order.
    ///
    /// Each field keeps its input's tiling, whatever that is.
    pub fn new(inputs: Vec<Arc<dyn TileOperator>>) -> Self {
        assert!(!inputs.is_empty(), "MakeRecord requires at least one input");
        let names = (0..inputs.len()).map(tuple_field).collect();
        Self::new_impl(names, inputs)
    }

    /// Construct a `MakeRecord` with explicit named fields for record literals.
    ///
    /// Like [`Self::new`] but uses the caller-supplied field names instead of
    /// the synthetic `_0`, `_1`, … names used for tuples.
    pub fn new_named(inputs: Vec<(SmolStr, Arc<dyn TileOperator>)>) -> Self {
        assert!(!inputs.is_empty(), "MakeRecord requires at least one input");
        let (names, ops) = inputs.into_iter().unzip();
        Self::new_impl(names, ops)
    }

    fn new_impl(names: Vec<SmolStr>, inputs: Vec<Arc<dyn TileOperator>>) -> Self {
        let tiling = Tiling::Record(
            names
                .iter()
                .zip(inputs.iter())
                .map(|(name, op)| (name.clone(), op.tiling().clone()))
                .collect(),
        );
        Self {
            base: OperatorBase::new(tiling),
            names,
            inputs,
        }
    }
}

impl TileOperator for MakeRecord {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        for (i, input) in self.inputs.iter().enumerate() {
            visit(value_at(i, &**input));
        }
    }

    fn fields_arrive_by_push(&self) -> Option<Vec<(SmolStr, bool)>> {
        Some(
            self.names
                .iter()
                .zip(&self.inputs)
                .map(|(name, input)| (name.clone(), input.keys_arrive_by_push()))
                .collect(),
        )
    }

    fn subscribe(
        self: Arc<Self>,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        let shared = shared_consumer(consumer);
        Box::new(MakeRecordProducer {
            base: ProducerBase::new(
                MakeRecordProducer::alloc_id(),
                self.tiling(),
                self.clone(),
                cx,
            ),
            names: self.names.clone(),
            // A region of an operand names that field of the record.
            inputs: self
                .names
                .iter()
                .zip(&self.inputs)
                .map(|(name, input)| {
                    input.clone().subscribe(
                        input.tiling().universal_guard(),
                        crate::interpreter::notifications::fielding(
                            name.clone(),
                            self.names.clone(),
                            forwarding_consumer_keeping_keys(&shared),
                        ),
                        cx,
                    )
                })
                .collect(),
        })
    }
}

/// Producer for [`MakeRecord`]: pulls every operand and builds a `Tile::Record` of their
/// tiles.
struct MakeRecordProducer {
    base: ProducerBase,
    names: Vec<SmolStr>,
    inputs: Vec<Box<dyn TileProducer>>,
}

impl TileProducer for MakeRecordProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        for (i, input) in self.inputs.iter().enumerate() {
            visit(&format!("{i}"), &**input);
        }
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        for (i, input) in self.inputs.iter_mut().enumerate() {
            visit(&format!("{i}"), &mut **input);
        }
    }

    /// A record of values has no keys to project: the projection names each field's part, and
    /// each operand is pulled at its field's part. A guard naming keys is a consumer's bug.
    fn get_impl(&self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if let Projection::Keys { .. } = projection {
            panic!(
                "{} is a record of values, which has no keys to project: {projection_guard:?}",
                self.name()
            );
        }
        // An operand withholds what [`Self::release_impl`] told it a consumer finished with, so a
        // field that settled early is not re-delivered.
        let fields: HashMap<SmolStr, Tile> = self
            .names
            .iter()
            .zip(self.inputs.iter())
            .map(|(name, input)| {
                let field = projection.field(name);
                let tile = match field {
                    Projection::Nothing => input.tiling().empty_tile(),
                    field => input.get(field.guard(input.tiling())),
                };
                (name.clone(), tile)
            })
            .collect();
        Tile::record(fields)
    }

    fn release_impl(&self, obsolete_guard: TileGuard) {
        // A record guard names one guard per field, and each goes to that field's operand.
        // A later pull re-reads every operand, and each withholds what it was told.
        match &obsolete_guard {
            g if g.is_empty() => {}
            TileGuard::Record(fields) => {
                for (name, input) in self.names.iter().zip(self.inputs.iter()) {
                    if let Some(field) = fields.get(name) {
                        input.release(field.clone());
                    }
                }
            }
            g if g.is_universal() => {
                for input in self.inputs.iter() {
                    input.release(input.tiling().universal_guard());
                }
            }
            other => panic!(
                "{} cannot honor the release guard {other:?}, which does not name its fields",
                self.name()
            ),
        }
    }
}

/// Pick one field out of a **product value**, or one component out of a record codomain:
/// the eliminator for [`MakeRecord`], handing back that field's tile.
///
/// The `RecordField` application is the other projection, and it reads a record one row
/// at a time, so every field must fit in a column. See
/// `src/interpreter/design-operators.md`, "A product value is a record of tiles".
pub struct SelectField {
    base: OperatorBase,
    /// The product whose field this selects.
    input: Arc<dyn TileOperator>,
    /// The field's name — `_0`, `_1`, … for a tuple.
    name: SmolStr,
}

/// Restate a selector's release at field `name` in the product `tiling`.
/// Enclosing keys release those records whole. Unused collection fields remain available at
/// later rows: a zip needs their presence to retain each record. Unused keyless fields can be
/// released whole because a zip represents their missing cells. A bare product has no enclosing
/// rows, so its unused fields are released whole.
fn guard_at_field(tiling: &Tiling, name: &str, guard: TileGuard) -> TileGuard {
    fn at_field(tiling: &Tiling, name: &str, guard: TileGuard, under_keys: bool) -> TileGuard {
        match tiling {
            Tiling::DataFunction { codomain, .. } => match guard {
                g if g.is_universal() => tiling.universal_guard(),
                TileGuard::Function(FunctionGuard::Codomain(inner)) => TileGuard::Function(
                    FunctionGuard::Codomain(Box::new(at_field(codomain, name, *inner, true))),
                ),
                TileGuard::Or(arms) => TileGuard::flatten_or(
                    arms.into_iter()
                        .map(|arm| at_field(tiling, name, arm, under_keys))
                        .collect(),
                ),
                keys @ TileGuard::Function(FunctionGuard::Domain(_)) => {
                    let field = select_field_tiling(codomain, name).empty_guard();
                    TileGuard::flatten_or(vec![
                        keys,
                        TileGuard::Function(FunctionGuard::Codomain(Box::new(at_field(
                            codomain, name, field, true,
                        )))),
                    ])
                }
                other => unreachable!("a collection's guard is a function guard, got {other:?}"),
            },
            Tiling::Record(fields) => {
                let release_unused = !under_keys || guard.is_universal();
                TileGuard::Record(
                    fields
                        .iter()
                        .map(|(field, tiling)| {
                            let released = if field == name {
                                guard.clone()
                            } else if release_unused || !tiling.holds_a_level() {
                                tiling.universal_guard()
                            } else {
                                tiling.empty_guard()
                            };
                            (field.clone(), released)
                        })
                        .collect(),
                )
            }
            other => unreachable!("SelectField's input holds a record, got {other}"),
        }
    }
    at_field(tiling, name, guard, false)
}

/// Replace the record at a chain's deepest values with its `name` field, keeping the levels.
fn select_field_tiling(tiling: &Tiling, name: &str) -> Tiling {
    match tiling {
        Tiling::DataFunction { domain, codomain } => Tiling::DataFunction {
            domain: domain.clone(),
            codomain: Box::new(select_field_tiling(codomain, name)),
        },
        Tiling::Record(fields) => fields.get(name).cloned().unwrap_or_else(|| {
            panic!("SelectField({name}) over a product with no such field; got {tiling}")
        }),
        other => panic!(
            "SelectField reads a product value, so its input's values are a record; got {other}"
        ),
    }
}

impl SelectField {
    /// Construct a `SelectField` for `name` over a product value.
    ///
    /// The record may sit under any number of levels — a collection of products is one
    /// product per key — and the selection keeps them, because what it replaces is the
    /// record where it stands.
    ///
    /// # Panics
    ///
    /// Panics unless `input`'s deepest values are a `Tiling::Record` holding `name`.
    pub fn new(input: Arc<dyn TileOperator>, name: impl Into<SmolStr>) -> Self {
        let name = name.into();
        let tiling = select_field_tiling(input.tiling(), &name);
        Self {
            base: OperatorBase::new(tiling),
            input,
            name,
        }
    }
}

impl TileOperator for SelectField {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
    }

    fn subscribe(
        self: Arc<Self>,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        // A stream of records is pulled at the projection, and a record of values at the part of
        // the selected field the projection names, whose regions are the selected field's part of
        // the record's.
        let consumer = match self.input.tiling().is_data_function() {
            true => crate::interpreter::notifications::selecting_field_beneath_keys(
                self.name.clone(),
                consumer,
            ),
            false => {
                crate::interpreter::notifications::selecting_field(self.name.clone(), consumer)
            }
        };
        // An intent may only widen on its way upstream, so the input is asked for all of
        // it. [`guard_at_field`] narrows, which is sound for a release and not here.
        let input_tiling = self.input.tiling().clone();
        let input_producer =
            self.input
                .clone()
                .subscribe(input_tiling.universal_guard(), consumer, cx);
        Box::new(SelectFieldProducer {
            dropped_rows: Default::default(),
            base: ProducerBase::new(
                SelectFieldProducer::alloc_id(),
                self.tiling(),
                self.clone(),
                cx,
            ),
            input: input_producer,
            name: self.name.clone(),
            input_tiling,
        })
    }

    /// The input's correlation, one step further into the record: what the `RecordField`
    /// application reports for the same projection.
    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        let mut correlation = self.input.result_correlation()?;
        correlation.push(TilePathStep::Record(self.name.clone()));
        Some(correlation)
    }
}

/// Producer for [`SelectField`].
///
/// **A pull of a record of values names the selected field.** A [`Memo`] over the record answers
/// a pull from what it has read, so a pull naming one field reads only what the memo was consumed
/// at. Every field reaches the memo: a field's change and completion arrive as that part of the
/// record (`notifications::fielding`), and a field nothing pushes is read at the start
/// (`src/interpreter/design-dispatcher.md`, "Running a compiled program"). A pull of a stream of
/// records may name keys of the stream the field sits under, since a key brings every field of
/// its record. A release names this field's part; enclosing keys release their whole records
/// ([`guard_at_field`]).
struct SelectFieldProducer {
    dropped_rows: DroppedRows,
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    name: SmolStr,
    /// The product's tiling, for naming this field in a guard travelling upward.
    input_tiling: Tiling,
}

impl SelectFieldProducer {
    fn at_field(&self, guard: TileGuard) -> TileGuard {
        guard_at_field(&self.input_tiling, &self.name, guard)
    }
}

impl TileProducer for SelectFieldProducer {
    impl_producer_base!();

    /// A stream of records keeps its keys at every level above the record, so its input is pulled
    /// at a projection there; the levels of a field that is itself a collection are inside the
    /// record's values. A product of collections is pulled at the selected field's part, at any
    /// level of the field.
    fn restates(&self) -> Restates {
        match self.input.tiling().is_data_function() {
            true => Restates::Above(CurryLevel::values_of(self.input.tiling())),
            false => Restates::Every,
        }
    }

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit("input", &mut *self.input);
    }

    /// A stream of records keeps its keys under the field, so the input is pulled at the
    /// projection. A product of collections has no keys of its own: it is pulled at the selected
    /// field's part of the projection ([`Projection::of_field`]), and the field cut after.
    fn get_impl(&self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection_for(self);
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let input_guard = match self.input.tiling().is_data_function() {
            true => projection.guard(self.input.tiling()),
            false => {
                Projection::of_field(&self.name, projection.clone()).guard(self.input.tiling())
            }
        };
        let mut tile = self.input.get(input_guard);
        // A row holding no cell of this field gave that cell back to this reader's release
        // (`Tile::Record`'s `absent`), and the field is the whole value here, so the row
        // leaves with it. The record gathers its other fields' cells along.
        let missing = match tile.deepest_values() {
            Tile::Record { absent, .. } => absent.get(&self.name).cloned(),
            _ => None,
        };
        if let Some(missing) = missing {
            let rows = tile.deepest_values().rows();
            let level = CurryLevel::innermost_of(self.input.tiling())
                .expect("only a record beneath a level holds no cell at a row");
            tile.values_at_mut(level).retain_keys(
                &(0..rows)
                    .map(|row| !missing.contains(row))
                    .collect::<Vec<bool>>(),
            );
        }
        // The record stands at the chain's deepest values, so the field takes its place and
        // every level above it is left where it was.
        let slot = tile.deepest_values_mut();
        let Tile::Record { mut fields, .. } = std::mem::replace(slot, Tile::record(HashMap::new()))
        else {
            panic!("SelectField({}) expected a record tile", self.name);
        };
        *slot = fields.remove(&self.name).unwrap_or_else(|| {
            panic!(
                "SelectField({}) over a record tile with no such field",
                self.name
            )
        });
        // The input is released only where every reader of it has released
        // ([`guard_at_field`]), so it can still hold what this consumer released. The
        // field's own deleted rows are dropped too and reach no consumer, so they are released.
        let dropped = tile.deleted_keys_guard();
        tile.remove_guarded(self.obsolete_guard().clone());
        tile.compact();
        if let Some(dropped) = dropped {
            let at_field = self.at_field(dropped);
            self.dropped_rows.remember(at_field);
        }
        // A row is complete for this field once the field's value is, where the input states a
        // row complete only once all its fields are. A plain field is complete once held, so each
        // held row is; a field of any other value states nothing here.
        tile.state_held_values_complete();
        tile.restrict_to(&projection, self.tiling());
        tile
    }

    fn release_impl(&self, obsolete_guard: TileGuard) {
        self.dropped_rows.release_to(&*self.input);
        let released = self.at_field(obsolete_guard);
        self.input.release(released);
    }
}

#[cfg(test)]
mod nested_projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        ProjectionSpyOp, assert_conforms_beneath, two_levels_of_ints,
    };

    fn spy() -> Arc<dyn TileOperator> {
        let (tile, tiling) = two_levels_of_ints();
        Arc::new(ProjectionSpyOp::new(tile, tiling).0)
    }

    #[test]
    fn a_wrap_beneath_two_levels_answers_a_projection_of_paths() {
        assert_conforms_beneath(|| {
            Arc::new(RecordWrap::new_at("a".into(), spy(), CurryLevel::new(2)))
        });
    }

    #[test]
    fn a_zip_beneath_two_levels_answers_a_projection_of_paths() {
        assert_conforms_beneath(|| {
            Arc::new(Zip::new_at(
                vec!["a".into(), "b".into()],
                vec![spy(), spy()],
                CurryLevel::new(2),
            ))
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        QuietSpy, ReleaseSpy, ScriptedProducer, TestTileProducer, keys_between,
    };
    use crate::interpreter::{BaseType, ColumnValue, Extent, Value, validate_tile};
    use bit_set::BitSet;

    #[rstest::rstest]
    #[case::row_close(true)]
    #[case::remaining_history_keys(false)]
    fn zip_announces_the_first_match_then_reads_only_the_new_history_item(
        #[case] closes_row: bool,
        #[values(true, false)] orders_first: bool,
    ) {
        use crate::interpreter::tile_operators::test_helpers::{
            ConsumeInPipeline, NotifyingOp, RegionLog, notify_input,
        };
        let int = Tiling::Scalar(Extent::Base(BaseType::Int));
        let keyed = |value| Tiling::data_function(Extent::uint_range(16), value);
        let by_customer = |values, closed| {
            Tile::data_function(
                ColumnValue::UInts(vec![7]),
                Box::new(values),
                if closed {
                    Predicate::point(Value::UInt(7))
                } else {
                    Predicate::False
                },
                BitSet::new(),
            )
        };
        let orders = |items: &[u64], closed| {
            by_customer(
                Tile::grouped(
                    vec![0],
                    ColumnValue::UInts(items.to_vec()),
                    Box::new(Tile::Scalar(ColumnValue::Ints(
                        items.iter().map(|x| *x as i64 * 10).collect(),
                    ))),
                    Predicate::False,
                    BitSet::new(),
                ),
                closed,
            )
        };
        let name_ty = keyed(int.clone());
        let orders_ty = keyed(keyed(int));
        let (mut name, name_push, name_value, name_reads) =
            NotifyingOp::scripted(name_ty.empty_tile(), name_ty.clone());
        let (mut history, history_push, history_value, history_reads) =
            NotifyingOp::scripted(orders_ty.empty_tile(), orders_ty.clone());
        name.pushed_keys = true;
        history.pushed_keys = true;
        let zip = Arc::new(Zip::new_at(
            vec!["name".into(), "history".into()],
            vec![Arc::new(name), Arc::new(history)],
            CurryLevel::new(1),
        ));
        let ty = zip.tiling().clone();
        let (log, notifications) = RegionLog::new();
        let input = zip.subscribe(
            ty.universal_guard(),
            Box::new(log),
            &mut SubscribeContext::new(),
        );
        let mut memo = MemoProducer::over(input, &ty);
        let point = |k| Predicate::point(Value::UInt(k));
        let row = Projection::admitting(point(7));
        let order = |i| Projection::of_path(&[Value::UInt(7), Value::UInt(i)]);
        let pop = || std::mem::take(&mut *notifications.write().unwrap());
        let consume = |memo: &mut MemoProducer, p: &Projection| {
            memo.consume_in_pipeline(InputId::ONLY, p.guard(&ty))
        };
        let deliver_orders = || {
            *history_value.write().unwrap() = orders(&[1, 2], false);
            notify_input(&history_push, &order(1).union(&order(2)));
        };
        let deliver_name = || {
            *name_value.write().unwrap() =
                by_customer(Tile::Scalar(ColumnValue::Ints(vec![42])), true);
            notify_input(&name_push, &row);
        };
        if orders_first {
            deliver_orders();
            assert!(pop().is_empty());
            deliver_name();
        } else {
            deliver_name();
            assert!(pop().is_empty());
            deliver_orders();
        }
        assert_eq!(pop(), vec![row.clone()]);
        consume(&mut memo, &row);
        let first = memo.read_in_pipeline(row.guard(&ty));
        let Tile::Record { fields, .. } = first.deepest_values() else {
            unreachable!()
        };
        assert_eq!(fields["name"], Tile::Scalar(ColumnValue::Ints(vec![42])));
        assert_eq!(
            fields["history"].deepest_values(),
            &Tile::Scalar(ColumnValue::Ints(vec![10, 20]))
        );
        name_reads.write().unwrap().clear();
        history_reads.write().unwrap().clear();
        *history_value.write().unwrap() = orders(&[1, 2, 3], false);
        notify_input(&history_push, &order(3));
        let item = Projection::within(
            CurryLevel::OUTERMOST,
            point(7),
            Projection::of_field("history", Projection::admitting(point(3))),
        );
        assert_eq!(pop(), vec![item.clone()]);
        consume(&mut memo, &item);
        assert!(name_reads.read().unwrap().is_empty());
        assert_eq!(*history_reads.read().unwrap(), [order(3).guard(&orders_ty)]);
        let answer = memo.read_in_pipeline(item.guard(&ty));
        assert_eq!(answer.to_guard(), item.guard(&ty));
        let Tile::Record { fields, .. } = answer.deepest_values() else {
            unreachable!()
        };
        assert_eq!(
            fields["history"].deepest_values(),
            &Tile::Scalar(ColumnValue::Ints(vec![30]))
        );
        // Either form of closure arrives without an order. The memo still learns that
        // customer 7 is complete, including the orders that arrived before the name.
        *history_value.write().unwrap() = orders(&[1, 2, 3], true);
        let closing = if closes_row {
            row.clone()
        } else {
            row.minus(&order(1).union(&order(2)).union(&order(3)))
        };
        notify_input(&history_push, &closing);
        assert_eq!(pop(), vec![row.clone()]);
        consume(&mut memo, &row);
        let closed = memo.read_in_pipeline(row.guard(&ty));
        assert!(closed.to_guard().subsumes(&row.guard(&ty)));
        let Tile::Record { fields, .. } = closed.deepest_values() else {
            unreachable!()
        };
        assert_eq!(
            fields["history"].deepest_values(),
            &Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30]))
        );
    }

    fn record_wrap_over(
        input_tile: Tile,
        input_tiling: Tiling,
        name: &str,
    ) -> (RecordWrapProducer, Arc<RwLock<Vec<TileGuard>>>) {
        let (spy, log) = ReleaseSpy::new(input_tile, input_tiling.clone());
        let level = CurryLevel::new(1);
        let record = Tiling::Record(
            [(SmolStr::new(name), input_tiling.values_at(level).clone())]
                .into_iter()
                .collect(),
        );
        let out_tiling = with_values_at(&input_tiling, level, record);
        let producer = RecordWrapProducer {
            base: ProducerBase::unowned(RecordWrapProducer::alloc_id(), &out_tiling),
            name: SmolStr::new(name),
            level,
            input: Box::new(spy),
        };
        (producer, log)
    }

    fn keyed_ints() -> (Tile, Tiling) {
        let int = Extent::Base(BaseType::Int);
        let tiling = Tiling::data_function(Extent::Base(BaseType::UInt), Tiling::Scalar(int));
        let tile = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1]),
            Box::new(Tile::Scalar(ColumnValue::from_ints(vec![10, 20]))),
            Predicate::True,
            BitSet::new(),
        );
        (tile, tiling)
    }

    /// The keys of the input pass through and its values become the one field of a record.
    #[test]
    fn record_wrap_keeps_the_keys_and_wraps_the_values() {
        let (tile, tiling) = keyed_ints();
        let (mut producer, _) = record_wrap_over(tile, tiling, "f");
        let wrapped = producer.read_in_pipeline(producer.tiling().universal_guard());
        let Tile::DataFunction {
            domain, codomain, ..
        } = &wrapped
        else {
            panic!("a wrapped function is a function, got {wrapped:?}");
        };
        assert_eq!(domain.len(), 2, "the keys pass through");
        let Tile::Record { fields, .. } = codomain.as_ref() else {
            panic!("the values are a record, got {codomain:?}");
        };
        assert_eq!(fields.len(), 1);
        let Some(Tile::Scalar(values)) = fields.get(&SmolStr::new("f")) else {
            panic!("the one field holds the input's values, got {fields:?}");
        };
        assert_eq!(values.len(), 2);
    }

    /// The universal release of the record reaches the input whole.
    #[test]
    fn record_wrap_forwards_a_release_to_its_input() {
        let (tile, tiling) = keyed_ints();
        let (producer, log) = record_wrap_over(tile, tiling, "f");
        producer.release(producer.tiling().universal_guard());
        assert!(
            log.read()
                .unwrap_or_else(PoisonError::into_inner)
                .iter()
                .any(|g| g.is_universal()),
            "the universal release reaches the input, saw {:?}",
            log.read().unwrap_or_else(PoisonError::into_inner)
        );
    }

    /// A release of the record's keys reaches the input as the same keys.
    #[test]
    fn record_wrap_forwards_a_release_of_its_keys() {
        let (tile, tiling) = keyed_ints();
        let (producer, log) = record_wrap_over(tile, tiling, "f");
        let key_zero = Predicate::at_or_below(Value::UInt(0));
        producer.release(TileGuard::Function(FunctionGuard::Domain(key_zero.clone())));
        assert_eq!(
            *log.read().unwrap_or_else(PoisonError::into_inner),
            vec![TileGuard::Function(FunctionGuard::Domain(key_zero))],
            "key 0 of the record is key 0 of the input"
        );
    }

    /// A release of part of the field reaches the input as that part of its values. The field's
    /// values are a collection, so a part of them is a region and not the whole: the arm of
    /// `onto_record_field` that restates a record guard for the field's operand.
    #[test]
    fn record_wrap_forwards_the_part_of_the_field_a_release_names() {
        let int = Extent::Base(BaseType::Int);
        let uint = Extent::Base(BaseType::UInt);
        let tiling = Tiling::data_function(
            uint.clone(),
            Tiling::data_function(uint, Tiling::Scalar(int)),
        );
        let (producer, log) = record_wrap_over(tiling.empty_tile(), tiling.clone(), "f");
        let key_zero = TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(
            Value::UInt(0),
        )));
        let field = TileGuard::Record(HashMap::from([(SmolStr::new("f"), key_zero.clone())]));
        producer.release(TileGuard::Function(FunctionGuard::Codomain(Box::new(
            field,
        ))));
        assert_eq!(
            *log.read().unwrap_or_else(PoisonError::into_inner),
            vec![TileGuard::Function(FunctionGuard::Codomain(Box::new(
                key_zero.clone()
            )))],
            "key 0 of the field's values is key 0 of the input's values"
        );
    }

    /// A universal guard names every field, so every operand is released. Swallowing it
    /// strands every producer beneath a record field, and because [`FanOut`] forwards the
    /// intersection of its branches' guards, one branch that never releases blocks
    /// reclamation for all of them.
    #[test]
    fn make_record_forwards_a_universal_release_to_every_component() {
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let mut logs = Vec::new();
        let mut inputs: Vec<Box<dyn TileProducer>> = Vec::new();
        for _ in 0..2 {
            let (spy, log) =
                ReleaseSpy::new(Tile::Scalar(ColumnValue::Ints(vec![1])), tiling.clone());
            logs.push(log);
            inputs.push(Box::new(spy));
        }
        let out_tiling = Tiling::Record((0..2).map(|i| (tuple_field(i), tiling.clone())).collect());
        let producer = MakeRecordProducer {
            base: ProducerBase::unowned(MakeRecordProducer::alloc_id(), &out_tiling),
            names: (0..2).map(tuple_field).collect(),
            inputs,
        };

        producer.release(out_tiling.universal_guard());
        for (i, log) in logs.iter().enumerate() {
            let seen = log.read().unwrap_or_else(PoisonError::into_inner);
            assert!(
                seen.iter().any(|g| g.is_universal()),
                "operand {i} should have been released universally, saw {seen:?}"
            );
        }
    }

    /// An empty guard names no field, so it reaches no operand.
    #[test]
    fn make_record_does_not_forward_an_empty_release() {
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let (spy, log) = ReleaseSpy::new(Tile::Scalar(ColumnValue::Ints(vec![1])), tiling.clone());
        let out_tiling = Tiling::Record([(tuple_field(0), tiling.clone())].into_iter().collect());
        let producer = MakeRecordProducer {
            base: ProducerBase::unowned(MakeRecordProducer::alloc_id(), &out_tiling),
            names: vec![tuple_field(0)],
            inputs: vec![Box::new(spy)],
        };

        producer.release(out_tiling.empty_guard());
        assert!(
            log.read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_empty(),
            "an empty release names nothing to free, so nothing is forwarded"
        );
    }

    /// A guard between the two extremes names one field, and that field's operand is
    /// what it releases. A product whose components settle at different moments is
    /// released a field at a time as a matter of course, so this is the ordinary
    /// case rather than an edge: `to_guard` reports a settled component as covered
    /// and an unsettled one as not.
    ///
    /// The operand is what withholds the released region afterwards — a conforming
    /// producer answers a released region empty — so what is asserted here is that
    /// the guard reaches the right one and not its neighbour.
    #[test]
    fn make_record_releases_the_operand_a_guard_names() {
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let mut logs = Vec::new();
        let mut inputs: Vec<Box<dyn TileProducer>> = Vec::new();
        for _ in 0..2 {
            let (spy, log) =
                ReleaseSpy::new(Tile::Scalar(ColumnValue::Ints(vec![1])), tiling.clone());
            logs.push(log);
            inputs.push(Box::new(spy));
        }
        let names: Vec<SmolStr> = (0..2).map(tuple_field).collect();
        let out_tiling =
            Tiling::Record(names.iter().map(|n| (n.clone(), tiling.clone())).collect());
        let producer = MakeRecordProducer {
            base: ProducerBase::unowned(MakeRecordProducer::alloc_id(), &out_tiling),
            names: names.clone(),
            inputs,
        };

        // Field `_0` released, `_1` still live — neither empty nor universal.
        let partial = TileGuard::Record(
            [
                (names[0].clone(), TileGuard::Scalar(Predicate::True)),
                (names[1].clone(), TileGuard::Scalar(Predicate::False)),
            ]
            .into_iter()
            .collect(),
        );
        producer.release(partial);

        assert_eq!(
            *logs[0].read().unwrap_or_else(PoisonError::into_inner),
            vec![TileGuard::Scalar(Predicate::True)],
            "the named field's operand is released",
        );
        assert!(
            logs[1]
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .iter()
                .all(TileGuard::is_empty),
            "the other operand is not, got {:?}",
            logs[1].read().unwrap_or_else(PoisonError::into_inner),
        );
    }

    /// `UInt ⤇ {a: Int, xs: UInt ⤇ Int}`: a record holding a collection, under a level.
    fn record_under_a_level() -> Tiling {
        Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Record(HashMap::from([
                ("a".into(), Tiling::Scalar(Extent::Base(BaseType::Int))),
                (
                    "xs".into(),
                    Tiling::data_function(
                        Extent::Base(BaseType::UInt),
                        Tiling::Scalar(Extent::Base(BaseType::Int)),
                    ),
                ),
            ])),
        )
    }

    /// An operator that states a correlation and is never subscribed.
    struct Correlated {
        tiling: Tiling,
        correlation: Vec<TilePathStep>,
    }

    impl TileOperator for Correlated {
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }

        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}

        fn subscribe(
            self: Arc<Self>,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            unreachable!("only the correlation is read")
        }

        fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
            Some(self.correlation.clone())
        }
    }

    /// A selection is one record step further in than its input, as the `RecordField`
    /// application it stands in for reports; `MapResultWithSource` needs the path.
    #[test]
    fn select_field_extends_its_input_correlation_by_the_field() {
        let select = SelectField::new(
            Arc::new(Correlated {
                tiling: record_under_a_level(),
                correlation: vec![TilePathStep::Codomain],
            }),
            "a",
        );
        assert_eq!(
            select.result_correlation(),
            Some(vec![
                TilePathStep::Codomain,
                TilePathStep::Record("a".into())
            ]),
        );
    }

    /// Finishing one row releases that record, including its unused collection field, and
    /// leaves the other rows available for the next morsel.
    #[test]
    fn small_morsels_release_only_the_selected_records_rows() {
        let input_tiling = record_under_a_level();
        let (spy, log) = ReleaseSpy::new(
            Tile::Scalar(ColumnValue::Ints(vec![])),
            input_tiling.clone(),
        );
        let output_tiling = select_field_tiling(&input_tiling, "a");
        let producer = SelectFieldProducer {
            dropped_rows: Default::default(),
            base: ProducerBase::unowned(SelectFieldProducer::alloc_id(), &output_tiling),
            input: Box::new(spy),
            name: "a".into(),
            input_tiling,
        };
        let rows = TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(Value::UInt(
            0,
        ))));
        producer.release(rows.clone());
        assert_eq!(
            *log.read().unwrap_or_else(PoisonError::into_inner),
            vec![rows]
        );
    }

    #[test]
    fn small_morsels_keep_unused_collections_while_record_cells_are_live() {
        let scalar = Tiling::Scalar(Extent::Base(BaseType::Int));
        let selected = Tiling::Record(HashMap::from([
            ("x".into(), scalar.clone()),
            ("y".into(), scalar.clone()),
        ]));
        let sibling = Tiling::data_function(Extent::uint_range(2), scalar.clone());
        let input = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Record(HashMap::from([
                ("a".into(), selected),
                ("xs".into(), sibling.clone()),
                ("q".into(), scalar),
            ])),
        );
        let cells = TileGuard::Record(HashMap::from([
            ("x".into(), TileGuard::Scalar(Predicate::True)),
            ("y".into(), TileGuard::Scalar(Predicate::False)),
        ]));
        let released = guard_at_field(
            &input,
            "a",
            TileGuard::Function(FunctionGuard::Codomain(Box::new(cells.clone()))),
        );
        assert_eq!(
            released,
            TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Record(
                HashMap::from([
                    ("a".into(), cells),
                    ("xs".into(), sibling.empty_guard()),
                    ("q".into(), TileGuard::Scalar(Predicate::True)),
                ])
            ))))
        );
    }

    /// Over a bare product the other fields are released whole and the selected one as its
    /// consumer released it.
    #[test]
    fn select_field_over_a_bare_product_releases_every_other_field() {
        let int = Tiling::Scalar(Extent::Base(BaseType::Int));
        let product = Tiling::Record(HashMap::from([
            ("a".into(), int.clone()),
            ("b".into(), int.clone()),
        ]));
        assert_eq!(
            guard_at_field(&product, "a", TileGuard::Scalar(Predicate::False)),
            TileGuard::Record(HashMap::from([
                ("a".into(), TileGuard::Scalar(Predicate::False)),
                ("b".into(), TileGuard::Scalar(Predicate::True)),
            ])),
        );
    }

    /// Whether `guard` names key `key` of a collection and not key `kept`.
    fn names_key(guard: &TileGuard, key: u64, kept: u64) -> bool {
        matches!(guard, TileGuard::Function(FunctionGuard::Domain(p))
            if p.contains(&Value::UInt(key)) && !p.contains(&Value::UInt(kept)))
    }

    /// A collection with keys `0, 1, 2` whose row 1 a filter removed.
    fn filtered_collection() -> Tile {
        let mut deleted = BitSet::new();
        deleted.insert(1);
        Tile::data_function(
            ColumnValue::UInts(vec![0, 1, 2]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 11, 12]))),
            Predicate::False,
            deleted,
        )
    }

    /// The field's deleted row is dropped from what `SelectField` emits, so it is released.
    #[test]
    fn select_field_releases_the_rows_it_drops() {
        let field_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let input_tiling = Tiling::Record(HashMap::from([("xs".into(), field_tiling.clone())]));
        let (spy, log) = ReleaseSpy::new(
            Tile::record(HashMap::from([("xs".into(), filtered_collection())])),
            input_tiling.clone(),
        );
        let mut producer = SelectFieldProducer {
            dropped_rows: Default::default(),
            base: ProducerBase::unowned(SelectFieldProducer::alloc_id(), &field_tiling),
            input: Box::new(spy),
            name: "xs".into(),
            input_tiling,
        };
        producer.read_in_pipeline(producer.tiling().universal_guard());
        assert!(
            log.read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_empty(),
            "reads must not release inputs"
        );
        producer.release(Projection::Nothing.guard(producer.tiling()));
        assert!(
            log.read()
                .unwrap_or_else(PoisonError::into_inner)
                .iter()
                .any(|g| matches!(g, TileGuard::Record(fields)
                if fields.get("xs").is_some_and(|g| names_key(g, 1, 0)))),
            "the field's row 1 is released: {:?}",
            log.read().unwrap_or_else(PoisonError::into_inner),
        );
    }

    /// A row holding no cell of the selected field gave that cell back, so it leaves the
    /// output rather than standing under its key with no value: `a` holds `5` at key `1`
    /// only, beside `b`, a collection still growing under both keys.
    #[test]
    fn select_field_drops_a_row_whose_cell_was_given_back() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let row_tiling = Tiling::Record(HashMap::from([
            ("a".into(), Tiling::Scalar(int())),
            (
                "b".into(),
                Tiling::data_function(uint(), Tiling::Scalar(int())),
            ),
        ]));
        let input_tiling = Tiling::data_function(uint(), row_tiling);
        let field_tiling = Tiling::data_function(uint(), Tiling::Scalar(int()));
        let input = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::Record {
                fields: HashMap::from([
                    ("a".into(), Tile::Scalar(ColumnValue::Ints(vec![5]))),
                    (
                        "b".into(),
                        Tile::grouped(
                            vec![0, 1],
                            ColumnValue::UInts(vec![0, 0]),
                            Box::new(Tile::Scalar(ColumnValue::Ints(vec![7, 8]))),
                            Predicate::False,
                            BitSet::new(),
                        ),
                    ),
                ]),
                absent: HashMap::from([("a".into(), BitSet::from_iter([0]))]),
            }),
            Predicate::False,
            BitSet::new(),
        );
        let mut producer = SelectFieldProducer {
            dropped_rows: Default::default(),
            base: ProducerBase::unowned(SelectFieldProducer::alloc_id(), &field_tiling),
            input: Box::new(TestTileProducer::new(input, input_tiling.clone())),
            name: "a".into(),
            input_tiling,
        };
        let out = producer.read_in_pipeline(producer.tiling().universal_guard());
        let Tile::DataFunction {
            domain, codomain, ..
        } = &out
        else {
            panic!("the field is a collection: {out:?}")
        };
        assert_eq!(*domain, ColumnValue::UInts(vec![1]));
        assert_eq!(**codomain, Tile::Scalar(ColumnValue::Ints(vec![5])));
    }

    /// What `SelectField(a)` states complete over key `0` of rows `{a, b}`, where `b` is a
    /// collection still growing: first with `a` holding `earlier`, then after the part of key
    /// `0` that holds `later` merges into its input.
    fn stated_as_a_arrives(earlier: Tile, later: Tile, a_tiling: Tiling) -> (Predicate, Predicate) {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let row_tiling = Tiling::Record(HashMap::from([
            ("a".into(), a_tiling.clone()),
            (
                "b".into(),
                Tiling::data_function(uint(), Tiling::Scalar(int())),
            ),
        ]));
        let input_tiling = Tiling::data_function(uint(), row_tiling);
        let field_tiling = Tiling::data_function(uint(), a_tiling);
        // Key `0`'s part holding `a` and the `b` element at `b_key`.
        let part = |a: Tile, b_key: u64| {
            let b = Tile::grouped(
                vec![0],
                ColumnValue::UInts(vec![b_key]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![7]))),
                Predicate::False,
                BitSet::new(),
            );
            Tile::data_function(
                ColumnValue::UInts(vec![0]),
                Box::new(Tile::record(HashMap::from([
                    ("a".into(), a),
                    ("b".into(), b),
                ]))),
                Predicate::False,
                BitSet::new(),
            )
        };
        let (input, cell) = ScriptedProducer::new(part(earlier, 0), input_tiling.clone());
        let mut producer = SelectFieldProducer {
            dropped_rows: Default::default(),
            base: ProducerBase::unowned(SelectFieldProducer::alloc_id(), &field_tiling),
            input: Box::new(input),
            name: "a".into(),
            input_tiling,
        };
        let mut stated = || {
            let out = producer.read_in_pipeline(producer.tiling().universal_guard());
            assert!(validate_tile(&out), "{out:?}");
            let Tile::DataFunction {
                domain_predicate, ..
            } = out
            else {
                panic!("the field is a collection: {out:?}")
            };
            domain_predicate
        };
        let before = stated();
        cell.write()
            .unwrap_or_else(PoisonError::into_inner)
            .merge(part(later, 1));
        (before, stated())
    }

    /// A selected scalar that has not arrived leaves its row open, and the row is complete once
    /// the scalar arrives.
    #[test]
    fn select_field_leaves_a_row_open_until_its_scalar_arrives() {
        let (before, after) = stated_as_a_arrives(
            Tile::Scalar(ColumnValue::Ints(vec![])),
            Tile::Scalar(ColumnValue::Ints(vec![5])),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        assert!(before.is_false(), "{before:?}");
        assert!(after.contains(&Value::UInt(0)), "{after:?}");
    }

    /// A selected record of scalars with one field arrived leaves its row open, and the row is
    /// complete once the other field arrives.
    #[test]
    fn select_field_leaves_a_row_open_until_every_field_of_its_record_arrives() {
        let int = || Tiling::Scalar(Extent::Base(BaseType::Int));
        let record_tiling =
            Tiling::Record(HashMap::from([("x".into(), int()), ("y".into(), int())]));
        let record = |x: Vec<i64>, y: Vec<i64>| {
            Tile::record(HashMap::from([
                ("x".into(), Tile::Scalar(ColumnValue::Ints(x))),
                ("y".into(), Tile::Scalar(ColumnValue::Ints(y))),
            ]))
        };
        let (before, after) = stated_as_a_arrives(
            record(vec![5], vec![]),
            record(vec![], vec![6]),
            record_tiling,
        );
        assert!(before.is_false(), "{before:?}");
        assert!(after.contains(&Value::UInt(0)), "{after:?}");
    }

    /// Each input's deleted row is dropped from what `Zip` emits, so each input is released
    /// through its own.
    #[test]
    fn zip_releases_the_rows_it_drops() {
        let input_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let output_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Record(HashMap::from([
                ("a".into(), Tiling::Scalar(Extent::Base(BaseType::Int))),
                ("b".into(), Tiling::Scalar(Extent::Base(BaseType::Int))),
            ])),
        );
        let (spy_a, log_a) = ReleaseSpy::new(filtered_collection(), input_tiling.clone());
        let (spy_b, log_b) = ReleaseSpy::new(filtered_collection(), input_tiling);
        let mut zip = ZipProducer {
            level: CurryLevel::new(1),
            state: Mutex::new(ZipState::new(2)),
            base: ProducerBase::unowned(ZipProducer::alloc_id(), &output_tiling),
            names: vec!["a".into(), "b".into()],
            inputs: vec![Box::new(spy_a), Box::new(spy_b)],
        };
        zip.read_in_pipeline(zip.tiling().universal_guard());
        assert!(
            log_a
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_empty()
                && log_b
                    .read()
                    .unwrap_or_else(PoisonError::into_inner)
                    .is_empty()
        );
        zip.release(Projection::Nothing.guard(zip.tiling()));
        for log in [log_a, log_b] {
            assert!(
                log.read()
                    .unwrap_or_else(PoisonError::into_inner)
                    .iter()
                    .any(|g| names_key(g, 1, 0)),
                "each input's row 1 is released: {:?}",
                log.read().unwrap_or_else(PoisonError::into_inner),
            );
        }
    }

    // ── ZipProducer: asymmetric per-branch presence ────────────────────────

    /// Two `DataFunction` inputs with different sets of present positions.
    /// The output should restrict to the intersection of those positions.
    #[test]
    fn zip_producer_intersects_branch_presence() {
        let input_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::UInt)),
        );
        let tile_a = Tile::data_function(
            ColumnValue::UInts(vec![0, 1, 2]),
            Box::new(Tile::Scalar(ColumnValue::UInts(vec![10, 11, 12]))),
            // Non-terminal: branch A has emitted [0, 1, 2] but its
            // upstream hasn't yet signaled "no more".
            Predicate::False,
            BitSet::new(),
        );
        let tile_b = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::Scalar(ColumnValue::UInts(vec![20, 21]))),
            Predicate::False,
            BitSet::new(),
        );

        let output_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Record(HashMap::from([
                ("a".into(), Tiling::Scalar(Extent::Base(BaseType::UInt))),
                ("b".into(), Tiling::Scalar(Extent::Base(BaseType::UInt))),
            ])),
        );
        let mut zip = ZipProducer {
            level: CurryLevel::new(1),
            state: Mutex::new(ZipState::new(2)),
            base: ProducerBase::unowned(ZipProducer::alloc_id(), &output_tiling),
            names: vec!["a".into(), "b".into()],
            inputs: vec![
                Box::new(TestTileProducer::new(tile_a, input_tiling.clone())),
                Box::new(TestTileProducer::new(tile_b, input_tiling)),
            ],
        };

        let result = zip.read_in_pipeline(zip.tiling().universal_guard());
        let Tile::DataFunction {
            domain, codomain, ..
        } = result
        else {
            panic!("expected Function output, got {result:?}");
        };
        // Intersection of [0, 1, 2] and [0, 1] is [0, 1].
        let ColumnValue::UInts(domain_vals) = domain else {
            panic!("expected UInts keys, got {domain:?}");
        };
        assert_eq!(
            domain_vals,
            vec![0, 1],
            "output keys should be the intersection of input presences"
        );

        let Tile::Record {
            fields: field_tiles,
            ..
        } = *codomain
        else {
            panic!("expected Record values");
        };
        assert_eq!(
            scalar_tile_to_column_value(field_tiles.get("a").unwrap().clone()),
            ColumnValue::UInts(vec![10, 11]),
            "branch a's values should be filtered to positions [0, 1]",
        );
        assert_eq!(
            scalar_tile_to_column_value(field_tiles.get("b").unwrap().clone()),
            ColumnValue::UInts(vec![20, 21]),
            "branch b's values should remain [0, 1] (already its full presence)",
        );
    }

    /// A pair's keys are complete where every arm's are, each arm's read through
    /// `Tile::level_statement`: the collection arm's keys follow its complete level beneath, so the
    /// pair's keys are complete though no arm's `domain_predicate` says so alone. The pair's level
    /// follows no level of its own: its values are a record of the arms'.
    #[test]
    fn a_pair_states_the_meet_of_its_arms_level_statements() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let arm0_tiling = Tiling::data_function(uint(), Tiling::Scalar(int()));
        let arm1_tiling =
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int())));
        let arm0 = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![5]))),
            Predicate::True,
            BitSet::new(),
        );
        let mut arm1 = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::grouped(
                vec![0],
                ColumnValue::from_uints(vec![3]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![30]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );
        let Tile::DataFunction {
            keys_follow_beneath,
            ..
        } = &mut arm1
        else {
            unreachable!("a collection")
        };
        *keys_follow_beneath = KeysFollow::Follows;
        let out_tiling = Tiling::data_function(
            uint(),
            Tiling::Record(HashMap::from([
                (tuple_field(0), Tiling::Scalar(int())),
                (
                    tuple_field(1),
                    Tiling::data_function(uint(), Tiling::Scalar(int())),
                ),
            ])),
        );
        let (spy0, _) = QuietSpy::new(arm0, arm0_tiling);
        let (spy1, _) = QuietSpy::new(arm1, arm1_tiling);
        let mut zip = ZipProducer {
            base: ProducerBase::unowned(ZipProducer::alloc_id(), &out_tiling),
            names: vec![tuple_field(0), tuple_field(1)],
            inputs: vec![Box::new(spy0), Box::new(spy1)],
            level: CurryLevel::new(1),
            state: Mutex::new(ZipState::new(2)),
        };
        let out = zip.read_in_pipeline(out_tiling.universal_guard());
        let Tile::DataFunction {
            domain_predicate,
            keys_follow_beneath,
            ..
        } = &out
        else {
            panic!("the zip is a collection, got {out:?}")
        };
        assert!(domain_predicate.is_true(), "{out:?}");
        assert_ne!(*keys_follow_beneath, KeysFollow::Follows, "{out:?}");
    }

    /// A release naming part of the pair record reaches each arm as that arm's field, spelled
    /// against the arm's own tiling. The guard is the one a consumer builds with `to_guard`
    /// while row 0 of the collection-valued arm is still open.
    #[test]
    fn a_zip_release_reaches_each_arm_as_its_own_field() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let arm0_tiling = Tiling::data_function(uint(), Tiling::Scalar(int()));
        let arm1_tiling =
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int())));
        let arm0 = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![5]))),
            Predicate::False,
            BitSet::new(),
        );
        let arm1 = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::grouped(
                vec![0],
                ColumnValue::from_uints(vec![3]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![30]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );
        let out_tiling = Tiling::data_function(
            uint(),
            Tiling::Record(HashMap::from([
                (tuple_field(0), Tiling::Scalar(int())),
                (
                    tuple_field(1),
                    Tiling::data_function(uint(), Tiling::Scalar(int())),
                ),
            ])),
        );
        let (spy0, released0) = QuietSpy::new(arm0, arm0_tiling.clone());
        let (spy1, released1) = QuietSpy::new(arm1, arm1_tiling.clone());
        let mut zip = ZipProducer {
            base: ProducerBase::unowned(ZipProducer::alloc_id(), &out_tiling),
            names: vec![tuple_field(0), tuple_field(1)],
            inputs: vec![Box::new(spy0), Box::new(spy1)],
            level: CurryLevel::new(1),
            state: Mutex::new(ZipState::new(2)),
        };
        let out = zip.read_in_pipeline(out_tiling.universal_guard());
        let guard = out.to_guard();
        zip.release(guard.clone());
        // Key 0 is open, since the collection arm can still grow under it. The scalar arm's
        // value there is whole once delivered, so it is released at its row — for that arm,
        // its key 0 — and the collection arm is released the inner key it delivered beneath
        // key 0.
        let covers = |log: &Arc<RwLock<Vec<TileGuard>>>, path: &[Value]| {
            log.read()
                .unwrap_or_else(PoisonError::into_inner)
                .iter()
                .any(|g| TileGuard::flatten_or(vec![g.clone()]).covers_path(path))
        };
        assert!(
            covers(&released0, &[Value::UInt(0)]),
            "the scalar arm was not released its taken value: {:?}, from {guard:?}",
            released0.read().unwrap_or_else(PoisonError::into_inner)
        );
        assert!(
            covers(&released1, &[Value::UInt(0), Value::UInt(3)]),
            "the collection arm was not released its inner key: {:?}, from {guard:?}",
            released1.read().unwrap_or_else(PoisonError::into_inner)
        );
        // The row stays while its collection is open, holding no cell of the scalar field.
        let Tile::DataFunction {
            domain, codomain, ..
        } = zip.read_in_pipeline(out_tiling.universal_guard())
        else {
            panic!("the zip is a collection")
        };
        assert_eq!(domain, ColumnValue::from_uints(vec![0]), "key 0 stays");
        let Tile::Record { absent, .. } = codomain.as_ref() else {
            panic!("the pair is a record: {codomain:?}")
        };
        assert_eq!(
            absent.get(&tuple_field(0)),
            Some(&BitSet::from_iter([0])),
            "the scalar field's cell at key 0 was released: {codomain:?}"
        );
        // Releasing key 0 whole reaches both arms as key 0.
        zip.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::point(Value::UInt(0)),
        )));
        for (log, tiling) in [(&released0, &arm0_tiling), (&released1, &arm1_tiling)] {
            for g in log.read().unwrap_or_else(PoisonError::into_inner).iter() {
                assert!(
                    g.check_from(tiling),
                    "{g:?} is not a guard over the arm's tiling {tiling}"
                );
            }
            assert!(
                covers(log, &[Value::UInt(0)]),
                "an arm was not released key 0: {:?}",
                log.read().unwrap_or_else(PoisonError::into_inner)
            );
        }
    }

    /// A release of one field reaches an arm only at the pairs the zip has emitted. A consumer
    /// done with a field may name it at every row, and an arm releasing a row's cells gives the
    /// row back, so a row one arm holds and another has not reached stays with the arm.
    #[test]
    fn a_field_release_reaches_an_arm_only_at_emitted_pairs() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let arm_tiling = Tiling::data_function(uint(), Tiling::Scalar(int()));
        // Arm 0 holds rows 0 and 1, arm 1 row 0 alone: the pair emits row 0.
        let arm0 = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![5, 6]))),
            Predicate::False,
            BitSet::new(),
        );
        let arm1 = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![7]))),
            Predicate::False,
            BitSet::new(),
        );
        let out_tiling = Tiling::data_function(
            uint(),
            Tiling::Record(HashMap::from([
                (tuple_field(0), Tiling::Scalar(int())),
                (tuple_field(1), Tiling::Scalar(int())),
            ])),
        );
        let (spy0, released0) = QuietSpy::new(arm0, arm_tiling.clone());
        let (spy1, _) = QuietSpy::new(arm1, arm_tiling);
        let mut zip = ZipProducer {
            base: ProducerBase::unowned(ZipProducer::alloc_id(), &out_tiling),
            names: vec![tuple_field(0), tuple_field(1)],
            inputs: vec![Box::new(spy0), Box::new(spy1)],
            level: CurryLevel::new(1),
            state: Mutex::new(ZipState::new(2)),
        };
        zip.read_in_pipeline(out_tiling.universal_guard());
        // A consumer done with field `_0` at every row.
        zip.release(TileGuard::Function(FunctionGuard::Codomain(Box::new(
            TileGuard::Record(HashMap::from([
                (tuple_field(0), TileGuard::Scalar(Predicate::True)),
                (tuple_field(1), TileGuard::Scalar(Predicate::False)),
            ])),
        ))));
        let covers = |path: &[Value]| {
            released0
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .iter()
                .any(|g| TileGuard::flatten_or(vec![g.clone()]).covers_path(path))
        };
        assert!(
            covers(&[Value::UInt(0)]),
            "arm 0 was not released the row the pair emitted: {:?}",
            released0.read().unwrap_or_else(PoisonError::into_inner)
        );
        assert!(
            !covers(&[Value::UInt(1)]),
            "arm 0 was released row 1, which arm 1 has not reached: {:?}",
            released0.read().unwrap_or_else(PoisonError::into_inner)
        );
        let other_field = TileGuard::Function(FunctionGuard::Codomain(Box::new(
            TileGuard::Record(HashMap::from([
                (tuple_field(0), TileGuard::Scalar(Predicate::False)),
                (tuple_field(1), TileGuard::Scalar(Predicate::True)),
            ])),
        )));
        let first_row =
            TileGuard::Function(FunctionGuard::Domain(Predicate::exactly(&[Value::UInt(0)])));
        zip.release(other_field.intersect(&first_row));
        assert!(
            zip.state
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .held
                .iter()
                .all(|paths| !paths.contains(&vec![Value::UInt(0)])),
            "a released pair must leave the row-tracking state"
        );
        assert!(
            zip.state
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .held[0]
                .contains(&vec![Value::UInt(1)]),
            "an unpaired row stays held until released"
        );
        assert!(
            !zip.state
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .emitted
                .contains(&Value::UInt(0)),
            "a released pair must leave the emitted-key predicate"
        );
        zip.release(out_tiling.universal_guard());
        assert!(
            zip.state
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .held
                .iter()
                .all(HashSet::is_empty)
        );
        assert_eq!(
            zip.state
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .emitted,
            Predicate::False
        );
    }

    /// An arm whose tile a test sets between pulls, returned as it stands, deleted rows
    /// included.
    struct Scripted {
        base: ProducerBase,
        tile: Arc<RwLock<Tile>>,
    }

    impl TileProducer for Scripted {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
            self.tile
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .clone()
        }

        fn release_impl(&self, _obsolete_guard: TileGuard) {}
    }

    /// A row an arm deletes reaches no consumer, so the zip stops tracking it where it gives the
    /// row back to the arm, and a consumer's release of every pair it saw leaves nothing held.
    #[test]
    fn a_row_an_arm_deletes_leaves_the_row_tracking_state() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let arm_tiling = Tiling::data_function(uint(), Tiling::Scalar(int()));
        let rows = |keys: Vec<u64>, deleted: BitSet| {
            let values = keys.iter().map(|k| *k as i64).collect();
            Tile::data_function(
                ColumnValue::from_uints(keys),
                Box::new(Tile::Scalar(ColumnValue::Ints(values))),
                Predicate::False,
                deleted,
            )
        };
        // Arm 0 holds rows 0 and 1, arm 1 row 0.
        let arm0 = Arc::new(RwLock::new(rows(vec![0, 1], BitSet::new())));
        let arm1 = Arc::new(RwLock::new(rows(vec![0], BitSet::new())));
        let out_tiling = Tiling::data_function(
            uint(),
            Tiling::Record(HashMap::from([
                (tuple_field(0), Tiling::Scalar(int())),
                (tuple_field(1), Tiling::Scalar(int())),
            ])),
        );
        let scripted = |tile: &Arc<RwLock<Tile>>| -> Box<dyn TileProducer> {
            Box::new(Scripted {
                base: ProducerBase::unowned(Scripted::alloc_id(), &arm_tiling),
                tile: Arc::clone(tile),
            })
        };
        let mut zip = ZipProducer {
            base: ProducerBase::unowned(ZipProducer::alloc_id(), &out_tiling),
            names: vec![tuple_field(0), tuple_field(1)],
            inputs: vec![scripted(&arm0), scripted(&arm1)],
            level: CurryLevel::new(1),
            state: Mutex::new(ZipState::new(2)),
        };
        zip.read_in_pipeline(out_tiling.universal_guard());
        assert!(
            zip.state
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .held[0]
                .contains(&vec![Value::UInt(1)])
        );
        // Arm 0 deletes row 1, and the consumer releases row 0, the pair it saw.
        *arm0.write().unwrap_or_else(PoisonError::into_inner) =
            rows(vec![0, 1], BitSet::from_iter([1]));
        zip.read_in_pipeline(out_tiling.universal_guard());
        zip.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::exactly(&[Value::UInt(0)]),
        )));
        assert!(
            zip.state
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .held
                .iter()
                .all(HashSet::is_empty),
            "a deleted row stays tracked: {:?}",
            zip.state
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .held
        );
    }

    /// An arm answering only the keys a pull asks for, out of `0..KEYS`.
    struct KeysAsked {
        base: ProducerBase,
    }

    impl TileProducer for KeysAsked {
        impl_producer_base!();

        fn get_impl(&self, projection_guard: TileGuard) -> Tile {
            let asked = projection_guard.whole_keys();
            let keys: Vec<u64> = (0..KEYS)
                .filter(|key| asked.contains_path(&[Value::UInt(*key)]))
                .collect();
            let values = keys.iter().map(|key| *key as i64).collect();
            Tile::data_function(
                ColumnValue::from_uints(keys),
                Box::new(Tile::Scalar(ColumnValue::Ints(values))),
                Predicate::False,
                BitSet::new(),
            )
        }

        fn release_impl(&self, _obsolete_guard: TileGuard) {}
    }

    const KEYS: u64 = 64;

    /// Pulls of one zip from several threads at once, each for its own keys, leave the zip
    /// recording, per arm, the rows of every pull: no pull's rows are lost to another's.
    #[test]
    fn concurrent_pulls_keep_the_rows_each_arm_holds() {
        const THREADS: u64 = 8;
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let arm_tiling = Tiling::data_function(uint(), Tiling::Scalar(int()));
        let out_tiling = Tiling::data_function(
            uint(),
            Tiling::Record(HashMap::from([
                (tuple_field(0), Tiling::Scalar(int())),
                (tuple_field(1), Tiling::Scalar(int())),
            ])),
        );
        let arm = || -> Box<dyn TileProducer> {
            Box::new(KeysAsked {
                base: ProducerBase::unowned(KeysAsked::alloc_id(), &arm_tiling),
            })
        };
        let per_thread = KEYS / THREADS;
        // Each round starts its pulls together, on a zip with nothing recorded.
        for round in 0..100 {
            let zip = ZipProducer {
                base: ProducerBase::unowned(ZipProducer::alloc_id(), &out_tiling),
                names: vec![tuple_field(0), tuple_field(1)],
                inputs: vec![arm(), arm()],
                level: CurryLevel::new(1),
                state: Mutex::new(ZipState::new(2)),
            };
            let start = std::sync::Barrier::new(THREADS as usize);
            std::thread::scope(|scope| {
                for thread in 0..THREADS {
                    let (zip, start) = (&zip, &start);
                    scope.spawn(move || {
                        let first = thread * per_thread;
                        start.wait();
                        crate::interpreter::dispatcher::in_a_run(|| {
                            zip.get(keys_between(first, first + per_thread - 1))
                        });
                    });
                }
            });
            let state = zip.state.lock().unwrap_or_else(PoisonError::into_inner);
            assert_eq!(state.held.len(), 2, "the zip tracks each arm's rows");
            for (index, held) in state.held.iter().enumerate() {
                assert_eq!(
                    held.len(),
                    KEYS as usize,
                    "round {round}: arm {index} holds the rows of every pull"
                );
            }
        }
    }

    #[test]
    fn a_zip_keeps_an_unselected_collections_keys_under_standing_levels() {
        let uint = Extent::Base(BaseType::UInt);
        let scalar = Tiling::Scalar(Extent::Base(BaseType::Int));
        let under = |mut tiling: Tiling, levels| {
            for _ in 0..levels {
                tiling = Tiling::data_function(uint.clone(), tiling);
            }
            tiling
        };
        for levels in 1..=3 {
            let collection = under(Tiling::data_function(uint.clone(), scalar.clone()), levels);
            let value = under(scalar.clone(), levels);
            let out = under(
                Tiling::Record(HashMap::from([
                    (
                        tuple_field(0),
                        Tiling::data_function(uint.clone(), scalar.clone()),
                    ),
                    (tuple_field(1), scalar.clone()),
                ])),
                levels,
            );
            let (xs, released) = QuietSpy::new(collection.empty_tile(), collection.clone());
            let (n, _) = QuietSpy::new(value.empty_tile(), value.clone());
            let zip = ZipProducer {
                base: ProducerBase::unowned(ZipProducer::alloc_id(), &out),
                names: vec![tuple_field(0), tuple_field(1)],
                inputs: vec![Box::new(xs), Box::new(n)],
                level: CurryLevel::new(levels),
                state: Mutex::new(ZipState::new(2)),
            };
            let selected = tuple_field(1);
            zip.release(guard_at_field(&out, &selected, value.empty_guard()));
            assert!(
                released
                    .read()
                    .unwrap_or_else(PoisonError::into_inner)
                    .iter()
                    .all(TileGuard::is_empty)
            );

            let path = vec![Value::UInt(0); levels];
            let keys = CurryLevel::new(levels - 1).wrap_guard(TileGuard::Function(
                FunctionGuard::Domain(Predicate::exactly(&path)),
            ));
            zip.release(guard_at_field(&out, &selected, keys));
            let covers = |path: &[Value]| {
                released
                    .read()
                    .unwrap_or_else(PoisonError::into_inner)
                    .iter()
                    .any(|g| g.covers_path(path))
            };
            assert!(covers(&path));
            for depth in 0..levels {
                let mut later = path.clone();
                later[depth] = Value::UInt(1);
                assert!(
                    !covers(&later),
                    "level {depth} of {levels} was released: {:?}",
                    released.read().unwrap_or_else(PoisonError::into_inner)
                );
            }

            zip.release(TileGuard::Function(FunctionGuard::Domain(
                Predicate::point(Value::UInt(0)),
            )));
            let below = vec![Value::UInt(0); levels + 1];
            assert!(covers(&below));
            let mut sibling = below;
            sibling[0] = Value::UInt(1);
            assert!(!covers(&sibling));
            assert!(
                released
                    .read()
                    .unwrap_or_else(PoisonError::into_inner)
                    .iter()
                    .all(|g| g.check_from(&collection))
            );
        }
    }

    /// Beneath a standing level, an arm whose field the consumer released at every path holds no
    /// row of its own afterwards, and the rows the other arm holds stay: a released arm has given
    /// those rows back rather than lacking them, at the outermost keys as at the rows.
    #[test]
    fn rows_an_arm_gave_back_beneath_a_standing_level_stay() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let arm0_tiling =
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int())));
        let arm1_tiling = Tiling::data_function(
            uint(),
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int()))),
        );
        let arm1 = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 1],
                ColumnValue::from_uints(vec![7, 7]),
                Box::new(Tile::grouped(
                    vec![0, 1],
                    ColumnValue::from_uints(vec![3, 3]),
                    Box::new(Tile::Scalar(ColumnValue::Ints(vec![30, 31]))),
                    Predicate::False,
                    BitSet::new(),
                )),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );
        let out_tiling = Tiling::data_function(
            uint(),
            Tiling::data_function(
                uint(),
                Tiling::Record(HashMap::from([
                    (tuple_field(0), Tiling::Scalar(int())),
                    (
                        tuple_field(1),
                        Tiling::data_function(uint(), Tiling::Scalar(int())),
                    ),
                ])),
            ),
        );
        let (spy0, _) = QuietSpy::new(arm0_tiling.empty_tile(), arm0_tiling.clone());
        let (spy1, _) = QuietSpy::new(arm1, arm1_tiling);
        let mut zip = ZipProducer {
            base: ProducerBase::unowned(ZipProducer::alloc_id(), &out_tiling),
            names: vec![tuple_field(0), tuple_field(1)],
            inputs: vec![Box::new(spy0), Box::new(spy1)],
            level: CurryLevel::new(2),
            // Arm `_0` held both rows before the consumer released its field, so it gives them
            // back rather than lacking them.
            state: Mutex::new(ZipState {
                held: vec![
                    HashSet::from([
                        vec![Value::UInt(0), Value::UInt(7)],
                        vec![Value::UInt(1), Value::UInt(7)],
                    ]),
                    HashSet::new(),
                ],
                ..ZipState::new(2)
            }),
        };
        // The consumer reads field `_1` only, so it releases field `_0` at every path.
        let every_path = |field: TileGuard| {
            TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Function(
                FunctionGuard::Codomain(Box::new(field)),
            ))))
        };
        zip.release(every_path(TileGuard::Record(HashMap::from([
            (tuple_field(0), TileGuard::Scalar(TileGuard::leaf(true))),
            (
                tuple_field(1),
                TileGuard::Function(FunctionGuard::Domain(Predicate::False)),
            ),
        ]))));
        let out = zip.read_in_pipeline(out_tiling.universal_guard());
        let Tile::DataFunction { domain, .. } = &out else {
            panic!("the zip is a collection")
        };
        assert_eq!(
            *domain,
            ColumnValue::from_uints(vec![0, 1]),
            "both rows stay"
        );
        assert_eq!(
            out.paths_at(CurryLevel::new(1)),
            vec![
                vec![Value::UInt(0), Value::UInt(7)],
                vec![Value::UInt(1), Value::UInt(7)]
            ],
            "the rows beneath stay"
        );
        let Tile::Record { fields, absent } = out.values_at(CurryLevel::new(2)) else {
            panic!("the pair is a record: {out:?}")
        };
        assert_eq!(
            absent.get(&tuple_field(0)),
            Some(&BitSet::from_iter([0, 1])),
            "no row holds a cell of the field given back: {out:?}"
        );
        let Some(Tile::DataFunction { codomain, .. }) = fields.get(&tuple_field(1)) else {
            panic!("the other field is a collection: {out:?}")
        };
        assert_eq!(
            **codomain,
            Tile::Scalar(ColumnValue::Ints(vec![30, 31])),
            "the other arm's values are paired at their rows"
        );
    }

    /// Beneath a standing level, an arm that lacks a row it has not given back drops the row from
    /// every arm: only a release counts as giving a row back.
    #[test]
    fn a_row_an_arm_lacks_without_a_release_drops_beneath_a_standing_level() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let arm0_tiling =
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int())));
        let arm1_tiling = Tiling::data_function(
            uint(),
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int()))),
        );
        let arm0 = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::grouped(
                vec![0],
                ColumnValue::from_uints(vec![7]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![5]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );
        let arm1 = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 1],
                ColumnValue::from_uints(vec![7, 7]),
                Box::new(Tile::grouped(
                    vec![0, 1],
                    ColumnValue::from_uints(vec![3, 3]),
                    Box::new(Tile::Scalar(ColumnValue::Ints(vec![30, 31]))),
                    Predicate::False,
                    BitSet::new(),
                )),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );
        let out_tiling = Tiling::data_function(
            uint(),
            Tiling::data_function(
                uint(),
                Tiling::Record(HashMap::from([
                    (tuple_field(0), Tiling::Scalar(int())),
                    (
                        tuple_field(1),
                        Tiling::data_function(uint(), Tiling::Scalar(int())),
                    ),
                ])),
            ),
        );
        let (spy0, _) = QuietSpy::new(arm0, arm0_tiling);
        let (spy1, _) = QuietSpy::new(arm1, arm1_tiling);
        let mut zip = ZipProducer {
            base: ProducerBase::unowned(ZipProducer::alloc_id(), &out_tiling),
            names: vec![tuple_field(0), tuple_field(1)],
            inputs: vec![Box::new(spy0), Box::new(spy1)],
            level: CurryLevel::new(2),
            state: Mutex::new(ZipState::new(2)),
        };
        let Tile::DataFunction { domain, .. } = zip.read_in_pipeline(out_tiling.universal_guard())
        else {
            panic!("the zip is a collection")
        };
        assert_eq!(
            domain,
            ColumnValue::from_uints(vec![0]),
            "row 1 waits for arm 0"
        );
    }
}

/// How the operators of this module are pulled in the shapes they are built for: a record
/// literal over a stream (`(a: x for x in xs)`), a pair of streams zipped by key, and a field
/// read out of a record stream.
#[cfg(test)]
mod projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, assert_conforms, int_entries, ints_by_position, keys_between,
    };
    use crate::interpreter::{BaseType, Extent};

    const ROWS: u64 = 8;

    fn ints() -> Tiling {
        Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        )
    }

    fn stream(offset: i64) -> (ProjectionSpy, GuardLog) {
        let values: Vec<i64> = (0..ROWS as i64).map(|i| i + offset).collect();
        let (spy, pulled, _) = ProjectionSpy::new(ints_by_position(&values, true), ints());
        (spy, pulled)
    }

    /// `(a: x for x in xs)`: one field over a stream.
    fn wrapped() -> (RecordWrapProducer, GuardLog) {
        let (input, pulled) = stream(0);
        let out = Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Record(
                [(
                    SmolStr::new("a"),
                    Tiling::Scalar(Extent::Base(BaseType::Int)),
                )]
                .into_iter()
                .collect(),
            ),
        );
        (
            RecordWrapProducer {
                base: ProducerBase::unowned(RecordWrapProducer::alloc_id(), &out),
                name: SmolStr::new("a"),
                level: CurryLevel::new(1),
                input: Box::new(input),
            },
            pulled,
        )
    }

    #[test]
    fn a_wrapped_stream_pulls_its_input_at_the_morsel() {
        let (mut wrap, pulled) = wrapped();
        let morsel = wrap.read_in_pipeline(keys_between(2, 4));
        let Tile::DataFunction { domain, .. } = &morsel else {
            panic!("a collection")
        };
        assert_eq!(domain.len(), 3);
        assert_eq!(
            *pulled.read().unwrap_or_else(PoisonError::into_inner),
            [keys_between(2, 4)]
        );
    }

    #[test]
    fn a_wrapped_morsel_is_the_whole_pull_cut_to_it() {
        for guard in [keys_between(0, 2), keys_between(6, 20)] {
            assert_conforms(|| Box::new(wrapped().0), guard);
        }
    }

    /// `[r.amount for r in rows]`: a field read out of a stream of records.
    fn amounts_of_records() -> (SelectFieldProducer, GuardLog) {
        let rows = Tile::data_function(
            ColumnValue::UInts((0..ROWS).collect()),
            Box::new(Tile::record(HashMap::from([
                (
                    SmolStr::new("amount"),
                    Tile::Scalar(ColumnValue::Ints(
                        (0..ROWS as i64).map(|i| 100 + i).collect(),
                    )),
                ),
                (
                    SmolStr::new("qty"),
                    Tile::Scalar(ColumnValue::Ints((0..ROWS as i64).collect())),
                ),
            ]))),
            Predicate::True,
            BitSet::new(),
        );
        let in_tiling = Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Record(
                ["amount", "qty"]
                    .into_iter()
                    .map(|name| {
                        (
                            SmolStr::new(name),
                            Tiling::Scalar(Extent::Base(BaseType::Int)),
                        )
                    })
                    .collect(),
            ),
        );
        let (input, pulled, _) = ProjectionSpy::new(rows, in_tiling.clone());
        (
            SelectFieldProducer {
                dropped_rows: Default::default(),
                base: ProducerBase::unowned(SelectFieldProducer::alloc_id(), &ints()),
                input: Box::new(input),
                name: SmolStr::new("amount"),
                input_tiling: in_tiling,
            },
            pulled,
        )
    }

    #[test]
    fn a_field_of_a_record_stream_is_read_at_the_morsel() {
        let (mut select, pulled) = amounts_of_records();
        let morsel = select.read_in_pipeline(keys_between(1, 3));
        assert_eq!(int_entries(&morsel), [(1, 101), (2, 102), (3, 103)]);
        assert_eq!(
            *pulled.read().unwrap_or_else(PoisonError::into_inner),
            [keys_between(1, 3)]
        );
    }

    #[test]
    fn a_field_morsel_is_the_whole_pull_cut_to_it() {
        for guard in [keys_between(0, 1), keys_between(6, 20)] {
            assert_conforms(|| Box::new(amounts_of_records().0), guard);
        }
    }

    /// A product of two collections, as a `Let` or a record of comprehensions makes it, is pulled
    /// at the selected field's part of the projection, and the field is cut after.
    #[test]
    fn a_field_of_a_product_is_pulled_at_its_part_of_the_product() {
        let product_tiling = Tiling::Record(
            ["a", "b"]
                .into_iter()
                .map(|name| (SmolStr::new(name), ints()))
                .collect(),
        );
        let make = || {
            let product = Tile::record(HashMap::from([
                (
                    SmolStr::new("a"),
                    ints_by_position(&(0..ROWS as i64).collect::<Vec<_>>(), true),
                ),
                (
                    SmolStr::new("b"),
                    ints_by_position(&(100..100 + ROWS as i64).collect::<Vec<_>>(), true),
                ),
            ]));
            let (input, pulled, _) = ProjectionSpy::new(product, product_tiling.clone());
            (
                SelectFieldProducer {
                    dropped_rows: Default::default(),
                    base: ProducerBase::unowned(SelectFieldProducer::alloc_id(), &ints()),
                    input: Box::new(input),
                    name: SmolStr::new("a"),
                    input_tiling: product_tiling.clone(),
                },
                pulled,
            )
        };
        let (mut select, pulled) = make();
        let morsel = select.read_in_pipeline(keys_between(2, 3));
        assert_eq!(int_entries(&morsel), [(2, 2), (3, 3)]);
        assert_eq!(
            *pulled.read().unwrap_or_else(PoisonError::into_inner),
            [
                Projection::of_field("a", Projection::of(&keys_between(2, 3)).unwrap())
                    .guard(&product_tiling)
            ]
        );
        assert_conforms(|| Box::new(make().0), keys_between(2, 3));
    }

    /// `[(x, y) for ...]`: two arms over the same positions, the second holding only what has
    /// been delivered of `delivered` positions.
    fn pair(delivered: usize) -> (ZipProducer, GuardLog, GuardLog) {
        let (a, a_pulled) = stream(0);
        let values: Vec<i64> = (0..delivered as i64).map(|i| 100 + i).collect();
        let (b, b_pulled, _) =
            ProjectionSpy::new(ints_by_position(&values, delivered as u64 == ROWS), ints());
        let out = Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Record(
                [0, 1]
                    .into_iter()
                    .map(|i| (tuple_field(i), Tiling::Scalar(Extent::Base(BaseType::Int))))
                    .collect(),
            ),
        );
        (
            ZipProducer {
                base: ProducerBase::unowned(ZipProducer::alloc_id(), &out),
                names: vec![tuple_field(0), tuple_field(1)],
                inputs: vec![Box::new(a), Box::new(b)],
                level: CurryLevel::new(1),
                state: Mutex::new(ZipState::new(2)),
            },
            a_pulled,
            b_pulled,
        )
    }

    /// Both arms are pulled at the morsel, so neither reads the other's rows.
    #[test]
    fn a_pair_of_streams_pulls_each_arm_at_the_morsel() {
        let (mut zip, a_pulled, b_pulled) = pair(ROWS as usize);
        let morsel = zip.read_in_pipeline(keys_between(2, 4));
        let Tile::DataFunction {
            domain,
            domain_predicate,
            ..
        } = &morsel
        else {
            panic!("a collection")
        };
        assert_eq!(domain.len(), 3);
        let TileGuard::Function(FunctionGuard::Domain(stated)) = keys_between(2, 4) else {
            unreachable!("a morsel is a domain guard")
        };
        assert_eq!(*domain_predicate, stated);
        assert_eq!(
            *a_pulled.read().unwrap_or_else(PoisonError::into_inner),
            [keys_between(2, 4)]
        );
        assert_eq!(
            *b_pulled.read().unwrap_or_else(PoisonError::into_inner),
            [keys_between(2, 4)]
        );
    }

    /// An arm that has delivered less pairs only the keys both hold, and the pair is complete
    /// only where both arms are: the morsel past the slower arm is not stated complete.
    #[test]
    fn a_morsel_past_a_lagging_arm_pairs_the_common_keys_and_states_them_complete() {
        let (mut zip, _, _) = pair(4);
        let morsel = zip.read_in_pipeline(keys_between(2, 6));
        let Tile::DataFunction {
            domain,
            domain_predicate,
            ..
        } = &morsel
        else {
            panic!("a collection")
        };
        assert_eq!(*domain, ColumnValue::UInts(vec![2, 3]));
        let TileGuard::Function(FunctionGuard::Domain(stated)) = keys_between(2, 3) else {
            unreachable!("a morsel is a domain guard")
        };
        assert_eq!(*domain_predicate, stated);
    }

    #[test]
    fn a_paired_morsel_is_the_whole_pull_cut_to_it() {
        for delivered in [ROWS as usize, 5] {
            for guard in [keys_between(0, 2), keys_between(3, 20)] {
                assert_conforms(|| Box::new(pair(delivered).0), guard);
            }
        }
    }

    #[test]
    fn nothing_pairs_nothing() {
        let (zip, a_pulled, b_pulled) = pair(ROWS as usize);
        let nothing = zip.tiling().empty_guard();
        assert_eq!(zip.get(nothing), zip.tiling().empty_tile());
        assert!(
            a_pulled
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_empty()
                && b_pulled
                    .read()
                    .unwrap_or_else(PoisonError::into_inner)
                    .is_empty()
        );
    }

    /// `(a: 1, b: 2)`: a record of two values, each pulled whole.
    fn two_values() -> (MakeRecordProducer, GuardLog, GuardLog) {
        let scalar = Tiling::Scalar(Extent::Base(BaseType::Int));
        let spy = |value: i64| {
            ProjectionSpy::new(Tile::Scalar(ColumnValue::Ints(vec![value])), scalar.clone())
        };
        let ((a, a_pulled, _), (b, b_pulled, _)) = (spy(1), spy(2));
        let out = Tiling::Record(
            ["a", "b"]
                .into_iter()
                .map(|name| (SmolStr::new(name), scalar.clone()))
                .collect(),
        );
        (
            MakeRecordProducer {
                base: ProducerBase::unowned(MakeRecordProducer::alloc_id(), &out),
                names: vec![SmolStr::new("a"), SmolStr::new("b")],
                inputs: vec![Box::new(a), Box::new(b)],
            },
            a_pulled,
            b_pulled,
        )
    }

    #[test]
    fn a_record_of_values_pulls_each_value_whole() {
        let (record, a_pulled, b_pulled) = two_values();
        let whole = record.tiling().universal_guard();
        let tile = record.get(whole);
        let Tile::Record { fields, .. } = &tile else {
            panic!("a record")
        };
        assert_eq!(fields.len(), 2);
        let scalar = Tiling::Scalar(Extent::Base(BaseType::Int)).universal_guard();
        assert_eq!(
            *a_pulled.read().unwrap_or_else(PoisonError::into_inner),
            std::slice::from_ref(&scalar)
        );
        assert_eq!(
            *b_pulled.read().unwrap_or_else(PoisonError::into_inner),
            [scalar]
        );
    }

    #[test]
    fn nothing_makes_no_record_and_pulls_no_value() {
        let (record, a_pulled, b_pulled) = two_values();
        let nothing = record.tiling().empty_guard();
        assert_eq!(record.get(nothing), record.tiling().empty_tile());
        assert!(
            a_pulled
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_empty()
                && b_pulled
                    .read()
                    .unwrap_or_else(PoisonError::into_inner)
                    .is_empty()
        );
    }

    #[test]
    #[should_panic(expected = "a record of values, which has no keys to project")]
    fn a_projection_of_keys_is_refused_by_a_record_of_values() {
        let (mut record, _, _) = two_values();
        record.read_in_pipeline(keys_between(0, 1));
    }

    #[test]
    fn nothing_wraps_nothing() {
        let (wrap, pulled) = wrapped();
        let nothing = wrap.tiling().empty_guard();
        assert_eq!(wrap.get(nothing), wrap.tiling().empty_tile());
        assert!(
            pulled
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_empty()
        );
    }
}
