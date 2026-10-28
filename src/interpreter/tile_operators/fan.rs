use smol_str::SmolStr;
use std::collections::{HashMap, HashSet};

use bit_set::BitSet;

use super::*;
use crate::interpreter::operator_graph::{value, value_at};
use crate::interpreter::{
    Consumer, Projection, RowIndex, Scheduler, Value, shared_consumer, tuple_field,
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
    inputs: Vec<Box<dyn TileOperator>>,
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
    pub fn new_at(names: Vec<SmolStr>, ops: Vec<Box<dyn TileOperator>>, level: CurryLevel) -> Self {
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
pub fn zip_arms_at(inputs: Vec<Box<dyn TileOperator>>, level: CurryLevel) -> Box<dyn TileOperator> {
    if inputs.iter().all(|op| op.tiling().is_scalar()) {
        return Box::new(MakeRecord::new(inputs));
    }
    let names = (0..inputs.len()).map(tuple_field).collect();
    Box::new(Zip::new_at(names, inputs, level))
}

/// Named-field variant of [`zip_arms_at`], for record literals.
pub fn zip_arms_named_at(
    inputs: Vec<(SmolStr, Box<dyn TileOperator>)>,
    level: CurryLevel,
) -> Box<dyn TileOperator> {
    if inputs.iter().all(|(_, op)| op.tiling().is_scalar()) {
        return Box::new(MakeRecord::new_named(inputs));
    }
    // A lone arm over a collection has nothing to pair with, so its values are wrapped in place.
    let inputs = match <[_; 1]>::try_from(inputs) {
        Ok([(name, input)]) => return Box::new(RecordWrap::new_at(name, input, level)),
        Err(inputs) => inputs,
    };
    let (names, ops) = inputs.into_iter().unzip();
    Box::new(Zip::new_at(names, ops, level))
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
    input: Box<dyn TileOperator>,
    /// The level the record sits at — the values every standing level is over.
    level: CurryLevel,
}

impl RecordWrap {
    /// Wrap the values `input` holds at `level` as the field `name`.
    pub fn new_at(name: SmolStr, input: Box<dyn TileOperator>, level: CurryLevel) -> Self {
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
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // The input is pulled at the projection.
        let input = self.input.subscribe(
            self.input.tiling().universal_guard(),
            keys_only(consumer),
            scheduler,
        );
        Box::new(RecordWrapProducer {
            base: ProducerBase::new(
                RecordWrapProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
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

    /// Wrapping keeps the input's keys, so the input is pulled at the projection.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
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

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
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
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let (shared, gate) = shared_consumer(consumer);
        Box::new(ZipProducer {
            base: ProducerBase::new(
                ZipProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            )
            .sharing(gate),
            names: self.names.clone(),
            level: self.level,
            inputs: self
                .inputs
                .iter_mut()
                // Every arm is pulled at the projection: the arms share the pair's keys.
                .map(|i| subscribe_forwarding_keeping_keys(&mut **i, &shared, scheduler))
                .collect(),
        })
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
}

impl TileProducer for ZipProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        for (i, input) in self.inputs.iter().enumerate() {
            visit(&format!("_{i}"), &**input);
        }
    }

    /// The arms share the pair's keys, so each arm is pulled at the projection.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
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
            .iter_mut()
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
        let gave_back = |arm: usize, path: &[Value]| {
            released[arm]
                .as_ref()
                .is_some_and(|guard| guard.covers_path(path))
        };

        // Every level above the pair has to agree before anything pairs beneath it. The
        // arms are pulled from their own branches, so one may already hold a row under a
        // key the other has not reached, and beneath a standing level a key alone does not
        // name that row — it repeats across its siblings' groups. So the arms are aligned
        // over whole paths, level by level: each keeps the paths every arm holds.
        //
        // Level by level rather than by extension, because a group may legitimately be
        // empty. A key holding nothing extends to no path of the level below, and reading
        // the levels above off the deepest one's paths would take that key away — where
        // what every arm agrees on is that the key is there and holds nothing.
        // Only where something stands above the pair's own enclosing level. One level up is
        // the flat case, which the presence intersection below already aligns over the
        // outermost keys, and a path set per arm per pull is not worth building for it.
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
                    let rows = depth == above.index();
                    held.iter()
                        .flatten()
                        .filter(|path| {
                            held.iter().enumerate().all(|(arm, paths)| {
                                paths.contains(*path) || (rows && gave_back(arm, path))
                            })
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
                // Beneath a standing level the rows were aligned by path above, so only the
                // outermost keys of a flat pair are read here.
                let flat = self.level.index() == 1;
                let outermost: Vec<Value> = match flat {
                    true => tiles
                        .iter()
                        .flat_map(|t| match t {
                            Tile::DataFunction { domain, .. } => {
                                (0..domain.len()).map(|k| domain.index_at(k)).collect()
                            }
                            _ => Vec::new(),
                        })
                        .collect(),
                    false => Vec::new(),
                };
                for (arm, t) in tiles.iter().enumerate() {
                    let Tile::DataFunction {
                        domain,
                        domain_predicate,
                        ..
                    } = t
                    else {
                        panic!("Zip: cannot mix function and non-function tiles")
                    };
                    let mut p = Predicate::from_column_value(domain);
                    if flat && released[arm].is_some() {
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
                    domain_pred = Some(match domain_pred {
                        None => domain_predicate.clone(),
                        Some(prev) => prev.intersect(domain_predicate),
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
                        let Tile::DataFunction {
                            domain_predicate, ..
                        } = filtered.values_at(CurryLevel::new(depth))
                        else {
                            unreachable!("the levels above the pair are collections")
                        };
                        match standing.get_mut(depth - 1) {
                            Some(meet) => *meet = meet.intersect(domain_predicate),
                            None => standing.push(domain_predicate.clone()),
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
                for (arm, filtered) in filtered_tiles.iter_mut().enumerate() {
                    let held = filtered.paths_at(rows_level);
                    // Lift the values out, leaving the chain of keys behind: what stays is
                    // the output's own shape, and every input has to agree on it.
                    let values = std::mem::replace(
                        filtered.values_at_mut(self.level),
                        Tile::record(HashMap::new()),
                    );
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
                for (input, dropped) in self.inputs.iter_mut().zip(dropped) {
                    if let Some(dropped) = dropped {
                        input.release(dropped);
                    }
                }
                let mut out = skeleton;
                *out.values_at_mut(self.level) = codomain_record;
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
                out
            }
            other => panic!("Zip: every input must be a function tile, got {other:?}"),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let level = self.level.index();
        for (name, input) in self.names.iter().zip(self.inputs.iter_mut()) {
            let guard = match &obsolete_guard {
                g if g.is_universal() => input.tiling().universal_guard(),
                g if g.is_empty() => input.tiling().empty_guard(),
                // A zip pairs its arms at the same positions, so the levels above the pair
                // name the same keys of every arm; at the pair each arm is one field of the
                // record, and takes that field's part.
                g => crate::interpreter::tiling::onto_record_field(
                    g.clone(),
                    level,
                    name,
                    input.tiling(),
                ),
            };
            input.release(guard);
        }
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
    inputs: Vec<Box<dyn TileOperator>>,
}

impl MakeRecord {
    /// Construct a `MakeRecord` whose fields are `inputs`, named `_0`, `_1`, … in order.
    ///
    /// Each field keeps its input's tiling, whatever that is.
    pub fn new(inputs: Vec<Box<dyn TileOperator>>) -> Self {
        assert!(!inputs.is_empty(), "MakeRecord requires at least one input");
        let names = (0..inputs.len()).map(tuple_field).collect();
        Self::new_impl(names, inputs)
    }

    /// Construct a `MakeRecord` with explicit named fields for record literals.
    ///
    /// Like [`Self::new`] but uses the caller-supplied field names instead of
    /// the synthetic `_0`, `_1`, … names used for tuples.
    pub fn new_named(inputs: Vec<(SmolStr, Box<dyn TileOperator>)>) -> Self {
        assert!(!inputs.is_empty(), "MakeRecord requires at least one input");
        let (names, ops) = inputs.into_iter().unzip();
        Self::new_impl(names, ops)
    }

    fn new_impl(names: Vec<SmolStr>, inputs: Vec<Box<dyn TileOperator>>) -> Self {
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

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let (shared, gate) = shared_consumer(consumer);
        Box::new(MakeRecordProducer {
            base: ProducerBase::new(
                MakeRecordProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            )
            .sharing(gate),
            names: self.names.clone(),
            inputs: self
                .inputs
                .iter_mut()
                .map(|i| subscribe_forwarding(&mut **i, &shared, scheduler))
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

    /// A record of values has no keys to project: the projection is the whole record or
    /// nothing, and a guard naming keys is a consumer's bug.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        match projection_guard.projection(&self.name()) {
            Projection::Everything => {}
            Projection::Nothing => return self.tiling().empty_tile(),
            Projection::Keys(_) | Projection::Fields(_) => panic!(
                "{} is a record of values, which has no keys to project: {projection_guard:?}",
                self.name()
            ),
        }
        // Every operand is pulled whole ([`SelectFieldProducer`] says why a pull naming one
        // field is unsound). An operand withholds what [`Self::release_impl`] told it a
        // consumer finished with, so a field that settled early is not re-delivered.
        let fields: HashMap<SmolStr, Tile> = self
            .names
            .iter()
            .zip(self.inputs.iter_mut())
            .map(|(name, input)| {
                let tile = input.get(input.tiling().universal_guard());
                (name.clone(), tile)
            })
            .collect();
        Tile::record(fields)
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // A record guard names one guard per field, and each goes to that field's operand.
        // A later pull re-reads every operand, and each withholds what it was told.
        match &obsolete_guard {
            g if g.is_empty() => {}
            TileGuard::Record(fields) => {
                for (name, input) in self.names.iter().zip(self.inputs.iter_mut()) {
                    if let Some(field) = fields.get(name) {
                        input.release(field.clone());
                    }
                }
            }
            g if g.is_universal() => {
                for input in self.inputs.iter_mut() {
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
    input: Box<dyn TileOperator>,
    /// The field's name — `_0`, `_1`, … for a tuple.
    name: SmolStr,
}

/// What a selector of field `name` releases of the product `tiling`, given its consumer's
/// release `guard` of that field: `guard` on the field, and every other field whole.
///
/// **A selector's subscription reads one field**, so nothing beneath it needs the others.
/// A sibling selector reads the product through the [`FanOut`] a shared product sits
/// behind, which forwards only the meet of its readers' releases, so a field reaches the
/// product released only where every reader has released it. The meet of two such releases
/// beneath a level names one field's cells under some rows, which a keyless field's guard
/// states by the rows above it ([`TileGuard::Scalar`]).
///
/// A guard naming keys of a level above the record names every field at those keys, and it
/// passes through as those keys.
fn guard_at_field(tiling: &Tiling, name: &str, guard: TileGuard) -> TileGuard {
    match tiling {
        Tiling::DataFunction { codomain, .. } => match guard {
            g if g.is_universal() => tiling.universal_guard(),
            TileGuard::Function(FunctionGuard::Codomain(inner)) => TileGuard::Function(
                FunctionGuard::Codomain(Box::new(guard_at_field(codomain, name, *inner))),
            ),
            TileGuard::Or(arms) => TileGuard::flatten_or(
                arms.into_iter()
                    .map(|arm| guard_at_field(tiling, name, arm))
                    .collect(),
            ),
            keys @ TileGuard::Function(FunctionGuard::Domain(_)) => {
                let field = select_field_tiling(codomain, name).empty_guard();
                TileGuard::flatten_or(vec![
                    keys,
                    TileGuard::Function(FunctionGuard::Codomain(Box::new(guard_at_field(
                        codomain, name, field,
                    )))),
                ])
            }
            other => unreachable!("a collection's guard is a function guard, got {other:?}"),
        },
        Tiling::Record(fields) => TileGuard::Record(
            fields
                .iter()
                .map(|(field, t)| match field == name {
                    true => (field.clone(), guard.clone()),
                    false => (field.clone(), t.universal_guard()),
                })
                .collect(),
        ),
        other => unreachable!("SelectField's input holds a record, got {other}"),
    }
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
    pub fn new(input: Box<dyn TileOperator>, name: impl Into<SmolStr>) -> Self {
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
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // A stream of records is pulled at the projection; a product of collections is read whole.
        let keeps_keys = self.input.tiling().is_data_function();
        // An intent may only widen on its way upstream, so the input is asked for all of
        // it. [`guard_at_field`] narrows, which is sound for a release and not here.
        let input_tiling = self.input.tiling().clone();
        let input_producer = self.input.subscribe(
            input_tiling.universal_guard(),
            consumer_keeping_keys_if(keeps_keys, consumer),
            scheduler,
        );
        Box::new(SelectFieldProducer {
            base: ProducerBase::new(
                SelectFieldProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
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
/// **A pull reads every field of the product.** A pull that names one field is unsound through
/// a cumulative cache: [`Memo`] merges what a pull returned and answers later pulls from it
/// without going below, so a pull naming one field would record a partial answer as the
/// whole one, and a sibling selector would read a field never fetched. A pull may name keys
/// of the stream the field sits under, since a key brings every field of its record. A
/// release names this field's part and every other field whole ([`guard_at_field`]).
struct SelectFieldProducer {
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

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    /// A stream of records keeps its keys under the field, so the input is pulled at the
    /// projection. A product of collections has no projection guard of its own: it is pulled
    /// whole, and the field cut after.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let input_guard = match self.input.tiling().is_data_function() {
            true => projection.guard(self.input.tiling()),
            false => self.input.tiling().universal_guard(),
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
            self.input.release(at_field);
        }
        tile.restrict_to(&projection, self.tiling());
        tile
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let released = self.at_field(obsolete_guard);
        self.input.release(released);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        QuietSpy, ReleaseSpy, TestTileProducer,
    };
    use crate::interpreter::{BaseType, ColumnValue, Extent, Value};
    use bit_set::BitSet;
    use std::sync::Mutex;

    fn record_wrap_over(
        input_tile: Tile,
        input_tiling: Tiling,
        name: &str,
    ) -> (RecordWrapProducer, Arc<Mutex<Vec<TileGuard>>>) {
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
        let wrapped = producer.get(producer.tiling().universal_guard());
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
        let (mut producer, log) = record_wrap_over(tile, tiling, "f");
        producer.release(producer.tiling().universal_guard());
        assert!(
            log.lock_now().iter().any(|g| g.is_universal()),
            "the universal release reaches the input, saw {:?}",
            log.lock_now()
        );
    }

    /// A release of the record's keys reaches the input as the same keys.
    #[test]
    fn record_wrap_forwards_a_release_of_its_keys() {
        let (tile, tiling) = keyed_ints();
        let (mut producer, log) = record_wrap_over(tile, tiling, "f");
        let key_zero = Predicate::at_or_below(Value::UInt(0));
        producer.release(TileGuard::Function(FunctionGuard::Domain(key_zero.clone())));
        assert_eq!(
            *log.lock_now(),
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
        let (mut producer, log) = record_wrap_over(tiling.empty_tile(), tiling.clone(), "f");
        let key_zero = TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(
            Value::UInt(0),
        )));
        let field = TileGuard::Record(HashMap::from([(SmolStr::new("f"), key_zero.clone())]));
        producer.release(TileGuard::Function(FunctionGuard::Codomain(Box::new(
            field,
        ))));
        assert_eq!(
            *log.lock_now(),
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
        let mut producer = MakeRecordProducer {
            base: ProducerBase::unowned(MakeRecordProducer::alloc_id(), &out_tiling),
            names: (0..2).map(tuple_field).collect(),
            inputs,
        };

        producer.release(out_tiling.universal_guard());
        for (i, log) in logs.iter().enumerate() {
            let seen = log.lock_now();
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
        let mut producer = MakeRecordProducer {
            base: ProducerBase::unowned(MakeRecordProducer::alloc_id(), &out_tiling),
            names: vec![tuple_field(0)],
            inputs: vec![Box::new(spy)],
        };

        producer.release(out_tiling.empty_guard());
        assert!(
            log.lock_now().is_empty(),
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
        let mut producer = MakeRecordProducer {
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
            *logs[0].lock_now(),
            vec![TileGuard::Scalar(Predicate::True)],
            "the named field's operand is released",
        );
        assert!(
            logs[1].lock_now().iter().all(TileGuard::is_empty),
            "the other operand is not, got {:?}",
            logs[1].lock_now(),
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
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
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
            Box::new(Correlated {
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

    /// A consumer finishing rows of one field releases those rows whole, and every other
    /// field everywhere: nothing beneath the selector reads the others ([`guard_at_field`]).
    #[test]
    fn select_field_releases_finished_rows_and_every_other_field() {
        let input_tiling = record_under_a_level();
        let (spy, log) = ReleaseSpy::new(
            Tile::Scalar(ColumnValue::Ints(vec![])),
            input_tiling.clone(),
        );
        let output_tiling = select_field_tiling(&input_tiling, "a");
        let mut producer = SelectFieldProducer {
            base: ProducerBase::unowned(SelectFieldProducer::alloc_id(), &output_tiling),
            input: Box::new(spy),
            name: "a".into(),
            input_tiling: input_tiling.clone(),
        };
        let rows = TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(Value::UInt(
            0,
        ))));
        producer.release(rows.clone());

        let Tiling::DataFunction { codomain, .. } = &input_tiling else {
            unreachable!("built as a collection")
        };
        let Tiling::Record(fields) = &**codomain else {
            unreachable!("built over a record")
        };
        let other_fields = TileGuard::Function(FunctionGuard::Codomain(Box::new(
            TileGuard::Record(HashMap::from([
                ("a".into(), TileGuard::Scalar(Predicate::False)),
                ("xs".into(), fields["xs"].universal_guard()),
            ])),
        )));
        assert_eq!(
            *log.lock_now(),
            vec![TileGuard::flatten_or(vec![rows, other_fields])],
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
            base: ProducerBase::unowned(SelectFieldProducer::alloc_id(), &field_tiling),
            input: Box::new(spy),
            name: "xs".into(),
            input_tiling,
        };
        producer.get(producer.tiling().universal_guard());
        assert!(
            log.lock_now()
                .iter()
                .any(|g| matches!(g, TileGuard::Record(fields)
                if fields.get("xs").is_some_and(|g| names_key(g, 1, 0)))),
            "the field's row 1 is released: {:?}",
            log.lock_now(),
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
            base: ProducerBase::unowned(SelectFieldProducer::alloc_id(), &field_tiling),
            input: Box::new(TestTileProducer::new(input, input_tiling.clone())),
            name: "a".into(),
            input_tiling,
        };
        let out = producer.get(producer.tiling().universal_guard());
        let Tile::DataFunction {
            domain, codomain, ..
        } = &out
        else {
            panic!("the field is a collection: {out:?}")
        };
        assert_eq!(*domain, ColumnValue::UInts(vec![1]));
        assert_eq!(**codomain, Tile::Scalar(ColumnValue::Ints(vec![5])));
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
            base: ProducerBase::unowned(ZipProducer::alloc_id(), &output_tiling),
            names: vec!["a".into(), "b".into()],
            inputs: vec![Box::new(spy_a), Box::new(spy_b)],
        };
        zip.get(zip.tiling().universal_guard());
        for log in [log_a, log_b] {
            assert!(
                log.lock_now().iter().any(|g| names_key(g, 1, 0)),
                "each input's row 1 is released: {:?}",
                log.lock_now(),
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
            base: ProducerBase::unowned(ZipProducer::alloc_id(), &output_tiling),
            names: vec!["a".into(), "b".into()],
            inputs: vec![
                Box::new(TestTileProducer::new(tile_a, input_tiling.clone())),
                Box::new(TestTileProducer::new(tile_b, input_tiling)),
            ],
        };

        let result = zip.get(zip.tiling().universal_guard());
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
        };
        let out = zip.get(out_tiling.universal_guard());
        let guard = out.to_guard();
        zip.release(guard.clone());
        // Key 0 is open, since the collection arm can still grow under it. The scalar arm's
        // value there is whole once delivered, so it is released at its row — for that arm,
        // its key 0 — and the collection arm is released the inner key it delivered beneath
        // key 0.
        let covers = |log: &Arc<Mutex<Vec<TileGuard>>>, path: &[Value]| {
            log.lock_now()
                .iter()
                .any(|g| TileGuard::flatten_or(vec![g.clone()]).covers_path(path))
        };
        assert!(
            covers(&released0, &[Value::UInt(0)]),
            "the scalar arm was not released its taken value: {:?}, from {guard:?}",
            released0.lock_now()
        );
        assert!(
            covers(&released1, &[Value::UInt(0), Value::UInt(3)]),
            "the collection arm was not released its inner key: {:?}, from {guard:?}",
            released1.lock_now()
        );
        // The row stays while its collection is open, holding no cell of the scalar field.
        let Tile::DataFunction {
            domain, codomain, ..
        } = zip.get(out_tiling.universal_guard())
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
            for g in log.lock_now().iter() {
                assert!(
                    g.check_from(tiling),
                    "{g:?} is not a guard over the arm's tiling {tiling}"
                );
            }
            assert!(
                covers(log, &[Value::UInt(0)]),
                "an arm was not released key 0: {:?}",
                log.lock_now()
            );
        }
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
        let morsel = wrap.get(keys_between(2, 4));
        let Tile::DataFunction { domain, .. } = &morsel else {
            panic!("a collection")
        };
        assert_eq!(domain.len(), 3);
        assert_eq!(*pulled.lock_now(), [keys_between(2, 4)]);
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
        let morsel = select.get(keys_between(1, 3));
        assert_eq!(int_entries(&morsel), [(1, 101), (2, 102), (3, 103)]);
        assert_eq!(*pulled.lock_now(), [keys_between(1, 3)]);
    }

    #[test]
    fn a_field_morsel_is_the_whole_pull_cut_to_it() {
        for guard in [keys_between(0, 1), keys_between(6, 20)] {
            assert_conforms(|| Box::new(amounts_of_records().0), guard);
        }
    }

    /// A product of two collections, as a `Let` or a record of comprehensions makes it, has no
    /// projection guard of its own: the field is read whole from the product and cut after.
    #[test]
    fn a_field_of_a_product_is_pulled_whole_and_cut() {
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
                    base: ProducerBase::unowned(SelectFieldProducer::alloc_id(), &ints()),
                    input: Box::new(input),
                    name: SmolStr::new("a"),
                    input_tiling: product_tiling.clone(),
                },
                pulled,
            )
        };
        let (mut select, pulled) = make();
        let morsel = select.get(keys_between(2, 3));
        assert_eq!(int_entries(&morsel), [(2, 2), (3, 3)]);
        assert_eq!(*pulled.lock_now(), [product_tiling.universal_guard()]);
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
            },
            a_pulled,
            b_pulled,
        )
    }

    /// Both arms are pulled at the morsel, so neither reads the other's rows.
    #[test]
    fn a_pair_of_streams_pulls_each_arm_at_the_morsel() {
        let (mut zip, a_pulled, b_pulled) = pair(ROWS as usize);
        let morsel = zip.get(keys_between(2, 4));
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
        assert_eq!(*a_pulled.lock_now(), [keys_between(2, 4)]);
        assert_eq!(*b_pulled.lock_now(), [keys_between(2, 4)]);
    }

    /// An arm that has delivered less pairs only the keys both hold, and the pair is complete
    /// only where both arms are: the morsel past the slower arm is not stated complete.
    #[test]
    fn a_morsel_past_a_lagging_arm_pairs_the_common_keys_and_states_them_complete() {
        let (mut zip, _, _) = pair(4);
        let morsel = zip.get(keys_between(2, 6));
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
        let (mut zip, a_pulled, b_pulled) = pair(ROWS as usize);
        let nothing = zip.tiling().empty_guard();
        assert_eq!(zip.get(nothing), zip.tiling().empty_tile());
        assert!(a_pulled.lock_now().is_empty() && b_pulled.lock_now().is_empty());
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
        let (mut record, a_pulled, b_pulled) = two_values();
        let whole = record.tiling().universal_guard();
        let tile = record.get(whole);
        let Tile::Record { fields, .. } = &tile else {
            panic!("a record")
        };
        assert_eq!(fields.len(), 2);
        let scalar = Tiling::Scalar(Extent::Base(BaseType::Int)).universal_guard();
        assert_eq!(*a_pulled.lock_now(), std::slice::from_ref(&scalar));
        assert_eq!(*b_pulled.lock_now(), [scalar]);
    }

    #[test]
    fn nothing_makes_no_record_and_pulls_no_value() {
        let (mut record, a_pulled, b_pulled) = two_values();
        let nothing = record.tiling().empty_guard();
        assert_eq!(record.get(nothing), record.tiling().empty_tile());
        assert!(a_pulled.lock_now().is_empty() && b_pulled.lock_now().is_empty());
    }

    #[test]
    #[should_panic(expected = "a record of values, which has no keys to project")]
    fn a_projection_of_keys_is_refused_by_a_record_of_values() {
        let (mut record, _, _) = two_values();
        record.get(keys_between(0, 1));
    }

    #[test]
    fn nothing_wraps_nothing() {
        let (mut wrap, pulled) = wrapped();
        let nothing = wrap.tiling().empty_guard();
        assert_eq!(wrap.get(nothing), wrap.tiling().empty_tile());
        assert!(pulled.lock_now().is_empty());
    }
}
