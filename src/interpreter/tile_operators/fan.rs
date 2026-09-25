use std::collections::HashMap;

use super::*;
use crate::interpreter::operator_graph::{value, value_at};
use crate::{
    interpreter::{Consumer, Scheduler, forwarding_consumer, shared_consumer, tuple_field},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

/// Pairs its operands over their first `depth` levels, producing a collection carrying those
/// levels whose values are a record of what each operand holds below them.
///
/// `depth` is the **ambient iteration** — the levels every operand runs over, which is a
/// property of what they were applied to and not of their own shapes, so the caller states
/// it ([`zip_arms_at`]). Below it the operands may differ, which is what lets one of them
/// hold a collection while its sibling holds a column.
///
/// Output fields are named `_0`, `_1`, … matching the input order.
pub struct Zip {
    /// Output tiling: the ambient levels, with a `Record` where the operands' values sat.
    base: OperatorBase,
    /// Field names in input order, used when producing the output Record tile.
    names: Vec<String>,
    /// The input collections to pair.
    inputs: Vec<Box<dyn TileOperator>>,
    /// The ambient levels the pair sits under.
    depth: usize,
}

/// The number of collection levels `tiling` carries before its values.
pub fn level_count(tiling: &Tiling) -> usize {
    match tiling {
        Tiling::DataFunction { codomain, .. } => 1 + level_count(codomain),
        _ => 0,
    }
}

/// `tiling`'s first `depth` levels, with `inner` beneath them.
fn with_values_at(tiling: &Tiling, depth: usize, inner: Tiling) -> Tiling {
    if depth == 0 {
        return inner;
    }
    let Tiling::DataFunction { domain, codomain } = tiling else {
        unreachable!("the depth was counted off this tiling")
    };
    Tiling::DataFunction {
        domain: domain.clone(),
        codomain: Box::new(with_values_at(codomain, depth - 1, inner)),
    }
}

impl Zip {
    /// Create a `Zip` pairing its operands over their first `depth` levels.
    ///
    /// `depth` is the **ambient iteration** — how many levels the operands were applied
    /// over. It is the caller's to state, not something the operands say: two arms that
    /// agree below the ambient (two projections of one grouped row, say) look pairable all
    /// the way down, and two that differ there are the collection-valued component case.
    pub fn new_at(names: Vec<String>, ops: Vec<Box<dyn TileOperator>>, depth: usize) -> Self {
        assert!(!ops.is_empty(), "Zip requires at least one input");
        assert!(depth > 0, "Zip pairs under at least one ambient level");
        // The operands agree on the ambient levels — they were applied over them — and may
        // differ below, which is what lets one hold a collection while its sibling holds a
        // column. Their runtime *presence* may still differ (one branch has emitted 0..3
        // while another has 0..2), which `ZipProducer::get_impl` intersects.
        for op in ops.iter() {
            for d in 0..depth {
                let (
                    Tiling::DataFunction { domain, .. },
                    Tiling::DataFunction { domain: other, .. },
                ) = (ops[0].tiling().values_at(d), op.tiling().values_at(d))
                else {
                    panic!(
                        "Zip pairs collections over {depth} ambient level(s), got {} and {}",
                        ops[0].tiling(),
                        op.tiling()
                    )
                };
                assert_eq!(
                    domain, other,
                    "Zip's operands share the ambient iteration, so they agree on its keys \
                     at every level"
                );
            }
        }
        let record = Tiling::Record(
            names
                .iter()
                .zip(ops.iter())
                .map(|(name, op)| (name.clone(), op.tiling().values_at(depth).clone()))
                .collect(),
        );
        let tiling = with_values_at(ops[0].tiling(), depth, record);
        Self {
            base: OperatorBase::new(tiling),
            names,
            inputs: ops,
            depth,
        }
    }
}

/// Build the right product combinator for the compiled arms, pairing over `depth` ambient
/// levels.
///
/// A scalar-only product is a record of values ([`MakeRecord`]); anything with a collection
/// among its arms is a pointwise pairing over the ambient iteration ([`Zip`]). `depth` is
/// how many levels that iteration has — the caller's to know, since the arms were applied
/// over it. See the "CCL types vs. tilings" section of
/// [`design-operators.md`](./design-operators.md) for why the same CCL-level `zip` compiles
/// to two different tile operators.
pub fn zip_arms_at(inputs: Vec<Box<dyn TileOperator>>, depth: usize) -> Box<dyn TileOperator> {
    if inputs.iter().all(|op| op.tiling().is_scalar()) {
        return Box::new(MakeRecord::new(inputs));
    }
    let names = (0..inputs.len()).map(tuple_field).collect();
    Box::new(Zip::new_at(names, inputs, depth))
}

/// Named-field variant of [`zip_arms_at`], for record literals.
pub fn zip_arms_named_at(
    inputs: Vec<(String, Box<dyn TileOperator>)>,
    depth: usize,
) -> Box<dyn TileOperator> {
    if inputs.iter().all(|(_, op)| op.tiling().is_scalar()) {
        return Box::new(MakeRecord::new_named(inputs));
    }
    let (names, ops) = inputs.into_iter().unzip();
    Box::new(Zip::new_at(names, ops, depth))
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
        let shared = shared_consumer(consumer);
        Box::new(ZipProducer {
            base: ProducerBase::new(ZipProducer::alloc_id(), self.tiling()),
            names: self.names.clone(),
            depth: self.depth,
            inputs: self
                .inputs
                .iter_mut()
                .map(|i| {
                    i.subscribe(
                        i.tiling().universal_guard(),
                        forwarding_consumer(&shared),
                        scheduler,
                    )
                })
                .collect(),
        })
    }
}

/// Producer for [`Zip`]: pulls each input and assembles a record-codomain tile.
struct ZipProducer {
    base: ProducerBase,
    /// Field names in input order, used when producing the output Record tile.
    names: Vec<String>,
    /// Live input producers, in field order.
    inputs: Vec<Box<dyn TileProducer>>,
    /// The ambient levels the pair sits under ([`Zip`]).
    depth: usize,
}

impl TileProducer for ZipProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, mut node: InspectNode, opts: &VizOptions) -> InspectNode {
        for (i, input) in self.inputs.iter().enumerate() {
            node = node.child(format!("_{i}"), input.inspect(opts));
        }
        node
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // Cost note: the presence-intersection path below runs
        // unconditionally on every pull — N predicate intersections, N
        // `to_remove` minuses, and one `remove_guarded` per input.  Non-
        // cyclic zips over well-aligned inputs pay the same per-pull
        // cost as the mutation-loop body's lagging-branch case (where the
        // recursive_input legitimately trails the source branch).  If
        // profiling later shows this on a hot path, consider gating the
        // intersection on a `cyclic: bool` constructor flag (mirroring
        // `FanOut::new` vs `FanOut::new_cyclic`) and keeping the simpler
        // "all inputs agree" path for zips that can't lag.
        let tiles: Vec<Tile> = self
            .inputs
            .iter_mut()
            .map(|i| i.get(i.tiling().universal_guard()))
            .collect();

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
                for t in tiles.iter() {
                    let Tile::DataFunction {
                        domain,
                        domain_predicate,
                        ..
                    } = t
                    else {
                        panic!("Zip: cannot mix function and non-function tiles")
                    };
                    let p = Predicate::from_column_value(domain);
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
                let mut skeleton: Option<Tile> = None;
                let mut codomains: Vec<Tile> = Vec::with_capacity(tiles.len());
                for mut filtered in tiles.into_iter() {
                    let Tile::DataFunction { domain, .. } = &filtered else {
                        unreachable!()
                    };
                    let to_remove = Predicate::from_column_value(domain).minus(&presence);
                    if to_remove.as_bool() != Some(false) {
                        filtered
                            .remove_guarded(TileGuard::Function(FunctionGuard::Domain(to_remove)));
                    }
                    filtered.compact();
                    // Lift the values out, leaving the chain of keys behind: what stays is
                    // the output's own shape, and every input has to agree on it.
                    codomains.push(std::mem::replace(
                        filtered.values_at_mut(self.depth),
                        Tile::Record(HashMap::new()),
                    ));
                    // Presence is intersected over the outermost keys only, so arms that
                    // disagree beneath them would pair one arm's values under another's keys.
                    assert!(
                        skeleton.as_ref().is_none_or(|s: &Tile| {
                            s.key_levels()[..self.depth] == filtered.key_levels()[..self.depth]
                        }),
                        "Zip: inputs disagree on the levels they are paired over"
                    );
                    skeleton.get_or_insert(filtered);
                }

                let names = &self.names;
                let codomain_record = Tile::Record(
                    codomains
                        .into_iter()
                        .enumerate()
                        .map(move |(i, cv)| (names[i].clone(), cv))
                        .collect(),
                );
                let mut out = skeleton.expect("Zip has at least one input");
                *out.values_at_mut(self.depth) = codomain_record;
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
        self.inputs.iter_mut().for_each(|i| {
            i.release(match &obsolete_guard {
                g if g.is_universal() => i.tiling().universal_guard(),
                g if g.is_empty() => i.tiling().empty_guard(),
                TileGuard::Function(FunctionGuard::Domain(p)) => {
                    TileGuard::Function(FunctionGuard::Domain(p.clone()))
                }
                TileGuard::Function(FunctionGuard::Codomain(g)) => {
                    TileGuard::Function(FunctionGuard::Codomain(g.clone()))
                }
                g => unimplemented!("Zip cannot honor the release guard {g:?}"),
            })
        });
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
    names: Vec<String>,
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
    pub fn new_named(inputs: Vec<(String, Box<dyn TileOperator>)>) -> Self {
        assert!(!inputs.is_empty(), "MakeRecord requires at least one input");
        let (names, ops) = inputs.into_iter().unzip();
        Self::new_impl(names, ops)
    }

    fn new_impl(names: Vec<String>, inputs: Vec<Box<dyn TileOperator>>) -> Self {
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
        let shared = shared_consumer(consumer);
        Box::new(MakeRecordProducer {
            base: ProducerBase::new(MakeRecordProducer::alloc_id(), self.tiling()),
            names: self.names.clone(),
            inputs: self
                .inputs
                .iter_mut()
                .map(|i| {
                    i.subscribe(
                        i.tiling().universal_guard(),
                        forwarding_consumer(&shared),
                        scheduler,
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
    names: Vec<String>,
    inputs: Vec<Box<dyn TileProducer>>,
}

impl TileProducer for MakeRecordProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, mut node: InspectNode, opts: &VizOptions) -> InspectNode {
        for (i, input) in self.inputs.iter().enumerate() {
            node = node.child(format!("{i}"), input.inspect(opts));
        }
        node
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // Every operand is pulled whole ([`SelectFieldProducer`] says why a narrowed pull
        // is unsound). An operand withholds what [`Self::release_impl`] told it a consumer
        // finished with, so a field that settled early is not re-delivered.
        let fields: HashMap<String, Tile> = self
            .names
            .iter()
            .zip(self.inputs.iter_mut())
            .map(|(name, input)| {
                let tile = input.get(input.tiling().universal_guard());
                (name.clone(), tile)
            })
            .collect();
        Tile::Record(fields)
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

/// Pick one field out of a **product value**: the eliminator for [`MakeRecord`], handing
/// back that field's tile.
///
/// The `RecordField` application is the other projection, and it reads a record one row
/// at a time, so every field must fit in a column. See
/// `src/interpreter/design-operators.md`, "A product value is a record of tiles".
pub struct SelectField {
    base: OperatorBase,
    /// The product whose field this selects.
    input: Box<dyn TileOperator>,
    /// The field's name — `_0`, `_1`, … for a tuple.
    name: String,
}

/// What a selector of field `name` releases of the product `tiling`, given its consumer's
/// release `guard` of that field: `guard` placed at the field, under one `Codomain` wrapper
/// per level the record sits beneath, and nothing on the other fields.
///
/// TODO(exact-field-release): this release is lossy, which the guard algebra forbids
/// (`src/interpreter/design-operators.md`, "Guard operations are exact"). Do not copy it. It
/// drops a guard naming keys of a level above the record, and releases nothing of the other
/// fields, so a `FanOut` meeting two selectors releases nothing at all. The exact release is
/// `guard` on this field and every other field whole, and the `FanOut` meet of two of those
/// beneath a level names one field's cells under some of the rows. That region needs a scalar
/// guard qualified by the rows above it, which the guard algebra cannot spell yet.
fn guard_at_field(tiling: &Tiling, name: &str, guard: TileGuard) -> TileGuard {
    match tiling {
        Tiling::DataFunction { codomain, .. } => match guard {
            TileGuard::Function(FunctionGuard::Codomain(inner)) => TileGuard::Function(
                FunctionGuard::Codomain(Box::new(guard_at_field(codomain, name, *inner))),
            ),
            TileGuard::Or(arms) => TileGuard::flatten_or(
                arms.into_iter()
                    .map(|arm| guard_at_field(tiling, name, arm))
                    .collect(),
            ),
            _ => tiling.empty_guard(),
        },
        Tiling::Record(_) => {
            let TileGuard::Record(mut fields) = tiling.empty_guard() else {
                unreachable!("a record tiling answers a record guard")
            };
            fields.insert(name.to_string(), guard);
            TileGuard::Record(fields)
        }
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
    pub fn new(input: Box<dyn TileOperator>, name: impl Into<String>) -> Self {
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
        // An intent may only widen on its way upstream, so the input is asked for all of
        // it. [`guard_at_field`] narrows, which is sound for a release and not here.
        let input_tiling = self.input.tiling().clone();
        let input_producer =
            self.input
                .subscribe(input_tiling.universal_guard(), consumer, scheduler);
        Box::new(SelectFieldProducer {
            base: ProducerBase::new(SelectFieldProducer::alloc_id(), self.tiling()),
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
/// **A pull reads the whole product.** A narrowed pull is unsound through a cumulative
/// cache: [`Memo`] merges what a pull returned and answers later pulls from it without going
/// below, so a pull naming one field would record a partial answer as the whole one, and a
/// sibling selector would read a field never fetched. A release names only this field's
/// part ([`guard_at_field`], whose TODO says why that is lossy).
struct SelectFieldProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    name: String,
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

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let mut tile = self.input.get(self.input.tiling().universal_guard());
        // The record stands at the chain's deepest values, so the field takes its place and
        // every level above it is left where it was.
        let slot = tile.deepest_values_mut();
        let Tile::Record(mut fields) = std::mem::replace(slot, Tile::Record(HashMap::new())) else {
            panic!("SelectField({}) expected a record tile", self.name);
        };
        *slot = fields.remove(&self.name).unwrap_or_else(|| {
            panic!(
                "SelectField({}) over a record tile with no such field",
                self.name
            )
        });
        // The input is released only where every reader of it has released, and less than
        // that ([`guard_at_field`]), so it can still hold what this consumer released.
        tile.remove_guarded(self.obsolete_guard().clone());
        tile.compact();
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
    use crate::interpreter::tile_operators::test_helpers::{ReleaseSpy, TestTileProducer};
    use crate::interpreter::{BaseType, ColumnValue, Extent, Value};
    use bit_set::BitSet;

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
            base: ProducerBase::new(MakeRecordProducer::alloc_id(), &out_tiling),
            names: (0..2).map(tuple_field).collect(),
            inputs,
        };

        producer.release(out_tiling.universal_guard());
        for (i, log) in logs.iter().enumerate() {
            let seen = log.borrow();
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
            base: ProducerBase::new(MakeRecordProducer::alloc_id(), &out_tiling),
            names: vec![tuple_field(0)],
            inputs: vec![Box::new(spy)],
        };

        producer.release(out_tiling.empty_guard());
        assert!(
            log.borrow().is_empty(),
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
        let names: Vec<String> = (0..2).map(tuple_field).collect();
        let out_tiling =
            Tiling::Record(names.iter().map(|n| (n.clone(), tiling.clone())).collect());
        let mut producer = MakeRecordProducer {
            base: ProducerBase::new(MakeRecordProducer::alloc_id(), &out_tiling),
            names: names.clone(),
            inputs,
        };

        // Field `_0` released, `_1` still live — neither empty nor universal.
        let partial = TileGuard::Record(
            [
                (names[0].clone(), TileGuard::Scalar(true)),
                (names[1].clone(), TileGuard::Scalar(false)),
            ]
            .into_iter()
            .collect(),
        );
        producer.release(partial);

        assert_eq!(
            *logs[0].borrow(),
            vec![TileGuard::Scalar(true)],
            "the named field's operand is released",
        );
        assert!(
            logs[1].borrow().iter().all(TileGuard::is_empty),
            "the other operand is not, got {:?}",
            logs[1].borrow(),
        );
    }

    /// `UInt ⤇ {a: Int, xs: UInt ⤇ Int}`: a record holding a collection, under a level.
    fn record_under_a_level() -> Tiling {
        Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Record(HashMap::from([
                ("a".to_string(), Tiling::Scalar(Extent::Base(BaseType::Int))),
                (
                    "xs".to_string(),
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
                TilePathStep::Record("a".to_string())
            ]),
        );
    }

    /// A release naming rows of the level above the record reaches nothing upstream today
    /// (TODO(exact-field-release) on [`guard_at_field`]). This pins the gap: the exact release
    /// names those rows, and this assertion flips when the guard algebra can spell it.
    #[test]
    fn select_field_drops_a_release_naming_rows_above_the_record() {
        let input_tiling = record_under_a_level();
        let (spy, log) = ReleaseSpy::new(
            Tile::Scalar(ColumnValue::Ints(vec![])),
            input_tiling.clone(),
        );
        let output_tiling = select_field_tiling(&input_tiling, "a");
        let mut producer = SelectFieldProducer {
            base: ProducerBase::new(SelectFieldProducer::alloc_id(), &output_tiling),
            input: Box::new(spy),
            name: "a".to_string(),
            input_tiling,
        };
        producer.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::LessThanEq(Value::UInt(0)),
        )));
        assert!(
            log.borrow().iter().all(TileGuard::is_empty),
            "the rows reach upstream now, so the TODO is done: {:?}",
            log.borrow(),
        );
    }

    // ── ZipProducer: asymmetric per-branch presence ────────────────────────
    //
    // Regression for the per-branch presence-intersection added to
    // `ZipProducer::get_impl` for cyclic mutation loops, where one branch
    // (the body) can have emitted more positions than another (a still-
    // converging `recursive_input`).  Before the intersection step, the
    // output tile carried whichever branch happened to be at index 0 of
    // the inputs vec — fine for branches that always advance in lockstep,
    // wrong as soon as they don't.
    //
    // We construct two `DataFunction` test tiles over the same domain
    // type but with *different actual positions present* (branch A has
    // positions [0, 1, 2]; branch B has only [0, 1]) and a `ZipProducer`
    // directly over them, then check that the merged output is restricted
    // to the intersection [0, 1].

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
                (
                    "a".to_string(),
                    Tiling::Scalar(Extent::Base(BaseType::UInt)),
                ),
                (
                    "b".to_string(),
                    Tiling::Scalar(Extent::Base(BaseType::UInt)),
                ),
            ])),
        );
        let mut zip = ZipProducer {
            depth: 1,
            base: ProducerBase::new(ZipProducer::alloc_id(), &output_tiling),
            names: vec!["a".to_string(), "b".to_string()],
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

        let Tile::Record(field_tiles) = *codomain else {
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
}
