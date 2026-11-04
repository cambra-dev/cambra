use bit_set::BitSet;
use log::trace;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

use super::*;
use crate::interpreter::nest_levels;
use crate::interpreter::operator_graph::value;
use crate::{
    ccl::AggregateKind,
    interpreter::{ColumnValue, Consumer, Projection, Scheduler, Value},
};

/// Folds a collection's values into one [`Tile::Aggregation`].
///
/// Accumulation, completion, and release follow `src/interpreter/design-operators.md`,
/// "Aggregation and extraction". [`ExtractAggregate`] reads the terminal result.
pub struct Aggregate {
    /// The `DataFunction`-typed input whose codomain elements are aggregated.
    input: Box<dyn TileOperator>,
    base: OperatorBase,
}

impl Aggregate {
    /// Construct an `Aggregate` operator.
    ///
    /// Panics if `input` does not have a `DataFunction` tiling, or if `kind`
    /// does not support the codomain element type.
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind) -> Self {
        let err = || panic!("Cannot apply {kind:?} to non-function {:?}", input.tiling());
        let values = input.tiling().codomain().unwrap_or_else(err);
        let tiling = Tiling::Aggregation {
            kind,
            accumulator: Box::new(kind.output_tiling(&values).unwrap_or_else(err)),
        };
        Self {
            base: OperatorBase::new(tiling),
            input,
        }
    }
}

impl TileOperator for Aggregate {
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
        let input = BreakerInput::new(consumer, self.input.tiling(), false, scheduler);
        let input_producer = self.input.subscribe(
            self.input.tiling().universal_guard(),
            input.consumer,
            scheduler,
        );
        Box::new(AggregateProducer::new(
            ProducerBase::new(
                AggregateProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            )
            .breaking(input.downstream, input.placement),
            input_producer,
        ))
    }
}

struct AggregateProducer {
    base: ProducerBase,
    /// The subscribed input producer.
    input: Box<dyn TileProducer>,
    /// The aggregation operation.
    kind: AggregateKind,
    /// Running accumulation state; updated in place on each `get`.
    accumulator: Tile,
    /// Suppresses subsequent emissions after universal release.
    released: bool,
    /// Whether [`Breaker::consume_impl`] has run: a consuming aggregate answers from its
    /// accumulator and never pulls its input.
    consuming: bool,
}

/// An aggregate over `input` that nothing subscribed, for a test that builds a chain of pipelines
/// by hand.
#[cfg(test)]
pub(crate) fn aggregate_over(
    input: Box<dyn TileProducer>,
    tiling: &Tiling,
) -> crate::interpreter::dispatcher::BreakerHandle {
    Rc::new(RefCell::new(AggregateProducer::new(
        ProducerBase::unowned(AggregateProducer::alloc_id(), tiling),
        input,
    )))
}

/// An extraction of a `kind` aggregation from `input` that nothing subscribed, answering
/// `tiling`, for a test that builds a chain of pipelines by hand.
#[cfg(test)]
pub(crate) fn extract_aggregate_over(
    input: Box<dyn TileProducer>,
    tiling: &Tiling,
    kind: AggregateKind,
) -> crate::interpreter::dispatcher::BreakerHandle {
    Rc::new(RefCell::new(ExtractAggregateProducer::new(
        ProducerBase::unowned(ExtractAggregateProducer::alloc_id(), tiling),
        input,
        kind,
    )))
}

impl AggregateProducer {
    /// Initialize through [`AggregateKind::initial_accumulator`]. An extremum without an identity
    /// starts without a value and waits for its first element.
    fn new(base: ProducerBase, input: Box<dyn TileProducer>) -> Self {
        let (kind, accumulator) = match &base.tiling {
            Tiling::Aggregation {
                kind,
                accumulator: acc_tiling,
            } => (
                *kind,
                Tile::Aggregation {
                    kind: *kind,
                    accumulator: Box::new(kind.initial_accumulator(acc_tiling)),
                    terminal: ColumnValue::Bools(vec![false; 1]),
                },
            ),
            other => panic!("AggregateProducer created with non-Aggregation tiling: {other:?}"),
        };
        Self {
            base,
            input,
            kind,
            accumulator,
            released: false,
            consuming: false,
        }
    }

    /// Pull the input at `guard`, fold what it answers into the accumulator, and release the
    /// input at what the answer stated. The accumulator is terminal once the input is released
    /// whole.
    fn fold_input(&mut self, guard: TileGuard) {
        let mut input_result = self.input.get(guard);
        let upstream_guard = input_result.to_guard();
        input_result.compact();
        let Tile::DataFunction { codomain, .. } = input_result else {
            panic!("Aggregate expected a collection, got {input_result:?}");
        };
        self.input.release(upstream_guard);
        let values = *codomain;

        let is_terminal = self.input.obsolete_guard().is_universal();
        trace!(
            "Aggregate input is_terminal: {is_terminal} from guard {:?}",
            self.input.obsolete_guard()
        );
        let Tile::Aggregation {
            kind: _,
            ref mut accumulator,
            terminal: ColumnValue::Bools(ref mut terminal),
        } = self.accumulator
        else {
            panic!("Accumulator must be Aggregation tile")
        };
        self.kind.accumulate(accumulator, &values, 0, values.rows());
        terminal[0] = is_terminal;
    }

    /// The accumulator, or nothing while an extreme with no identity has no element: no
    /// terminal flag can be emitted before the accumulator has a value.
    fn answer(&self) -> Tile {
        let Tile::Aggregation {
            ref accumulator,
            terminal: ColumnValue::Bools(ref terminal),
            ..
        } = self.accumulator
        else {
            panic!("Accumulator must be Aggregation tile")
        };
        if self.kind.awaits_first_element(accumulator) {
            if terminal[0] {
                self.kind.no_extreme_of_nothing();
            }
            return self.tiling().empty_tile();
        }
        self.accumulator.clone()
    }
}

impl TileProducer for AggregateProducer {
    fn state_info(&self) -> ProducerStateInfo {
        ProducerStateInfo::holding(self.accumulator.cell_count())
    }

    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit("input", &mut *self.input);
    }

    fn as_breaking_mut(&mut self) -> Option<&mut dyn BreakingProducer> {
        Some(self)
    }

    /// An accumulator has no keys to project, so the projection is all of it or none. The
    /// input is read whole whatever the consumer asks.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection =
            projection_of_one_value(&self.name(), "is one accumulator", &projection_guard);
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        if self.released {
            return self.tiling().empty_tile();
        }
        if self.consuming {
            return self.offer_impl(projection_guard);
        }
        self.fold_input(self.input.tiling().universal_guard());
        self.answer()
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Universal release also covers input not yet delivered. Per-delivery releases in
        // `get_impl` cover only the received tiles.
        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            self.released = true;
            self.input.release(self.input.tiling().universal_guard());
        }
    }
}

impl Breaker for AggregateProducer {
    /// Folds what the input answers at `guard`, a guard of the input's tiling, into the
    /// accumulator, and releases the input at what the answer stated. The aggregate stays
    /// consuming.
    fn consume_impl(&mut self, _: InputId, guard: TileGuard) {
        debug_assert!(
            guard.check_from(self.input.tiling()),
            "{} consumes a guard of its input's tiling: {guard:?}",
            self.name()
        );
        self.consuming = true;
        if self.released || guard.projection(&self.input.name()) == Projection::Nothing {
            return;
        }
        self.fold_input(guard);
    }

    fn input_tiling(&self, _: InputId) -> Tiling {
        self.input.tiling().clone()
    }

    fn input_released(&self, _: InputId) -> TileGuard {
        self.input.obsolete_guard().clone()
    }

    /// Pushes the accumulator once it is final.
    ///
    /// # Panics
    ///
    /// At the last epoch, where the output is not released and the input has not been released
    /// whole. A dispatcher issues no `consume_impl` after the last epoch, so the accumulator would
    /// stay partial and the reader would get no value.
    fn finish(&mut self, pushes: &mut Pushes<'_>, last: bool) {
        assert!(
            !last || self.released || self.input.obsolete_guard().is_universal(),
            "{} finishes the last epoch after its input was released whole",
            self.name()
        );
        pushes.push_final(self);
    }

    fn as_producer(&self) -> Option<&dyn BreakingProducer> {
        Some(self)
    }
}

impl BreakingProducer for AggregateProducer {
    /// The accumulator is one value, held once it is final, when the input has been released
    /// whole, and unless an extreme has not seen its first element. A partial accumulator is held
    /// by no guard, so nothing reads it as final.
    fn held(&self) -> TileGuard {
        let Tile::Aggregation { accumulator, .. } = &self.accumulator else {
            panic!("Accumulator must be Aggregation tile")
        };
        if !self.input.obsolete_guard().is_universal() {
            return self.tiling().empty_guard();
        }
        match self.kind.awaits_first_element(accumulator) {
            true => self.tiling().empty_guard(),
            false => self.tiling().universal_guard(),
        }
    }

    fn offer_impl(&mut self, guard: TileGuard) -> Tile {
        let projection = projection_of_one_value(&self.name(), "is one accumulator", &guard);
        if projection == Projection::Nothing || self.released {
            return self.tiling().empty_tile();
        }
        self.answer()
    }
}

/// Extracts a terminal result from an aggregation. Partial-result extraction is unsupported.
pub struct ExtractAggregate {
    input: Box<dyn TileOperator>,
    base: OperatorBase,
    kind: AggregateKind,
    only_terminal: bool,
}

impl ExtractAggregate {
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind, only_terminal: bool) -> Self {
        let tiling = if only_terminal {
            Tiling::Scalar(input.extent())
        } else {
            todo!("functions on partial aggregates")
        };
        Self {
            base: OperatorBase::new(tiling),
            input,
            kind,
            only_terminal,
        }
    }
}

impl TileOperator for ExtractAggregate {
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
        let input = BreakerInput::new(consumer, self.input.tiling(), false, scheduler);
        let mut producer = ExtractAggregateProducer::new(
            ProducerBase::new(
                ExtractAggregateProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            )
            .breaking(input.downstream, input.placement),
            self.input.subscribe(
                self.input.tiling().universal_guard(),
                input.consumer,
                scheduler,
            ),
            self.kind,
        );
        producer.only_terminal = self.only_terminal;
        Box::new(producer)
    }
}

struct ExtractAggregateProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    kind: AggregateKind,
    only_terminal: bool,
    /// The value a consume extracted from a terminal input, until the consumer releases the
    /// output. Empty before then.
    extracted: Tile,
    /// Whether [`Breaker::consume_impl`] has run: a consuming extraction answers from
    /// what it extracted and never pulls its input.
    consuming: bool,
}

impl ExtractAggregateProducer {
    fn new(base: ProducerBase, input: Box<dyn TileProducer>, kind: AggregateKind) -> Self {
        let extracted = base.tiling.empty_tile();
        Self {
            base,
            input,
            kind,
            only_terminal: true,
            extracted,
            consuming: false,
        }
    }

    /// The value `input_result` extracts to, or nothing while the input is not terminal.
    fn extract(&self, input_result: Tile) -> Tile {
        let Tile::Aggregation {
            kind: _,
            accumulator,
            terminal,
        } = input_result
        else {
            panic!(
                "ExtractAggregate expected Aggregation tiling, got {:?}",
                self.input.tiling()
            );
        };
        // An empty tile has no terminal flag; it is not the completed fold of an empty input.
        if terminal.is_empty() {
            return self.tiling().empty_tile();
        }
        if self.only_terminal {
            if terminal.index_at(0).as_bool() {
                self.kind.extract(*accumulator)
            } else {
                self.tiling().empty_tile()
            }
        } else {
            todo!()
        }
    }
}

impl TileProducer for ExtractAggregateProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit("input", &mut *self.input);
    }

    fn as_breaking_mut(&mut self) -> Option<&mut dyn BreakingProducer> {
        Some(self)
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection =
            projection_of_one_value(&self.name(), "extracts one value", &projection_guard);
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        if self.consuming {
            return self.offer_impl(projection_guard);
        }
        let input_result = self.input.get(self.input.tiling().universal_guard());
        self.extract(input_result)
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            self.extracted = self.tiling().empty_tile();
            self.input.release(self.input.tiling().universal_guard());
        }
    }
}

impl Breaker for ExtractAggregateProducer {
    /// Pulls the input at `guard`, a guard of the aggregation, and extracts its value once the
    /// input is terminal. A terminal input is released at what it stated, which is all of it. A
    /// partial one states nothing releasable, so it is left for the next consume. Once the value
    /// is extracted, or the output released, the input is not pulled again.
    fn consume_impl(&mut self, _: InputId, guard: TileGuard) {
        debug_assert!(
            guard.check_from(self.input.tiling()),
            "{} consumes a guard of its input's tiling: {guard:?}",
            self.name()
        );
        self.consuming = true;
        if !self.extracted.is_empty()
            || self.obsolete_guard().is_universal()
            || guard.projection(&self.input.name()) == Projection::Nothing
        {
            return;
        }
        let input_result = self.input.get(guard);
        let upstream_guard = input_result.to_guard();
        let value = self.extract(input_result);
        if !value.is_empty() {
            self.extracted = value;
        }
        self.input.release(upstream_guard);
    }

    fn input_tiling(&self, _: InputId) -> Tiling {
        self.input.tiling().clone()
    }

    fn input_released(&self, _: InputId) -> TileGuard {
        self.input.obsolete_guard().clone()
    }

    fn as_producer(&self) -> Option<&dyn BreakingProducer> {
        Some(self)
    }
}

impl BreakingProducer for ExtractAggregateProducer {
    /// The extracted value, once there is one.
    fn held(&self) -> TileGuard {
        match self.extracted.is_empty() {
            true => self.tiling().empty_guard(),
            false => self.tiling().universal_guard(),
        }
    }

    fn offer_impl(&mut self, guard: TileGuard) -> Tile {
        let projection = projection_of_one_value(&self.name(), "extracts one value", &guard);
        match projection {
            Projection::Nothing => self.tiling().empty_tile(),
            _ => self.extracted.clone(),
        }
    }
}

/// Extracts terminal results beneath a chain of collection levels.
///
/// Preserves the enclosing levels and removes innermost keys whose aggregation is not terminal.
/// See `src/interpreter/design-operators.md`, "Aggregation and extraction".
pub struct MapExtractAggregate {
    input: Box<dyn TileOperator>,
    /// The aggregation operation used to extract final values from accumulators.
    kind: AggregateKind,
    base: OperatorBase,
}

impl MapExtractAggregate {
    /// Create a new `MapExtractAggregate` operator.
    ///
    /// `input` must be a collection chain ending in `Aggregation { accumulator: A }`, at
    /// whatever depth. The output replaces that aggregation with what it extracts to.
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind) -> Self {
        assert!(
            input.tiling().is_data_function(),
            "MapExtractAggregate expected a collection input, got {}",
            input.tiling()
        );
        let tiling = extract_innermost(input.tiling());
        Self {
            base: OperatorBase::new(tiling),
            input,
            kind,
        }
    }
}

/// Replace the aggregation a collection chain ends in with the value it extracts to.
fn extract_innermost(tiling: &Tiling) -> Tiling {
    match tiling {
        Tiling::DataFunction { domain, codomain } => Tiling::DataFunction {
            domain: domain.clone(),
            codomain: Box::new(extract_innermost(codomain)),
        },
        Tiling::Aggregation { accumulator, .. } => (**accumulator).clone(),
        t => panic!("MapExtractAggregate expected an aggregation under the keys, got {t}"),
    }
}

impl TileOperator for MapExtractAggregate {
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
        // The groups keep the input's outermost keys.
        let input_producer =
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler);
        Box::new(MapExtractAggregateProducer {
            base: ProducerBase::new(
                MapExtractAggregateProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            input: input_producer,
            kind: self.kind,
        })
    }
}

/// Producer for [`MapExtractAggregate`].
struct MapExtractAggregateProducer {
    base: ProducerBase,
    /// The subscribed input producer.
    input: Box<dyn TileProducer>,
    /// The aggregation operation used to extract final values.
    kind: AggregateKind,
}

impl TileProducer for MapExtractAggregateProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit("input", &mut *self.input);
    }

    /// The keys of every level of the input are the output's, and only what sits under the
    /// innermost changes. A `Sole` aggregation's element can be a collection, and that
    /// collection's levels are no levels of the input.
    fn restates(&self) -> Restates {
        Restates::Above(CurryLevel::new(self.input.tiling().levels()))
    }

    /// Every level keeps the input's keys and only the unfinished ones drop, so the input is
    /// pulled at the projection, and the answer keeps its keys.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection_for(self);
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let mut output = self.input.get(projection.guard(self.input.tiling()));
        // Every level passes through; only what sits under the innermost changes, and the
        // non-terminal keys of that level go. Keeping the levels is what leaves a deeper
        // fold's grouping intact for the fold above it.
        let slot = output.deepest_values_mut();
        let folded = std::mem::replace(slot, Tile::record(HashMap::new()));
        let Tile::Aggregation {
            accumulator,
            terminal,
            ..
        } = folded
        else {
            panic!("MapExtractAggregate expected an aggregation under the keys, got {folded:?}")
        };
        // Emit only the elements whose aggregation is terminal.
        let mask = terminal
            .as_bools()
            .unwrap_or_else(|| panic!("Expected bools"));
        *slot = self.kind.extract(*accumulator);
        // One bool per accumulator, so the mask is over the innermost collection's keys.
        output
            .innermost_level_mut()
            .unwrap_or_else(|| unreachable!("the input tiles as a collection"))
            .retain_keys(mask);
        output
    }

    /// Restates releases through the unchanged collection levels. Releasing part of an
    /// extracted value does not release its input aggregation.
    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        self.input.release(match obsolete_guard {
            g if g.is_universal() => self.input.tiling().universal_guard(),
            g if g.is_empty() => self.input.tiling().empty_guard(),
            // What sits under the innermost level is the extract, not the input's
            // aggregation, so only a release of all of it reaches the input's values.
            g @ (TileGuard::Function(_) | TileGuard::Or(_)) => {
                let input = self.input.tiling();
                crate::interpreter::tiling::through_shared_levels(g, input.levels(), input)
            }
            g => unreachable!("MapExtractAggregate's tiling is a collection, released by {g:?}"),
        });
    }
}

/// Order two element paths lexicographically.
///
/// One level's keys share a type, so comparing two paths compares like with like at every
/// component and the order is total — which is what [`build_levels_from_paths`] needs, a
/// parent's children being contiguous only under one.
///
/// [`Value`] is `PartialOrd` and not `Ord`, so that precondition is checked rather than
/// assumed. Treating an incomparable pair as equal would not restore the order: the
/// comparison would fall through to the next component and sort a parent's children apart,
/// leaving the rebuild to emit one key twice. `MapResult` makes the same demand of a domain
/// it sorts (`Tile::DataFunction`'s keys, `map.rs`).
fn compare_paths(a: &[Value], b: &[Value]) -> Ordering {
    for (x, y) in a.iter().zip(b) {
        match x.partial_cmp(y) {
            Some(Ordering::Equal) => continue,
            Some(other) => return other,
            None => panic!(
                "a level holds keys of two types, so its elements have no order: \
                 {x:?} against {y:?}"
            ),
        }
    }
    a.len().cmp(&b.len())
}

/// Rebuild a function of `extents.len()` domain levels from the sorted paths of its
/// innermost elements, with `codomain` already vectorized over those elements.
///
/// Each level nests inside the one above it, so a new key at a level starts its run of
/// children where the level below has reached. The paths must arrive sorted: a parent's
/// children are contiguous only then.
fn build_levels_from_paths(
    paths: &[&[Value]],
    extents: &[Extent],
    codomain: Tile,
    domain_predicate: Predicate,
) -> Tile {
    let depth = extents.len();
    let mut columns: Vec<Vec<Value>> = vec![Vec::new(); depth];
    let mut starts: Vec<Vec<usize>> = vec![Vec::new(); depth.saturating_sub(1)];
    let mut last: Vec<Option<Vec<Value>>> = vec![None; depth];
    for path in paths {
        // A path may stop short of the innermost level: a key with nothing beneath.
        for level in 0..path.len() {
            let prefix = &path[..=level];
            if last[level].as_deref() == Some(prefix) {
                continue;
            }
            if level + 1 < depth {
                starts[level].push(columns[level + 1].len());
            }
            columns[level].push(path[level].clone());
            last[level] = Some(prefix.to_vec());
            // A new element invalidates every prefix below it, so the next path opens fresh
            // elements there instead of extending the previous parent's last child.
            for deeper in last.iter_mut().skip(level + 1) {
                *deeper = None;
            }
        }
    }
    let mut domains: Vec<ColumnValue> = columns
        .into_iter()
        .zip(extents)
        .map(|(values, extent)| ColumnValue::from_values(values, extent))
        .collect();
    if depth == 1 {
        return Tile::data_function(
            domains.pop().unwrap_or_else(|| unreachable!()),
            Box::new(codomain),
            domain_predicate,
            BitSet::new(),
        );
    }
    nest_levels(domains, starts, codomain, domain_predicate)
}

/// Collapses the innermost collection of a nested tile into an aggregation, leaving the
/// levels above it intact.
///
/// Accumulators use complete key paths to distinguish equal keys under different parents.
/// Completion and release follow `src/interpreter/design-operators.md`,
/// "Aggregation and extraction".
pub struct MapAggregate {
    /// The lookup-function input to aggregate per key.
    input: Box<dyn TileOperator>,
    /// The aggregation operation (Sum, Max, …).
    kind: AggregateKind,
    base: OperatorBase,
}

impl MapAggregate {
    /// Create a new `MapAggregate` operator.
    ///
    /// `input` must have a `DataFunction` tiling whose codomain is a collection; `kind` must
    /// support that collection's element type. The innermost level becomes an
    /// `Aggregation` and the levels above it are left as they are
    /// ([`fold_innermost`]), so a two-level input yields
    /// `DataFunction { domain, codomain: Aggregation { .. } }`.
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind) -> Self {
        // A collection whose values are not themselves a collection has no level above the
        // one being folded, which is `Aggregate`'s shape rather than this one's.
        let Tiling::DataFunction { codomain, .. } = input.tiling() else {
            panic!(
                "MapAggregate requires a collection input, got {}",
                input.tiling()
            )
        };
        assert!(
            matches!(codomain.as_ref(), Tiling::DataFunction { .. }),
            "MapAggregate folds a collection of collections, got {}",
            input.tiling()
        );
        let tiling = fold_innermost(input.tiling(), kind);
        Self {
            base: OperatorBase::new(tiling),
            input,
            kind,
        }
    }
}

/// Replace `tiling`'s innermost collection with the aggregation that folds it.
fn fold_innermost(tiling: &Tiling, kind: AggregateKind) -> Tiling {
    let Tiling::DataFunction { domain, codomain } = tiling else {
        panic!("fold_innermost walks a chain of collections, got {tiling}")
    };
    match codomain.as_ref() {
        Tiling::DataFunction { .. } => Tiling::DataFunction {
            domain: domain.clone(),
            codomain: Box::new(fold_innermost(codomain, kind)),
        },
        inner => {
            let accumulator = kind
                .output_tiling(inner)
                .unwrap_or_else(|| panic!("Cannot apply {kind:?} to values {inner}"));
            Tiling::Aggregation {
                kind,
                accumulator: Box::new(accumulator),
            }
        }
    }
}

/// A folded tiling's key extent per level, outermost first, and the accumulator tiling the
/// chain ends in.
fn folded_shape(tiling: &Tiling) -> (Vec<Extent>, Tiling) {
    let mut extents = Vec::new();
    let mut node = tiling;
    loop {
        match node {
            Tiling::DataFunction { domain, codomain } => {
                extents.push(domain.clone());
                node = codomain;
            }
            Tiling::Aggregation { accumulator, .. } => return (extents, (**accumulator).clone()),
            other => panic!("MapAggregate leaves collections around an aggregation, got {other}"),
        }
    }
}

impl TileOperator for MapAggregate {
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
        // The groups keep the input's outermost keys.
        let input = BreakerInput::new(consumer, self.input.tiling(), true, scheduler);
        let input_producer = self.input.subscribe(
            self.input.tiling().universal_guard(),
            input.consumer,
            scheduler,
        );
        Box::new(MapAggregateProducer::new(
            ProducerBase::new(
                MapAggregateProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            )
            .breaking(input.downstream, input.placement),
            input_producer,
            self.kind,
        ))
    }
}

/// Producer for [`MapAggregate`].
struct MapAggregateProducer {
    base: ProducerBase,
    /// The subscribed lookup-function producer.
    input: Box<dyn TileProducer>,
    /// The aggregation operation.
    kind: AggregateKind,
    /// Running accumulators indexed by complete paths, outermost key first.
    accumulators: HashMap<Vec<Value>, Tile>,
    /// Keys above the accumulators whose every accumulator was released without the key
    /// itself: a key is there only through what it maps to, and a release naming part of
    /// what lies beneath leaves it in place, holding nothing unreleased
    /// (`src/interpreter/design-operators.md`, "The completeness contract").
    emptied_keys: HashSet<Vec<Value>>,
    /// Whether [`Breaker::consume_impl`] has run: a consuming map aggregate answers from
    /// its accumulators and never pulls its input.
    consuming: bool,
    /// What the answers consumed state about completeness, together.
    stated: Option<Stated>,
}

/// A map-aggregate over `input` that nothing subscribed, folding each group with `kind` into the
/// output `tiling`, for a test that builds a chain of pipelines by hand.
#[cfg(test)]
pub(crate) fn map_aggregate_over(
    input: Box<dyn TileProducer>,
    tiling: &Tiling,
    kind: AggregateKind,
) -> crate::interpreter::dispatcher::BreakerHandle {
    Rc::new(RefCell::new(MapAggregateProducer::new(
        ProducerBase::unowned(MapAggregateProducer::alloc_id(), tiling),
        input,
        kind,
    )))
}

impl MapAggregateProducer {
    fn new(base: ProducerBase, input: Box<dyn TileProducer>, kind: AggregateKind) -> Self {
        Self {
            base,
            input,
            kind,
            accumulators: HashMap::new(),
            emptied_keys: HashSet::new(),
            consuming: false,
            stated: None,
        }
    }

    /// Pull the input at `guard`, fold what it answers into the accumulators, and release the
    /// input at what the answer stated. What the answer states about completeness comes back.
    fn read_input(&mut self, guard: TileGuard) -> Stated {
        let mut input_tile = self.input.get(guard);
        trace!("{} received {input_tile:?}", self.name());
        let upstream_guard = input_tile.to_guard();
        input_tile.compact();
        let stated = self.fold(&input_tile);
        // Release received values
        self.input.release(upstream_guard);
        stated
    }

    /// Fold the groups of `input_tile` into the accumulators.
    fn fold(&mut self, input_tile: &Tile) -> Stated {
        let Tile::DataFunction {
            domain_predicate,
            absent_keys,
            ..
        } = input_tile
        else {
            panic!("MapAggregate requires a collection tile, got {input_tile:?}")
        };
        // A group known absent is complete: it has no element to fold, in any region.
        let domain_predicate = domain_predicate.union(absent_keys);

        // The collection being folded is the innermost one, and the rows it stands over
        // are the groups: `parent_paths` names them, one path per group.
        //
        // Every level above it states its own completion, which is collected here: a level
        // says which of *its* keys are closed, and no other level says it for it.
        let depth = input_tile.innermost_depth().unwrap_or_else(|| {
            panic!("MapAggregate folds a collection of collections, got {input_tile:?}")
        });
        assert!(
            depth >= 1,
            "MapAggregate folds a collection of collections, so the fold sits under a \
             level: {input_tile:?}"
        );
        let level_predicates: Vec<Predicate> = (0..depth)
            .map(|level| {
                let Tile::DataFunction {
                    domain_predicate, ..
                } = input_tile.values_at(CurryLevel::new(level))
                else {
                    unreachable!("every level above the innermost one is a collection")
                };
                domain_predicate.clone()
            })
            .collect();
        let parent_paths = input_tile.row_paths_at(depth);
        let folded = input_tile.values_at(CurryLevel::new(depth));
        let Tile::DataFunction {
            codomain,
            domain_predicate: elements,
            ..
        } = folded
        else {
            unreachable!("the loop breaks on a collection")
        };
        let elements = elements.clone();
        // Which groups are complete, over whole paths: those some level on the path calls
        // complete ([`Tile::completion_at`]). `Stated::settled` adds the held groups whose every
        // element the folded level calls complete.
        let complete = input_tile.completion_at(CurryLevel::new(depth - 1));
        let values = (**codomain).clone();
        let (_, output_tiling) = folded_shape(self.tiling());

        // Fold each group into its row's accumulator. A group is a contiguous run of the
        // folded collection's values, so the fold stays vectorized.
        let kind = &self.kind;
        let accumulators = &mut self.accumulators;
        for (row, path) in parent_paths.iter().enumerate() {
            let (start, end) = folded.row_run(row);
            let acc = accumulators
                .entry(path.clone())
                .or_insert_with(|| kind.initial_accumulator(&output_tiling));
            kind.accumulate(acc, &values, start, end);
        }

        Stated {
            domain_predicate,
            level_predicates,
            elements,
            complete,
        }
        .settled(self.accumulators.keys())
    }

    /// The output over every accumulator held, with the completeness `stated` names, cut to
    /// `projection`.
    fn build(&self, stated: &Stated, projection: &Projection) -> Tile {
        let Stated {
            domain_predicate,
            level_predicates,
            complete,
            ..
        } = stated;
        let (extents, output_tiling) = folded_shape(self.tiling());
        let kind = &self.kind;
        // Completion is per path. An inner group can be complete while its enclosing
        // collections remain open; `complete` combines the statements at every level.
        let mut entries: Vec<(Vec<Value>, Tile)> = self
            .accumulators
            .iter()
            .map(|(path, acc)| (path.clone(), acc.clone()))
            .collect();
        // Sorted so the outermost column stays ordered and a parent's children sit
        // contiguously, which is what rebuilding the offsets assumes.
        entries.sort_by(|a, b| compare_paths(&a.0, &b.0));
        // Omit identity-free extrema until they have values; a completed empty group is invalid.
        entries.retain(|(path, acc)| {
            if !kind.awaits_first_element(acc) {
                return true;
            }
            if complete.contains_path(path) {
                kind.no_extreme_of_nothing();
            }
            false
        });

        let terminal: Vec<bool> = entries
            .iter()
            .map(|(path, _)| complete.contains_path(path))
            .collect();
        // One accumulator per key, run together in path order: a scalar fold's rows are a
        // column, and `Sole`'s are the elements' own levels.
        let mut accumulator = output_tiling.empty_at_no_rows();
        for (_, acc) in &entries {
            accumulator.merge_rows(acc.clone());
        }
        let aggregation = Tile::Aggregation {
            kind: self.kind,
            accumulator: Box::new(accumulator),
            terminal: ColumnValue::Bools(terminal),
        };
        let mut paths: Vec<&[Value]> = entries.iter().map(|(path, _)| path.as_slice()).collect();
        paths.extend(
            self.emptied_keys
                .iter()
                .filter(|key| !entries.iter().any(|(path, _)| path.starts_with(key)))
                .map(Vec::as_slice),
        );
        paths.sort_by(|a, b| compare_paths(a, b));
        let mut out =
            build_levels_from_paths(&paths, &extents, aggregation, domain_predicate.clone());
        // Each level beneath the outermost holds the input's keys at that level, so it
        // states what the input's does there: a group settles once some level on its path
        // is complete, and a level saying nothing would leave it looking open downstream.
        for (level, stated) in level_predicates.iter().enumerate().skip(1) {
            if let Tile::DataFunction {
                domain_predicate, ..
            } = out.values_at_mut(CurryLevel::new(level))
            {
                *domain_predicate = stated.clone();
            }
        }
        out.restrict_to(projection, self.tiling());
        out
    }
}

/// What the answers of a map aggregate's input state about completeness: the outermost keys
/// that are complete, each level's, the folded level's, and the groups that are, over whole
/// paths.
struct Stated {
    domain_predicate: Predicate,
    level_predicates: Vec<Predicate>,
    /// The folded level's statement: the elements no answer will add to, over whole paths.
    elements: Predicate,
    complete: Predicate,
}

impl Stated {
    /// What two answers state together.
    fn union(&self, other: &Stated) -> Stated {
        Stated {
            domain_predicate: self.domain_predicate.union(&other.domain_predicate),
            level_predicates: self
                .level_predicates
                .iter()
                .zip(&other.level_predicates)
                .map(|(a, b)| a.union(b))
                .collect(),
            elements: self.elements.union(&other.elements),
            complete: self.complete.union(&other.complete),
        }
    }

    /// This statement with each of `groups`, the paths of the groups held, called complete where
    /// the elements' statement covers every element under it, in `complete` and at the groups'
    /// level: an answer of a pull beneath the groups' keys states only the elements it reads, so
    /// a group's elements can be stated complete in parts across answers, and a group that will
    /// gain no element is complete at its level, as the input would state it of an answer
    /// naming the whole group.
    fn settled<'a>(mut self, groups: impl Iterator<Item = &'a Vec<Value>>) -> Stated {
        let depth = self.level_predicates.len();
        let whole = Predicate::union_all(
            groups
                .filter(|path| {
                    debug_assert_eq!(
                        path.len(),
                        depth,
                        "a group's path names a key at every level above the folded one"
                    );
                    !self.complete.contains_path(path) && self.elements.within(path, 0).is_true()
                })
                .map(|path| Predicate::exactly(path))
                .collect(),
        );
        if whole.is_false() {
            return self;
        }
        self.complete = self.complete.union(&whole);
        let at_groups = self
            .level_predicates
            .last_mut()
            .expect("a map aggregate folds beneath at least one level");
        *at_groups = at_groups.union(&whole);
        if depth == 1 {
            self.domain_predicate = self.domain_predicate.union(&whole);
        }
        self
    }
}

impl TileProducer for MapAggregateProducer {
    fn state_info(&self) -> ProducerStateInfo {
        let accumulators: usize = self
            .accumulators
            .iter()
            .map(|(path, acc)| path.len() + acc.cell_count())
            .sum();
        ProducerStateInfo::holding(accumulators + self.emptied_keys.len())
    }

    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit("input", &mut *self.input);
    }

    fn as_breaking_mut(&mut self) -> Option<&mut dyn BreakingProducer> {
        Some(self)
    }

    /// Every level of the output is a level of the input, and the aggregation folds only the
    /// innermost beneath them.
    fn restates(&self) -> Restates {
        Restates::Every
    }

    /// The keys at every level are the input's, with each group beneath one whole, so the input
    /// is pulled at the projection and the answer is cut to it: accumulators for keys pulled
    /// earlier stay held, and a pull names the keys it wants. What the answers state is kept
    /// across pulls with the accumulators, since a pull beneath the groups' keys states only the
    /// elements it reads (`Stated::settled`).
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection_for(self);
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        if self.consuming {
            return self.offer_impl(projection_guard);
        }
        let stated = self.read_input(projection.guard(self.input.tiling()));
        let stated = match self.stated.take() {
            Some(before) => before.union(&stated).settled(self.accumulators.keys()),
            None => stated,
        };
        let answer = self.build(&stated, &projection);
        self.stated = Some(stated);
        answer
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Remove covered accumulators before another pull rebuilds the output from this map.
        match obsolete_guard {
            g if g.is_empty() => {}
            g if g.is_universal() => {
                self.accumulators.clear();
                self.emptied_keys.clear();
                self.input.release(self.input.tiling().universal_guard());
            }
            // Preserve unreleased ancestor keys even when their last accumulator is removed.
            // The input has a collection where the output has an accumulator, so restate
            // the guard through their shared levels rather than forwarding it unchanged.
            g => {
                let released: Vec<Vec<Value>> = self
                    .accumulators
                    .keys()
                    .filter(|path| g.covers_path(path))
                    .cloned()
                    .collect();
                self.accumulators.retain(|path, _| !g.covers_path(path));
                for path in released {
                    for len in 1..path.len() {
                        let key = &path[..len];
                        if !g.covers_path(key) {
                            self.emptied_keys.insert(key.to_vec());
                        }
                    }
                }
                self.emptied_keys.retain(|key| !g.covers_path(key));
                let levels = self.tiling().levels();
                let input = self.input.tiling();
                self.input
                    .release(crate::interpreter::tiling::through_shared_levels(
                        g, levels, input,
                    ));
            }
        }
    }
}

impl Breaker for MapAggregateProducer {
    /// Folds the groups the input answers at `guard`, a guard of the input's tiling, into the
    /// accumulators, releases the input at what the answer stated, and keeps what the answers
    /// state about completeness, together. The producer stays consuming.
    fn consume_impl(&mut self, _: InputId, guard: TileGuard) {
        debug_assert!(
            guard.check_from(self.input.tiling()),
            "{} consumes a guard of its input's tiling: {guard:?}",
            self.name()
        );
        self.consuming = true;
        if guard.is_empty() {
            return;
        }
        let stated = self.read_input(guard);
        self.stated = Some(match self.stated.take() {
            Some(before) => before.union(&stated).settled(self.accumulators.keys()),
            None => stated,
        });
    }

    fn input_tiling(&self, _: InputId) -> Tiling {
        self.input.tiling().clone()
    }

    fn input_released(&self, _: InputId) -> TileGuard {
        self.input.obsolete_guard().clone()
    }

    fn as_producer(&self) -> Option<&dyn BreakingProducer> {
        Some(self)
    }
}

impl BreakingProducer for MapAggregateProducer {
    /// It holds an accumulator per group beneath the groups' keys, and what is left of that
    /// after a release beneath them is a region beneath the outermost keys, and a reader's chain
    /// may restate only the outermost keys (`TileProducer::restates`).
    fn pushes_while_consuming(&self) -> bool {
        false
    }

    /// The guard of the output the accumulators build, less every group whose accumulator is not
    /// terminal; empty before the first consume. A group still folding holds no decided value, so
    /// a push names it once its input is complete, and a reader that read it before reads it again
    /// then (`Pushes::push_final` pushes each region once).
    fn held(&self) -> TileGuard {
        let Some(stated) = &self.stated else {
            return self.tiling().empty_guard();
        };
        let built = self.build(stated, &Projection::Everything).to_guard();
        let folding: Vec<Predicate> = self
            .accumulators
            .keys()
            .filter(|path| !stated.complete.contains_path(path))
            .map(|path| Predicate::exactly(path))
            .collect();
        let Some(depth) = self.accumulators.keys().next().map(Vec::len) else {
            return built;
        };
        debug_assert!(
            self.accumulators.keys().all(|path| path.len() == depth),
            "every group of a map aggregate is keyed at the same depth"
        );
        match Projection::keys_at(CurryLevel::new(depth - 1), Predicate::union_all(folding)) {
            Projection::Nothing => built,
            folding => guard_minus(&built, &folding.collection_guard()),
        }
    }

    /// Cut at the groups the accumulators hold.
    fn morsels(&self, guard: &TileGuard, rows: usize) -> Vec<TileGuard> {
        let Some(stated) = &self.stated else {
            return vec![guard.clone()];
        };
        let output = self.build(stated, &Projection::Everything);
        let keys = output.live_keys().into_iter().flatten();
        cut_at_keys(guard, keys.map(|(_, key)| key), rows, self.tiling())
    }

    fn offer_impl(&mut self, guard: TileGuard) -> Tile {
        let projection = guard.projection_for(self);
        match (projection, &self.stated) {
            (Projection::Nothing, _) | (_, None) => self.tiling().empty_tile(),
            (projection, Some(stated)) => self.build(stated, &projection),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{QuietSpy, ReleaseSpy};
    use crate::interpreter::{BaseType, Extent, Predicate, Tile};
    fn int_function(domain: Vec<u64>, values: Vec<i64>) -> Tile {
        Tile::data_function(
            ColumnValue::from_uints(domain),
            Box::new(Tile::Scalar(ColumnValue::Ints(values))),
            Predicate::True,
            BitSet::new(),
        )
    }

    /// A pulled aggregate keeps what its answers state across pulls, so a group whose elements
    /// two answers state complete in parts is terminal once the parts cover it.
    #[test]
    fn a_pulled_group_stated_complete_in_parts_is_terminal() {
        use crate::interpreter::tile_operators::test_helpers::ScriptedProducer;
        let point = |k: u64| Predicate::point(Value::UInt(k));
        let input_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        let through_two = Predicate::at_or_below(Value::UInt(2));
        // Group 0's elements, stated complete through `stated` beneath it.
        let group = |keys: Vec<u64>, values: Vec<i64>, stated: Predicate| {
            Tile::data_function(
                ColumnValue::UInts(vec![0]),
                Box::new(Tile::grouped(
                    vec![0],
                    ColumnValue::from_uints(keys),
                    Box::new(Tile::Scalar(ColumnValue::Ints(values))),
                    Predicate::qualified(point(0), stated),
                    BitSet::new(),
                )),
                Predicate::False,
                BitSet::new(),
            )
        };
        let (input, cell) = ScriptedProducer::new(
            group(vec![0, 1, 2], vec![1, 2, 3], through_two.clone()),
            input_tiling,
        );
        let output = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
            },
        );
        let mut sums = MapAggregateProducer::new(
            ProducerBase::unowned(MapAggregateProducer::alloc_id(), &output),
            Box::new(input),
            AggregateKind::Sum,
        );
        let key = TileGuard::Function(FunctionGuard::Domain(point(0)));
        sums.get(key.clone());
        *cell.borrow_mut() = group(vec![3, 4], vec![4, 5], Predicate::True.minus(&through_two));
        let answer = sums.get(key);
        let Tile::DataFunction { codomain, .. } = &answer else {
            panic!("a collection of sums, got {answer:?}")
        };
        assert!(codomain.is_terminal(), "{answer:?}");
    }

    /// Beneath an enclosing level, a group still folding is left out of what the aggregate holds
    /// decided, and its sibling settled by the same answer is not.
    #[test]
    fn a_folding_group_beneath_a_level_is_not_held_decided() {
        use crate::interpreter::tile_operators::test_helpers::ProjectionSpy;
        let uints = || Extent::Base(BaseType::UInt);
        let input_tiling = Tiling::data_function(
            uints(),
            Tiling::data_function(
                uints(),
                Tiling::data_function(uints(), Tiling::Scalar(Extent::Base(BaseType::Int))),
            ),
        );
        // Row 0 holds groups 0 and 1, each of elements 0 and 1; group 0 is stated whole and
        // group 1 through element 1.
        let groups = Tile::grouped(
            vec![0],
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 2],
                ColumnValue::UInts(vec![0, 1, 0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3, 4]))),
                Predicate::qualified(
                    Predicate::exactly(&[Value::UInt(0), Value::UInt(0)]),
                    Predicate::True,
                )
                .union(&Predicate::qualified(
                    Predicate::exactly(&[Value::UInt(0), Value::UInt(1)]),
                    Predicate::at_or_below(Value::UInt(1)),
                )),
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );
        let input = Tile::data_function(
            ColumnValue::UInts(vec![0]),
            Box::new(groups),
            Predicate::False,
            BitSet::new(),
        );
        let (input, _, _) = ProjectionSpy::new(input, input_tiling.clone());
        let output = Tiling::data_function(
            uints(),
            Tiling::data_function(
                uints(),
                Tiling::Aggregation {
                    kind: AggregateKind::Sum,
                    accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
                },
            ),
        );
        let mut sums = MapAggregateProducer::new(
            ProducerBase::unowned(MapAggregateProducer::alloc_id(), &output),
            Box::new(input),
            AggregateKind::Sum,
        );
        sums.consume_impl(InputId::ONLY, input_tiling.universal_guard());
        let held = sums.held();
        let group = |g: u64| [Value::UInt(0), Value::UInt(g)];
        assert!(held.covers_path(&group(0)), "group 0 is settled: {held:?}");
        assert!(
            !held.covers_path(&group(1)),
            "group 1 is still folding: {held:?}"
        );
    }

    /// A group whose elements two answers state complete in parts is complete once the parts
    /// cover every element, as answers of pulls beneath the groups' keys state them; until then
    /// its accumulator is not terminal and the aggregate holds nothing decided under its key.
    #[test]
    fn a_group_stated_complete_in_parts_settles_once_they_cover_it() {
        use crate::interpreter::tile_operators::test_helpers::{ProjectionSpy, paths_guard};
        let point = |k: u64| Predicate::point(Value::UInt(k));
        let input_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        // Group 0 holds the elements 0 to 4, every one stated complete.
        let whole = Tile::data_function(
            ColumnValue::UInts(vec![0]),
            Box::new(int_function(vec![0, 1, 2, 3, 4], vec![1, 2, 3, 4, 5])),
            Predicate::True,
            BitSet::new(),
        );
        let (input, _, _) = ProjectionSpy::new(whole, input_tiling);
        let output = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
            },
        );
        let mut sums = MapAggregateProducer::new(
            ProducerBase::unowned(MapAggregateProducer::alloc_id(), &output),
            Box::new(input),
            AggregateKind::Sum,
        );
        let through_two = Predicate::at_or_below(Value::UInt(2));
        sums.consume_impl(
            InputId::ONLY,
            paths_guard(Predicate::qualified(point(0), through_two.clone())),
        );
        assert!(
            !sums.held().covers_path(&[Value::UInt(0)]),
            "group 0 is still folding: {:?}",
            sums.held()
        );
        sums.consume_impl(
            InputId::ONLY,
            paths_guard(Predicate::qualified(
                point(0),
                Predicate::True.minus(&through_two),
            )),
        );
        assert!(
            sums.held().covers_path(&[Value::UInt(0)]),
            "{:?}",
            sums.held()
        );
        let answer = sums.offer_impl(output.universal_guard());
        let Tile::DataFunction {
            codomain,
            domain_predicate,
            ..
        } = &answer
        else {
            panic!("a collection of sums, got {answer:?}")
        };
        assert!(domain_predicate.contains(&Value::UInt(0)), "{answer:?}");
        assert!(codomain.is_terminal(), "{answer:?}");
    }

    /// An `Aggregate`'s accumulator *is* its whole output, so once the consumer
    /// has released it there is nothing left to hand back. Re-emitting it would
    /// return released data, which a caching consumer merges into itself twice.
    #[test]
    fn aggregate_goes_quiet_after_a_universal_release() {
        let in_tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let (spy, _released) = ReleaseSpy::new(int_function(vec![0, 1], vec![10, 20]), in_tiling);
        let tiling = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        let mut producer = AggregateProducer::new(
            ProducerBase::unowned(AggregateProducer::alloc_id(), &tiling),
            Box::new(spy),
        );

        let first = producer.get(tiling.universal_guard());
        let Tile::Aggregation { accumulator, .. } = &first else {
            panic!("expected an Aggregation tile, got {first:?}");
        };
        assert_eq!(
            *accumulator,
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![30])))
        );

        producer.release(tiling.universal_guard());
        assert_eq!(
            producer.get(tiling.universal_guard()),
            tiling.empty_tile(),
            "a released accumulator must not be handed back"
        );
    }

    /// The release also has to reach the input in full. `get_impl` only releases
    /// what was actually delivered, so an aggregate finishing before its source
    /// ran dry would otherwise strand the remainder upstream.
    #[test]
    fn aggregate_releases_its_input_universally() {
        let in_tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let (spy, released) = ReleaseSpy::new(int_function(vec![0], vec![10]), in_tiling.clone());
        let tiling = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        let mut producer = AggregateProducer::new(
            ProducerBase::unowned(AggregateProducer::alloc_id(), &tiling),
            Box::new(spy),
        );

        producer.release(tiling.universal_guard());
        assert!(
            released.borrow().iter().any(TileGuard::is_universal),
            "expected a universal release to reach the input, got {:?}",
            released.borrow()
        );
        let _ = in_tiling;
    }

    /// A **per-key** release drops exactly those accumulators. `get_impl` rebuilds its
    /// output from every accumulator it holds, so a kept-but-released key is re-emitted.
    ///
    /// The input here declares itself final, so the first pull already releases it whole
    /// ([`Tile::to_guard`]) and every later guard is covered by that one. Forwarding is
    /// therefore not observable on this fixture, and
    /// [`map_aggregate_forwards_a_per_key_release_to_an_open_input`] pins it on one where
    /// it is.
    #[test]
    fn map_aggregate_drops_a_per_key_release() {
        let key_extent = Extent::Base(BaseType::Int);
        let in_tiling = Tiling::data_function(
            key_extent.clone(),
            Tiling::data_function(
                Extent::Base(BaseType::Int),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        // Keys 1 and 2, each with two values: 1 -> [10, 20], 2 -> [30, 40].
        let tile = Tile::data_function(
            ColumnValue::Ints(vec![1, 2]),
            Box::new(Tile::grouped(
                vec![0, 2],
                ColumnValue::Ints(vec![0, 1, 0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30, 40]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let (spy, released) = QuietSpy::new(tile, in_tiling.clone());
        let out_tiling = Tiling::data_function(
            key_extent,
            Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
            },
        );
        let mut producer = MapAggregateProducer::new(
            ProducerBase::unowned(MapAggregateProducer::alloc_id(), &out_tiling),
            Box::new(spy),
            AggregateKind::Sum,
        );

        let first = producer.get(out_tiling.universal_guard());
        let Tile::DataFunction { domain, .. } = &first else {
            panic!("expected a collection, got {first:?}");
        };
        assert_eq!(domain.len(), 2, "both keys aggregate on the first pull");

        // Release key 1 only.
        let key_one = TileGuard::Function(FunctionGuard::Domain(Predicate::Intervals(
            intervalsets::IntervalSet::from(intervalsets::Interval::closed(
                Value::Int(1),
                Value::Int(1),
            )),
        )));
        producer.release(key_one.clone());

        // Key 1 is released at the input, by the universal release the first pull already
        // issued. Which guard covered it is the sibling test's subject, not this one's.
        assert!(
            released
                .borrow()
                .iter()
                .any(|g| g.is_universal() || *g == key_one),
            "the released key must be covered at the input, got {:?}",
            released.borrow()
        );
        let second = producer.get(out_tiling.universal_guard());
        let Tile::DataFunction { domain, .. } = &second else {
            panic!("expected a collection, got {second:?}");
        };
        assert_eq!(
            domain.index_at(0),
            Value::Int(2),
            "only the unreleased key may be emitted, got {second:?}"
        );
        assert_eq!(domain.len(), 1, "the released key must be gone: {second:?}");
    }

    /// A per-key release **reaches the input**, which the case above cannot show.
    ///
    /// Key 2's group is still growing, so [`Tile::to_guard`] stops inside it and the first
    /// pull releases only the path as far as it got. Releasing key 2 whole reaches past
    /// that path, making it the one guard the producer has to forward for the key to be
    /// reclaimed — the input's own keys being this producer's accumulator key set. A key
    /// the first pull already covered would be dropped by the release accumulation in
    /// [`TileProducer::release`] instead, and show nothing about forwarding.
    #[test]
    fn map_aggregate_forwards_a_per_key_release_to_an_open_input() {
        let key_extent = Extent::Base(BaseType::Int);
        let in_tiling = Tiling::data_function(
            key_extent.clone(),
            Tiling::data_function(
                Extent::Base(BaseType::Int),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        // Key 1 holds its whole group; key 2 has delivered the first of its two.
        let tile = Tile::data_function(
            ColumnValue::Ints(vec![1, 2]),
            Box::new(Tile::grouped(
                vec![0, 2],
                ColumnValue::Ints(vec![0, 1, 0]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::at_or_below(Value::Int(1)),
            BitSet::new(),
        );
        let (spy, released) = QuietSpy::new(tile, in_tiling.clone());
        let out_tiling = Tiling::data_function(
            key_extent,
            Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
            },
        );
        let mut producer = MapAggregateProducer::new(
            ProducerBase::unowned(MapAggregateProducer::alloc_id(), &out_tiling),
            Box::new(spy),
            AggregateKind::Sum,
        );
        producer.get(out_tiling.universal_guard());
        assert!(
            !released.borrow().iter().any(TileGuard::is_universal),
            "a bounded predicate is not released whole, got {:?}",
            released.borrow()
        );

        let key_two = TileGuard::Function(FunctionGuard::Domain(Predicate::Intervals(
            intervalsets::IntervalSet::from(intervalsets::Interval::closed(
                Value::Int(2),
                Value::Int(2),
            )),
        )));
        producer.release(key_two.clone());
        assert!(
            released.borrow().contains(&key_two),
            "the per-key release must reach the input, got {:?}",
            released.borrow()
        );
    }

    /// An input holding the group `[0, 2, 1]` under an open outer key, the order `Tile::merge`
    /// gives two interleaving deliveries. The first pull sums 330 and releases what it read,
    /// so a second pull adds nothing.
    #[test]
    fn a_sum_over_a_group_held_out_of_order_counts_each_element_once() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let in_tiling =
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int())));
        let tile = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::grouped(
                vec![0],
                ColumnValue::from_uints(vec![0, 2, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![100, 120, 110]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );
        let (spy, _) = QuietSpy::new(tile, in_tiling);
        let out_tiling = Tiling::data_function(
            uint(),
            Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(Tiling::Scalar(int())),
            },
        );
        let mut producer = MapAggregateProducer::new(
            ProducerBase::unowned(MapAggregateProducer::alloc_id(), &out_tiling),
            Box::new(spy),
            AggregateKind::Sum,
        );
        producer.get(out_tiling.universal_guard());
        let second = producer.get(out_tiling.universal_guard());
        let Tile::Aggregation { accumulator, .. } = second.values_at(CurryLevel::new(1)) else {
            panic!("the fold sits beneath one level, got {second:?}")
        };
        assert_eq!(
            **accumulator,
            Tile::Scalar(ColumnValue::Ints(vec![330])),
            "each element counted once"
        );
    }

    /// A group the input settles at an inner level is stated settled at the same level of
    /// the output, which holds the input's keys there.
    #[test]
    fn map_aggregate_states_a_settled_group_at_its_own_level() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let in_tiling = Tiling::data_function(
            uint(),
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int()))),
        );
        // Outer row 0 is open; the level beneath calls key 0 under row 0 complete, so the
        // group at (0, 0) is whole.
        let tile = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::grouped(
                vec![0],
                ColumnValue::from_uints(vec![0]),
                Box::new(Tile::grouped(
                    vec![0],
                    ColumnValue::from_uints(vec![0, 1]),
                    Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20]))),
                    Predicate::False,
                    BitSet::new(),
                )),
                Predicate::qualified(Predicate::point(Value::UInt(0)), Predicate::True),
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );
        let (spy, _released) = QuietSpy::new(tile, in_tiling);
        let out_tiling = Tiling::data_function(
            uint(),
            Tiling::data_function(
                uint(),
                Tiling::Aggregation {
                    kind: AggregateKind::Sum,
                    accumulator: Box::new(Tiling::Scalar(int())),
                },
            ),
        );
        let mut producer = MapAggregateProducer::new(
            ProducerBase::unowned(MapAggregateProducer::alloc_id(), &out_tiling),
            Box::new(spy),
            AggregateKind::Sum,
        );
        let out = producer.get(out_tiling.universal_guard());
        let Tile::Aggregation { terminal, .. } = out.values_at(CurryLevel::new(2)) else {
            panic!("the fold sits beneath two levels, got {out:?}")
        };
        assert_eq!(
            terminal,
            &ColumnValue::Bools(vec![true; 1]),
            "the any-level rule settles the group: {out:?}"
        );
        let Tile::DataFunction {
            domain_predicate, ..
        } = out.values_at(CurryLevel::new(1))
        else {
            panic!("the output's second level is a collection, got {out:?}")
        };
        assert!(
            domain_predicate.contains_path(&[Value::UInt(0), Value::UInt(0)]),
            "the input settles (0, 0) at this level, and the output says nothing: \
             {domain_predicate:?}"
        );
    }
}

#[cfg(test)]
mod aggregate_projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, ints_by_position, keys_between,
    };
    use crate::interpreter::{BaseType, Extent, Tile};

    /// `sum(xs)` over a finished stream `[1, 2, 3, 4]`, with the stream's pulls logged.
    fn sum_of_finished_stream() -> (AggregateProducer, GuardLog) {
        let in_tiling = Tiling::data_function(
            Extent::uint_range(4),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let (stream, pulled, _) =
            ProjectionSpy::new(ints_by_position(&[1, 2, 3, 4], true), in_tiling);
        let tiling = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        (
            AggregateProducer::new(
                ProducerBase::unowned(AggregateProducer::alloc_id(), &tiling),
                Box::new(stream),
            ),
            pulled,
        )
    }

    /// `sum(evens ++ odds)` while the odd arm delivers late. Each pull of the union returns
    /// what the arms hold and have not had released, and the aggregate releases what it folded,
    /// so a row is folded once however many times the union is pulled: the sum grows by the
    /// rows that arrive and by nothing else.
    #[test]
    fn a_sum_over_a_union_folds_each_row_once_across_pulls() {
        use crate::interpreter::tile_operators::UnionOperator;
        use crate::interpreter::tile_operators::test_helpers::{ScriptedOp, int_column};
        use crate::interpreter::{FunctionGuard, Predicate, Scheduler, Value};

        let stream = Tiling::data_function(
            Extent::uint_range(8),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let TileGuard::Function(FunctionGuard::Domain(through_3)) = keys_between(0, 3) else {
            unreachable!("keys_between names a key region")
        };
        let (even, _) = ScriptedOp::new(
            int_column(vec![0, 2, 4, 6], Predicate::True),
            stream.clone(),
        );
        let (odd, odd_cell) = ScriptedOp::new(int_column(vec![1, 3], through_3), stream);
        let union = UnionOperator::new_flat(
            vec![Box::new(even), Box::new(odd)],
            Extent::Base(BaseType::Int),
        );
        let mut sum = Aggregate::new(Box::new(union), AggregateKind::Sum);
        let mut scheduler = Scheduler::new();
        let mut producer = sum.subscribe(
            sum.tiling().universal_guard(),
            Box::new(|| {}),
            &mut scheduler,
        );
        let total = |tile: Tile| {
            let Tile::Aggregation {
                accumulator,
                terminal,
                ..
            } = tile
            else {
                panic!("an aggregation, got {tile:?}")
            };
            (*accumulator, terminal)
        };
        let open = || ColumnValue::Bools(vec![false]);

        // The odd arm has decided `0..=3` only, so the sum is a running one.
        let (first, terminal) = total(producer.get(sum.tiling().universal_guard()));
        assert_eq!(
            first,
            Tile::Scalar(ColumnValue::Ints(vec![1 + 2 + 3 + 4 + 6]))
        );
        assert_eq!(terminal, open());

        // Nothing has arrived since, so the same pull adds nothing and stays open.
        let (again, terminal) = total(producer.get(sum.tiling().universal_guard()));
        assert_eq!(again, first);
        assert_eq!(terminal, open());

        // The odd arm delivers row 5 without finishing: the sum takes it once and stays open.
        *odd_cell.borrow_mut() = int_column(vec![1, 3, 5], Predicate::exactly(&[Value::UInt(5)]));
        let (partial, terminal) = total(producer.get(sum.tiling().universal_guard()));
        assert_eq!(partial, Tile::Scalar(ColumnValue::Ints(vec![16 + 5])));
        assert_eq!(terminal, open());

        // Both arms have now decided every position, so the sum is final.
        *odd_cell.borrow_mut() = int_column(vec![1, 3, 5, 7], Predicate::True);
        let (last, terminal) = total(producer.get(sum.tiling().universal_guard()));
        assert_eq!(last, Tile::Scalar(ColumnValue::Ints(vec![(0..8).sum()])));
        assert_eq!(terminal, ColumnValue::Bools(vec![true]));
    }

    /// The fold reads the whole stream, and what it answers is one terminal accumulator.
    #[test]
    fn a_sum_reads_the_whole_stream() {
        let (mut sum, pulled) = sum_of_finished_stream();
        let tile = sum.get(sum.tiling().universal_guard());
        let Tile::Aggregation {
            accumulator,
            terminal,
            ..
        } = tile
        else {
            panic!("an aggregation")
        };
        assert_eq!(*accumulator, Tile::Scalar(ColumnValue::Ints(vec![10])));
        assert_eq!(terminal, ColumnValue::Bools(vec![true]));
        assert_eq!(pulled.borrow().len(), 1);
        assert!(pulled.borrow()[0].is_universal());
    }

    #[test]
    fn a_sum_asked_for_nothing_reads_nothing() {
        let (mut sum, pulled) = sum_of_finished_stream();
        let tile = sum.get(sum.tiling().empty_guard());
        assert_eq!(tile, sum.tiling().empty_tile());
        assert!(pulled.borrow().is_empty());
    }

    #[test]
    #[should_panic(expected = "one accumulator")]
    fn a_key_projection_of_a_sum_is_rejected() {
        let (mut sum, _) = sum_of_finished_stream();
        sum.get(keys_between(0, 1));
    }
}

#[cfg(test)]
mod extract_aggregate_projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{GuardLog, ProjectionSpy, keys_between};
    use crate::interpreter::{BaseType, Extent, Tile};

    /// `sum(xs)` extracted once the aggregation is terminal: an accumulator holding `10`.
    fn extract_of_finished_sum() -> (ExtractAggregateProducer, GuardLog) {
        let accumulator = Tiling::Scalar(Extent::Base(BaseType::Int));
        let in_tiling = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(accumulator.clone()),
        };
        let finished = Tile::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10]))),
            terminal: ColumnValue::Bools(vec![true]),
        };
        let (input, pulled, _) = ProjectionSpy::new(finished, in_tiling);
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        (
            ExtractAggregateProducer::new(
                ProducerBase::unowned(ExtractAggregateProducer::alloc_id(), &tiling),
                Box::new(input),
                AggregateKind::Sum,
            ),
            pulled,
        )
    }

    #[test]
    fn a_finished_sum_extracts_whole() {
        let (mut extract, pulled) = extract_of_finished_sum();
        let tile = extract.get(extract.tiling().universal_guard());
        assert_eq!(tile, Tile::Scalar(ColumnValue::Ints(vec![10])));
        assert!(pulled.borrow()[0].is_universal());
    }

    #[test]
    fn an_extract_asked_for_nothing_reads_nothing() {
        let (mut extract, pulled) = extract_of_finished_sum();
        let tile = extract.get(extract.tiling().empty_guard());
        assert_eq!(tile, extract.tiling().empty_tile());
        assert!(pulled.borrow().is_empty());
    }

    #[test]
    #[should_panic(expected = "extracts one value")]
    fn a_key_projection_of_an_extracted_value_is_rejected() {
        let (mut extract, _) = extract_of_finished_sum();
        extract.get(keys_between(0, 1));
    }
}

#[cfg(test)]
mod map_aggregate_nested_projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        ProjectionSpyOp, assert_conforms_beneath,
    };
    use crate::interpreter::{BaseType, Extent, Tile};

    /// `k ⤇ j ⤇ z ⤇ Int`: the keys 0 and 1, each holding the positions 0 to 2, each holding the
    /// positions 0 and 1 valued `100k + 10j + z`, every level stated complete.
    fn three_levels_of_ints() -> Box<dyn TileOperator> {
        let tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::data_function(
                Extent::uint_range(3),
                Tiling::data_function(
                    Extent::uint_range(2),
                    Tiling::Scalar(Extent::Base(BaseType::Int)),
                ),
            ),
        );
        let values = (0..2)
            .flat_map(|k| (0..3).flat_map(move |j| (0..2).map(move |z| 100 * k + 10 * j + z)))
            .collect();
        let tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 3],
                ColumnValue::UInts(vec![0, 1, 2, 0, 1, 2]),
                Box::new(Tile::grouped(
                    vec![0, 2, 4, 6, 8, 10],
                    ColumnValue::UInts(vec![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]),
                    Box::new(Tile::Scalar(ColumnValue::Ints(values))),
                    Predicate::True,
                    BitSet::new(),
                )),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        Box::new(ProjectionSpyOp::new(tile, tiling).0)
    }

    /// The sum of each `(k, j)`'s positions, pulled at paths of `(k, j)`, answers what the whole
    /// answer cut to those paths answers: a loop's round pulls a sum at its position's path.
    #[test]
    fn a_sum_of_each_path_answers_a_projection_of_paths() {
        assert_conforms_beneath(|| {
            Box::new(MapAggregate::new(
                three_levels_of_ints(),
                AggregateKind::Sum,
            ))
        });
    }

    /// The final sum of each `(k, j)` answers a projection of paths as the whole answer cut to
    /// them: `MapExtractAggregate` keeps every level of its input.
    #[test]
    fn a_final_sum_of_each_path_answers_a_projection_of_paths() {
        assert_conforms_beneath(|| {
            Box::new(MapExtractAggregate::new(
                Box::new(MapAggregate::new(
                    three_levels_of_ints(),
                    AggregateKind::Sum,
                )),
                AggregateKind::Sum,
            ))
        });
    }

    /// A consuming sum consumed at paths of `(k, j)` offers at those paths what a sum in pull mode
    /// answers there: its accumulators are keyed by the whole path.
    #[test]
    fn a_consuming_sum_offers_a_projection_of_paths_as_a_pull_answers_it() {
        use crate::interpreter::tile_operators::test_helpers::paths_guard;
        use crate::interpreter::{Predicate, Value};
        let point = |k: u64| Predicate::point(Value::UInt(k));
        let paths = paths_guard(
            Predicate::qualified(point(0), point(1))
                .union(&Predicate::qualified(point(1), point(0))),
        );
        let subscribe = || {
            let mut op = MapAggregate::new(three_levels_of_ints(), AggregateKind::Sum);
            let guard = op.tiling().universal_guard();
            op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new())
        };
        let expected = subscribe().get(paths.clone());
        let mut input = three_levels_of_ints();
        let input_guard = input.tiling().universal_guard();
        let out_tiling = fold_innermost(input.tiling(), AggregateKind::Sum);
        let mut consuming = MapAggregateProducer::new(
            ProducerBase::unowned(MapAggregateProducer::alloc_id(), &out_tiling),
            input.subscribe(input_guard, Box::new(|| {}), &mut Scheduler::new()),
            AggregateKind::Sum,
        );
        consuming.consume_impl(InputId::ONLY, paths.clone());
        assert_eq!(consuming.offer_impl(paths), expected);
    }

    /// A sum pulled at one path and then at another answers the second as a fresh sum does: the
    /// accumulators the first pull left held are cut from the second answer.
    #[test]
    fn a_sum_pulled_at_two_paths_in_turn_answers_the_second_alone() {
        use crate::interpreter::tile_operators::test_helpers::paths_guard;
        use crate::interpreter::{Predicate, Value};
        let path = |k: u64, j: u64| {
            paths_guard(Predicate::qualified(
                Predicate::point(Value::UInt(k)),
                Predicate::point(Value::UInt(j)),
            ))
        };
        let subscribe = || {
            let mut op = MapAggregate::new(three_levels_of_ints(), AggregateKind::Sum);
            let guard = op.tiling().universal_guard();
            op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new())
        };
        let expected = subscribe().get(path(1, 0));
        let mut sums = subscribe();
        sums.get(path(0, 1));
        assert_eq!(sums.get(path(1, 0)), expected);
    }

    /// `k ⤇ j ⤇ z ⤇ w ⤇ Int`: every level holds the positions 0 and 1, the values
    /// `1000k + 100j + 10z + w`, every level stated complete.
    fn four_levels_of_ints() -> Box<dyn TileOperator> {
        let level = |inner: Tiling| Tiling::data_function(Extent::uint_range(2), inner);
        let tiling = level(level(level(level(Tiling::Scalar(Extent::Base(
            BaseType::Int,
        ))))));
        let values = (0..16).map(|i| 1000 * (i / 8) + 100 * (i / 4 % 2) + 10 * (i / 2 % 2) + i % 2);
        let positions = |n: usize| ColumnValue::UInts((0..n as u64).map(|i| i % 2).collect());
        let offsets = |groups: usize| (0..groups).map(|g| 2 * g).collect::<Vec<_>>();
        let tile = Tile::data_function(
            positions(2),
            Box::new(Tile::grouped(
                offsets(2),
                positions(4),
                Box::new(Tile::grouped(
                    offsets(4),
                    positions(8),
                    Box::new(Tile::grouped(
                        offsets(8),
                        positions(16),
                        Box::new(Tile::Scalar(ColumnValue::Ints(values.collect()))),
                        Predicate::True,
                        BitSet::new(),
                    )),
                    Predicate::True,
                    BitSet::new(),
                )),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        Box::new(ProjectionSpyOp::new(tile, tiling).0)
    }

    /// The sum of each `(k, j, z)`'s positions, pulled at paths of `(k, j, z)`, answers what the
    /// whole answer cut to those paths answers: `Restates::Every` holds beneath level 1 too.
    #[test]
    fn a_sum_of_each_path_of_three_keys_answers_a_projection_of_them() {
        use crate::interpreter::tile_operators::test_helpers::assert_conforms;
        use crate::interpreter::{FunctionGuard, Predicate, Value};
        let path = |k: u64, j: u64, z: u64| {
            Predicate::qualified(
                Predicate::exactly(&[Value::UInt(k), Value::UInt(j)]),
                Predicate::point(Value::UInt(z)),
            )
        };
        let paths = path(0, 1, 1).union(&path(1, 0, 0));
        assert_conforms(
            || {
                let mut op = MapAggregate::new(four_levels_of_ints(), AggregateKind::Sum);
                let guard = op.tiling().universal_guard();
                op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new())
            },
            CurryLevel::new(2).wrap_guard(TileGuard::Function(FunctionGuard::Domain(paths))),
        );
    }
}

#[cfg(test)]
mod map_extract_aggregate_nested_projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::ProjectionSpy;
    use crate::interpreter::{BaseType, Extent};

    /// A `Sole` element that is a collection adds a level beneath the keys, which is no level of
    /// the input, so it is not restated.
    #[test]
    fn the_levels_of_a_sole_collection_are_not_restated() {
        let element = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let in_tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Aggregation {
                kind: AggregateKind::Sole,
                accumulator: Box::new(element),
            },
        );
        let (spy, _, _) = ProjectionSpy::new(in_tiling.empty_tile(), in_tiling.clone());
        let producer = MapExtractAggregateProducer {
            base: ProducerBase::unowned(
                MapExtractAggregateProducer::alloc_id(),
                &extract_innermost(&in_tiling),
            ),
            input: Box::new(spy),
            kind: AggregateKind::Sole,
        };
        assert!(producer.restates().refuses(CurryLevel::new(1)));
        assert!(!producer.restates().refuses(CurryLevel::OUTERMOST));
    }
}

#[cfg(test)]
mod map_aggregate_projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, assert_conforms, keys_between,
    };
    use crate::interpreter::{BaseType, Extent, Tile};

    const GROUPS: u64 = 4;

    /// `{k: sum(group) for k, group in groups}` over the groups `0: [1, 2]`, `1: [3]`,
    /// `2: [4, 5]`, `3: [6]`, each stated whole, with the pulls of the groups logged.
    fn sums_of_groups() -> (MapAggregateProducer, GuardLog) {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let in_tiling = Tiling::data_function(
            Extent::uint_range(GROUPS),
            Tiling::data_function(uint(), Tiling::Scalar(int())),
        );
        let groups = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1, 2, 3]),
            Box::new(Tile::grouped(
                vec![0, 2, 3, 5],
                ColumnValue::from_uints(vec![0, 1, 0, 0, 1, 0]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3, 4, 5, 6]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let (input, pulled, _) = ProjectionSpy::new(groups, in_tiling);
        let out_tiling = Tiling::data_function(
            Extent::uint_range(GROUPS),
            Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(Tiling::Scalar(int())),
            },
        );
        (
            MapAggregateProducer::new(
                ProducerBase::unowned(MapAggregateProducer::alloc_id(), &out_tiling),
                Box::new(input),
                AggregateKind::Sum,
            ),
            pulled,
        )
    }

    /// The group keys and sums an answer holds.
    fn sums(tile: &Tile) -> Vec<(Value, i64)> {
        let Tile::DataFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("a collection, got {tile:?}")
        };
        let Tile::Aggregation { accumulator, .. } = &**codomain else {
            panic!("an aggregation per key, got {codomain:?}")
        };
        let Tile::Scalar(ColumnValue::Ints(sums)) = &**accumulator else {
            panic!("integer sums, got {accumulator:?}")
        };
        (0..domain.len())
            .map(|i| (domain.index_at(i), sums[i]))
            .collect()
    }

    /// A morsel of groups pulls the input at the morsel and answers the morsel's sums, which is
    /// what a worker that owns those groups reads.
    #[test]
    fn a_morsel_of_groups_is_summed_from_a_morsel_of_the_input() {
        let (mut sums_of, pulled) = sums_of_groups();
        let morsel = sums_of.get(keys_between(1, 2));
        assert_eq!(
            sums(&morsel),
            vec![(Value::UInt(1), 3), (Value::UInt(2), 9)]
        );
        assert_eq!(*pulled.borrow(), vec![keys_between(1, 2)]);
    }

    /// The consumer releases a morsel before the next, which drops the first morsel's
    /// accumulators, so the second's answer holds its own groups.
    #[test]
    fn successive_morsels_answer_their_own_groups() {
        let (mut sums_of, _) = sums_of_groups();
        sums_of.get(keys_between(0, 1));
        sums_of.release(keys_between(0, 1));
        let next = sums_of.get(keys_between(2, 3));
        assert_eq!(sums(&next), vec![(Value::UInt(2), 9), (Value::UInt(3), 6)]);
    }

    #[test]
    fn sums_asked_for_nothing_read_nothing() {
        let (mut sums_of, pulled) = sums_of_groups();
        let tile = sums_of.get(sums_of.tiling().empty_guard());
        assert_eq!(tile, sums_of.tiling().empty_tile());
        assert!(pulled.borrow().is_empty());
    }

    #[test]
    fn the_morsels_together_are_the_whole_pull() {
        for guard in [keys_between(0, 3), keys_between(2, 5), keys_between(5, 5)] {
            assert_conforms(|| Box::new(sums_of_groups().0), guard);
        }
    }
}

#[cfg(test)]
mod map_extract_aggregate_projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, assert_conforms, keys_between,
    };
    use crate::interpreter::{BaseType, Extent, Tile};

    const GROUPS: u64 = 4;

    /// The per-group sums `[3, 3, 9, 6]` of a grouped fold, of which group 2 is still open,
    /// extracted for the finished ones, with the pulls of the sums logged.
    fn finished_sums() -> (MapExtractAggregateProducer, GuardLog) {
        let int = || Extent::Base(BaseType::Int);
        let in_tiling = Tiling::data_function(
            Extent::uint_range(GROUPS),
            Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(Tiling::Scalar(int())),
            },
        );
        let sums = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1, 2, 3]),
            Box::new(Tile::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(Tile::Scalar(ColumnValue::Ints(vec![3, 3, 9, 6]))),
                terminal: ColumnValue::Bools(vec![true, true, false, true]),
            }),
            // Groups 0 and 1 are stated settled. Group 3 is terminal but not yet stated.
            Predicate::at_or_below(Value::UInt(1)),
            BitSet::new(),
        );
        let (input, pulled, _) = ProjectionSpy::new(sums, in_tiling);
        let out_tiling = Tiling::data_function(Extent::uint_range(GROUPS), Tiling::Scalar(int()));
        (
            MapExtractAggregateProducer {
                base: ProducerBase::unowned(MapExtractAggregateProducer::alloc_id(), &out_tiling),
                input: Box::new(input),
                kind: AggregateKind::Sum,
            },
            pulled,
        )
    }

    fn extracted(tile: &Tile) -> Vec<(Value, i64)> {
        let Tile::DataFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("a collection, got {tile:?}")
        };
        let Tile::Scalar(ColumnValue::Ints(sums)) = &**codomain else {
            panic!("integer sums, got {codomain:?}")
        };
        (0..domain.len())
            .map(|i| (domain.index_at(i), sums[i]))
            .collect()
    }

    /// A morsel pulls the sums at the morsel, and answers the finished groups in it: group 2 is
    /// open, so it is not there yet.
    #[test]
    fn a_morsel_extracts_the_finished_groups_in_it() {
        let (mut extract, pulled) = finished_sums();
        let morsel = extract.get(keys_between(1, 2));
        assert_eq!(extracted(&morsel), vec![(Value::UInt(1), 3)]);
        assert_eq!(*pulled.borrow(), vec![keys_between(1, 2)]);
    }

    /// Group 2 is still open, so it is not emitted and the statement, the input's, does not
    /// name it. Group 3 is finished and emitted though the input has not stated it settled. A
    /// consumer releases what the tile holds and states complete, which does not reach group 2.
    #[test]
    fn an_open_group_is_not_emitted_stated_complete_or_released() {
        let (mut extract, _) = finished_sums();
        let tile = extract.get(extract.tiling().universal_guard());
        let Tile::DataFunction {
            domain_predicate, ..
        } = &tile
        else {
            panic!("a collection, got {tile:?}")
        };
        assert_eq!(*domain_predicate, Predicate::at_or_below(Value::UInt(1)));
        assert_eq!(
            extracted(&tile),
            vec![
                (Value::UInt(0), 3),
                (Value::UInt(1), 3),
                (Value::UInt(3), 6)
            ]
        );
        extract.release(tile.to_guard());
        let released = extract.input.obsolete_guard();
        let TileGuard::Function(FunctionGuard::Domain(region)) = released else {
            panic!("a key region, got {released:?}")
        };
        assert!(
            region.intersect(&Predicate::exactly(&[Value::UInt(2)])) == Predicate::False,
            "group 2 is still open: {region:?}"
        );
        for held in [0, 1, 3] {
            assert!(
                region.contains(&Value::UInt(held)),
                "group {held} was emitted, so its release is forwarded: {region:?}"
            );
        }
    }

    #[test]
    fn extracts_asked_for_nothing_read_nothing() {
        let (mut extract, pulled) = finished_sums();
        let tile = extract.get(extract.tiling().empty_guard());
        assert_eq!(tile, extract.tiling().empty_tile());
        assert!(pulled.borrow().is_empty());
    }

    #[test]
    fn the_morsels_together_are_the_whole_pull() {
        for guard in [keys_between(0, 3), keys_between(2, 5), keys_between(5, 5)] {
            assert_conforms(|| Box::new(finished_sums().0), guard);
        }
    }
}

/// A consuming `Aggregate` over an input that grows and is released: what its accumulator holds,
/// what its final guard names and what reaches the input, against a model of the rows consumed.
#[cfg(test)]
mod aggregate_consuming_tests {
    use super::*;
    use std::collections::BTreeSet;

    use crate::interpreter::BaseType;
    use crate::interpreter::dispatcher::{Dispatcher, PipelineId};
    use crate::interpreter::tile_operators::fanout::MemoProducer;
    use crate::interpreter::tile_operators::growing::{
        Input, InputModel, KEYS, Region, Rng, Shared, Step, growing_source, ints, predicate,
        source, value,
    };
    use crate::interpreter::tile_operators::test_helpers::keys_between;
    use crate::interpreter::tile_operators::test_helpers::push_to;
    use Region::{All, Keys};
    use Step::{Add, Close, Consume, Notify, Release};

    fn sum_tiling() -> Tiling {
        Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        }
    }

    fn sum_over(source: &Shared) -> AggregateProducer {
        AggregateProducer::new(
            ProducerBase::unowned(AggregateProducer::alloc_id(), &sum_tiling()),
            Box::new(Input::over(source)),
        )
    }

    /// The accumulator's sum and whether it is terminal.
    fn held(aggregate: &AggregateProducer) -> (i64, bool) {
        let Tile::Aggregation {
            accumulator,
            terminal: ColumnValue::Bools(terminal),
            ..
        } = &aggregate.accumulator
        else {
            panic!("an accumulator, got {:?}", aggregate.accumulator)
        };
        let Tile::Scalar(ColumnValue::Ints(sum)) = accumulator.as_ref() else {
            panic!("an integer sum, got {accumulator:?}")
        };
        (sum[0], terminal[0])
    }

    fn sum_of(keys: impl IntoIterator<Item = u64>) -> i64 {
        keys.into_iter().map(value).sum()
    }

    /// A consume at a region folds the rows of that region, pulls the input at it and releases
    /// the input at it; the accumulator is not terminal until the input is released whole.
    #[test]
    fn a_region_is_folded_pulled_and_released_once() {
        let source = source(0..10);
        let mut aggregate = sum_over(&source);
        aggregate.consume_impl(InputId::ONLY, keys_between(2, 5));
        assert_eq!(held(&aggregate), (sum_of(2..=5), false));
        assert_eq!(source.borrow().pulled, vec![keys_between(2, 5)]);
        assert_eq!(source.borrow().released, vec![keys_between(2, 5)]);
    }

    /// A second disjoint region adds its rows, and an overlapping one adds only the rows the
    /// input still holds, so no row is folded twice.
    #[test]
    fn disjoint_and_overlapping_regions_fold_each_row_once() {
        let source = source(0..10);
        let mut aggregate = sum_over(&source);
        aggregate.consume_impl(InputId::ONLY, keys_between(1, 2));
        aggregate.consume_impl(InputId::ONLY, keys_between(7, 9));
        assert_eq!(held(&aggregate).0, sum_of([1, 2, 7, 8, 9]));
        aggregate.consume_impl(InputId::ONLY, keys_between(2, 7));
        assert_eq!(
            held(&aggregate).0,
            sum_of(1..=9),
            "rows 2 and 7 are not folded again"
        );
    }

    /// Everything consumed drains the input: the accumulator is terminal and `final_guard` holds
    /// the whole value.
    #[test]
    fn everything_consumed_is_terminal_and_the_final_guard_holds_the_value() {
        let source = source(0..10);
        let mut aggregate = sum_over(&source);
        aggregate.consume_impl(InputId::ONLY, ints().universal_guard());
        assert_eq!(held(&aggregate), (sum_of(0..10), true));
        assert_eq!(aggregate.final_guard(), sum_tiling().universal_guard());
        assert_eq!(
            aggregate.get(sum_tiling().universal_guard()),
            aggregate.accumulator,
            "the offer is the accumulator"
        );
    }

    /// Nothing consumed pulls nothing.
    #[test]
    fn nothing_consumed_pulls_nothing() {
        let source = source(0..10);
        let mut aggregate = sum_over(&source);
        aggregate.consume_impl(InputId::ONLY, ints().empty_guard());
        assert!(source.borrow().pulled.is_empty());
        assert_eq!(held(&aggregate), (0, false));
    }

    /// A release of the whole output leaves nothing held, and the input is released whole.
    #[test]
    fn final_guard_after_a_release_holds_nothing() {
        let source = source(0..4);
        let mut aggregate = sum_over(&source);
        aggregate.consume_impl(InputId::ONLY, ints().universal_guard());
        aggregate.release(sum_tiling().universal_guard());
        assert_eq!(aggregate.final_guard(), sum_tiling().empty_guard());
        assert!(aggregate.get(sum_tiling().universal_guard()).is_empty());
    }

    /// An input released in part by the last epoch leaves a partial accumulator that no later
    /// consume completes, so the last epoch's finish panics rather than push nothing.
    #[test]
    #[should_panic(expected = "finishes the last epoch after its input was released whole")]
    fn finish_of_the_last_epoch_over_a_partial_input_panics() {
        let source = source(0..10);
        let mut aggregate = sum_over(&source);
        aggregate.consume_impl(InputId::ONLY, keys_between(0, 4));
        aggregate.finish(
            &mut Dispatcher::new(vec![vec![]], usize::MAX).pushes(PipelineId(0)),
            true,
        );
    }

    /// An epoch before the last finishes over a partial input and pushes nothing: the
    /// accumulator is held by no guard until a later epoch's consume completes it.
    #[test]
    fn an_epoch_before_the_last_finishes_over_a_partial_input() {
        let source = source(0..10);
        let mut aggregate = sum_over(&source);
        aggregate.consume_impl(InputId::ONLY, keys_between(0, 4));
        push_to(&mut aggregate, &[1]);
        let dispatcher = Dispatcher::new(vec![vec![], vec![0]], usize::MAX);
        dispatcher.seal();
        dispatcher.finish_by_hand(PipelineId(0), |pushes| aggregate.finish(pushes, false));
        assert!(
            dispatcher.pop().is_none(),
            "a partial accumulator pushes nothing"
        );
    }

    /// An aggregate whose output was released needs no value, so the last epoch's finish over a
    /// partial input neither panics nor pushes.
    #[test]
    fn finish_of_the_last_epoch_after_the_output_was_released_pushes_nothing() {
        let source = source(0..10);
        let mut aggregate = sum_over(&source);
        aggregate.consume_impl(InputId::ONLY, keys_between(0, 4));
        aggregate.release(sum_tiling().universal_guard());
        push_to(&mut aggregate, &[1]);
        let dispatcher = Dispatcher::new(vec![vec![], vec![0]], usize::MAX);
        dispatcher.finish_by_hand(PipelineId(0), |pushes| aggregate.finish(pushes, true));
        assert!(
            dispatcher.pop().is_none(),
            "a released output pushes nothing"
        );
    }

    /// A consuming aggregate answers from its accumulator and pulls nothing.
    #[test]
    fn a_consuming_aggregate_offers_without_pulling() {
        let source = source(0..10);
        let mut aggregate = sum_over(&source);
        aggregate.consume_impl(InputId::ONLY, ints().universal_guard());
        let pulls = source.borrow().pulled.len();
        for _ in 0..3 {
            aggregate.get(sum_tiling().universal_guard());
        }
        assert_eq!(source.borrow().pulled.len(), pulls);
    }

    /// A growing input withholds a key it does not hold yet: the release leaves it, and a row that
    /// arrives there later is folded by the next consume and released.
    #[test]
    fn a_key_the_input_withheld_is_folded_by_a_later_consume() {
        let source = growing_source([0, 1, 2, 4, 5]);
        let mut aggregate = sum_over(&source);
        aggregate.consume_impl(InputId::ONLY, keys_between(0, 5));
        assert!(!predicate(&source.borrow().released[0]).contains(&Value::UInt(3)));
        source.borrow_mut().rows.insert(3, value(3));
        aggregate.consume_impl(InputId::ONLY, keys_between(0, 5));
        assert_eq!(held(&aggregate).0, sum_of(0..=5));
        assert!(predicate(source.borrow().released.last().unwrap()).contains(&Value::UInt(3)));
    }

    /// A consume after the output was released pulls nothing: the input was released whole.
    #[test]
    fn a_consume_after_a_release_pulls_nothing() {
        let source = growing_source(0..4);
        let mut aggregate = sum_over(&source);
        aggregate.consume_impl(InputId::ONLY, keys_between(0, 1));
        aggregate.release(sum_tiling().universal_guard());
        let pulls = source.borrow().pulled.len();
        aggregate.consume_impl(InputId::ONLY, ints().universal_guard());
        assert_eq!(source.borrow().pulled.len(), pulls);
        assert_eq!(source.borrow().wasted, 0);
    }

    /// The model of a run over a growing input: which rows were folded, whether the output was
    /// released, and the input.
    struct Run {
        sut: AggregateProducer,
        sut_source: Shared,
        input: InputModel,
        folded: BTreeSet<u64>,
        released: bool,
        trace: String,
    }

    impl Run {
        fn new(initial: &[u64], trace: String) -> Self {
            let sut_source = growing_source(initial.iter().copied());
            Self {
                sut: sum_over(&sut_source),
                sut_source,
                input: InputModel::new(initial),
                folded: BTreeSet::new(),
                released: false,
                trace,
            }
        }

        fn apply(&mut self, step: Step) {
            self.trace.push_str(&format!(" {step:?}"));
            match step {
                Add(key) => {
                    if self.input.add(key) {
                        self.sut_source.borrow_mut().rows.insert(key, value(key));
                    }
                }
                Close => {
                    self.input.closed = true;
                    self.sut_source.borrow_mut().closed = true;
                }
                // The aggregate listens to no region: its input's notifications reach its
                // consumer widened.
                Notify(_) => unreachable!("the steps of an aggregate carry no notification"),
                Consume(region) => {
                    self.sut.consume_impl(InputId::ONLY, region.guard());
                    if !self.released {
                        self.folded.extend(self.input.pull(region).0);
                    }
                }
                // An accumulator has no sub-regions, so only the whole output is released.
                Release(_) => {
                    self.sut.release(sum_tiling().universal_guard());
                    if !self.released {
                        self.released = true;
                        self.input.release(All);
                    }
                }
            }
        }

        fn check(&mut self) {
            let trace = &self.trace;
            if !self.released {
                let (sum, terminal) = held(&self.sut);
                assert_eq!(sum, sum_of(self.folded.iter().copied()), "{trace}: the sum");
                assert_eq!(terminal, self.input.drained(), "{trace}: the terminal flag");
            }
            self.input.check(&self.sut_source, trace);
            if self.input.drained() {
                let expected = match self.released {
                    true => sum_tiling().empty_guard(),
                    false => sum_tiling().universal_guard(),
                };
                assert_eq!(self.sut.final_guard(), expected, "{trace}: final guard");
            } else {
                assert!(
                    self.sut.held().is_empty(),
                    "{trace}: a partial accumulator is held by no guard"
                );
            }
        }

        /// Close the input and consume everything: an aggregate in pull mode over exactly the
        /// rows the consuming one folded answers what it offers.
        fn finish(&mut self) {
            if !self.input.closed {
                self.apply(Close);
            }
            self.apply(Consume(All));
            self.check();
            if self.released {
                return;
            }
            let twin_source = source(self.folded.iter().copied());
            let mut twin = sum_over(&twin_source);
            assert_eq!(
                self.sut.get(sum_tiling().universal_guard()),
                twin.get(sum_tiling().universal_guard()),
                "{}: the offer is the answer of an aggregate in pull mode",
                self.trace
            );
        }

        fn run(steps: &[Step], initial: &[u64]) {
            let mut run = Run::new(initial, format!("initial {initial:?} steps"));
            for step in steps {
                run.apply(*step);
                run.check();
            }
            run.finish();
        }
    }

    #[test]
    fn enumerated_interleavings_keep_the_model() {
        let sequences: &[&[Step]] = &[
            &[Consume(Keys(0, 3)), Add(3), Add(8), Consume(Keys(0, 11))],
            &[
                Consume(Keys(0, 3)),
                Add(2),
                Add(9),
                Close,
                Consume(Keys(0, 11)),
            ],
            &[
                Add(3),
                Consume(Keys(2, 4)),
                Add(3),
                Consume(Keys(2, 4)),
                Release(All),
            ],
            &[
                Consume(Keys(0, 5)),
                Consume(Keys(3, 8)),
                Release(All),
                Consume(All),
            ],
            &[Close, Consume(All), Add(4), Consume(Keys(0, 6))],
        ];
        for steps in sequences {
            Run::run(steps, &[0, 1, 2, 4, 5, 6]);
        }
    }

    #[test]
    fn random_interleavings_keep_the_model() {
        const SEED: u64 = 0x5851_f42d_4c95_7f2d;
        let mut rng = Rng(SEED);
        for iteration in 0..300 {
            let initial: Vec<u64> = (0..KEYS).filter(|_| rng.below(2) == 0).collect();
            let trace = format!("seed {SEED:#x} iteration {iteration} initial {initial:?} steps");
            let mut run = Run::new(&initial, trace);
            for _ in 0..14 {
                let step = rng.step_among(&run.folded, false);
                run.apply(step);
                run.check();
            }
            run.finish();
        }
    }

    /// An aggregate over a memo: the memo's final guard is the aggregate's consume guard.
    #[test]
    fn an_aggregate_consumes_the_final_guard_of_a_memo() {
        let source = source(0..10);
        let mut memo = MemoProducer::over(Box::new(Input::over(&source)), &ints());
        memo.consume_impl(InputId::ONLY, ints().universal_guard());
        memo.release(keys_between(2, 3));
        let handed = memo.final_guard();
        let mut aggregate = AggregateProducer::new(
            ProducerBase::unowned(AggregateProducer::alloc_id(), &sum_tiling()),
            Box::new(memo),
        );
        aggregate.consume_impl(InputId::ONLY, handed);
        assert_eq!(held(&aggregate), (sum_of([0, 1, 4, 5, 6, 7, 8, 9]), true));
    }

    fn scalar_tiling() -> Tiling {
        Tiling::Scalar(Extent::Base(BaseType::Int))
    }

    fn extract_over_input(input: Box<dyn TileProducer>) -> ExtractAggregateProducer {
        ExtractAggregateProducer::new(
            ProducerBase::unowned(ExtractAggregateProducer::alloc_id(), &scalar_tiling()),
            input,
            AggregateKind::Sum,
        )
    }

    fn extract_over(source: &Shared) -> ExtractAggregateProducer {
        extract_over_input(Box::new(sum_over(source)))
    }

    fn scalar_of(tile: &Tile) -> Option<i64> {
        match tile {
            Tile::Scalar(ColumnValue::Ints(values)) => values.first().copied(),
            other if other.is_empty() => None,
            other => panic!("an integer, got {other:?}"),
        }
    }

    /// A terminal aggregation is extracted, and its input is released at what it stated: all of
    /// it. Nothing is pulled from the source for an answer after that.
    #[test]
    fn a_terminal_aggregation_is_extracted_and_released() {
        let source = source(0..10);
        let mut sum = sum_over(&source);
        sum.consume_impl(InputId::ONLY, ints().universal_guard());
        let mut extract = extract_over_input(Box::new(sum));
        extract.consume_impl(InputId::ONLY, sum_tiling().universal_guard());
        assert_eq!(
            scalar_of(&extract.get(scalar_tiling().universal_guard())),
            Some(sum_of(0..10))
        );
        assert!(extract.input.obsolete_guard().is_universal());
        assert_eq!(extract.final_guard(), scalar_tiling().universal_guard());
        let pulls = source.borrow().pulled.len();
        extract.get(scalar_tiling().universal_guard());
        assert_eq!(
            source.borrow().pulled.len(),
            pulls,
            "the offer pulls nothing"
        );
    }

    /// An aggregation that is not terminal yields no value and releases nothing.
    #[test]
    fn a_partial_aggregation_extracts_nothing() {
        let source = source(0..10);
        let mut sum = sum_over(&source);
        sum.consume_impl(InputId::ONLY, keys_between(0, 3));
        let mut extract = extract_over_input(Box::new(sum));
        extract.consume_impl(InputId::ONLY, sum_tiling().universal_guard());
        assert_eq!(
            scalar_of(&extract.get(scalar_tiling().universal_guard())),
            None
        );
        assert!(!extract.input.obsolete_guard().is_universal());
    }

    /// Once the value is extracted, a second consume pulls nothing.
    #[test]
    fn a_second_consume_after_extraction_pulls_nothing() {
        let source = source(0..4);
        let mut extract = extract_over(&source);
        extract.consume_impl(InputId::ONLY, sum_tiling().universal_guard());
        let pulls = (extract.input.base().pulls, source.borrow().pulled.len());
        extract.consume_impl(InputId::ONLY, sum_tiling().universal_guard());
        assert_eq!(
            (extract.input.base().pulls, source.borrow().pulled.len()),
            pulls
        );
    }

    /// A released output is not extracted again either: the input is not pulled.
    #[test]
    fn an_extraction_after_a_release_pulls_nothing() {
        let source = source(0..4);
        let mut extract = extract_over(&source);
        extract.consume_impl(InputId::ONLY, sum_tiling().universal_guard());
        extract.release(scalar_tiling().universal_guard());
        let pulls = extract.input.base().pulls;
        extract.consume_impl(InputId::ONLY, sum_tiling().universal_guard());
        assert_eq!(extract.input.base().pulls, pulls);
    }

    /// `Nothing` consumed pulls nothing.
    #[test]
    fn an_extraction_of_nothing_pulls_nothing() {
        let source = source(0..10);
        let mut extract = extract_over(&source);
        extract.consume_impl(InputId::ONLY, sum_tiling().empty_guard());
        assert!(source.borrow().pulled.is_empty());
        assert_eq!(
            extract.input.base().pulls,
            0,
            "the input is not pulled either"
        );
    }

    /// Releasing the extracted value leaves nothing held.
    #[test]
    fn final_guard_after_a_release_holds_nothing_extracted() {
        let source = source(0..4);
        let mut extract = extract_over(&source);
        extract.consume_impl(InputId::ONLY, sum_tiling().universal_guard());
        extract.release(scalar_tiling().universal_guard());
        assert_eq!(extract.final_guard(), scalar_tiling().empty_guard());
        assert_eq!(
            scalar_of(&extract.get(scalar_tiling().universal_guard())),
            None
        );
    }

    /// An aggregation that is not terminal yields nothing and is not released; the next consume,
    /// once the input has closed, extracts the sum and releases the aggregation whole.
    #[test]
    fn a_partial_then_terminal_aggregation_is_extracted_once_terminal() {
        let source = growing_source(0..4);
        let mut extract = extract_over(&source);
        extract.consume_impl(InputId::ONLY, sum_tiling().universal_guard());
        assert_eq!(
            scalar_of(&extract.get(scalar_tiling().universal_guard())),
            None
        );
        assert!(
            extract.input.obsolete_guard().is_empty(),
            "nothing is released"
        );

        source.borrow_mut().closed = true;
        extract.consume_impl(InputId::ONLY, sum_tiling().universal_guard());
        assert_eq!(
            scalar_of(&extract.get(scalar_tiling().universal_guard())),
            Some(sum_of(0..4))
        );
        assert!(extract.input.obsolete_guard().is_universal());
    }

    /// A consuming extraction and one in pull mode over the same growing script answer alike at
    /// every consume. The model: the sum the first consume after the close extracts.
    struct ExtractRun {
        sut: ExtractAggregateProducer,
        sut_source: Shared,
        twin: ExtractAggregateProducer,
        twin_source: Shared,
        input: InputModel,
        taken: Option<i64>,
        released: bool,
        trace: String,
    }

    impl ExtractRun {
        fn new(initial: &[u64], trace: String) -> Self {
            let (sut_source, twin_source) = (
                growing_source(initial.iter().copied()),
                growing_source(initial.iter().copied()),
            );
            Self {
                sut: extract_over(&sut_source),
                sut_source,
                twin: extract_over(&twin_source),
                twin_source,
                input: InputModel::new(initial),
                taken: None,
                released: false,
                trace,
            }
        }

        fn apply(&mut self, step: Step) {
            self.trace.push_str(&format!(" {step:?}"));
            match step {
                Add(key) => {
                    if self.input.add(key) {
                        for source in [&self.sut_source, &self.twin_source] {
                            source.borrow_mut().rows.insert(key, value(key));
                        }
                    }
                }
                Close => {
                    self.input.closed = true;
                    for source in [&self.sut_source, &self.twin_source] {
                        source.borrow_mut().closed = true;
                    }
                }
                Notify(_) => unreachable!("an extraction listens to no region"),
                // An aggregation has no keys: a consume and a release name all of it.
                Consume(_) => {
                    self.sut
                        .consume_impl(InputId::ONLY, sum_tiling().universal_guard());
                    let lazy = self.twin.get(scalar_tiling().universal_guard());
                    let offered = self.sut.get(scalar_tiling().universal_guard());
                    assert_eq!(
                        offered, lazy,
                        "{}: the offer is the answer in pull mode",
                        self.trace
                    );
                    // The aggregation is terminal once the input has closed, and the first
                    // consume then reads every row there is.
                    if self.taken.is_none() && !self.released && self.input.closed {
                        self.taken = Some(sum_of(self.input.rows.iter().copied()));
                    }
                }
                Release(_) => {
                    self.sut.release(scalar_tiling().universal_guard());
                    self.twin.release(scalar_tiling().universal_guard());
                    self.released = true;
                }
            }
        }

        fn check(&mut self) {
            let trace = &self.trace;
            let expected = match self.released {
                true => None,
                false => self.taken,
            };
            // A pull before the first consume is a pull in pull mode, which reads the input.
            if self.sut.consuming {
                assert_eq!(
                    scalar_of(&self.sut.get(scalar_tiling().universal_guard())),
                    expected,
                    "{trace}: the extracted value"
                );
            }
            if self.taken.is_some() || self.released {
                let guard = match self.released {
                    true => scalar_tiling().empty_guard(),
                    false => scalar_tiling().universal_guard(),
                };
                assert_eq!(self.sut.final_guard(), guard, "{trace}: final guard");
            }
        }

        fn run(steps: &[Step], initial: &[u64]) {
            let mut run = ExtractRun::new(initial, format!("initial {initial:?} steps"));
            for step in steps {
                run.apply(*step);
                run.check();
            }
        }
    }

    #[test]
    fn enumerated_extraction_interleavings_keep_the_model() {
        let sequences: &[&[Step]] = &[
            &[Consume(All), Close, Consume(All)],
            &[Add(8), Consume(All), Add(9), Close, Consume(All)],
            &[Close, Consume(All), Release(All), Consume(All), Add(3)],
            &[Release(All), Add(3), Close, Consume(All)],
            &[
                Add(1),
                Add(2),
                Consume(All),
                Release(All),
                Close,
                Consume(All),
            ],
        ];
        for steps in sequences {
            ExtractRun::run(steps, &[0, 4, 5]);
        }
    }

    #[test]
    fn random_extraction_interleavings_keep_the_model() {
        const SEED: u64 = 0x2545_f491_4f6c_dd1d;
        let mut rng = Rng(SEED);
        for iteration in 0..300 {
            let initial: Vec<u64> = (0..KEYS).filter(|_| rng.below(2) == 0).collect();
            let trace = format!("seed {SEED:#x} iteration {iteration} initial {initial:?} steps");
            let mut run = ExtractRun::new(&initial, trace);
            for _ in 0..10 {
                let step = match rng.step_among(&BTreeSet::new(), false) {
                    Consume(_) => Consume(All),
                    Release(_) => Release(All),
                    other => other,
                };
                run.apply(step);
                run.check();
            }
        }
    }
}

/// A consuming `MapAggregate` over an input of groups that grows and is released: the
/// accumulators it holds, what its final guard names and what reaches the input, against a model.
#[cfg(test)]
mod map_aggregate_consuming_tests {
    use super::*;
    use std::collections::{BTreeMap, BTreeSet};

    use crate::interpreter::BaseType;
    use crate::interpreter::tile_operators::fanout::MemoProducer;
    use crate::interpreter::tile_operators::growing::{
        KEYS, NestedInput, Region, Rng, Shared, Step, growing_source, members, members_of,
        nested_tiling, source, value,
    };
    use crate::interpreter::tile_operators::test_helpers::keys_between;
    use Region::{All, Keys};
    use Step::{Add, Close, Consume, Notify, Release};

    fn out_tiling() -> Tiling {
        Tiling::data_function(
            Extent::uint_range(KEYS),
            Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
            },
        )
    }

    fn sums_over_input(input: Box<dyn TileProducer>) -> MapAggregateProducer {
        MapAggregateProducer::new(
            ProducerBase::unowned(MapAggregateProducer::alloc_id(), &out_tiling()),
            input,
            AggregateKind::Sum,
        )
    }

    fn sums_over(source: &Shared) -> MapAggregateProducer {
        sums_over_input(Box::new(NestedInput::over(source)))
    }

    /// The guard of the input's tiling that names `region`'s groups.
    fn input_guard(region: Region) -> TileGuard {
        region.projection().guard(&nested_tiling())
    }

    /// The guard of the output's tiling that names `region`'s groups.
    fn output_guard(region: Region) -> TileGuard {
        match region {
            All => out_tiling().universal_guard(),
            Keys(first, last) => keys_between(first, last),
        }
    }

    fn group_sum(key: u64) -> i64 {
        members(key).iter().sum()
    }

    /// The group sums the accumulators hold, by key.
    fn held(map: &MapAggregateProducer) -> BTreeMap<u64, i64> {
        map.accumulators
            .iter()
            .map(|(path, accumulator)| {
                let Value::UInt(key) = path[0] else {
                    panic!("a group key, got {path:?}")
                };
                let Tile::Scalar(ColumnValue::Ints(sum)) = accumulator else {
                    panic!("a sum per group, got {accumulator:?}")
                };
                (key, sum[0])
            })
            .collect()
    }

    fn sums_of(keys: impl IntoIterator<Item = u64>) -> BTreeMap<u64, i64> {
        keys.into_iter().map(|key| (key, group_sum(key))).collect()
    }

    /// The outermost keys of the universe a guard names, wherever it names them.
    fn outer_keys(guard: &TileGuard) -> BTreeSet<u64> {
        match guard {
            TileGuard::Function(FunctionGuard::Domain(predicate)) => (0..KEYS)
                .filter(|key| predicate.contains(&Value::UInt(*key)))
                .collect(),
            TileGuard::Or(arms) => arms.iter().flat_map(outer_keys).collect(),
            _ => BTreeSet::new(),
        }
    }

    fn released_keys(source: &Shared) -> BTreeSet<u64> {
        source
            .borrow()
            .released
            .iter()
            .flat_map(outer_keys)
            .collect()
    }

    #[test]
    fn a_region_is_folded_pulled_and_released() {
        let source = source(0..10);
        let mut map = sums_over(&source);
        map.consume_impl(InputId::ONLY, input_guard(Keys(2, 5)));
        assert_eq!(held(&map), sums_of(2..=5));
        assert_eq!(source.borrow().pulled, vec![input_guard(Keys(2, 5))]);
        assert_eq!(released_keys(&source), (2..=5).collect());
    }

    #[test]
    fn disjoint_and_overlapping_regions_fold_each_group_once() {
        let source = source(0..10);
        let mut map = sums_over(&source);
        map.consume_impl(InputId::ONLY, input_guard(Keys(1, 2)));
        map.consume_impl(InputId::ONLY, input_guard(Keys(7, 9)));
        assert_eq!(held(&map), sums_of([1, 2, 7, 8, 9]));
        map.consume_impl(InputId::ONLY, input_guard(Keys(2, 7)));
        assert_eq!(
            held(&map),
            sums_of(1..=9),
            "groups 2 and 7 are not folded again"
        );
    }

    #[test]
    fn nothing_consumed_pulls_nothing() {
        let source = source(0..10);
        let mut map = sums_over(&source);
        map.consume_impl(InputId::ONLY, nested_tiling().empty_guard());
        assert!(source.borrow().pulled.is_empty());
        assert!(held(&map).is_empty());
    }

    /// Everything consumed drains the input; the offer is what a pull in pull mode at everything
    /// answers over the same rows, and `final_guard` names all of it.
    #[test]
    fn everything_consumed_offers_what_a_lazy_pull_answers() {
        let source = source(0..10);
        let mut consuming = sums_over(&source);
        consuming.consume_impl(InputId::ONLY, nested_tiling().universal_guard());
        let mut lazy = sums_over(&self::source(0..10));
        let guard = out_tiling().universal_guard();
        assert_eq!(consuming.get(guard.clone()), lazy.get(guard.clone()));
        assert_eq!(consuming.final_guard(), out_tiling().universal_guard());
    }

    #[test]
    fn final_guard_excludes_what_was_released() {
        let source = source(0..10);
        let mut map = sums_over(&source);
        map.consume_impl(InputId::ONLY, nested_tiling().universal_guard());
        map.release(output_guard(Keys(2, 3)));
        assert_eq!(held(&map), sums_of([0, 1, 4, 5, 6, 7, 8, 9]));
        let guard = map.final_guard();
        let kept: BTreeSet<u64> = outer_keys(&guard);
        assert_eq!(kept, (0..KEYS).filter(|k| ![2, 3].contains(k)).collect());
    }

    #[test]
    fn a_consuming_map_aggregate_offers_without_pulling() {
        let source = source(0..10);
        let mut map = sums_over(&source);
        map.consume_impl(InputId::ONLY, nested_tiling().universal_guard());
        let pulls = source.borrow().pulled.len();
        for _ in 0..3 {
            map.get(out_tiling().universal_guard());
            map.get(keys_between(1, 3));
        }
        assert_eq!(source.borrow().pulled.len(), pulls);
    }

    /// What the answers state is united: an offer at an earlier region still states its keys
    /// complete after a later consume has been merged.
    #[test]
    fn a_later_consume_does_not_withdraw_what_an_earlier_one_stated() {
        let source = source(0..10);
        let mut map = sums_over(&source);
        map.consume_impl(InputId::ONLY, input_guard(Keys(1, 2)));
        map.consume_impl(InputId::ONLY, input_guard(Keys(5, 6)));
        let Tile::DataFunction {
            domain_predicate, ..
        } = map.get(output_guard(Keys(1, 2)))
        else {
            panic!("a collection of sums")
        };
        assert!(
            domain_predicate.contains(&Value::UInt(1))
                && domain_predicate.contains(&Value::UInt(2))
        );
        assert!(
            !domain_predicate.contains(&Value::UInt(5)),
            "the offer is cut to its region"
        );
    }

    /// Groups stated open fold into their accumulators and are not terminal; the offer is what a
    /// pull-mode map aggregate answers over the same groups, each level's statement included.
    #[test]
    fn open_groups_are_folded_and_offered_open() {
        let mut consuming = sums_over_input(Box::new(NestedInput::open_over(&source(0..6))));
        consuming.consume_impl(InputId::ONLY, nested_tiling().universal_guard());
        let mut pulled = sums_over_input(Box::new(NestedInput::open_over(&source(0..6))));
        let guard = out_tiling().universal_guard();
        let offered = consuming.get(guard.clone());
        assert_eq!(offered, pulled.get(guard));
        let Tile::DataFunction { codomain, .. } = &offered else {
            panic!("a collection of sums")
        };
        let Tile::Aggregation { terminal, .. } = &**codomain else {
            panic!("an aggregation per group, got {codomain:?}")
        };
        assert_eq!(
            terminal,
            &ColumnValue::Bools(vec![false; 6]),
            "no group is complete"
        );
        assert_eq!(held(&consuming), sums_of(0..6));
    }

    /// A map aggregate over a memo consumes the final guard of the memo.
    #[test]
    fn a_map_aggregate_consumes_the_final_guard_of_a_memo() {
        let source = source(0..10);
        let mut memo = MemoProducer::over(Box::new(NestedInput::over(&source)), &nested_tiling());
        memo.consume_impl(InputId::ONLY, nested_tiling().universal_guard());
        let handed = memo.final_guard();
        let mut map = sums_over_input(Box::new(memo));
        map.consume_impl(InputId::ONLY, handed);
        assert_eq!(held(&map), sums_of(0..10));
    }

    /// A growing input of groups withholds a group it does not hold yet; one that arrives later
    /// is folded by the next consume.
    #[test]
    fn a_group_the_input_withheld_is_folded_by_a_later_consume() {
        let source = growing_source([0, 1, 2, 4, 5]);
        let mut map = sums_over(&source);
        map.consume_impl(InputId::ONLY, input_guard(Keys(0, 5)));
        assert!(
            !released_keys(&source).contains(&3),
            "the input did not answer group 3"
        );
        source.borrow_mut().rows.insert(3, value(3));
        map.consume_impl(InputId::ONLY, input_guard(Keys(0, 5)));
        assert_eq!(held(&map), sums_of(0..=5));
    }

    /// Open groups release only the members answered, never a group's key, so a member that
    /// arrives later is folded into its group by the next consume.
    #[test]
    fn a_member_added_to_an_open_group_is_folded_by_a_later_consume() {
        let source = source(0..8);
        let mut map = sums_over_input(Box::new(NestedInput::open_over(&source)));
        map.consume_impl(InputId::ONLY, input_guard(Keys(2, 5)));
        assert!(
            released_keys(&source).is_empty(),
            "no group key is released: {:?}",
            source.borrow().released
        );
        source.borrow_mut().members.insert(3, 4);
        map.consume_impl(InputId::ONLY, input_guard(Keys(2, 5)));
        let mut expected = sums_of(2..=5);
        expected.insert(3, members_of(3, 4).iter().sum());
        assert_eq!(held(&map), expected);
    }

    /// A release of the whole output leaves nothing held.
    #[test]
    fn final_guard_after_releasing_everything_holds_nothing() {
        let mut map = sums_over(&source(0..6));
        map.consume_impl(InputId::ONLY, nested_tiling().universal_guard());
        map.release(out_tiling().universal_guard());
        assert_eq!(map.final_guard(), out_tiling().empty_guard());
    }

    /// A release of nothing changes neither the groups nor what `final_guard` returns.
    #[test]
    fn a_release_of_nothing_changes_nothing() {
        let mut map = sums_over(&source(0..6));
        map.consume_impl(InputId::ONLY, nested_tiling().universal_guard());
        let before = (held(&map), map.final_guard());
        map.release(out_tiling().empty_guard());
        assert_eq!((held(&map), map.final_guard()), before);
    }

    /// A consuming map aggregate and a twin in pull mode over growing inputs that receive the
    /// same script. The twin pulls its input at the same guards, so the two hold the same groups.
    /// The model holds the groups each consume must fold, whole and once: the groups the input
    /// holds in the region that no consume folded and no release named, less the keys the input
    /// was released at, which a nested answer names as a prefix of what it held.
    struct Run {
        sut: MapAggregateProducer,
        sut_source: Shared,
        twin: MapAggregateProducer,
        twin_source: Shared,
        rows: BTreeSet<u64>,
        closed: bool,
        folded_ever: BTreeSet<u64>,
        groups: BTreeSet<u64>,
        memo_released: BTreeSet<u64>,
        touched: BTreeSet<u64>,
        trace: String,
    }

    impl Run {
        fn new(initial: &[u64], trace: String) -> Self {
            let (sut_source, twin_source) = (
                growing_source(initial.iter().copied()),
                growing_source(initial.iter().copied()),
            );
            Self {
                sut: sums_over(&sut_source),
                sut_source,
                twin: sums_over(&twin_source),
                twin_source,
                rows: initial.iter().copied().collect(),
                closed: false,
                folded_ever: BTreeSet::new(),
                groups: BTreeSet::new(),
                memo_released: BTreeSet::new(),
                touched: BTreeSet::new(),
                trace,
            }
        }

        fn apply(&mut self, step: Step) {
            self.trace.push_str(&format!(" {step:?}"));
            match step {
                Add(_) if self.closed => {}
                Add(key) => {
                    self.rows.insert(key);
                    for source in [&self.sut_source, &self.twin_source] {
                        source.borrow_mut().rows.insert(key, value(key));
                    }
                }
                Close => {
                    self.closed = true;
                    for source in [&self.sut_source, &self.twin_source] {
                        source.borrow_mut().closed = true;
                    }
                }
                Notify(_) => unreachable!("a map aggregate listens to no region"),
                Consume(region) => {
                    let released_before = released_keys(&self.sut_source);
                    self.sut.consume_impl(InputId::ONLY, input_guard(region));
                    let lazy = self.twin.get(output_guard(region));
                    let offered = self.sut.get(output_guard(region));
                    assert_eq!(
                        offered, lazy,
                        "{}: the offer is the answer in pull mode at {region:?}",
                        self.trace
                    );
                    let keys = region.keys();
                    let answered: Vec<u64> = self
                        .rows
                        .iter()
                        .copied()
                        .filter(|key| {
                            keys.contains(key)
                                && !self.folded_ever.contains(key)
                                && !self.memo_released.contains(key)
                                && !released_before.contains(key)
                        })
                        .collect();
                    self.folded_ever.extend(answered.iter().copied());
                    self.groups.extend(answered);
                    self.touched.extend(keys);
                }
                Release(region) => {
                    self.sut.release(output_guard(region));
                    self.twin.release(output_guard(region));
                    let keys = region.keys();
                    self.groups.retain(|key| !keys.contains(key));
                    self.memo_released.extend(keys.iter().copied());
                    self.touched.extend(keys);
                }
            }
        }

        fn check(&mut self) {
            let trace = &self.trace;
            assert_eq!(
                held(&self.sut),
                sums_of(self.groups.iter().copied()),
                "{trace}: the groups"
            );
            assert_eq!(
                held(&self.twin),
                held(&self.sut),
                "{trace}: the twin's groups"
            );
            assert!(
                released_keys(&self.sut_source).is_subset(&self.touched),
                "{trace}: the input is released only at keys a consume or a release named"
            );
        }

        fn run(steps: &[Step], initial: &[u64]) {
            let mut run = Run::new(initial, format!("initial {initial:?} steps"));
            for step in steps {
                run.apply(*step);
                run.check();
            }
            if !run.closed {
                run.apply(Close);
            }
            run.apply(Consume(All));
            run.check();
        }
    }

    #[test]
    fn enumerated_interleavings_keep_the_model() {
        let sequences: &[&[Step]] = &[
            &[Consume(Keys(0, 3)), Add(3), Add(8), Consume(Keys(0, 11))],
            &[
                Consume(Keys(0, 3)),
                Release(Keys(1, 2)),
                Add(9),
                Close,
                Consume(Keys(4, 11)),
            ],
            &[Add(2), Consume(Keys(0, 3)), Add(3), Consume(Keys(0, 3))],
            &[
                Release(Keys(5, 6)),
                Add(5),
                Add(6),
                Add(7),
                Consume(Keys(4, 8)),
            ],
            &[
                Consume(Keys(0, 5)),
                Consume(Keys(3, 8)),
                Release(Keys(4, 6)),
                Consume(All),
            ],
            &[Release(All), Add(3), Consume(All)],
        ];
        for steps in sequences {
            Run::run(steps, &[0, 1, 2, 4, 5, 6]);
        }
    }

    #[test]
    fn random_interleavings_keep_the_model() {
        const SEED: u64 = 0x3c6e_f372_fe94_f82b;
        let mut rng = Rng(SEED);
        for iteration in 0..300 {
            let initial: Vec<u64> = (0..KEYS).filter(|_| rng.below(2) == 0).collect();
            let trace = format!("seed {SEED:#x} iteration {iteration} initial {initial:?} steps");
            let mut run = Run::new(&initial, trace);
            for _ in 0..14 {
                let step = rng.step_among(&run.groups, false);
                run.apply(step);
                run.check();
            }
            if !run.closed {
                run.apply(Close);
            }
            run.apply(Consume(All));
            run.check();
        }
    }
}
