use bit_set::BitSet;
use log::trace;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

use super::*;
use crate::interpreter::nest_levels;
use crate::interpreter::operator_graph::value;
use crate::{
    ccl::AggregateKind,
    interpreter::{ColumnValue, Consumer, FunctionGuard, Predicate, Projection, Scheduler, Value},
};

/// Reduces a `DataFunction` input to a single scalar via an aggregation operation.
///
/// On each `get`, reads all codomain values from the input and folds them into a
/// running `Tile::Aggregation` accumulator. The result becomes terminal once the
/// input's `domain_predicate` is `True` (all elements seen).
pub struct Aggregate {
    /// The `DataFunction`-typed input whose codomain elements are aggregated.
    input: Box<dyn TileOperator>,
    /// Output tiling — always `Tiling::Aggregation { accumulator: <output extent> }`.
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
        let arrivals = Arrivals::new();
        let consumer = Downstream::new(consumer);
        let input_producer = self.input.subscribe(
            self.input.tiling().universal_guard(),
            arrivals.consumer(widening(Box::new(consumer.clone()))),
            scheduler,
        );
        let producer = AggregateProducer::new(
            ProducerBase::new(
                AggregateProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            input_producer,
            arrivals,
            consumer,
        );
        if let Some(operator) = self.operator_id() {
            scheduler.register_breaker(operator, &producer.breaker);
        }
        Box::new(producer)
    }
}

/// What an aggregate holds between pulls, shared by its producer and its breaker handle: the
/// producer answers `get`, and the dispatcher drives the breaker. Execution is single-threaded, so
/// the lock is never contended.
struct AggregateState {
    /// The subscribed input producer.
    input: Box<dyn TileProducer>,
    /// The aggregation operation.
    kind: AggregateKind,
    /// Running accumulation state; updated in place on each `get` in pull mode and on each
    /// `pull_sink` in sink mode.
    accumulator: Tile,
    /// Set once the consumer has released this output universally, after which
    /// the accumulator must never be handed back — it *is* the whole output, so
    /// re-emitting it returns released data.
    released: bool,
    /// What the input notified since it was last read, which sink mode swallows.
    arrivals: Arrivals,
    /// The operator's own consumer, which `finalize` wakes on the terminal round.
    consumer: Downstream,
    /// Whether the aggregate is in sink mode: the dispatcher pulls the input, and `get` never does.
    sinking: bool,
}

impl AggregateState {
    /// Fold `input_result`, an answer of the input, into the accumulator.
    fn accumulate(&mut self, mut input_result: Tile) {
        input_result.compact();
        let Tile::DataFunction { codomain, .. } = input_result else {
            panic!("Aggregate expected a collection, got {input_result:?}");
        };
        let values = *codomain;
        let Tile::Aggregation {
            ref mut accumulator,
            ..
        } = self.accumulator
        else {
            panic!("Accumulator must be Aggregation tile")
        };
        self.kind.accumulate(accumulator, &values, 0, values.rows());
    }

    /// State whether the accumulator is the whole result.
    fn set_terminal(&mut self, is_terminal: bool) {
        let Tile::Aggregation {
            terminal: ColumnValue::Bools(ref mut terminal),
            ..
        } = self.accumulator
        else {
            panic!("Accumulator must be Aggregation tile")
        };
        terminal[0] = is_terminal;
    }

    /// What `get` answers: the accumulator, or nothing while an extreme has no first element,
    /// which an empty `terminal` says to [`ExtractAggregate`], however many pulls come first.
    fn answer(&mut self, is_terminal: bool, empty: Tile) -> Tile {
        let Tile::Aggregation {
            ref accumulator, ..
        } = self.accumulator
        else {
            panic!("Accumulator must be Aggregation tile")
        };
        if self.kind.awaits_first_element(accumulator) {
            if is_terminal {
                self.kind.no_extreme_of_nothing();
            }
            return empty;
        }
        self.accumulator.clone()
    }
}

struct AggregateBreaker {
    // shared-state-ok: the aggregate's own state, shared between its producer and its breaker on
    // the dispatcher's one thread; no tile passes between operators through it.
    state: Arc<Mutex<AggregateState>>,
}

struct AggregateProducer {
    base: ProducerBase,
    // shared-state-ok: the aggregate's own state, shared with its breaker as `AggregateBreaker`
    // says.
    state: Arc<Mutex<AggregateState>>,
    /// The handle the scheduler's registry holds weakly; the producer owns the state it reaches.
    breaker: BreakerHandle,
}

impl AggregateProducer {
    /// Construct an `AggregateProducer`, seeding the accumulator with the identity element.
    fn new(
        base: ProducerBase,
        input: Box<dyn TileProducer>,
        arrivals: Arrivals,
        consumer: Downstream,
    ) -> Self {
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
        let state = Arc::new(Mutex::new(AggregateState {
            input,
            kind,
            accumulator,
            released: false,
            arrivals,
            consumer,
            sinking: false,
        }));
        Self {
            base,
            breaker: Arc::new(AggregateBreaker {
                state: state.clone(),
            }),
            state,
        }
    }

    /// A producer over `input` with no consumer to wake, for a test.
    #[cfg(test)]
    fn detached(base: ProducerBase, input: Box<dyn TileProducer>) -> Self {
        Self::new(
            base,
            input,
            Arrivals::new(),
            Downstream::new(Box::new(|| {})),
        )
    }
}

impl Breaker for AggregateBreaker {
    /// Adopts the accumulator the aggregate holds: what pull mode folded stays folded, and the
    /// input released it.
    fn begin_sinking(&self) {
        let mut state = self.state.lock_now();
        assert!(!state.sinking, "an aggregate begins sinking once");
        state.sinking = true;
        // What the input notifies from here is not the downstream's business: it learns of the
        // result from `finalize`, on the terminal round.
        state.arrivals.swallow();
    }

    /// Pulls the input at `guard`, folds the answer into the accumulator, and releases the input at
    /// the guard: the answer states the whole guard complete, so the input keeps nothing of it.
    fn pull_sink(&self, guard: TileGuard) {
        let mut state = self.state.lock_now();
        let st = &mut *state;
        assert!(st.sinking, "an aggregate is pulled after it begins sinking");
        if st.released || guard.is_empty() {
            return;
        }
        let input = st.input.get(guard.clone());
        debug_assert!(
            match (&input, &guard) {
                (
                    Tile::DataFunction {
                        domain_predicate, ..
                    },
                    TileGuard::Function(FunctionGuard::Domain(region)),
                ) => region.minus(domain_predicate).is_false(),
                _ => true,
            },
            "the input answers a morsel complete over its guard: {input:?} for {guard:?}"
        );
        st.accumulate(input);
        st.input.release(guard);
    }

    /// An aggregate has no parent pipeline to push keys to.
    fn first_keys(&self, _region: &Predicate, _rows: u64) -> Vec<Value> {
        Vec::new()
    }

    /// States the result complete on the terminal round and wakes the consumer. A round before it
    /// changes nothing a reader acts on, since the extraction answers nothing until the result is
    /// terminal.
    fn finalize(&self, round: Round, _parents: &mut Pushes<'_>) {
        if !round.terminal {
            return;
        }
        let consumer = {
            let mut state = self.state.lock_now();
            assert!(
                state.sinking,
                "an aggregate finalizes after it begins sinking"
            );
            state.set_terminal(true);
            state.consumer.clone()
        };
        consumer.clone().notify(&Projection::Everything);
    }

    /// The accumulator has no keys.
    fn held_keys(&self) -> usize {
        0
    }
}

impl TileProducer for AggregateProducer {
    fn state_info(&self) -> ProducerStateInfo {
        ProducerStateInfo::holding(self.state.lock_now().accumulator.cell_count())
    }

    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.state.lock_now().input);
    }

    /// An accumulator has no keys to project, so the projection is all of it or none. In pull mode
    /// the input is read whole whatever the consumer asks; in sink mode it is not read.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        match projection_guard.projection(&self.name()) {
            Projection::Everything => {}
            Projection::Nothing => return self.tiling().empty_tile(),
            Projection::Keys(_) | Projection::Fields(_) => panic!(
                "{} is one accumulator, which has no keys to project: {projection_guard:?}",
                self.name()
            ),
        }
        let empty = self.tiling().empty_tile();
        let mut state = self.state.lock_now();
        let st = &mut *state;
        if st.released {
            return empty;
        }
        if st.sinking {
            drop(st.arrivals.take());
            let terminal = matches!(
                &st.accumulator,
                Tile::Aggregation { terminal: ColumnValue::Bools(t), .. } if t[0]
            );
            return st.answer(terminal, empty);
        }
        drop(st.arrivals.take());
        let i_tiling = st.input.tiling().clone();
        let input_result = st.input.get(i_tiling.universal_guard());
        let upstream_guard = input_result.to_guard();
        st.accumulate(input_result);
        st.input.release(upstream_guard);

        let is_terminal = st.input.obsolete_guard().is_universal();
        trace!(
            "Aggregate input is_terminal: {is_terminal} from guard {:?}",
            st.input.obsolete_guard()
        );
        st.set_terminal(is_terminal);
        st.answer(is_terminal, empty)
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // An `Aggregation` guard is all-or-nothing — the accumulator has no
        // sub-regions — so the only release that can arrive is the universal one.
        // Releasing the input in full is what `get_impl` cannot do: it releases
        // each delivery as it folds it in, so whatever the input never delivered
        // — this aggregate being done before its source ran dry — would stay
        // stranded upstream.
        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            let mut state = self.state.lock_now();
            state.released = true;
            let universal = state.input.tiling().universal_guard();
            state.input.release(universal);
        }
    }
}

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
        // TODO(pipeline breaker): a pooled chain stops notifying at this operator. The region of
        // its input ends here, and the breaker raises its own region to the dispatcher once a
        // worker has merged a morsel (`docs/parallel-execution.md`, "Pipeline boundaries"). The
        // serial scheduler still needs the notification passed on below.
        Box::new(ExtractAggregateProducer {
            base: ProducerBase::new(
                ExtractAggregateProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            input: self.input.subscribe(
                self.input.tiling().universal_guard(),
                widening(consumer),
                scheduler,
            ),
            kind: self.kind,
            only_terminal: self.only_terminal,
        })
    }
}

struct ExtractAggregateProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    kind: AggregateKind,
    only_terminal: bool,
}

impl TileProducer for ExtractAggregateProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    /// One extracted value has no keys to project: the projection is all of it or none.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        match projection_guard.projection(&self.name()) {
            Projection::Everything => {}
            Projection::Nothing => return self.tiling().empty_tile(),
            Projection::Keys(_) | Projection::Fields(_) => panic!(
                "{} extracts one value, which has no keys to project: {projection_guard:?}",
                self.name()
            ),
        }
        let input_result = self.input.get(self.input.tiling().universal_guard());
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
        // An empty accumulator is `⊥`, not a finished aggregation of nothing: the
        // input has either not produced yet, or has released what it produced and
        // gone quiet. Either way there is no terminal flag to read.
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

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            self.input.release(self.input.tiling().universal_guard());
        }
    }
}

/// Extracts terminal aggregation results from a `DataFunction(D, Aggregation)`, producing a
/// `DataFunction(D, Scalar)`.
///
/// One level, which is the fold's own: [`MapAggregate`] collapses the innermost collection,
/// so the levels above it stay and this operator reads the one that is left. A fold under
/// two or more levels leaves `DataFunction(D₀ … Dₙ₋₁, Aggregation)`, which this rejects.
/// An element is emitted only where its terminal flag is set; the rest are filtered out.
pub struct MapExtractAggregate {
    /// The `DataFunction(D, Aggregation)`-typed input.
    input: Box<dyn TileOperator>,
    /// The aggregation operation used to extract final values from accumulators.
    kind: AggregateKind,
    /// Output tiling: `DataFunction { domain: input.domain, codomain: Scalar(output_extent) }`.
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
        // TODO(pipeline breaker): a pooled chain stops notifying at this operator. The region of
        // its input ends here, and the breaker raises its own region to the dispatcher once a
        // worker has merged a morsel (`docs/parallel-execution.md`, "Pipeline boundaries"). The
        // serial scheduler still needs the notification passed on below.
        // The groups keep the input's outermost keys.
        let input_producer = self.input.subscribe(
            self.input.tiling().universal_guard(),
            keys_only(consumer),
            scheduler,
        );
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

    /// Every level keeps the input's keys and only the unfinished ones drop, so the input is
    /// pulled at the projection, and the answer keeps its keys.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
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

    /// Every level passes through and only what sits under the innermost changes, so a
    /// region named on the output names the same region of the input — a key of any level,
    /// or a path down to one, alike.
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

/// Collapses the **innermost** collection of a nested tile into an aggregation, leaving the
/// levels above it intact.
///
/// For `K₀ ⤇ … ⤇ Kₙ₋₁ ⤇ C` and an [`AggregateKind`] it produces `K₀ ⤇ … ⤇ Kₙ₋₂ ⤇
/// Aggregation(C)`. Collapsing one level per operator is what lets nested aggregation nest:
/// each `sum` in `sum([sum([…]) for …])` is one of these.
///
/// Accumulators are keyed by the **path** of the element being folded into, not by its own
/// value: a key repeats across its siblings' groups, so below the outermost level a value
/// does not identify an element. New data merges on each `get`; an element's aggregation
/// becomes terminal where the input's `domain_predicate` names its outermost ancestor.
pub struct MapAggregate {
    /// The lookup-function input to aggregate per key.
    input: Box<dyn TileOperator>,
    /// The aggregation operation (Sum, Max, …).
    kind: AggregateKind,
    /// Output tiling: `DataFunction { domain: input.domain, codomain: Aggregation { accumulator: output_extent } }`.
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
        let arrivals = Arrivals::new();
        let consumer = Downstream::new(consumer);
        let input_producer = self.input.subscribe(
            self.input.tiling().universal_guard(),
            arrivals.consumer(keys_only(Box::new(consumer.clone()))),
            scheduler,
        );
        let producer = MapAggregateProducer::new(
            ProducerBase::new(
                MapAggregateProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            input_producer,
            self.kind,
            arrivals,
            consumer,
        );
        if let Some(operator) = self.operator_id() {
            scheduler.register_breaker(operator, &producer.breaker);
        }
        Box::new(producer)
    }
}

/// What a `MapAggregate` holds between pulls, shared by its producer and its breaker handle: the
/// producer answers `get`, and the dispatcher drives the breaker. Execution is single-threaded, so
/// the lock is never contended.
struct MapAggregateState {
    /// The subscribed lookup-function producer.
    input: Box<dyn TileProducer>,
    /// The operator's output tiling.
    tiling: Tiling,
    /// The aggregation operation.
    kind: AggregateKind,
    /// Running per-key accumulators, grown as new keys arrive across `get` calls.
    accumulators: HashMap<Vec<Value>, Tile>,
    /// Keys above the accumulators whose every accumulator was released without the key
    /// itself: a key is there only through what it maps to, and a release naming part of
    /// what lies beneath leaves it in place, holding nothing unreleased
    /// (`src/interpreter/design-operators.md`, "The completeness contract").
    emptied_keys: HashSet<Vec<Value>>,
    /// What the input notified since it was last read, which sink mode swallows.
    arrivals: Arrivals,
    /// The operator's own consumer, which `finalize` wakes on the terminal round.
    consumer: Downstream,
    /// Whether the aggregate is in sink mode: the dispatcher pulls the input, and `get` never does.
    sinking: bool,
    /// Whether the terminal round has run: in sink mode every group is terminal from then, and
    /// none before.
    terminal: bool,
    /// What the last pull-mode answer stated, which sink mode states again: a producer does not
    /// withdraw a completion it stated.
    stated: Option<InputCompletion>,
}

struct MapAggregateBreaker {
    // shared-state-ok: the operator's own state, shared between its producer and its breaker on
    // the dispatcher's one thread; no tile passes between operators through it.
    state: Arc<Mutex<MapAggregateState>>,
}

struct MapAggregateProducer {
    base: ProducerBase,
    // shared-state-ok: the operator's own state, shared with its breaker as `MapAggregateBreaker`
    // says.
    state: Arc<Mutex<MapAggregateState>>,
    /// The handle the scheduler's registry holds weakly; the producer owns the state it reaches.
    breaker: BreakerHandle,
}

/// What a pull of the input says of the groups it answered, which the answer states again.
#[derive(Clone)]
struct InputCompletion {
    /// The outermost level's completion.
    domain_predicate: Predicate,
    /// Each level above the folded one states its own completion.
    level_predicates: Vec<Predicate>,
    /// The paths of the groups that some level on the path calls complete.
    complete: Predicate,
}

impl MapAggregateState {
    /// Fold `input_tile`, an answer of the input, into the accumulators, and say what it states
    /// complete.
    fn fold(&mut self, mut input_tile: Tile) -> InputCompletion {
        input_tile.compact();
        let Tile::DataFunction {
            domain_predicate, ..
        } = &input_tile
        else {
            panic!("MapAggregate requires a collection tile, got {input_tile:?}")
        };
        let domain_predicate = domain_predicate.clone();

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
        // Which groups are complete, over whole paths: those some level on the path calls
        // complete ([`Tile::completion_at`]).
        let complete = input_tile.completion_at(CurryLevel::new(depth - 1));
        let parent_paths = input_tile.row_paths_at(depth);
        let folded = input_tile.values_at(CurryLevel::new(depth));
        let Tile::DataFunction { codomain, .. } = folded else {
            unreachable!("the loop breaks on a collection")
        };
        let values = (**codomain).clone();
        let (_, output_tiling) = folded_shape(&self.tiling);

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
        InputCompletion {
            domain_predicate,
            level_predicates,
            complete,
        }
    }

    /// The answer at `projection`, built from every accumulator held.
    ///
    /// **Terminal per element, which is what the predicates say.** A level's
    /// `domain_predicate` names which of that level's keys are closed, and a key called
    /// closed is closed at every depth beneath it — so an element is final as soon as
    /// some level on its path calls that prefix closed, whatever the rest of the domain
    /// is still doing. Reading the predicate as one bool answers "not yet" for every
    /// element whenever any part of the domain is open, which is never right for a live
    /// source: a collection held per row is complete as soon as its row arrives, and an
    /// aggregate over one would otherwise never settle. Reading only the **outermost**
    /// level is the same mistake one level up: under a nested store the enclosing
    /// positions stay open while the one being run is decided, so an aggregate inside the
    /// nest would never settle either.
    fn answer(&self, projection: &Projection, completion: InputCompletion) -> Tile {
        let InputCompletion {
            domain_predicate,
            level_predicates,
            complete,
        } = completion;
        let kind = &self.kind;
        let (extents, output_tiling) = folded_shape(&self.tiling);
        let mut entries: Vec<(Vec<Value>, Tile)> = self
            .accumulators
            .iter()
            .map(|(path, acc)| (path.clone(), acc.clone()))
            .collect();
        // Sorted so the outermost column stays ordered and a parent's children sit
        // contiguously, which is what rebuilding the offsets assumes.
        entries.sort_by(|a, b| compare_paths(&a.0, &b.0));
        // A group whose extreme has no identity has no value until its first element, so
        // its key waits for one; complete without one, it has none at all.
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
        let mut out = build_levels_from_paths(&paths, &extents, aggregation, domain_predicate);
        // Each level beneath the outermost holds the input's keys at that level, so it
        // states what the input's does there: a group settles once some level on its path
        // is complete, and a level saying nothing would leave it looking open downstream.
        for (level, stated) in level_predicates.into_iter().enumerate().skip(1) {
            if let Tile::DataFunction {
                domain_predicate, ..
            } = out.values_at_mut(CurryLevel::new(level))
            {
                *domain_predicate = stated;
            }
        }
        out.restrict_to(projection, &self.tiling);
        out
    }

    /// What a sinking operator states of its groups: all complete once the terminal round has run,
    /// and none before.
    fn sink_completion(&self) -> InputCompletion {
        let stated = |complete: Predicate| InputCompletion {
            domain_predicate: complete.clone(),
            level_predicates: vec![complete.clone(); self.tiling.levels()],
            complete,
        };
        match (self.terminal, &self.stated) {
            (true, _) => stated(Predicate::True),
            (false, Some(before)) => before.clone(),
            (false, None) => stated(Predicate::False),
        }
    }
}

impl MapAggregateProducer {
    fn new(
        base: ProducerBase,
        input: Box<dyn TileProducer>,
        kind: AggregateKind,
        arrivals: Arrivals,
        consumer: Downstream,
    ) -> Self {
        let state = Arc::new(Mutex::new(MapAggregateState {
            input,
            tiling: base.tiling.clone(),
            kind,
            accumulators: HashMap::new(),
            emptied_keys: HashSet::new(),
            arrivals,
            consumer,
            sinking: false,
            terminal: false,
            stated: None,
        }));
        Self {
            base,
            breaker: Arc::new(MapAggregateBreaker {
                state: state.clone(),
            }),
            state,
        }
    }

    /// A producer over `input` with no consumer to wake, for a test.
    #[cfg(test)]
    fn detached(base: ProducerBase, input: Box<dyn TileProducer>, kind: AggregateKind) -> Self {
        Self::new(
            base,
            input,
            kind,
            Arrivals::new(),
            Downstream::new(Box::new(|| {})),
        )
    }
}

impl Breaker for MapAggregateBreaker {
    /// Adopts the accumulators the operator holds: what pull mode folded stays folded, and the
    /// input released it.
    fn begin_sinking(&self) {
        let mut state = self.state.lock_now();
        assert!(!state.sinking, "a MapAggregate begins sinking once");
        state.sinking = true;
        // What the input notifies from here is not the downstream's business: it learns of the
        // groups from `finalize`, on the terminal round.
        state.arrivals.swallow();
    }

    /// Pulls the input at `guard`, folds the answer into the groups its keys fall in, and
    /// releases the input at the guard.
    fn pull_sink(&self, guard: TileGuard) {
        let mut state = self.state.lock_now();
        let st = &mut *state;
        assert!(
            st.sinking,
            "a MapAggregate is pulled after it begins sinking"
        );
        assert!(
            !st.terminal,
            "a MapAggregate is not pulled after its terminal round"
        );
        if guard.is_empty() {
            return;
        }
        let input = st.input.get(guard.clone());
        st.fold(input);
        st.input.release(guard);
    }

    /// A group is final only when the input is, so no key is claimable before the terminal round,
    /// and what reads the groups reads them through `get`.
    fn first_keys(&self, _region: &Predicate, _rows: u64) -> Vec<Value> {
        Vec::new()
    }

    /// States every group terminal on the terminal round and wakes the consumer then: before it, a
    /// group is not final, and an extraction emits nothing.
    fn finalize(&self, round: Round, _parents: &mut Pushes<'_>) {
        if !round.terminal {
            return;
        }
        let consumer = {
            let mut state = self.state.lock_now();
            assert!(
                state.sinking,
                "a MapAggregate finalizes after it begins sinking"
            );
            state.terminal = true;
            state.consumer.clone()
        };
        consumer.clone().notify(&Projection::Everything);
    }

    fn held_keys(&self) -> usize {
        self.state.lock_now().accumulators.len()
    }
}

impl TileProducer for MapAggregateProducer {
    fn state_info(&self) -> ProducerStateInfo {
        let state = self.state.lock_now();
        let accumulators: usize = state
            .accumulators
            .iter()
            .map(|(path, acc)| path.len() + acc.cell_count())
            .sum();
        ProducerStateInfo::holding(accumulators + state.emptied_keys.len())
    }

    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.state.lock_now().input);
    }

    /// The outermost keys are the input's, with each group beneath one whole, so in pull mode the
    /// input is pulled at the projection and the answer is cut to it: accumulators for keys pulled
    /// earlier stay held, and a pull names the keys it wants. In sink mode the answer is built from
    /// the groups the dispatcher's pulls folded.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let mut state = self.state.lock_now();
        let st = &mut *state;
        drop(st.arrivals.take());
        if st.sinking {
            let completion = st.sink_completion();
            return st.answer(&projection, completion);
        }
        let input_tile = st.input.get(projection.guard(st.input.tiling()));
        trace!("{} received {input_tile:?}", self.name());
        let upstream_guard = input_tile.to_guard();
        let completion = st.fold(input_tile);
        // Release received values
        st.input.release(upstream_guard);
        st.stated = Some(completion.clone());
        st.answer(&projection, completion)
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let mut state = self.state.lock_now();
        let st = &mut *state;
        let levels = st.tiling.levels();
        // The output domain *is* this producer's accumulator key set, and the
        // input's own keys are that same key set, so a domain release names
        // exactly which accumulators to drop and forwards verbatim. Keeping a
        // released key would re-emit it on the next pull, since `get_impl` builds
        // its output from every accumulator it holds.
        match obsolete_guard {
            g if g.is_empty() => {}
            g if g.is_universal() => {
                st.accumulators.clear();
                st.emptied_keys.clear();
                let universal = st.input.tiling().universal_guard();
                st.input.release(universal);
            }
            // The guard is a region over the accumulators' own paths, whatever shape it
            // names it at, so it is read at each of them rather than matched arm by arm.
            // Keeping a released path would re-emit it on the next pull, `get_impl`
            // building its output from every accumulator it holds.
            // The input carries the aggregated level where the output holds each group's
            // accumulator, so a region of the output's keys passes through and only a
            // release of a whole accumulator reaches the group beneath its key.
            g => {
                let released: Vec<Vec<Value>> = st
                    .accumulators
                    .keys()
                    .filter(|path| g.covers_path(path))
                    .cloned()
                    .collect();
                st.accumulators.retain(|path, _| !g.covers_path(path));
                for path in released {
                    for len in 1..path.len() {
                        let key = &path[..len];
                        if !g.covers_path(key) {
                            st.emptied_keys.insert(key.to_vec());
                        }
                    }
                }
                st.emptied_keys.retain(|key| !g.covers_path(key));
                let input = st.input.tiling().clone();
                st.input
                    .release(crate::interpreter::tiling::through_shared_levels(
                        g, levels, &input,
                    ));
            }
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
        let mut producer = AggregateProducer::detached(
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
        let mut producer = AggregateProducer::detached(
            ProducerBase::unowned(AggregateProducer::alloc_id(), &tiling),
            Box::new(spy),
        );

        producer.release(tiling.universal_guard());
        assert!(
            released.lock_now().iter().any(TileGuard::is_universal),
            "expected a universal release to reach the input, got {:?}",
            released.lock_now()
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
        let mut producer = MapAggregateProducer::detached(
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
                .lock_now()
                .iter()
                .any(|g| g.is_universal() || *g == key_one),
            "the released key must be covered at the input, got {:?}",
            released.lock_now()
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
        let mut producer = MapAggregateProducer::detached(
            ProducerBase::unowned(MapAggregateProducer::alloc_id(), &out_tiling),
            Box::new(spy),
            AggregateKind::Sum,
        );
        producer.get(out_tiling.universal_guard());
        assert!(
            !released.lock_now().iter().any(TileGuard::is_universal),
            "a bounded predicate is not released whole, got {:?}",
            released.lock_now()
        );

        let key_two = TileGuard::Function(FunctionGuard::Domain(Predicate::Intervals(
            intervalsets::IntervalSet::from(intervalsets::Interval::closed(
                Value::Int(2),
                Value::Int(2),
            )),
        )));
        producer.release(key_two.clone());
        assert!(
            released.lock_now().contains(&key_two),
            "the per-key release must reach the input, got {:?}",
            released.lock_now()
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
        let mut producer = MapAggregateProducer::detached(
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
        let mut producer = MapAggregateProducer::detached(
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
            AggregateProducer::detached(
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
        *odd_cell.lock_now() = int_column(vec![1, 3, 5], Predicate::exactly(&[Value::UInt(5)]));
        let (partial, terminal) = total(producer.get(sum.tiling().universal_guard()));
        assert_eq!(partial, Tile::Scalar(ColumnValue::Ints(vec![16 + 5])));
        assert_eq!(terminal, open());

        // Both arms have now decided every position, so the sum is final.
        *odd_cell.lock_now() = int_column(vec![1, 3, 5, 7], Predicate::True);
        let (last, terminal) = total(producer.get(sum.tiling().universal_guard()));
        assert_eq!(last, Tile::Scalar(ColumnValue::Ints(vec![(0..8).sum()])));
        assert_eq!(terminal, ColumnValue::Bools(vec![true]));
    }

    /// The fold reads the whole stream, and what it answers is one terminal accumulator.
    /// The sum of `tile`, an aggregation, and whether it states itself terminal.
    fn sum_and_terminal(tile: Tile) -> (i64, bool) {
        let Tile::Aggregation {
            accumulator,
            terminal,
            ..
        } = tile
        else {
            panic!("an aggregation, got {tile:?}")
        };
        let Tile::Scalar(ColumnValue::Ints(sum)) = *accumulator else {
            panic!("an int accumulator")
        };
        let ColumnValue::Bools(terminal) = terminal else {
            panic!("a terminal flag")
        };
        (sum[0], terminal[0])
    }

    /// A sum over `[1, 2, 3, 4]` with the input's pulls and releases logged.
    fn sum_of_stream() -> (AggregateProducer, GuardLog, GuardLog) {
        let in_tiling = Tiling::data_function(
            Extent::uint_range(4),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let (stream, pulled, released) =
            ProjectionSpy::new(ints_by_position(&[1, 2, 3, 4], true), in_tiling);
        let tiling = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        (
            AggregateProducer::detached(
                ProducerBase::unowned(AggregateProducer::alloc_id(), &tiling),
                Box::new(stream),
            ),
            pulled,
            released,
        )
    }

    /// A sinking aggregate folds the morsels it is pulled at, in any order, to the sum a pulling
    /// one reads whole, and states the result terminal only on the terminal round.
    #[test]
    fn a_sinking_aggregate_folds_morsels_as_a_pulling_one_does() {
        let (mut sum, _, _) = sum_of_stream();
        sum.breaker.begin_sinking();
        for morsel in [keys_between(3, 3), keys_between(0, 1), keys_between(2, 2)] {
            sum.breaker.pull_sink(morsel);
        }
        let (total, terminal) = sum_and_terminal(sum.get(sum.tiling().universal_guard()));
        assert_eq!(total, 10);
        assert!(!terminal, "a result is terminal at the terminal round only");
    }

    /// A sinking aggregate never pulls its input from `get`, and releases the input at each morsel.
    #[test]
    fn a_sinking_aggregate_never_pulls_its_input_from_get() {
        let (mut sum, pulled, released) = sum_of_stream();
        sum.breaker.begin_sinking();
        sum.get(sum.tiling().universal_guard());
        assert!(pulled.lock_now().is_empty(), "get reads local state");
        sum.breaker.pull_sink(keys_between(0, 1));
        assert_eq!(*released.lock_now(), [keys_between(0, 1)]);
        sum.breaker.pull_sink(keys_between(0, 1));
        let (total, _) = sum_and_terminal(sum.get(sum.tiling().universal_guard()));
        assert_eq!(total, 3, "a morsel pulled again adds nothing");
    }

    /// The accumulator a pulling aggregate holds is adopted at the switch.
    #[test]
    fn the_switch_to_sink_mode_adopts_the_accumulator() {
        let (mut sum, _, _) = sum_of_stream();
        sum.get(sum.tiling().universal_guard());
        sum.breaker.begin_sinking();
        let (total, terminal) = sum_and_terminal(sum.get(sum.tiling().universal_guard()));
        assert_eq!(
            (total, terminal),
            (10, true),
            "what pull mode folded is kept"
        );
    }

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
        assert_eq!(pulled.lock_now().len(), 1);
        assert!(pulled.lock_now()[0].is_universal());
    }

    #[test]
    fn a_sum_asked_for_nothing_reads_nothing() {
        let (mut sum, pulled) = sum_of_finished_stream();
        let tile = sum.get(sum.tiling().empty_guard());
        assert_eq!(tile, sum.tiling().empty_tile());
        assert!(pulled.lock_now().is_empty());
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
            ExtractAggregateProducer {
                base: ProducerBase::unowned(ExtractAggregateProducer::alloc_id(), &tiling),
                input: Box::new(input),
                kind: AggregateKind::Sum,
                only_terminal: true,
            },
            pulled,
        )
    }

    #[test]
    fn a_finished_sum_extracts_whole() {
        let (mut extract, pulled) = extract_of_finished_sum();
        let tile = extract.get(extract.tiling().universal_guard());
        assert_eq!(tile, Tile::Scalar(ColumnValue::Ints(vec![10])));
        assert!(pulled.lock_now()[0].is_universal());
    }

    #[test]
    fn an_extract_asked_for_nothing_reads_nothing() {
        let (mut extract, pulled) = extract_of_finished_sum();
        let tile = extract.get(extract.tiling().empty_guard());
        assert_eq!(tile, extract.tiling().empty_tile());
        assert!(pulled.lock_now().is_empty());
    }

    #[test]
    #[should_panic(expected = "extracts one value")]
    fn a_key_projection_of_an_extracted_value_is_rejected() {
        let (mut extract, _) = extract_of_finished_sum();
        extract.get(keys_between(0, 1));
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
    fn sums_of_groups() -> (MapAggregateProducer, GuardLog, GuardLog) {
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
        let (input, pulled, released) = ProjectionSpy::new(groups, in_tiling);
        let out_tiling = Tiling::data_function(
            Extent::uint_range(GROUPS),
            Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(Tiling::Scalar(int())),
            },
        );
        (
            MapAggregateProducer::detached(
                ProducerBase::unowned(MapAggregateProducer::alloc_id(), &out_tiling),
                Box::new(input),
                AggregateKind::Sum,
            ),
            pulled,
            released,
        )
    }

    /// The `terminal` flags of the aggregations an answer holds, one per group.
    fn terminal_flags(tile: &Tile) -> Vec<bool> {
        let Tile::Aggregation { terminal, .. } = tile.values_at(CurryLevel::new(1)) else {
            panic!("the fold sits beneath one level, got {tile:?}")
        };
        terminal.as_bools().expect("bools").to_vec()
    }

    /// A sinking `MapAggregate` sums the morsels it is pulled at, in any order, into the groups a
    /// pulling one builds, and states no group terminal before the terminal round.
    #[test]
    fn a_sinking_map_aggregate_sums_its_morsels_and_states_no_group_terminal() {
        let (mut sums_of, _, _) = sums_of_groups();
        sums_of.breaker.begin_sinking();
        sums_of.breaker.pull_sink(keys_between(2, 3));
        sums_of.breaker.pull_sink(keys_between(0, 1));
        let answer = sums_of.get(sums_of.tiling().universal_guard());
        let (pulled, _, _) = sums_of_groups();
        let mut pulled = pulled;
        let whole = pulled.get(pulled.tiling().universal_guard());
        assert_eq!(sums(&answer), sums(&whole));
        assert_eq!(terminal_flags(&answer), [false; 4]);
        assert_eq!(terminal_flags(&whole), [true; 4]);
    }

    /// A sinking `MapAggregate` never pulls its input from `get`, and pulls it at the morsel
    /// it is given.
    #[test]
    fn a_sinking_map_aggregate_never_pulls_its_input_from_get() {
        let (mut sums_of, pulled, released) = sums_of_groups();
        sums_of.breaker.begin_sinking();
        sums_of.get(sums_of.tiling().universal_guard());
        assert!(pulled.lock_now().is_empty(), "get reads local state");
        sums_of.breaker.pull_sink(keys_between(1, 2));
        assert_eq!(*pulled.lock_now(), vec![keys_between(1, 2)]);
        assert_eq!(
            *released.lock_now(),
            vec![keys_between(1, 2)],
            "the input is released at the morsel"
        );
        assert_eq!(sums_of.breaker.held_keys(), 2);
    }

    /// What a pulling `MapAggregate` folded is adopted at the switch.
    #[test]
    fn the_switch_to_sink_mode_adopts_the_groups() {
        let (mut sums_of, _, _) = sums_of_groups();
        sums_of.get(keys_between(0, 1));
        sums_of.breaker.begin_sinking();
        sums_of.breaker.pull_sink(keys_between(2, 3));
        let answer = sums_of.get(sums_of.tiling().universal_guard());
        assert_eq!(sums(&answer).len(), 4);
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
        let (mut sums_of, pulled, _) = sums_of_groups();
        let morsel = sums_of.get(keys_between(1, 2));
        assert_eq!(
            sums(&morsel),
            vec![(Value::UInt(1), 3), (Value::UInt(2), 9)]
        );
        assert_eq!(*pulled.lock_now(), vec![keys_between(1, 2)]);
    }

    /// The consumer releases a morsel before the next, which drops the first morsel's
    /// accumulators, so the second's answer holds its own groups.
    #[test]
    fn successive_morsels_answer_their_own_groups() {
        let (mut sums_of, _, _) = sums_of_groups();
        sums_of.get(keys_between(0, 1));
        sums_of.release(keys_between(0, 1));
        let next = sums_of.get(keys_between(2, 3));
        assert_eq!(sums(&next), vec![(Value::UInt(2), 9), (Value::UInt(3), 6)]);
    }

    #[test]
    fn sums_asked_for_nothing_read_nothing() {
        let (mut sums_of, pulled, _) = sums_of_groups();
        let tile = sums_of.get(sums_of.tiling().empty_guard());
        assert_eq!(tile, sums_of.tiling().empty_tile());
        assert!(pulled.lock_now().is_empty());
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
        assert_eq!(*pulled.lock_now(), vec![keys_between(1, 2)]);
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
        assert!(pulled.lock_now().is_empty());
    }

    #[test]
    fn the_morsels_together_are_the_whole_pull() {
        for guard in [keys_between(0, 3), keys_between(2, 5), keys_between(5, 5)] {
            assert_conforms(|| Box::new(finished_sums().0), guard);
        }
    }
}
