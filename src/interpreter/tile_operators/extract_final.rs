use super::*;
use crate::interpreter::operator_graph::value;
#[cfg(test)]
use crate::interpreter::tile_operators::test_helpers::Announce as _;
use crate::{
    interpreter::{ColumnValue, Consumer, Projection, SubscribeContext, Value},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};
#[cfg(test)]
use std::sync::PoisonError;

/// Extracts the last live position's value once a collection is terminal.
///
/// The output has the source's codomain tiling, including collection-valued codomains.
/// See `src/interpreter/design-operators.md`, "Final-value extraction", for ordering, fallback,
/// and release. Induction histories use
/// [`StoreFinalRead`](crate::interpreter::commit_operator::StoreFinalRead) instead.
pub struct ExtractFinal {
    /// Operator producing the `DataFunction` tiling to extract from.
    source: Arc<dyn TileOperator>,
    /// Fallback for a terminal source with no live positions. Its extent must be included
    /// in the source codomain. `None` requires a source that cannot finish empty.
    default: Option<Arc<dyn TileOperator>>,
    /// Output tiling — what one position of the source holds.
    base: OperatorBase,
}

impl ExtractFinal {
    /// Extract from a collection, using `default` if it finishes without a live position.
    ///
    /// Panics if `source` is not a collection. Debug-asserts that its codomain extent includes
    /// the default's extent. The output has the source's codomain tiling.
    pub fn new(source: Arc<dyn TileOperator>, default: Arc<dyn TileOperator>) -> Self {
        let tiling = Self::source_codomain_tiling(source.as_ref());
        // Non-collection defaults are normalized through `scalar_tile_to_column_value`.
        // Record layouts may differ, and a variant default may carry fewer arms than the
        // declared output extent; equality of tilings would reject both cases.
        debug_assert!(
            tiling.extent().includes(&default.tiling().extent()),
            "ExtractFinal default must be representable in the source codomain: \
             default {} is not included in {tiling}",
            default.tiling(),
        );
        Self {
            base: OperatorBase::new(tiling),
            source,
            default: Some(default),
        }
    }

    /// Extract from a collection that cannot finish without a live position.
    ///
    /// Exhaustive tag partitions satisfy this precondition. A terminal empty source panics
    /// during extraction. Construction panics if `source` is not a collection.
    pub fn without_default(source: Arc<dyn TileOperator>) -> Self {
        let tiling = Self::source_codomain_tiling(source.as_ref());
        Self {
            base: OperatorBase::new(tiling),
            source,
            default: None,
        }
    }

    /// What one position of `source` holds: its levels minus the one being indexed.
    ///
    /// A one-level source holds a scalar per position; a deeper one holds a collection, and
    /// the final position's value is that collection rather than an element of it.
    fn source_codomain_tiling(source: &dyn TileOperator) -> Tiling {
        match source.tiling() {
            Tiling::DataFunction { codomain, .. } => *codomain.clone(),
            other => panic!("ExtractFinal source must have a collection tiling, got {other}"),
        }
    }
}

impl TileOperator for ExtractFinal {
    /// A breaker: its pipeline pushes its output to the pipelines that read it.
    fn keys_arrive_by_push(&self) -> bool {
        true
    }

    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("source", &*self.source));
        if let Some(default) = &self.default {
            visit(value("default", &**default));
        }
    }

    fn subscribe(
        self: Arc<Self>,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        let input = BreakerInput::new(consumer, self.source.tiling(), false);
        // Only source notifications reach the consumer. The default is subscribed eagerly
        // but pulled only after a terminal source has no live positions.
        let source_producer = self.source.clone().subscribe(
            self.source.tiling().universal_guard(),
            input.consumer,
            cx,
        );
        let default_producer = self.default.as_ref().map(|d| {
            d.clone()
                .subscribe(d.tiling().universal_guard(), Box::new(|| {}), cx)
        });
        share_breaker(ExtractFinalProducer::new(
            ProducerBase::new(
                ExtractFinalProducer::alloc_id(),
                self.tiling(),
                self.clone(),
                cx,
            )
            .breaking(input.downstream, input.placement),
            source_producer,
            default_producer,
        ))
    }
}

struct ExtractFinalProducer {
    base: ProducerBase,
    source: Box<dyn TileProducer>,
    default: Option<Box<dyn TileProducer>>,
    // shared-state-ok: this producer's own state, which `get`, `consume_impl` and `release` change
    // through `&self` on any worker thread; no other operator holds it.
    state: Mutex<FinalValueState>,
}
struct FinalValueState {
    /// Cached result, re-emitted until release. May remain absent after source completion
    /// while waiting for the default. Collection-valued results retain a whole sub-tile.
    final_tile: Option<Tile>,
    /// Completion survives reclamation of the extracted value.
    complete: bool,
    /// The source rows [`Breaker::consume_impl`] merged, kept to the row at the
    /// greatest key where the values are a column, and empty before the first consume.
    merged: Tile,
}

/// The final value of `source`, falling back to `default`, that nothing subscribed, answering at
/// `tiling`, for a test that builds a chain of pipelines by hand.
#[cfg(test)]
pub(crate) fn extract_final_of(
    source: Box<dyn TileProducer>,
    default: Option<Box<dyn TileProducer>>,
    tiling: &Tiling,
) -> crate::interpreter::dispatcher::BreakerHandle {
    Arc::new(RwLock::new(ExtractFinalProducer::new(
        ProducerBase::unowned(ExtractFinalProducer::alloc_id(), tiling),
        source,
        default,
    )))
}

#[cfg(test)]
impl ExtractFinal {
    /// This operator's producer over its subscribed source and default, unplaced, for a test
    /// that consumes it by hand.
    fn unplaced_producer(&self) -> ExtractFinalProducer {
        let mut cx = SubscribeContext::new();
        let source = self.source.clone().subscribe(
            self.source.tiling().universal_guard(),
            Box::new(|| {}),
            &mut cx,
        );
        let default = self.default.as_ref().map(|d| {
            d.clone()
                .subscribe(d.tiling().universal_guard(), Box::new(|| {}), &mut cx)
        });
        ExtractFinalProducer::new(
            ProducerBase::unowned(ExtractFinalProducer::alloc_id(), self.tiling()),
            source,
            default,
        )
    }

    /// [`unplaced_producer`](Self::unplaced_producer) once it has consumed its source whole.
    fn consumed_whole(&self) -> ExtractFinalProducer {
        use crate::interpreter::tile_operators::test_helpers::ConsumeInPipeline as _;
        let mut producer = self.unplaced_producer();
        let whole = producer.source.tiling().universal_guard();
        producer.consume_in_pipeline(InputId::ONLY, whole);
        producer
    }
}

impl ExtractFinalProducer {
    fn new(
        base: ProducerBase,
        source: Box<dyn TileProducer>,
        default: Option<Box<dyn TileProducer>>,
    ) -> Self {
        let merged = source.tiling().empty_tile();
        ExtractFinalProducer {
            base,
            source,
            default,
            state: Mutex::new(FinalValueState {
                final_tile: None,
                complete: false,
                merged,
            }),
        }
    }

    /// The value at row `final_idx` of a source whose keys are `domain`: the position being
    /// indexed is this collection's key, and what it holds is everything below it, a value where
    /// the values are a column and a whole collection where they are one.
    fn value_at(&self, source: &Tile, final_idx: usize) -> Tile {
        let Tile::DataFunction { codomain, .. } = source else {
            panic!("ExtractFinal source must be a collection tile");
        };
        if codomain.is_data_function() {
            // That key's group, taken out on its own, is the value at this position. Every
            // level's predicates are restated over the group's own paths: a level beneath
            // the group's own still names the indexed key in its enclosing paths.
            source
                .group_at(CurryLevel::new(1), final_idx)
                .expect("a live row of the source has a group")
                .into_owned()
        } else {
            // Built at the *declared* extent: a tag `match` collapses its arms to their
            // join, and the arm that answers carries only its own tag. Laid out as this
            // operator's tiling, which keeps a product a record of columns.
            let cv = scalar_tile_to_column_value((**codomain).clone());
            column_value_to_tile(
                ColumnValue::from_values(vec![cv.index_at(final_idx)], &self.tiling().extent()),
                self.tiling(),
            )
        }
    }

    /// The default's value once it has converged, which is when it is terminal, and `None`
    /// before. The default is released once it has been read.
    ///
    /// # Panics
    ///
    /// For a source declared total that emitted no value.
    fn pull_default(&self) -> Option<Tile> {
        let extent = self.tiling().extent();
        let yields_a_level = self.tiling().is_data_function();
        let Some(default) = self.default.as_ref() else {
            panic!(
                "ExtractFinal over a source declared total emitted no value; the \
                 partition feeding it was not exhaustive"
            );
        };
        let default_tiling = default.tiling().clone();
        let default_tile = default.get(default_tiling.universal_guard());
        // A collection-valued position falls back to the whole collection, so the default
        // is the tile it is rather than a value to rebuild a column from. It has converged
        // once it is terminal, which is what `as_single` says for the scalar case.
        if yields_a_level {
            if !default_tile.is_terminal() {
                return None;
            }
            default.release(default_tiling.universal_guard());
            return Some(default_tile);
        }
        // A subsequent pull can retry an incomplete default.
        let value = scalar_tile_to_column_value(default_tile).as_single()?;
        default.release(default_tiling.universal_guard());
        Some(Tile::Scalar(ColumnValue::from_values(vec![value], &extent)))
    }
}

impl TileProducer for ExtractFinalProducer {
    impl_producer_base!();

    fn state_info(&self) -> ProducerStateInfo {
        let mut state_guard = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        let state = &mut *state_guard;

        ProducerStateInfo::holding(
            state.merged.cell_count() + state.final_tile.as_ref().map_or(0, Tile::cell_count),
        )
    }

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("source", &*self.source);
        if let Some(default) = &self.default {
            visit("default", &**default);
        }
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit("source", &mut *self.source);
        if let Some(default) = &mut self.default {
            visit("default", &mut **default);
        }
    }

    fn as_breaking_mut(&mut self) -> Option<&mut dyn BreakingProducer> {
        Some(self)
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        let node = node.child("source", self.source.inspect(opts));
        match &self.default {
            Some(d) => node.child("default", d.inspect(opts)),
            None => node.annotate("total (no default)".to_string()),
        }
    }

    fn answers_from_state(&self) -> bool {
        true
    }

    /// The final position of a stream is one value, or one collection that a release takes
    /// whole, so the projection is all of it or none: the source is read whole whatever the
    /// consumer asks, because the last position is not known before the stream ends.
    fn get_impl(&self, guard: TileGuard) -> Tile {
        let mut state_guard = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        let state = &mut *state_guard;

        let projection = projection_of_one_value(&self.name(), "extracts one final value", &guard);
        if projection == Projection::Nothing || self.obsolete_guard().is_universal() {
            return self.tiling().empty_tile();
        }
        // A final record of values is pulled at a part of it as any record is.
        let mut tile = state
            .final_tile
            .clone()
            .unwrap_or_else(|| self.tiling().empty_tile());
        tile.restrict_to(&projection, self.tiling());
        tile
    }

    fn release_impl(&self, obsolete_guard: TileGuard) {
        let mut state_guard = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        let state = &mut *state_guard;

        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            state.final_tile = None;
            state.merged = self.source.tiling().empty_tile();
            self.source.release(self.source.tiling().universal_guard());
            if let Some(d) = self.default.as_ref() {
                d.release(d.tiling().universal_guard());
            }
        }
    }
}

impl Breaker for ExtractFinalProducer {
    fn input_tiling(&self, _: InputId) -> Tiling {
        self.source.tiling().clone()
    }

    fn input_released(&self, _: InputId) -> TileGuard {
        self.source.obsolete_guard().clone()
    }

    /// Pushes the extracted value, as every breaker pushes its final guard.
    ///
    /// # Panics
    ///
    /// When the output is unreleased and no value has been extracted: the source has not been
    /// released whole, or the default it fell back to has not converged. A dispatcher issues no
    /// `consume_impl` after the finish, so nothing would read that default again, and pushing
    /// nothing would leave the reader with no value.
    fn finish(&mut self, _input: InputId, pushes: &mut Pushes<'_>) {
        let mut state_guard = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        let state = &mut *state_guard;

        assert!(
            self.obsolete_guard().is_universal() || state.final_tile.is_some(),
            "{} finishes after it extracted its value: the source released whole and any \
             default it fell back to converged",
            self.name()
        );
        drop(state_guard);
        pushes.push_final(self);
    }

    fn as_producer(&self) -> Option<&dyn BreakingProducer> {
        Some(self)
    }

    /// Merges the source rows it answers at `guard`, a guard of the source's tiling, keeps the
    /// row at the greatest key, and releases the source at what the answer stated. Rows merge in
    /// the order they arrive, so the last row is not the final one: the key says which is. Once
    /// the source has been released whole the value is extracted, or the default read when the
    /// source held nothing.
    ///
    /// The source is pulled with no lock held, so packages of disjoint keys pull at once. The
    /// merge, the release and the extraction run under the state's lock, so the consume that
    /// sees the source released whole has merged every row another consume released.
    fn consume_impl(&self, _: InputId, guard: TileGuard) {
        debug_assert!(
            guard.check_from(self.source.tiling()),
            "{} consumes a guard of its source's tiling: {guard:?}",
            self.name()
        );
        if self.obsolete_guard().is_universal() || guard.is_empty() || self.extracted() {
            return;
        }
        let mut answered = self.source.get(guard);
        let upstream_guard = answered.to_guard();
        answered.compact();
        let mut state_guard = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        let state = &mut *state_guard;
        if state.final_tile.is_some() {
            self.source.release(upstream_guard);
            return;
        }
        state.merged.merge(answered);
        self.keep_greatest_key(state);
        self.source.release(upstream_guard);
        self.extract_once_released(state);
    }

    fn finish_parallel_input(&mut self) {
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        if self.obsolete_guard().is_universal() || state.final_tile.is_some() {
            return;
        }
        self.source.release(self.source.tiling().universal_guard());
        self.extract_once_released(&mut state);
    }
}

impl ExtractFinalProducer {
    /// Whether the value has been extracted.
    fn extracted(&self) -> bool {
        self.state
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .final_tile
            .is_some()
    }

    /// Release the rows beneath the greatest key merged, while the source is not released whole;
    /// once it is, extract the row at the greatest key, or read the default where the source held
    /// nothing.
    fn extract_once_released(&self, state: &mut FinalValueState) {
        if !self.source.obsolete_guard().is_universal() {
            let greatest = state
                .merged
                .live_keys()
                .into_iter()
                .flatten()
                .filter_map(|(_, key)| match key {
                    Value::UInt(position) => Some(position),
                    _ => None,
                })
                .max();
            if let Some(greatest) = greatest.filter(|position| *position > 0) {
                self.source
                    .release(TileGuard::Function(FunctionGuard::Domain(
                        Predicate::at_or_below(Value::UInt(greatest - 1)),
                    )));
            }
            return;
        }
        let Tile::DataFunction {
            domain, deleted, ..
        } = &mut state.merged
        else {
            panic!("ExtractFinal source must be a collection tile");
        };
        state.final_tile = match greatest_live_key(domain, deleted) {
            Some(final_idx) => Some(self.value_at(&state.merged, final_idx)),
            None => self.pull_default(),
        };
        if state.final_tile.is_some() {
            state.complete = true;
            state.merged = self.source.tiling().empty_tile();
        }
    }
}

impl BreakingProducer for ExtractFinalProducer {
    /// The final value once there is one, whether it is complete, and the row at the greatest key
    /// merged so far.
    fn checkpoint(&self) -> Box<dyn std::any::Any + Send> {
        let state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        Box::new((
            state.final_tile.clone(),
            state.complete,
            state.merged.clone(),
        ))
    }

    fn restore(&mut self, state: Box<dyn std::any::Any + Send>) {
        let (final_tile, complete, merged) =
            checkpoint::state_of::<(Option<Tile>, bool, Tile)>(&self.name(), state);
        *self.state.get_mut().unwrap_or_else(PoisonError::into_inner) = FinalValueState {
            final_tile,
            complete,
            merged,
        };
    }

    /// The extracted value, once there is one: none while the source has not drained, or while a
    /// default it fell back to has not converged. The next `consume_impl` reads the default again.
    fn complete(&self) -> TileGuard {
        let mut state_guard = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        let state = &mut *state_guard;

        match state.complete {
            true => self.tiling().universal_guard(),
            false => self.tiling().empty_guard(),
        }
    }
}

impl ExtractFinalProducer {
    /// Drop every merged row but the one at the greatest key, which is the only one an
    /// extraction can still need, where the values are a column of scalars. Any other shape of
    /// value keeps every merged row.
    fn keep_greatest_key(&self, state: &mut FinalValueState) {
        let Tile::DataFunction {
            domain,
            codomain,
            deleted,
            ..
        } = &state.merged
        else {
            return;
        };
        let Tile::Scalar(values) = &**codomain else {
            return;
        };
        let Some(idx) = greatest_live_key(domain, deleted) else {
            return;
        };
        let Tile::DataFunction {
            domain_predicate, ..
        } = &state.merged
        else {
            return;
        };
        state.merged = Tile::data_function(
            domain.select_indices(std::iter::once(idx), 1),
            Box::new(Tile::Scalar(values.select_indices(std::iter::once(idx), 1))),
            domain_predicate.clone(),
            bit_set::BitSet::new(),
        );
    }
}

/// The row at the greatest key among the rows `deleted` does not name. Merged rows are in the
/// order they arrived, which is not the order of their keys.
fn greatest_live_key(domain: &ColumnValue, deleted: &bit_set::BitSet) -> Option<usize> {
    (0..domain.len())
        .filter(|row| !deleted.contains(*row))
        .max_by(|a, b| {
            domain
                .index_at(*a)
                .partial_cmp(&domain.index_at(*b))
                .expect("the keys of one collection compare")
        })
}

#[cfg(test)]
mod tests {
    use crate::interpreter::tile_operators::test_helpers::SharedCounter as Cell;
    use std::sync::Arc;
    use std::sync::RwLock;

    use super::*;
    use crate::interpreter::tile_operators::{FunctionGuard, Predicate};
    use crate::interpreter::{BaseType, Extent};

    /// A non-terminal `DataFunction` source with domain `[0, 1, 2]`, recording
    /// every domain-release watermark it receives. Never becomes terminal, so it
    /// exercises `ExtractFinal`'s incremental (pre-terminal) release path.
    struct PartialSource {
        tiling: Tiling,
        releases: Arc<RwLock<Vec<u64>>>,
    }

    struct PartialSourceProducer {
        base: ProducerBase,
        releases: Arc<RwLock<Vec<u64>>>,
    }

    impl TileOperator for PartialSource {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            self: std::sync::Arc<Self>,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            Box::new(PartialSourceProducer {
                base: ProducerBase::unowned(PartialSourceProducer::alloc_id(), &self.tiling),
                releases: self.releases.clone(),
            })
        }
    }

    impl TileProducer for PartialSourceProducer {
        impl_producer_base!();
        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
            Tile::data_function(
                ColumnValue::from_uints(vec![0, 1, 2]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30]))),
                Predicate::False,
                bit_set::BitSet::new(),
            )
        }
        fn release_impl(&self, obsolete_guard: TileGuard) {
            if let TileGuard::Function(FunctionGuard::Domain(released)) = &obsolete_guard
                && let Some(Value::UInt(w)) = released.as_at_or_below()
            {
                self.releases
                    .write()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(w);
            }
        }
    }

    /// A **terminal** `DataFunction` source carrying `codomain_tile` over
    /// `domain`, used to drive `ExtractFinal` to its extract / default paths.
    struct TerminalSource {
        tiling: Tiling,
        domain: ColumnValue,
        codomain_tile: ColumnValue,
    }

    struct TerminalSourceProducer {
        base: ProducerBase,
        domain: ColumnValue,
        codomain_tile: ColumnValue,
    }

    impl TileOperator for TerminalSource {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            self: std::sync::Arc<Self>,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            Box::new(TerminalSourceProducer {
                base: ProducerBase::unowned(TerminalSourceProducer::alloc_id(), &self.tiling),
                domain: self.domain.clone(),
                codomain_tile: self.codomain_tile.clone(),
            })
        }
    }

    impl TileProducer for TerminalSourceProducer {
        impl_producer_base!();
        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
            Tile::data_function(
                self.domain.clone(),
                Box::new(Tile::Scalar(self.codomain_tile.clone())),
                Predicate::True,
                bit_set::BitSet::new(),
            )
        }
        fn release_impl(&self, _obsolete_guard: TileGuard) {}
    }

    fn named_variant(arms: &[(&str, Extent)]) -> Extent {
        Extent::Union(crate::ccl::TagMap::from_arms(
            arms.iter()
                .map(|(t, e)| (crate::ccl::FieldKey::Name((*t).into()), e.clone()))
                .collect(),
        ))
    }

    /// A scalar default whose availability and notifications are controlled by the test.
    struct DelayedDefault {
        tiling: Tiling,
        ready: Arc<Cell<bool>>,
        consumer: test_helpers::InputConsumer,
    }

    struct DelayedDefaultProducer {
        base: ProducerBase,
        ready: Arc<Cell<bool>>,
    }

    impl TileOperator for DelayedDefault {
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            self: std::sync::Arc<Self>,
            _intent_guard: TileGuard,
            consumer: Box<dyn Consumer>,
            _cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            *self
                .consumer
                .write()
                .unwrap_or_else(PoisonError::into_inner) = Some(consumer.into());
            Box::new(DelayedDefaultProducer {
                base: ProducerBase::unowned(DelayedDefaultProducer::alloc_id(), &self.tiling),
                ready: self.ready.clone(),
            })
        }
    }

    impl TileProducer for DelayedDefaultProducer {
        impl_producer_base!();
        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
            if self.ready.get() {
                Tile::Scalar(ColumnValue::Ints(vec![42]))
            } else {
                self.tiling().empty_tile()
            }
        }
        fn release_impl(&self, _obsolete_guard: TileGuard) {}
    }

    fn int_source(keys: Vec<u64>, values: Vec<i64>) -> TerminalSource {
        TerminalSource {
            tiling: Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
            domain: ColumnValue::from_uints(keys),
            codomain_tile: ColumnValue::Ints(values),
        }
    }

    /// BUG: a ready fallback should wake readers and let Memo deliver 42, but its notification
    /// is discarded, and Memo keeps returning an empty result. Convert this pin when repaired.
    #[test]
    fn bug_delayed_default_does_not_wake_a_memoized_consumer() {
        let ready = Arc::new(Cell::new(false));
        let consumer = Arc::new(RwLock::new(None));
        let default = DelayedDefault {
            tiling: Tiling::Scalar(Extent::Base(BaseType::Int)),
            ready: ready.clone(),
            consumer: consumer.clone(),
        };
        let extract = ExtractFinal::new(
            std::sync::Arc::new(int_source(vec![], vec![])),
            std::sync::Arc::new(default),
        );
        // Memo will not retry an incomplete upstream unless it receives a notification.
        let op = std::sync::Arc::new(Memo::new(std::sync::Arc::new(extract)));
        let guard = op.tiling().universal_guard();
        let notifications = Arc::new(Cell::new(0));
        let observed = notifications.clone();
        let mut producer = op.clone().subscribe(
            guard.clone(),
            Box::new(move || observed.set(observed.get() + 1)),
            &mut SubscribeContext::new(),
        );
        assert!(!producer.read_in_pipeline(guard.clone()).is_terminal());

        ready.set(true);
        test_helpers::subscribed(&consumer).announce(&Projection::Everything);
        assert_eq!(notifications.get(), 0, "bug pin: the fallback wake is lost");
        let Tile::Scalar(result) = producer.read_in_pipeline(guard) else {
            panic!("expected a scalar fallback");
        };
        assert_eq!(
            result.as_single(),
            None,
            "bug pin: Memo never retries extraction"
        );
    }

    /// A terminal source of one record `(a: 1, b: 2)` at key 0.
    struct RecordSource {
        tiling: Tiling,
    }

    struct RecordSourceProducer {
        base: ProducerBase,
    }

    impl RecordSource {
        fn new() -> Self {
            let int = || Tiling::Scalar(Extent::Base(BaseType::Int));
            RecordSource {
                tiling: Tiling::data_function(
                    Extent::Base(BaseType::UInt),
                    Tiling::Record([("a".into(), int()), ("b".into(), int())].into()),
                ),
            }
        }
    }

    impl TileOperator for RecordSource {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            self: std::sync::Arc<Self>,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            Box::new(RecordSourceProducer {
                base: ProducerBase::unowned(RecordSourceProducer::alloc_id(), &self.tiling),
            })
        }
    }

    impl TileProducer for RecordSourceProducer {
        impl_producer_base!();
        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
            let int = |v: i64| Tile::Scalar(ColumnValue::Ints(vec![v]));
            Tile::data_function(
                ColumnValue::from_uints(vec![0]),
                Box::new(Tile::record(
                    [("a".into(), int(1)), ("b".into(), int(2))].into(),
                )),
                Predicate::True,
                bit_set::BitSet::new(),
            )
        }
        fn release_impl(&self, _obsolete_guard: TileGuard) {}
    }

    /// An extractor pulled at the field `a` of the final record `(a: 1, b: 2)` answers `a` alone,
    /// on the first read and on a reread. `get` checks each answer against the projection in a
    /// debug build, and the test checks it in every build.
    #[test]
    fn an_extractor_answers_only_the_field_it_is_pulled_at() {
        let op = ExtractFinal::without_default(std::sync::Arc::new(RecordSource::new()));
        let mut producer = op.consumed_whole();
        let field_a = Projection::of_field("a", Projection::Everything);
        let guard = field_a.guard(op.tiling());
        for read in ["the first read", "a reread"] {
            let answer = producer.read_in_pipeline(guard.clone());
            let Tile::Record { fields, .. } = &answer else {
                panic!("{read}: a record: {answer:?}")
            };
            assert_eq!(
                fields["a"],
                Tile::Scalar(ColumnValue::Ints(vec![1])),
                "{read}"
            );
            assert!(fields["b"].is_empty(), "{read} answers b: {answer:?}");
        }
    }

    /// A universal release drops the cached final value, from the source or from the fallback,
    /// and a later pull emits nothing.
    #[test]
    fn a_universal_release_drops_the_cached_final_value() {
        fn retained(producer: &dyn TileProducer) -> usize {
            producer
                .inspect(&Default::default())
                .held_values
                .unwrap_or_default()
        }
        for use_default in [false, true] {
            let source = if use_default {
                int_source(vec![], vec![])
            } else {
                int_source(vec![0], vec![42])
            };
            let default = Constant::new(Value::Int(42), Extent::Base(BaseType::Int));
            let op = std::sync::Arc::new(ExtractFinal::new(
                std::sync::Arc::new(source),
                std::sync::Arc::new(default),
            ));
            let guard = op.tiling().universal_guard();
            let mut producer = op.consumed_whole();
            assert!(producer.read_in_pipeline(guard.clone()).is_terminal());
            assert!(retained(&producer) > 0);
            producer.release(guard.clone());
            assert_eq!(retained(&producer), 0, "a released cache holds nothing");
            assert_eq!(producer.read_in_pipeline(guard).cell_count(), 0);
        }
    }

    /// Terminal extraction selects the row at the greatest live key, not the last row: the value
    /// at key 2 is 20.
    #[test]
    fn terminal_extraction_selects_the_greatest_live_key() {
        let op = std::sync::Arc::new(ExtractFinal::without_default(std::sync::Arc::new(
            int_source(vec![2, 0, 1], vec![20, 0, 10]),
        )));
        let guard = op.tiling().universal_guard();
        let mut producer = op.consumed_whole();
        let Tile::Scalar(result) = producer.read_in_pipeline(guard) else {
            panic!("expected a scalar final value");
        };
        assert_eq!(result.as_single(), Some(Value::Int(20)));
    }

    fn union_value(tag: &str, inner: Value) -> Value {
        Value::Union {
            tag: crate::ccl::FieldKey::Name(tag.into()),
            inner: Box::new(inner),
        }
    }

    /// The tags a `ColumnValue::Union` carries, and which of them hold rows.
    fn arm_occupancy(cv: &ColumnValue) -> Vec<(String, usize)> {
        let ColumnValue::Union(arms) = cv else {
            panic!("expected a union column, got {cv:?}");
        };
        arms.iter()
            .map(|(k, arm)| (k.to_string(), arm.len()))
            .collect()
    }

    /// A conditional whose arms carry different tags collapses to the arms'
    /// **join**, so the value that survives has to be emitted at that merged tag
    /// set — every arm present, the ones that did not occur empty. Emitting the
    /// column the value alone implies would carry only `.pos`, which then fails to
    /// conform to this operator's own tiling and cannot merge with a sibling arm.
    #[test]
    fn extracted_variant_is_emitted_at_the_merged_tag_set() {
        let merged = named_variant(&[
            ("neg", Extent::Base(BaseType::Int)),
            ("pos", Extent::Base(BaseType::Int)),
        ]);
        let source = TerminalSource {
            tiling: Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(merged.clone()),
            ),
            domain: ColumnValue::from_uints(vec![0]),
            codomain_tile: ColumnValue::from_values(
                vec![union_value("pos", Value::Int(5))],
                &merged,
            ),
        };
        // The default is the *other* arm, so its own extent is width-narrower.
        let default = Constant::new(
            union_value("neg", Value::Int(0)),
            named_variant(&[("neg", Extent::Base(BaseType::Int))]),
        );
        let op = std::sync::Arc::new(ExtractFinal::new(
            std::sync::Arc::new(source),
            std::sync::Arc::new(default),
        ));
        let mut producer = op.consumed_whole();
        let tile = producer.read_in_pipeline(producer.tiling().universal_guard());

        let Tile::Scalar(cv) = tile else {
            panic!("expected a scalar tile");
        };
        assert_eq!(
            arm_occupancy(&cv),
            vec![("neg".to_string(), 0), ("pos".to_string(), 1)],
            "both tags present, only the one that occurred inhabited"
        );
        assert_eq!(cv.as_single(), Some(union_value("pos", Value::Int(5))));
    }

    /// The same widening on the **default** path: a terminal-but-empty source
    /// falls back to the trailing arm, whose value carries only its own tag.
    #[test]
    fn default_variant_is_emitted_at_the_merged_tag_set() {
        let merged = named_variant(&[
            ("neg", Extent::Base(BaseType::Int)),
            ("pos", Extent::Base(BaseType::Int)),
        ]);
        let source = TerminalSource {
            tiling: Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(merged.clone()),
            ),
            domain: ColumnValue::from_uints(vec![]),
            codomain_tile: ColumnValue::from_values(vec![], &merged),
        };
        let default = Constant::new(
            union_value("neg", Value::Int(7)),
            named_variant(&[("neg", Extent::Base(BaseType::Int))]),
        );
        let op = std::sync::Arc::new(ExtractFinal::new(
            std::sync::Arc::new(source),
            std::sync::Arc::new(default),
        ));
        let mut producer = op.consumed_whole();
        let tile = producer.read_in_pipeline(producer.tiling().universal_guard());

        let Tile::Scalar(cv) = tile else {
            panic!("expected a scalar tile");
        };
        assert_eq!(
            arm_occupancy(&cv),
            vec![("neg".to_string(), 1), ("pos".to_string(), 0)],
        );
        assert_eq!(cv.as_single(), Some(union_value("neg", Value::Int(7))));
    }

    /// On a consume of a non-terminal source, `ExtractFinal` needs only the highest-domain value,
    /// so it releases everything below it — `[0, max)`. Over a source with domain
    /// `[0, 1, 2]`, it forwards a release `≤ 1`, freeing the prefix that a
    /// never-terminating scalar-final loop would otherwise pin.
    #[test]
    fn extract_final_releases_below_the_running_max() {
        let value_tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let releases = Arc::new(RwLock::new(Vec::<u64>::new()));
        let source = PartialSource {
            tiling: Tiling::data_function(Extent::Base(BaseType::UInt), value_tiling.clone()),
            releases: releases.clone(),
        };
        let default = Constant::new(Value::Int(0), Extent::Base(BaseType::Int));
        let op = std::sync::Arc::new(ExtractFinal::new(
            std::sync::Arc::new(source),
            std::sync::Arc::new(default),
        ));
        // Non-terminal source → ExtractFinal's consume releases `[0, max)` and it emits empty.
        let mut producer = op.consumed_whole();
        let tile = producer.read_in_pipeline(producer.tiling().universal_guard());
        assert!(
            !tile.is_terminal(),
            "a non-terminal source stays non-terminal"
        );
        assert_eq!(
            releases
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .last()
                .copied(),
            Some(1),
            "ExtractFinal must release below the running max (positions 0, 1), keeping position 2"
        );
    }
}

#[cfg(test)]
mod projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpyOp, keys_between,
    };
    use crate::interpreter::{BaseType, Extent};

    /// `final_or_default(xs, 0)` over a finished stream `[10, 20, 30]`, with the pulls of the
    /// stream logged.
    fn final_of_finished_stream() -> (ExtractFinalProducer, GuardLog) {
        let int = || Extent::Base(BaseType::Int);
        let tiling = Tiling::data_function(Extent::uint_range(3), Tiling::Scalar(int()));
        let finished = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1, 2]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30]))),
            Predicate::True,
            bit_set::BitSet::new(),
        );
        let (stream, pulled, _) = ProjectionSpyOp::new(finished, tiling);
        let op = Arc::new(ExtractFinal::new(
            Arc::new(stream),
            Arc::new(Constant::new(Value::Int(0), int())),
        ));
        (op.unplaced_producer(), pulled)
    }

    /// The last position is not known before the stream ends, so the stream consumed whole is
    /// read once, and the value at its last position is the answer.
    #[test]
    fn the_stream_is_read_whole_to_find_its_last_position() {
        use crate::interpreter::tile_operators::test_helpers::ConsumeInPipeline as _;
        let (mut last, pulled) = final_of_finished_stream();
        let whole = last.source.tiling().universal_guard();
        last.consume_in_pipeline(InputId::ONLY, whole);
        let tile = last.read_in_pipeline(last.tiling().universal_guard());
        assert_eq!(tile, Tile::Scalar(ColumnValue::Ints(vec![30])));
        assert_eq!(
            pulled.read().unwrap_or_else(PoisonError::into_inner).len(),
            1
        );
        assert!(pulled.read().unwrap_or_else(PoisonError::into_inner)[0].is_universal());
    }

    #[test]
    fn asking_for_nothing_reads_nothing() {
        let (mut last, pulled) = final_of_finished_stream();
        let tile = last.read_in_pipeline(last.tiling().empty_guard());
        assert_eq!(tile, last.tiling().empty_tile());
        assert!(
            pulled
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_empty()
        );
    }

    #[test]
    #[should_panic(expected = "extracts one final value")]
    fn a_key_projection_is_rejected() {
        let (mut last, _) = final_of_finished_stream();
        last.read_in_pipeline(keys_between(0, 1));
    }
}

/// A consuming `ExtractFinal` over an input that grows and is released: the value it extracts, what
/// its final guard names and what reaches the source, against a model of the keys consumed.
#[cfg(test)]
mod consuming_tests {
    use super::*;
    use std::collections::BTreeSet;

    use crate::interpreter::dispatcher::{Dispatcher, PipelineId};
    use crate::interpreter::tile_operators::growing::{
        Input, InputModel, KEYS, Region, Rng, Shared, Step, growing_source, ints, predicate,
        source, value,
    };
    use crate::interpreter::tile_operators::test_helpers::push_to;
    use crate::interpreter::tile_operators::test_helpers::{
        ScriptedProducer, TestTileProducer, keys_between,
    };
    use crate::interpreter::{BaseType, Extent};
    use Region::{All, Keys};
    use Step::{Add, Close, Consume, Release};

    fn int() -> Tiling {
        Tiling::Scalar(Extent::Base(BaseType::Int))
    }

    fn default_of(value: i64) -> Option<Box<dyn TileProducer>> {
        Some(Box::new(TestTileProducer::new(
            Tile::Scalar(ColumnValue::Ints(vec![value])),
            int(),
        )))
    }

    fn final_over(source: &Shared, default: Option<Box<dyn TileProducer>>) -> ExtractFinalProducer {
        ExtractFinalProducer::new(
            ProducerBase::unowned(ExtractFinalProducer::alloc_id(), &int()),
            Box::new(Input::over(source)),
            default,
        )
    }

    fn scalar_of(tile: &Tile) -> Option<i64> {
        match tile {
            Tile::Scalar(ColumnValue::Ints(values)) => values.first().copied(),
            other if other.is_empty() => None,
            other => panic!("an integer, got {other:?}"),
        }
    }

    fn offer(extract: &mut ExtractFinalProducer) -> Option<i64> {
        scalar_of(&extract.get(int().universal_guard()))
    }

    /// Rows arrive in the order they are consumed, so the final value is the one at the greatest
    /// key, not the last to arrive.
    #[test]
    fn the_greatest_key_is_final_whatever_arrived_last() {
        let source = source(0..12);
        let mut extract = final_over(&source, None);
        extract.begin_run();
        extract.consume_in_pipeline(InputId::ONLY, keys_between(8, 11));
        assert_eq!(
            offer(&mut extract),
            None,
            "the source has not stated everything complete"
        );
        // The rows below arrive after the row at key 11, which stays final.
        extract.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        assert_eq!(offer(&mut extract), Some(value(11)));
        assert_eq!(
            source
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .pulled
                .len(),
            2
        );
    }

    /// Pending source rows are counted, and completed extraction retains only its result.
    #[test]
    fn extraction_reclaims_the_merged_source_and_accounts_for_pending_rows() {
        let source = source(0..10);
        let mut extract = final_over(&source, None);
        extract.consume_in_pipeline(InputId::ONLY, keys_between(2, 5));
        assert!(extract.state.get_mut().unwrap().merged.cell_count() > 0);
        assert_eq!(
            extract.state_info().values,
            extract.state.get_mut().unwrap().merged.cell_count()
        );
        extract.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        assert_eq!(offer(&mut extract), Some(value(9)));
        assert_eq!(extract.state.get_mut().unwrap().merged.cell_count(), 0);
        assert_eq!(
            extract.state_info().values,
            extract
                .state
                .get_mut()
                .unwrap()
                .final_tile
                .as_ref()
                .unwrap()
                .cell_count()
        );
        extract.release(extract.tiling().universal_guard());
        assert_eq!(extract.state_info().values, 0);
        assert!(extract.complete().is_universal());
    }

    /// A collection-valued result does not retain the other source rows after extraction.
    #[test]
    fn collection_extraction_retains_only_the_final_collection() {
        use crate::interpreter::tile_operators::test_helpers::two_levels_of_ints;
        let (tile, tiling) = two_levels_of_ints();
        let Tiling::DataFunction { codomain, .. } = &tiling else {
            unreachable!()
        };
        let mut extract = ExtractFinalProducer::new(
            ProducerBase::unowned(ExtractFinalProducer::alloc_id(), codomain),
            Box::new(TestTileProducer::new(tile.clone(), tiling.clone())),
            None,
        );
        let expected = extract.value_at(&tile, 1);
        extract.consume_in_pipeline(InputId::ONLY, tiling.universal_guard());
        assert_eq!(extract.get(extract.tiling().universal_guard()), expected);
        assert_eq!(extract.state.get_mut().unwrap().merged.cell_count(), 0);
        assert_eq!(extract.state_info().values, expected.cell_count());
    }

    /// Out-of-order morsels that end below the key a first morsel held leave that key final.
    #[test]
    fn a_later_morsel_with_smaller_keys_does_not_replace_the_final_row() {
        let source = source([1, 2, 9, 10]);
        let mut extract = final_over(&source, None);
        extract.begin_run();
        extract.consume_in_pipeline(InputId::ONLY, keys_between(9, 11));
        extract.consume_in_pipeline(InputId::ONLY, keys_between(0, 3));
        extract.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        assert_eq!(offer(&mut extract), Some(value(10)));
    }

    /// A region is pulled once and released at what the answer stated, then everything below the
    /// greatest key merged is released, and a partial source yields no value. The release below
    /// the greatest key follows every consume, a repeat of the last included.
    #[test]
    fn a_region_is_pulled_and_released_and_yields_no_value_yet() {
        let source = source(0..10);
        let mut extract = final_over(&source, None);
        extract.begin_run();
        extract.consume_in_pipeline(InputId::ONLY, keys_between(2, 5));
        assert_eq!(
            source.read().unwrap_or_else(PoisonError::into_inner).pulled,
            vec![keys_between(2, 5)]
        );
        assert_eq!(
            source
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released,
            vec![keys_between(2, 5), keys_between(0, 4)]
        );
        assert_eq!(offer(&mut extract), None);
        extract.consume_in_pipeline(InputId::ONLY, keys_between(7, 9));
        extract.consume_in_pipeline(InputId::ONLY, keys_between(4, 8));
        assert_eq!(
            source
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released,
            vec![
                keys_between(2, 5),
                keys_between(0, 4),
                keys_between(7, 9),
                keys_between(0, 8),
                keys_between(4, 8),
                keys_between(0, 8),
            ]
        );
    }

    #[test]
    fn nothing_consumed_pulls_nothing() {
        let source = source(0..10);
        let mut extract = final_over(&source, None);
        extract.begin_run();
        extract.consume_in_pipeline(InputId::ONLY, ints().empty_guard());
        assert!(
            source
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .pulled
                .is_empty()
        );
    }

    /// An empty source that has drained falls back to the default, read once.
    #[test]
    fn an_empty_drained_source_yields_the_default() {
        let source = source([]);
        let mut extract = final_over(&source, default_of(7));
        extract.begin_run();
        extract.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        assert_eq!(offer(&mut extract), Some(7));
        assert_eq!(extract.final_guard(), int().universal_guard());
    }

    /// A default that has not converged when the source drains leaves nothing held; the next
    /// consume reads it again, as every pull does queried inside a pipeline.
    #[test]
    fn an_unconverged_default_is_read_again_by_the_next_consume() {
        let source = source([]);
        let (default, cell) = ScriptedProducer::new(Tile::Scalar(ColumnValue::Ints(vec![])), int());
        let mut extract = final_over(&source, Some(Box::new(default)));
        extract.begin_run();
        extract.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        assert_eq!(offer(&mut extract), None, "the default has not converged");
        assert_eq!(
            extract.final_guard(),
            int().empty_guard(),
            "nothing is held yet"
        );

        *cell.write().unwrap_or_else(PoisonError::into_inner) =
            Tile::Scalar(ColumnValue::Ints(vec![7]));
        extract.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        assert_eq!(offer(&mut extract), Some(7));
        assert_eq!(extract.final_guard(), int().universal_guard());
    }

    /// A default that has not converged by the `finish` is never read again: the dispatcher
    /// issues no later `consume_impl`.
    #[test]
    #[should_panic(expected = "finishes after it extracted its value")]
    fn finish_with_an_unconverged_default_panics() {
        let source = source([]);
        let (default, _) = ScriptedProducer::new(Tile::Scalar(ColumnValue::Ints(vec![])), int());
        let mut extract = final_over(&source, Some(Box::new(default)));
        extract.begin_run();
        extract.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        extract.finish(
            InputId::ONLY,
            &mut Dispatcher::new(vec![vec![]], usize::MAX).pushes(PipelineId(0)),
        );
    }

    /// An output released before the value was extracted pushes nothing, and that is no error.
    #[test]
    fn finish_after_the_output_was_released_pushes_nothing() {
        let source = growing_source(0..4);
        let mut extract = final_over(&source, None);
        extract.begin_run();
        extract.consume_in_pipeline(InputId::ONLY, keys_between(0, 1));
        extract.release(int().universal_guard());
        assert_eq!(extract.complete(), int().empty_guard());
        push_to(&mut extract, &[1]);
        let dispatcher = Dispatcher::new(vec![vec![], vec![0]], usize::MAX);
        dispatcher.finish_by_hand(PipelineId(0), |pushes| {
            extract.finish(InputId::ONLY, pushes)
        });
        assert!(dispatcher.pop().is_none());
    }

    /// A total source that is empty is an invariant violation, as queried inside a pipeline.
    #[test]
    #[should_panic(expected = "declared total emitted no value")]
    fn an_empty_total_source_fails_loudly() {
        let source = source([]);
        let mut extract = final_over(&source, None);
        extract.begin_run();
        extract.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
    }

    #[test]
    fn final_guard_holds_the_value_until_it_is_released() {
        let source = source(0..4);
        let mut extract = final_over(&source, None);
        extract.begin_run();
        extract.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        assert_eq!(extract.final_guard(), int().universal_guard());
        extract.release(int().universal_guard());
        assert_eq!(extract.final_guard(), int().empty_guard());
        assert_eq!(extract.complete(), int().universal_guard());
        assert_eq!(offer(&mut extract), None);
    }

    #[test]
    fn a_consuming_extraction_offers_without_pulling() {
        let source = source(0..10);
        let mut extract = final_over(&source, None);
        extract.begin_run();
        extract.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        let pulls = source
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .pulled
            .len();
        for _ in 0..3 {
            offer(&mut extract);
        }
        assert_eq!(
            source
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .pulled
                .len(),
            pulls
        );
    }

    /// A growing source withholds a key it does not hold yet: the release leaves it, and a row
    /// that arrives there later is the final one once the source closes.
    #[test]
    fn a_key_the_source_withheld_is_merged_by_a_later_consume() {
        let source = growing_source([0, 1, 2]);
        let mut extract = final_over(&source, None);
        extract.begin_run();
        extract.consume_in_pipeline(InputId::ONLY, keys_between(0, 5));
        assert!(
            !predicate(
                &source
                    .read()
                    .unwrap_or_else(PoisonError::into_inner)
                    .released[0]
            )
            .contains(&Value::UInt(3))
        );
        source
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .rows
            .insert(3, value(3));
        source
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .closed = true;
        extract.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        assert_eq!(offer(&mut extract), Some(value(3)));
    }

    /// A consume after the output was released pulls nothing: the source was released whole.
    #[test]
    fn a_consume_after_a_release_pulls_nothing() {
        let source = growing_source(0..4);
        let mut extract = final_over(&source, None);
        extract.begin_run();
        extract.consume_in_pipeline(InputId::ONLY, keys_between(0, 1));
        extract.release(int().universal_guard());
        let pulls = source
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .pulled
            .len();
        extract.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        assert_eq!(
            source
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .pulled
                .len(),
            pulls
        );
        assert_eq!(
            source.read().unwrap_or_else(PoisonError::into_inner).wasted,
            0
        );
    }

    /// An extraction placed in a pipeline answers a pull before its first consume with nothing and
    /// pulls its input nothing.
    #[test]
    fn a_consuming_extraction_pulled_before_its_first_consume_pulls_nothing() {
        let source = growing_source(0..4);
        let mut extract = final_over(&source, None);
        extract.begin_run();
        assert_eq!(scalar_of(&extract.get(int().universal_guard())), None);
        assert!(
            source
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .pulled
                .is_empty()
        );
    }

    /// The model of a run over a growing source: the keys answered, whether the output was
    /// released, and the source.
    struct Run {
        sut: ExtractFinalProducer,
        sut_source: Shared,
        input: InputModel,
        answered: BTreeSet<u64>,
        /// Whether the value is extracted: the source drained by a consume, after which the
        /// extraction reads no more.
        extracted: bool,
        released: bool,
        trace: String,
    }

    impl Run {
        fn new(initial: &[u64], trace: String) -> Self {
            let sut_source = growing_source(initial.iter().copied());
            Self {
                sut: {
                    let mut breaker = final_over(&sut_source, default_of(-1));
                    breaker.begin_run();
                    breaker
                },
                sut_source,
                input: InputModel::new(initial),
                answered: BTreeSet::new(),
                extracted: false,
                released: false,
                trace,
            }
        }

        fn apply(&mut self, step: Step) {
            self.trace.push_str(&format!(" {step:?}"));
            match step {
                Add(key) => {
                    if self.input.add(key) {
                        self.sut_source
                            .write()
                            .unwrap_or_else(PoisonError::into_inner)
                            .rows
                            .insert(key, value(key));
                    }
                }
                Close => {
                    self.input.closed = true;
                    self.sut_source
                        .write()
                        .unwrap_or_else(PoisonError::into_inner)
                        .closed = true;
                }
                Consume(region) => {
                    self.sut.consume_in_pipeline(InputId::ONLY, region.guard());
                    if self.released || self.extracted {
                        return;
                    }
                    self.answered.extend(self.input.pull(region).0);
                    self.extracted = self.input.drained();
                    // Short of extraction, the source is released below the greatest key
                    // answered, which reaches it again on every consume.
                    if !self.extracted
                        && let Some(&greatest) = self.answered.iter().max()
                        && greatest > 0
                    {
                        self.input.release(Keys(0, greatest - 1));
                    }
                }
                Release(_) => {
                    // A repeated release reaches the source again.
                    self.sut.release(int().universal_guard());
                    self.released = true;
                    self.input.release(All);
                }
            }
        }

        /// The value a drained source leaves: the greatest key answered, or the default.
        fn expected(&self) -> Option<i64> {
            match (self.released, self.extracted) {
                (true, _) | (_, false) => None,
                (false, true) => Some(self.answered.iter().max().map_or(-1, |key| value(*key))),
            }
        }

        fn check(&mut self) {
            let trace = self.trace.clone();
            self.input.check(&self.sut_source, &trace);
            assert_eq!(offer(&mut self.sut), self.expected(), "{trace}: the value");
            if self.input.drained() {
                let expected = match self.extracted && !self.released {
                    true => int().universal_guard(),
                    false => int().empty_guard(),
                };
                assert_eq!(self.sut.final_guard(), expected, "{trace}: final guard");
            }
        }

        fn run(steps: &[Step], initial: &[u64]) {
            let mut run = Run::new(initial, format!("initial {initial:?} steps"));
            for step in steps {
                run.apply(*step);
                run.check();
            }
            run.finish();
        }

        fn finish(&mut self) {
            if !self.input.closed {
                self.apply(Close);
            }
            self.apply(Consume(All));
            self.check();
            if self.released {
                return;
            }
            // An extraction that consumes the keys that were answered whole yields the same value.
            let twin_source = source(self.answered.iter().copied());
            let mut twin = final_over(&twin_source, default_of(-1));
            twin.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
            assert_eq!(
                scalar_of(&twin.read_in_pipeline(int().universal_guard())),
                offer(&mut self.sut),
                "{}: the answer of an extraction consumed whole",
                self.trace
            );
        }
    }

    #[test]
    fn enumerated_interleavings_keep_the_model() {
        let sequences: &[&[Step]] = &[
            &[
                Consume(Keys(6, 9)),
                Consume(Keys(0, 3)),
                Add(10),
                Consume(Keys(4, 11)),
            ],
            &[Consume(Keys(0, 3)), Add(3), Add(9), Close, Consume(All)],
            &[Add(11), Consume(Keys(0, 5)), Release(All), Consume(All)],
            &[
                Consume(Keys(8, 11)),
                Add(9),
                Consume(Keys(8, 11)),
                Consume(Keys(0, 7)),
            ],
            &[Close, Consume(All), Add(11), Consume(All)],
        ];
        for steps in sequences {
            Run::run(steps, &[0, 1, 2, 4, 5, 6]);
        }
    }

    #[test]
    fn random_interleavings_keep_the_model() {
        const SEED: u64 = 0xd1b5_4a32_d192_ed03;
        let mut rng = Rng(SEED);
        for iteration in 0..300 {
            let initial: Vec<u64> = (0..KEYS).filter(|_| rng.below(2) == 0).collect();
            let trace = format!("seed {SEED:#x} iteration {iteration} initial {initial:?} steps");
            let mut run = Run::new(&initial, trace);
            for _ in 0..12 {
                let step = rng.step_among(&run.answered);
                run.apply(step);
                run.check();
            }
            run.finish();
        }
    }
}
