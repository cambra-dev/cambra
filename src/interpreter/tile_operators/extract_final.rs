use super::*;
use crate::interpreter::operator_graph::value;
use crate::{
    interpreter::{ColumnValue, Consumer, Projection, SubscribeContext, Value},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

/// Extracts the last live position's value once a collection is terminal.
///
/// The output has the source's codomain tiling, including collection-valued codomains.
/// See `src/interpreter/design-operators.md`, "Final-value extraction", for ordering, fallback,
/// and release. Induction histories use
/// [`StoreFinalRead`](crate::interpreter::commit_operator::StoreFinalRead) instead.
pub struct ExtractFinal {
    /// Operator producing the `DataFunction` tiling to extract from.
    source: Box<dyn TileOperator>,
    /// Fallback for a terminal source with no live positions. Its extent must be included
    /// in the source codomain. `None` requires a source that cannot finish empty.
    default: Option<Box<dyn TileOperator>>,
    /// Output tiling — what one position of the source holds.
    base: OperatorBase,
}

impl ExtractFinal {
    /// Extract from a collection, using `default` if it finishes without a live position.
    ///
    /// Panics if `source` is not a collection. Debug-asserts that its codomain extent includes
    /// the default's extent. The output has the source's codomain tiling.
    pub fn new(source: Box<dyn TileOperator>, default: Box<dyn TileOperator>) -> Self {
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
    pub fn without_default(source: Box<dyn TileOperator>) -> Self {
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
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("source", &*self.source));
        if let Some(default) = &self.default {
            visit(value("default", &**default));
        }
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        let input = BreakerInput::new(consumer, self.source.tiling(), false, cx);
        // Only source notifications reach the consumer. The default is subscribed eagerly
        // but pulled only after a terminal source has no live positions.
        let source_producer =
            self.source
                .subscribe(self.source.tiling().universal_guard(), input.consumer, cx);
        let default_producer = self
            .default
            .as_mut()
            .map(|d| d.subscribe(d.tiling().universal_guard(), Box::new(|| {}), cx));
        Box::new(ExtractFinalProducer::new(
            ProducerBase::new(
                ExtractFinalProducer::alloc_id(),
                self.tiling(),
                &self.base,
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
    /// Cached result, re-emitted until release. May remain absent after source completion
    /// while waiting for the default. Collection-valued results retain a whole sub-tile.
    final_tile: Option<Tile>,
    /// Suppresses subsequent emissions after universal release.
    released: bool,
    /// The source rows [`Breaker::consume_impl`] merged, kept to the row at the
    /// greatest key where the values are a column, and empty before the first consume.
    merged: Tile,
    /// Whether the extraction is in consuming mode for the run
    /// ([`Breaker::enter_consuming_mode`]): it then answers from `final_tile`, and only
    /// `consume_impl` pulls its source and its default.
    consuming: bool,
}

/// The final value of `source`, falling back to `default`, that nothing subscribed, answering at
/// `tiling`, for a test that builds a chain of pipelines by hand.
#[cfg(test)]
pub(crate) fn extract_final_of(
    source: Box<dyn TileProducer>,
    default: Option<Box<dyn TileProducer>>,
    tiling: &Tiling,
) -> crate::interpreter::dispatcher::BreakerHandle {
    Rc::new(RefCell::new(ExtractFinalProducer::new(
        ProducerBase::unowned(ExtractFinalProducer::alloc_id(), tiling),
        source,
        default,
    )))
}

impl ExtractFinalProducer {
    fn new(
        base: ProducerBase,
        source: Box<dyn TileProducer>,
        default: Option<Box<dyn TileProducer>>,
    ) -> Self {
        let merged = source.tiling().empty_tile();
        Self {
            base,
            source,
            default,
            final_tile: None,
            released: false,
            merged,
            consuming: false,
        }
    }

    /// The value at row `final_idx` of a source whose keys are `domain`: the position being
    /// indexed is this collection's key, and what it holds is everything below it, a value where
    /// the values are a column and a whole collection where they are one.
    fn value_at(&self, domain: &ColumnValue, codomain: Tile, final_idx: usize) -> Tile {
        let extent = self.tiling().extent();
        if codomain.is_data_function() {
            // Keeping one row leaves that key's group standing alone, which is the
            // value at this position. The source is terminal and this is its last
            // position, so what it holds is the whole collection.
            let mut sub = codomain;
            sub.retain_rows(
                &(0..domain.len())
                    .map(|i| i == final_idx)
                    .collect::<Vec<bool>>(),
            );
            let Tile::DataFunction {
                domain_predicate, ..
            } = &mut sub
            else {
                unreachable!("retain keeps a collection a collection")
            };
            *domain_predicate = Predicate::True;
            sub
        } else {
            // Built at the *declared* extent: a tag `match` collapses its arms to their
            // join, and the arm that answers carries only its own tag. Laid out as this
            // operator's tiling, which keeps a product a record of columns.
            let cv = scalar_tile_to_column_value(codomain);
            column_value_to_tile(
                ColumnValue::from_values(vec![cv.index_at(final_idx)], &extent),
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
    fn pull_default(&mut self) -> Option<Tile> {
        let extent = self.tiling().extent();
        let yields_a_level = self.tiling().is_data_function();
        let Some(default) = self.default.as_mut() else {
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
    fn state_info(&self) -> ProducerStateInfo {
        ProducerStateInfo::holding(self.final_tile.as_ref().map_or(0, Tile::cell_count))
    }

    impl_producer_base!();

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

    /// The final position of a stream is one value, or one collection that a release takes
    /// whole, so the projection is all of it or none: the source is read whole whatever the
    /// consumer asks, because the last position is not known before the stream ends.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        if projection_of_one_value(&self.name(), "extracts one final value", &projection_guard)
            == Projection::Nothing
        {
            return self.tiling().empty_tile();
        }
        // Scalar columns use the declared extent, retaining variant arms absent from the
        // selected value so downstream merges see the declared layout.
        let empty = self.tiling().empty_tile();
        if self.released {
            return empty;
        }
        if self.consuming {
            return self.offer_impl(projection_guard);
        }
        if let Some(tile) = &self.final_tile {
            return tile.clone();
        }
        let source_tiling = self.source.tiling().clone();
        let source_tile = self.source.get(source_tiling.universal_guard());
        if !source_tile.is_terminal() {
            // Release UInt positions below the highest live position without waiting for
            // completion. Retain that position because it can still supply the final value.
            if let Some(keys) = source_tile.live_keys() {
                let max_pos = keys
                    .filter_map(|(_, key)| match key {
                        Value::UInt(p) => Some(p),
                        _ => None,
                    })
                    .max();
                if let Some(max_pos) = max_pos
                    && max_pos >= 1
                {
                    self.source
                        .release(TileGuard::Function(FunctionGuard::Domain(
                            Predicate::at_or_below(Value::UInt(max_pos - 1)),
                        )));
                }
            }
            return empty;
        }
        // Release the completed source before selecting its final value or pulling the default.
        self.source.release(source_tiling.universal_guard());
        let Tile::DataFunction {
            domain,
            codomain,
            deleted,
            ..
        } = source_tile
        else {
            panic!("ExtractFinal source must be a collection tile");
        };
        // The position being indexed is this collection's key, and what it holds is
        // everything below it: a value where the values are a column, a whole collection
        // where they are one.
        // TODO don't assume sorting; we need to sort by the key value instead.
        let live_outer = (0..domain.len()).rev().find(|i| !deleted.contains(*i));
        if let Some(final_idx) = live_outer {
            let tile = self.value_at(&domain, *codomain, final_idx);
            self.final_tile = Some(tile.clone());
            return tile;
        }
        // No live positions remain. Cache the default only once it is complete.
        match self.pull_default() {
            Some(tile) => {
                self.final_tile = Some(tile.clone());
                tile
            }
            None => empty,
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            self.released = true;
            self.final_tile = None;
            self.merged = self.source.tiling().empty_tile();
            self.source.release(self.source.tiling().universal_guard());
            if let Some(d) = self.default.as_mut() {
                d.release(d.tiling().universal_guard());
            }
        }
    }
}

impl Breaker for ExtractFinalProducer {
    fn enter_consuming_mode(&mut self) {
        self.consuming = true;
    }

    /// Merges the source rows it answers at `guard`, a guard of the source's tiling, keeps the
    /// row at the greatest key, and releases the source at what the answer stated. Rows merge in
    /// the order they arrive, so the last row is not the final one: the key says which is. Once
    /// the source has been released whole the value is extracted, or the default read when the
    /// source held nothing.
    fn consume_impl(&mut self, _: InputId, guard: TileGuard) {
        debug_assert!(
            guard.check_from(self.source.tiling()),
            "{} consumes a guard of its source's tiling: {guard:?}",
            self.name()
        );
        debug_assert!(
            self.consuming,
            "{} consumes once a dispatched run has put it in consuming mode",
            self.name()
        );
        if self.released || self.final_tile.is_some() || guard.is_empty() {
            return;
        }
        let mut answered = self.source.get(guard);
        let upstream_guard = answered.to_guard();
        answered.compact();
        self.merged.merge(answered);
        self.keep_greatest_key();
        self.source.release(upstream_guard);
        if !self.source.obsolete_guard().is_universal() {
            return;
        }
        let Tile::DataFunction {
            domain,
            codomain,
            deleted,
            ..
        } = &self.merged
        else {
            panic!("ExtractFinal source must be a collection tile");
        };
        self.final_tile = match greatest_live_key(domain, deleted) {
            Some(final_idx) => Some(self.value_at(domain, (**codomain).clone(), final_idx)),
            None => self.pull_default(),
        };
    }

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
    /// When `last` and the output is unreleased and no value has been extracted: the source has
    /// not been released whole, or the default it fell back to has not converged. A dispatcher
    /// issues no `consume_impl` after the last epoch, so nothing would read that default again,
    /// and pushing nothing would leave the reader with no value.
    fn finish(&mut self, pushes: &mut Pushes<'_>, last: bool) {
        assert!(
            !last || self.released || self.final_tile.is_some(),
            "{} finishes after it extracted its value: the source released whole and any \
             default it fell back to converged",
            self.name()
        );
        pushes.push_final(self);
    }

    fn as_producer(&self) -> Option<&dyn BreakingProducer> {
        Some(self)
    }
}

impl BreakingProducer for ExtractFinalProducer {
    /// The extracted value, once there is one: none while the source has not drained, or while a
    /// default it fell back to has not converged. The next `consume_impl` reads the default again.
    fn held(&self) -> TileGuard {
        match self.final_tile {
            Some(_) => self.tiling().universal_guard(),
            None => self.tiling().empty_guard(),
        }
    }

    fn offer_impl(&mut self, guard: TileGuard) -> Tile {
        match guard.projection(&self.name()) {
            Projection::Nothing => self.tiling().empty_tile(),
            _ => self
                .final_tile
                .clone()
                .unwrap_or_else(|| self.tiling().empty_tile()),
        }
    }
}

impl ExtractFinalProducer {
    /// Drop every merged row but the one at the greatest key, which is the only one an
    /// extraction can still need, where the values are a column of scalars. Any other shape of
    /// value keeps every merged row.
    fn keep_greatest_key(&mut self) {
        let Tile::DataFunction {
            domain,
            codomain,
            deleted,
            ..
        } = &self.merged
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
        } = &self.merged
        else {
            return;
        };
        self.merged = Tile::data_function(
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
    use std::cell::{Cell, RefCell};
    use std::rc::Rc;

    use super::*;
    use crate::interpreter::tile_operators::{FunctionGuard, Predicate};
    use crate::interpreter::{BaseType, Extent};

    /// A non-terminal `DataFunction` source with domain `[0, 1, 2]`, recording
    /// every domain-release watermark it receives. Never becomes terminal, so it
    /// exercises `ExtractFinal`'s incremental (pre-terminal) release path.
    struct PartialSource {
        tiling: Tiling,
        releases: Rc<RefCell<Vec<u64>>>,
    }

    struct PartialSourceProducer {
        base: ProducerBase,
        releases: Rc<RefCell<Vec<u64>>>,
    }

    impl TileOperator for PartialSource {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            &mut self,
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
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            Tile::data_function(
                ColumnValue::from_uints(vec![0, 1, 2]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30]))),
                Predicate::False,
                bit_set::BitSet::new(),
            )
        }
        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            if let TileGuard::Function(FunctionGuard::Domain(released)) = &obsolete_guard
                && let Some(Value::UInt(w)) = released.as_at_or_below()
            {
                self.releases.borrow_mut().push(w);
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
            &mut self,
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
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            Tile::data_function(
                self.domain.clone(),
                Box::new(Tile::Scalar(self.codomain_tile.clone())),
                Predicate::True,
                bit_set::BitSet::new(),
            )
        }
        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
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
        ready: Rc<Cell<bool>>,
        consumer: Rc<RefCell<Option<Box<dyn Consumer>>>>,
    }

    struct DelayedDefaultProducer {
        base: ProducerBase,
        ready: Rc<Cell<bool>>,
    }

    impl TileOperator for DelayedDefault {
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            consumer: Box<dyn Consumer>,
            _cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            *self.consumer.borrow_mut() = Some(consumer);
            Box::new(DelayedDefaultProducer {
                base: ProducerBase::unowned(DelayedDefaultProducer::alloc_id(), &self.tiling),
                ready: self.ready.clone(),
            })
        }
    }

    impl TileProducer for DelayedDefaultProducer {
        impl_producer_base!();
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            if self.ready.get() {
                Tile::Scalar(ColumnValue::Ints(vec![42]))
            } else {
                self.tiling().empty_tile()
            }
        }
        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
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
    /// is discarded. A debug probe rejects the unnotified change; without assertions, Memo
    /// keeps returning an empty result. Convert this pin when repaired.
    #[test]
    #[cfg_attr(debug_assertions, should_panic(expected = "changed without notifying"))]
    fn bug_delayed_default_does_not_wake_a_memoized_consumer() {
        let ready = Rc::new(Cell::new(false));
        let consumer = Rc::new(RefCell::new(None));
        let default = DelayedDefault {
            tiling: Tiling::Scalar(Extent::Base(BaseType::Int)),
            ready: ready.clone(),
            consumer: consumer.clone(),
        };
        let extract = ExtractFinal::new(Box::new(int_source(vec![], vec![])), Box::new(default));
        // Memo will not retry an incomplete upstream unless it receives a notification.
        let mut op = Memo::new(Box::new(extract));
        let guard = op.tiling().universal_guard();
        let notifications = Rc::new(Cell::new(0));
        let observed = notifications.clone();
        let mut producer = op.subscribe(
            guard.clone(),
            Box::new(move || observed.set(observed.get() + 1)),
            &mut SubscribeContext::new(),
        );
        assert!(!producer.get(guard.clone()).is_terminal());

        ready.set(true);
        consumer
            .borrow_mut()
            .as_mut()
            .unwrap()
            .notify(&Projection::Everything);
        assert_eq!(notifications.get(), 0, "bug pin: the fallback wake is lost");
        let Tile::Scalar(result) = producer.get(guard) else {
            panic!("expected a scalar fallback");
        };
        assert_eq!(
            result.as_single(),
            None,
            "bug pin: Memo never retries extraction"
        );
    }

    /// A universal release drops the cached final value, from the source or from the fallback,
    /// and a later pull emits nothing.
    #[test]
    fn a_universal_release_drops_the_cached_final_value() {
        for use_default in [false, true] {
            let source = if use_default {
                int_source(vec![], vec![])
            } else {
                int_source(vec![0], vec![42])
            };
            let default = Constant::new(Value::Int(42), Extent::Base(BaseType::Int));
            let mut op = ExtractFinal::new(Box::new(source), Box::new(default));
            let guard = op.tiling().universal_guard();
            let mut producer =
                op.subscribe(guard.clone(), Box::new(|| {}), &mut SubscribeContext::new());
            assert!(producer.get(guard.clone()).is_terminal());
            assert!(producer.state_info().values > 0);
            producer.release(guard.clone());
            assert_eq!(
                producer.state_info().values,
                0,
                "a released cache holds nothing"
            );
            assert_eq!(producer.get(guard).cell_count(), 0);
        }
    }

    /// BUG: terminal extraction selects the last row instead of the greatest live key.
    /// Pin the current result until the ordering policy is fixed; the value at key 2 is 20.
    #[test]
    fn bug_unsorted_final_selection_uses_row_order() {
        let mut op =
            ExtractFinal::without_default(Box::new(int_source(vec![2, 0, 1], vec![20, 0, 10])));
        let guard = op.tiling().universal_guard();
        let mut producer =
            op.subscribe(guard.clone(), Box::new(|| {}), &mut SubscribeContext::new());
        let Tile::Scalar(result) = producer.get(guard) else {
            panic!("expected a scalar final value");
        };
        assert_eq!(result.as_single(), Some(Value::Int(10)));
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
        let mut op = ExtractFinal::new(Box::new(source), Box::new(default));
        let guard = op.tiling().universal_guard();
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut SubscribeContext::new());
        let tile = producer.get(producer.tiling().universal_guard());

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
        let mut op = ExtractFinal::new(Box::new(source), Box::new(default));
        let guard = op.tiling().universal_guard();
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut SubscribeContext::new());
        let tile = producer.get(producer.tiling().universal_guard());

        let Tile::Scalar(cv) = tile else {
            panic!("expected a scalar tile");
        };
        assert_eq!(
            arm_occupancy(&cv),
            vec![("neg".to_string(), 1), ("pos".to_string(), 0)],
        );
        assert_eq!(cv.as_single(), Some(union_value("neg", Value::Int(7))));
    }

    /// On a non-terminal pull, `ExtractFinal` needs only the highest-domain value,
    /// so it releases everything below it — `[0, max)`. Over a source with domain
    /// `[0, 1, 2]`, it forwards a release `≤ 1`, freeing the prefix that a
    /// never-terminating scalar-final loop would otherwise pin.
    #[test]
    fn extract_final_releases_below_the_running_max() {
        let value_tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let releases = Rc::new(RefCell::new(Vec::<u64>::new()));
        let source = PartialSource {
            tiling: Tiling::data_function(Extent::Base(BaseType::UInt), value_tiling.clone()),
            releases: releases.clone(),
        };
        let default = Constant::new(Value::Int(0), Extent::Base(BaseType::Int));
        let mut op = ExtractFinal::new(Box::new(source), Box::new(default));
        let guard = op.tiling().universal_guard();
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut SubscribeContext::new());

        // Non-terminal source → ExtractFinal emits empty but releases `[0, max)`.
        let tile = producer.get(producer.tiling().universal_guard());
        assert!(
            !tile.is_terminal(),
            "a non-terminal source stays non-terminal"
        );
        assert_eq!(
            releases.borrow().last().copied(),
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
    fn final_of_finished_stream() -> (Box<dyn TileProducer>, GuardLog) {
        let int = || Extent::Base(BaseType::Int);
        let tiling = Tiling::data_function(Extent::uint_range(3), Tiling::Scalar(int()));
        let finished = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1, 2]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30]))),
            Predicate::True,
            bit_set::BitSet::new(),
        );
        let (stream, pulled, _) = ProjectionSpyOp::new(finished, tiling);
        let mut op = ExtractFinal::new(
            Box::new(stream),
            Box::new(Constant::new(Value::Int(0), int())),
        );
        let guard = op.tiling().universal_guard();
        let producer = op.subscribe(guard, Box::new(|| {}), &mut SubscribeContext::new());
        (producer, pulled)
    }

    /// The last position is not known before the stream ends, so the source is read whole.
    #[test]
    fn the_stream_is_read_whole_to_find_its_last_position() {
        let (mut last, pulled) = final_of_finished_stream();
        let tile = last.get(last.tiling().universal_guard());
        assert_eq!(tile, Tile::Scalar(ColumnValue::Ints(vec![30])));
        assert_eq!(pulled.borrow().len(), 1);
        assert!(pulled.borrow()[0].is_universal());
    }

    #[test]
    fn asking_for_nothing_reads_nothing() {
        let (mut last, pulled) = final_of_finished_stream();
        let tile = last.get(last.tiling().empty_guard());
        assert_eq!(tile, last.tiling().empty_tile());
        assert!(pulled.borrow().is_empty());
    }

    #[test]
    #[should_panic(expected = "extracts one final value")]
    fn a_key_projection_is_rejected() {
        let (mut last, _) = final_of_finished_stream();
        last.get(keys_between(0, 1));
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
    use Step::{Add, Close, Consume, Notify, Release};

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
        extract.enter_consuming_mode();
        extract.consume_impl(InputId::ONLY, keys_between(8, 11));
        assert_eq!(
            offer(&mut extract),
            None,
            "the source has not stated everything complete"
        );
        // The rows below arrive after the row at key 11, which stays final.
        extract.consume_impl(InputId::ONLY, ints().universal_guard());
        assert_eq!(offer(&mut extract), Some(value(11)));
        assert_eq!(source.borrow().pulled.len(), 2);
    }

    /// Out-of-order morsels that end below the key a first morsel held leave that key final.
    #[test]
    fn a_later_morsel_with_smaller_keys_does_not_replace_the_final_row() {
        let source = source([1, 2, 9, 10]);
        let mut extract = final_over(&source, None);
        extract.enter_consuming_mode();
        extract.consume_impl(InputId::ONLY, keys_between(9, 11));
        extract.consume_impl(InputId::ONLY, keys_between(0, 3));
        extract.consume_impl(InputId::ONLY, ints().universal_guard());
        assert_eq!(offer(&mut extract), Some(value(10)));
    }

    /// A region is pulled and released once, and a partial source yields no value.
    #[test]
    fn a_region_is_pulled_and_released_and_yields_no_value_yet() {
        let source = source(0..10);
        let mut extract = final_over(&source, None);
        extract.enter_consuming_mode();
        extract.consume_impl(InputId::ONLY, keys_between(2, 5));
        assert_eq!(source.borrow().pulled, vec![keys_between(2, 5)]);
        assert_eq!(source.borrow().released, vec![keys_between(2, 5)]);
        assert_eq!(offer(&mut extract), None);
        extract.consume_impl(InputId::ONLY, keys_between(7, 9));
        extract.consume_impl(InputId::ONLY, keys_between(4, 8));
        assert_eq!(
            source.borrow().released,
            vec![keys_between(2, 5), keys_between(7, 9), keys_between(4, 8)]
        );
    }

    #[test]
    fn nothing_consumed_pulls_nothing() {
        let source = source(0..10);
        let mut extract = final_over(&source, None);
        extract.enter_consuming_mode();
        extract.consume_impl(InputId::ONLY, ints().empty_guard());
        assert!(source.borrow().pulled.is_empty());
    }

    /// An empty source that has drained falls back to the default, read once.
    #[test]
    fn an_empty_drained_source_yields_the_default() {
        let source = source([]);
        let mut extract = final_over(&source, default_of(7));
        extract.enter_consuming_mode();
        extract.consume_impl(InputId::ONLY, ints().universal_guard());
        assert_eq!(offer(&mut extract), Some(7));
        assert_eq!(extract.final_guard(), int().universal_guard());
    }

    /// A default that has not converged when the source drains leaves nothing held; the next
    /// consume reads it again, as every pull does in pull mode.
    #[test]
    fn an_unconverged_default_is_read_again_by_the_next_consume() {
        let source = source([]);
        let (default, cell) = ScriptedProducer::new(Tile::Scalar(ColumnValue::Ints(vec![])), int());
        let mut extract = final_over(&source, Some(Box::new(default)));
        extract.enter_consuming_mode();
        extract.consume_impl(InputId::ONLY, ints().universal_guard());
        assert_eq!(offer(&mut extract), None, "the default has not converged");
        assert_eq!(
            extract.final_guard(),
            int().empty_guard(),
            "nothing is held yet"
        );

        *cell.borrow_mut() = Tile::Scalar(ColumnValue::Ints(vec![7]));
        extract.consume_impl(InputId::ONLY, ints().universal_guard());
        assert_eq!(offer(&mut extract), Some(7));
        assert_eq!(extract.final_guard(), int().universal_guard());
    }

    /// An epoch before the last finishes with no value extracted yet: a later epoch's consume may
    /// still extract it.
    #[test]
    fn an_epoch_before_the_last_finishes_without_a_value() {
        let source = source([]);
        let (default, _) = ScriptedProducer::new(Tile::Scalar(ColumnValue::Ints(vec![])), int());
        let mut extract = final_over(&source, Some(Box::new(default)));
        extract.enter_consuming_mode();
        extract.consume_impl(InputId::ONLY, ints().universal_guard());
        push_to(&mut extract, &[1]);
        let dispatcher = Dispatcher::new(vec![vec![], vec![0]], usize::MAX);
        let mut pushes = dispatcher.pushes(PipelineId(0));
        extract.finish(&mut pushes, false);
        dispatcher.land(pushes);
        assert!(dispatcher.pop().is_none(), "nothing to push");
    }

    /// A default that has not converged by the last epoch's `finish` is never read again: the
    /// dispatcher issues no later `consume_impl`.
    #[test]
    #[should_panic(expected = "finishes after it extracted its value")]
    fn finish_with_an_unconverged_default_panics() {
        let source = source([]);
        let (default, _) = ScriptedProducer::new(Tile::Scalar(ColumnValue::Ints(vec![])), int());
        let mut extract = final_over(&source, Some(Box::new(default)));
        extract.enter_consuming_mode();
        extract.consume_impl(InputId::ONLY, ints().universal_guard());
        extract.finish(
            &mut Dispatcher::new(vec![vec![]], usize::MAX).pushes(PipelineId(0)),
            true,
        );
    }

    /// An output released before the value was extracted pushes nothing, and that is no error.
    #[test]
    fn finish_after_the_output_was_released_pushes_nothing() {
        let source = growing_source(0..4);
        let mut extract = final_over(&source, None);
        extract.enter_consuming_mode();
        extract.consume_impl(InputId::ONLY, keys_between(0, 1));
        extract.release(int().universal_guard());
        push_to(&mut extract, &[1]);
        let dispatcher = Dispatcher::new(vec![vec![], vec![0]], usize::MAX);
        dispatcher.finish_by_hand(PipelineId(0), |pushes| extract.finish(pushes, true));
        assert!(dispatcher.pop().is_none());
    }

    /// A total source that is empty is an invariant violation, as in pull mode.
    #[test]
    #[should_panic(expected = "declared total emitted no value")]
    fn an_empty_total_source_fails_loudly() {
        let source = source([]);
        let mut extract = final_over(&source, None);
        extract.enter_consuming_mode();
        extract.consume_impl(InputId::ONLY, ints().universal_guard());
    }

    #[test]
    fn final_guard_holds_the_value_until_it_is_released() {
        let source = source(0..4);
        let mut extract = final_over(&source, None);
        extract.enter_consuming_mode();
        extract.consume_impl(InputId::ONLY, ints().universal_guard());
        assert_eq!(extract.final_guard(), int().universal_guard());
        extract.release(int().universal_guard());
        assert_eq!(extract.final_guard(), int().empty_guard());
        assert_eq!(offer(&mut extract), None);
    }

    #[test]
    fn a_consuming_extraction_offers_without_pulling() {
        let source = source(0..10);
        let mut extract = final_over(&source, None);
        extract.enter_consuming_mode();
        extract.consume_impl(InputId::ONLY, ints().universal_guard());
        let pulls = source.borrow().pulled.len();
        for _ in 0..3 {
            offer(&mut extract);
        }
        assert_eq!(source.borrow().pulled.len(), pulls);
    }

    /// A growing source withholds a key it does not hold yet: the release leaves it, and a row
    /// that arrives there later is the final one once the source closes.
    #[test]
    fn a_key_the_source_withheld_is_merged_by_a_later_consume() {
        let source = growing_source([0, 1, 2]);
        let mut extract = final_over(&source, None);
        extract.enter_consuming_mode();
        extract.consume_impl(InputId::ONLY, keys_between(0, 5));
        assert!(!predicate(&source.borrow().released[0]).contains(&Value::UInt(3)));
        source.borrow_mut().rows.insert(3, value(3));
        source.borrow_mut().closed = true;
        extract.consume_impl(InputId::ONLY, ints().universal_guard());
        assert_eq!(offer(&mut extract), Some(value(3)));
    }

    /// A consume after the output was released pulls nothing: the source was released whole.
    #[test]
    fn a_consume_after_a_release_pulls_nothing() {
        let source = growing_source(0..4);
        let mut extract = final_over(&source, None);
        extract.enter_consuming_mode();
        extract.consume_impl(InputId::ONLY, keys_between(0, 1));
        extract.release(int().universal_guard());
        let pulls = source.borrow().pulled.len();
        extract.consume_impl(InputId::ONLY, ints().universal_guard());
        assert_eq!(source.borrow().pulled.len(), pulls);
        assert_eq!(source.borrow().wasted, 0);
    }

    /// An extraction in consuming mode answers a pull before its first consume with nothing and
    /// pulls its input nothing.
    #[test]
    fn a_consuming_extraction_pulled_before_its_first_consume_pulls_nothing() {
        let source = growing_source(0..4);
        let mut extract = final_over(&source, None);
        extract.enter_consuming_mode();
        assert_eq!(scalar_of(&extract.get(int().universal_guard())), None);
        assert!(source.borrow().pulled.is_empty());
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
                    breaker.enter_consuming_mode();
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
                        self.sut_source.borrow_mut().rows.insert(key, value(key));
                    }
                }
                Close => {
                    self.input.closed = true;
                    self.sut_source.borrow_mut().closed = true;
                }
                Notify(_) => unreachable!("an extraction listens to no region"),
                Consume(region) => {
                    self.sut.consume_impl(InputId::ONLY, region.guard());
                    if self.released || self.extracted {
                        return;
                    }
                    self.answered.extend(self.input.pull(region).0);
                    self.extracted = self.input.drained();
                }
                Release(_) => {
                    self.sut.release(int().universal_guard());
                    if !self.released {
                        self.released = true;
                        self.input.release(All);
                    }
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
            // An extraction in pull mode over the keys that were answered yields the same value.
            let twin_source = source(self.answered.iter().copied());
            let mut twin = final_over(&twin_source, default_of(-1));
            assert_eq!(
                scalar_of(&twin.get(int().universal_guard())),
                offer(&mut self.sut),
                "{}: the answer in pull mode",
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
                let step = rng.step_among(&run.answered, false);
                run.apply(step);
                run.check();
            }
            run.finish();
        }
    }
}
