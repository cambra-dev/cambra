use super::*;
use crate::interpreter::operator_graph::value;
use crate::{
    interpreter::{ColumnValue, Consumer, Scheduler, Value},
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
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Only source notifications reach the consumer. The default is subscribed eagerly
        // but pulled only after a terminal source has no live positions.
        let source_producer =
            self.source
                .subscribe(self.source.tiling().universal_guard(), consumer, scheduler);
        let default_producer = self
            .default
            .as_mut()
            .map(|d| d.subscribe(d.tiling().universal_guard(), Box::new(|| {}), scheduler));
        Box::new(ExtractFinalProducer {
            base: ProducerBase::new(
                ExtractFinalProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            source: source_producer,
            default: default_producer,
            final_tile: None,
            released: false,
        })
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

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        let node = node.child("source", self.source.inspect(opts));
        match &self.default {
            Some(d) => node.child("default", d.inspect(opts)),
            None => node.annotate("total (no default)".to_string()),
        }
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // Scalar columns use the declared extent, retaining variant arms absent from the
        // selected value so downstream merges see the declared layout.
        let extent = self.tiling().extent();
        let empty = self.tiling().empty_tile();
        if self.released {
            return empty;
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
            let tile = if codomain.is_data_function() {
                // Keeping one row leaves that key's group standing alone, which is the
                // value at this position. The source is terminal and this is its last
                // position, so what it holds is the whole collection.
                let mut sub = *codomain;
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
                let cv = scalar_tile_to_column_value(*codomain);
                column_value_to_tile(
                    ColumnValue::from_values(vec![cv.index_at(final_idx)], &extent),
                    self.tiling(),
                )
            };
            self.final_tile = Some(tile.clone());
            return tile;
        }
        // No live positions remain. Cache the default only once it is complete.
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
                return empty;
            }
            default.release(default_tiling.universal_guard());
            self.final_tile = Some(default_tile.clone());
            return default_tile;
        }
        match scalar_tile_to_column_value(default_tile).as_single() {
            Some(value) => {
                default.release(default_tiling.universal_guard());
                let tile = Tile::Scalar(ColumnValue::from_values(vec![value], &extent));
                self.final_tile = Some(tile.clone());
                tile
            }
            // A subsequent pull can retry an incomplete default.
            None => empty,
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            self.released = true;
            self.source.release(self.source.tiling().universal_guard());
            if let Some(d) = self.default.as_mut() {
                d.release(d.tiling().universal_guard());
            }
        }
    }
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
            _scheduler: &mut Scheduler,
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
            _scheduler: &mut Scheduler,
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
            _scheduler: &mut Scheduler,
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
            &mut Scheduler::new(),
        );
        assert!(!producer.get(guard.clone()).is_terminal());

        ready.set(true);
        consumer.borrow_mut().as_mut().unwrap().notify();
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

    /// BUG: universal release should clear the cached tile, but it retains one scalar cell.
    /// Both source and fallback results remain held even though later pulls emit nothing.
    #[test]
    fn bug_universal_release_retains_the_cached_final_value() {
        for use_default in [false, true] {
            let source = if use_default {
                int_source(vec![], vec![])
            } else {
                int_source(vec![0], vec![42])
            };
            let default = Constant::new(Value::Int(42), Extent::Base(BaseType::Int));
            let mut op = ExtractFinal::new(Box::new(source), Box::new(default));
            let guard = op.tiling().universal_guard();
            let mut producer = op.subscribe(guard.clone(), Box::new(|| {}), &mut Scheduler::new());
            assert!(producer.get(guard.clone()).is_terminal());
            assert!(producer.state_info().values > 0);
            producer.release(guard.clone());
            assert_eq!(
                producer.state_info().values,
                1,
                "bug pin: released cache remains held"
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
        let mut producer = op.subscribe(guard.clone(), Box::new(|| {}), &mut Scheduler::new());
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
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());
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
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());
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
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());

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
