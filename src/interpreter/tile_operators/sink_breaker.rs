//! A sink as a pipeline breaker, for the test-only `crate::interpreter::dispatcher::run_program`.
//! See `src/interpreter/design-operators.md`, "Running a compiled program".

use std::sync::Arc;

use super::*;
use crate::interpreter::DataSink;
use crate::interpreter::sinks::ProducerSlot;

/// The pipeline breaker of a sink: it consumes a package by pulling the sink's producer at the
/// package's guard, hands the answer to the sink, and releases the producer at what the answer
/// states, as a sink's pull in pull mode does at the universal guard. It holds nothing, and no
/// pipeline reads it.
///
/// A package's answer states only its own region complete, so it is terminal only where the
/// package is the producer's whole input. The sink is done once its producer is released whole
/// ([`input_released`]), however many packages that took, where pull mode is done at the first
/// terminal answer.
///
/// [`input_released`]: BreakingProducer::input_released
pub(crate) struct SinkBreaker {
    base: ProducerBase,
    producer: ProducerSlot,
    sink: Arc<dyn DataSink>,
}

impl SinkBreaker {
    /// The breaker of the sink that hands what it pulls of `producer`, which `subscribe` has
    /// filled, to `sink`.
    pub(crate) fn new(producer: ProducerSlot, sink: Arc<dyn DataSink>) -> Self {
        let tiling = Self::reading(&producer).tiling().clone();
        Self {
            base: ProducerBase::unowned(Self::alloc_id(), &tiling),
            producer,
            sink,
        }
    }

    fn input(producer: &ProducerSlot) -> std::cell::RefMut<'_, Box<dyn TileProducer>> {
        std::cell::RefMut::map(producer.borrow_mut(), |slot| {
            slot.as_mut()
                .expect("a sink's producer is filled once its output subscribed")
        })
    }

    fn reading(producer: &ProducerSlot) -> std::cell::Ref<'_, Box<dyn TileProducer>> {
        std::cell::Ref::map(producer.borrow(), |slot| {
            slot.as_ref()
                .expect("a sink's producer is filled once its output subscribed")
        })
    }
}

impl TileProducer for SinkBreaker {
    impl_producer_base!();

    fn get_impl(&mut self, _guard: TileGuard) -> Tile {
        unreachable!("no pipeline reads a sink, so nothing pulls its breaker")
    }

    fn release_impl(&mut self, _guard: TileGuard) {}
}

impl BreakingProducer for SinkBreaker {
    fn consume_impl(&mut self, guard: TileGuard) {
        let mut producer = Self::input(&self.producer);
        let tile = producer.get(guard);
        self.sink.process(&tile);
        producer.release(tile.to_guard());
    }

    fn input_tiling(&self) -> Tiling {
        self.tiling().clone()
    }

    fn input_released(&self) -> TileGuard {
        Self::reading(&self.producer).obsolete_guard().clone()
    }

    fn held(&self) -> TileGuard {
        self.tiling().empty_guard()
    }

    fn offer_impl(&mut self, _guard: TileGuard) -> Tile {
        unreachable!("no pipeline reads a sink, so nothing pulls its breaker")
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use super::*;
    use crate::interpreter::tile_operators::test_helpers::ProjectionSpy;
    use crate::interpreter::{BaseType, ColumnValue, Extent};

    /// A sink that counts the tiles it is handed.
    #[derive(Default)]
    struct Counting(AtomicUsize);

    impl DataSink for Counting {
        fn process(&self, _tile: &Tile) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }

    /// A sink breaker over a producer answering `tile`, and its sink.
    fn sink_over(tile: Tile) -> (SinkBreaker, Arc<Counting>) {
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let (spy, _, _) = ProjectionSpy::new(tile, tiling);
        let producer: ProducerSlot = Rc::new(RefCell::new(Some(Box::new(spy))));
        let sink = Arc::new(Counting::default());
        (SinkBreaker::new(producer, sink.clone()), sink)
    }

    /// A package reaches the sink as the producer's answer at its guard, and the producer is
    /// released at what the answer states.
    #[test]
    fn a_package_reaches_the_sink_and_releases_what_it_answered() {
        let (mut breaker, sink) = sink_over(Tile::Scalar(ColumnValue::Ints(vec![3])));
        breaker.consume_impl(breaker.input_tiling().universal_guard());
        assert_eq!(sink.0.load(Ordering::SeqCst), 1);
        assert!(breaker.input_released().is_universal());
        assert!(breaker.held().is_empty(), "a sink holds nothing");
    }

    /// A collection consumed in two packages is released whole only once both are consumed.
    #[test]
    fn a_collection_is_released_whole_once_every_package_is_consumed() {
        let tiling = Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let tile = Tile::data_function(
            ColumnValue::Ints(vec![1, 2]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20]))),
            Predicate::True,
            bit_set::BitSet::new(),
        );
        let (spy, _, _) = ProjectionSpy::new(tile, tiling);
        let producer: ProducerSlot = Rc::new(RefCell::new(Some(Box::new(spy))));
        let sink = Arc::new(Counting::default());
        let mut breaker = SinkBreaker::new(producer, sink.clone());
        let one = Predicate::from_column_value(&ColumnValue::Ints(vec![1]));
        let domain = |keys: Predicate| TileGuard::Function(FunctionGuard::Domain(keys));
        breaker.consume_impl(domain(one.clone()));
        assert!(
            !breaker.input_released().is_universal(),
            "one package of two"
        );
        breaker.consume_impl(domain(Predicate::True.minus(&one)));
        assert!(breaker.input_released().is_universal(), "both packages");
        assert_eq!(sink.0.load(Ordering::SeqCst), 2);
    }

    /// An answer that states nothing complete releases nothing, so the sink is not done.
    #[test]
    fn an_answer_stating_nothing_releases_nothing() {
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let (mut breaker, sink) = sink_over(tiling.empty_tile());
        breaker.consume_impl(breaker.input_tiling().universal_guard());
        assert_eq!(sink.0.load(Ordering::SeqCst), 1);
        assert!(!breaker.input_released().is_universal());
    }
}
