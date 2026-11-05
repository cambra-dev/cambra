//! A sink as a pipeline breaker, for `crate::interpreter::dispatcher::run_program`.
//! See `src/interpreter/design-operators.md`, "Running a compiled program".

use std::sync::Arc;

use super::*;
use crate::interpreter::DataSink;
use crate::interpreter::sinks::ProducerSlot;

/// The pipeline breaker of a sink or a `main` output: it consumes a package by pulling the
/// producer at the package's guard and releasing it at what the answer states, as a sink's pull
/// in pull mode does at the universal guard, and hands the answers to the sink ([`Hands`]). No
/// pipeline reads it, so it is no producer: it offers nothing and pushes nothing.
///
/// A package's answer states only its own region complete, so it is terminal only where the
/// package is the producer's whole input. The sink is done once its producer is released whole
/// ([`input_released`]), however many packages that took, where pull mode is done at the first
/// terminal answer.
///
/// [`input_released`]: Breaker::input_released
pub(crate) struct SinkBreaker {
    producer: ProducerSlot,
    sink: Arc<dyn DataSink>,
    hands: Hands,
    /// Whether a `main` output hands each package's answer as it consumes it
    /// ([`unsealed`](Self::unsealed)).
    unsealed: bool,
    /// Whether an answer handed so far was terminal.
    handed_terminal: bool,
}

/// When a [`SinkBreaker`] hands its sink what it pulled.
enum Hands {
    /// Each package's answer, as the package is consumed: a sink output's breaker.
    EachPackage,
    /// One answer per epoch, at the epoch's finish: the answers of the epoch's packages merged
    /// with a pull of the producer at the universal guard, which states what the producer states
    /// complete, so the answer is the one a pull in pull mode makes once the epoch's arrivals have
    /// reached it. The run's last finish answers a terminal tile. A `main` output's breaker, whose
    /// driver prints each answer as pull mode prints each pull's. Its pipeline is ordered
    /// (`Dispatcher::order`), so every package of an epoch is consumed after the finish of the
    /// epoch before it and before its own: `answer` holds one epoch's answers.
    EachEpoch {
        /// The answers of the packages consumed since the last finish, merged.
        answer: Option<Box<Tile>>,
        /// The epoch the breaker last finished.
        finished: Option<u64>,
        /// Whether the output reads a loop's scope, directly or through other pipelines
        /// ([`SinkBreaker::reads_a_loop`]).
        loop_beneath: bool,
    },
}

impl SinkBreaker {
    /// The breaker of the sink that hands what it pulls of `producer`, which `subscribe` has
    /// filled, to `sink`, one answer per package.
    pub(crate) fn new(producer: ProducerSlot, sink: Arc<dyn DataSink>) -> Self {
        Self {
            producer,
            sink,
            hands: Hands::EachPackage,
            unsealed: false,
            handed_terminal: false,
        }
    }

    /// The breaker of a `main` output, which hands what it pulls of `producer` to `sink` one
    /// answer per epoch ([`Hands::EachEpoch`]).
    pub(crate) fn per_epoch(producer: ProducerSlot, sink: Arc<dyn DataSink>) -> Self {
        Self {
            producer,
            sink,
            hands: Hands::EachEpoch {
                answer: None,
                finished: None,
                loop_beneath: false,
            },
            unsealed: false,
            handed_terminal: false,
        }
    }

    /// Have a `main` output hand each package's answer as it consumes it, and at its one finish
    /// the answer that states it complete: a run over a live source finishes it only once every
    /// source yields everything (`Dispatcher::without_seals`).
    pub(crate) fn unsealed(&mut self) {
        self.unsealed = true;
    }

    /// Record that this `main` output reads a loop's scope. The scope's store pushes once it is
    /// terminal, and a pipeline reading it takes it at the run's last epoch, so the pull at an
    /// earlier finish reads, through that pipeline's breaker in pull mode, rows the loop's rounds
    /// have written. Each is final as it is written, and the producer states it complete.
    pub(crate) fn reads_a_loop(&mut self) {
        if let Hands::EachEpoch { loop_beneath, .. } = &mut self.hands {
            *loop_beneath = true;
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

impl Breaker for SinkBreaker {
    /// A sink's breaker keeps no mode: it pulls its producer at each consume, in a dispatched run
    /// only.
    fn enter_consuming_mode(&mut self) {}

    fn consume_impl(&mut self, _: InputId, guard: TileGuard) {
        let mut producer = Self::input(&self.producer);
        let tile = producer.get(guard);
        producer.release(tile.to_guard());
        match &mut self.hands {
            Hands::EachPackage => self.sink.process(&tile),
            // A run that no seal ends finishes the output once, at its end, so each package's
            // answer is handed as it is consumed.
            Hands::EachEpoch { answer, .. } if self.unsealed => {
                self.handed_terminal |= tile.is_terminal();
                self.sink.process(&tile);
                // Kept only for the check at the finish that the answers add up to a terminal one.
                if cfg!(debug_assertions) {
                    match answer {
                        None => *answer = Some(Box::new(tile)),
                        Some(answer) => answer.merge(tile),
                    }
                }
            }
            Hands::EachEpoch { answer, .. } => match answer {
                None => *answer = Some(Box::new(tile)),
                Some(answer) => answer.merge(tile),
            },
        }
    }

    fn finish(&mut self, pushes: &mut Pushes<'_>, last: bool) {
        let Hands::EachEpoch {
            answer: epoch,
            finished,
            loop_beneath,
        } = &mut self.hands
        else {
            return;
        };
        debug_assert!(
            finished.is_none_or(|finished| finished < pushes.epoch()),
            "a `main` output's pipeline is ordered, so it finishes its epochs in order and the \
             answers merged at a finish are that epoch's alone"
        );
        *finished = Some(pushes.epoch());
        let mut producer = Self::input(&self.producer);
        let tiling = producer.tiling().clone();
        let rest = producer.get(tiling.universal_guard()).closed_over(&tiling);
        producer.release(rest.to_guard());
        // The epoch's packages consumed all the producer holds, so the pull adds no key, except
        // the rows of a loop's rounds where the output reads a loop's scope (`reads_a_loop`).
        debug_assert!(
            rest.is_empty()
                || *loop_beneath
                    && matches!(&rest, Tile::DataFunction { domain_predicate, .. }
                        if rest.within(&Projection::admitting(domain_predicate.clone())).is_ok()),
            "the pull at the finish of an epoch of a `main` output adds no key, unless it reads \
             a loop's scope, and then only keys the producer states complete: {rest:?}"
        );
        if self.unsealed {
            if cfg!(debug_assertions) {
                let mut handed = epoch.take().map_or_else(|| rest.clone(), |answer| *answer);
                handed.merge(rest.clone());
                debug_assert!(
                    !last || handed.is_terminal(),
                    "the answers handed to a `main` output add up to a terminal one: {handed:?}"
                );
            }
            // Handed even with no row where no answer handed before was terminal: it states the
            // output complete, as after a delivery of no key or a key a filter drops.
            if !self.handed_terminal {
                self.sink.process(&rest);
            }
            return;
        }
        let answer = match epoch.take() {
            None => rest,
            Some(mut answer) => {
                answer.merge(rest);
                *answer
            }
        };
        debug_assert!(
            !last || answer.is_terminal(),
            "the run's last epoch hands a `main` output a terminal answer"
        );
        self.sink.process(&answer);
    }

    fn input_tiling(&self, _: InputId) -> Tiling {
        Self::reading(&self.producer).tiling().clone()
    }

    fn input_released(&self, _: InputId) -> TileGuard {
        Self::reading(&self.producer).obsolete_guard().clone()
    }

    fn as_producer(&self) -> Option<&dyn BreakingProducer> {
        None
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
        breaker.consume_impl(
            InputId::ONLY,
            breaker.input_tiling(InputId::ONLY).universal_guard(),
        );
        assert_eq!(sink.0.load(Ordering::SeqCst), 1);
        assert!(breaker.input_released(InputId::ONLY).is_universal());
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
        breaker.consume_impl(InputId::ONLY, domain(one.clone()));
        assert!(
            !breaker.input_released(InputId::ONLY).is_universal(),
            "one package of two"
        );
        breaker.consume_impl(InputId::ONLY, domain(Predicate::True.minus(&one)));
        assert!(
            breaker.input_released(InputId::ONLY).is_universal(),
            "both packages"
        );
        assert_eq!(sink.0.load(Ordering::SeqCst), 2);
    }

    /// An answer that states nothing complete releases nothing, so the sink is not done.
    #[test]
    fn an_answer_stating_nothing_releases_nothing() {
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let (mut breaker, sink) = sink_over(tiling.empty_tile());
        breaker.consume_impl(
            InputId::ONLY,
            breaker.input_tiling(InputId::ONLY).universal_guard(),
        );
        assert_eq!(sink.0.load(Ordering::SeqCst), 1);
        assert!(!breaker.input_released(InputId::ONLY).is_universal());
    }

    /// A sink that keeps each tile it is handed.
    #[derive(Default)]
    struct Recording(Mutex<Vec<Tile>>);

    impl DataSink for Recording {
        fn process(&self, tile: &Tile) {
            self.0
                .lock()
                .expect("no hand-off panics")
                .push(tile.clone());
        }
    }

    /// A `main` output's breaker hands one answer per epoch: the epoch's packages' answers merged
    /// with what the producer states complete, an answer of no key for an epoch of no package, and
    /// a terminal answer at the last epoch.
    #[test]
    fn a_main_output_is_handed_one_answer_per_epoch() {
        let tiling = Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let input = |keys: Vec<i64>, complete: Predicate| {
            let values = keys.iter().map(|key| key * 10).collect();
            Tile::data_function(
                ColumnValue::Ints(keys),
                Box::new(Tile::Scalar(ColumnValue::Ints(values))),
                complete,
                bit_set::BitSet::new(),
            )
        };
        let keys = |keys: Vec<i64>| {
            TileGuard::Function(FunctionGuard::Domain(Predicate::from_column_value(
                &ColumnValue::Ints(keys),
            )))
        };
        let through = |key: i64| Predicate::at_or_below(Value::Int(key));
        let (spy, script) = ProjectionSpy::scripted(input(vec![0], through(0)), tiling);
        let producer: ProducerSlot = Rc::new(RefCell::new(Some(Box::new(spy))));
        let sink = Arc::new(Recording::default());
        let mut breaker = SinkBreaker::per_epoch(producer, sink.clone());
        let dispatcher = crate::interpreter::dispatcher::Dispatcher::new(vec![vec![]], 1);
        let finish = |breaker: &mut SinkBreaker, epoch: u64, last: bool| {
            let mut pushes =
                dispatcher.pushes_in(crate::interpreter::dispatcher::PipelineId(0), epoch);
            breaker.finish(&mut pushes, last);
        };
        // Epoch 0: one package of key 0.
        breaker.consume_impl(InputId::ONLY, keys(vec![0]));
        finish(&mut breaker, 0, false);
        // Epoch 1: no package; the producer states key 1 complete and holds nothing at it.
        *script.borrow_mut() = input(vec![0], through(1));
        finish(&mut breaker, 1, false);
        // Epoch 2: two packages, keys 2 and 3, and everything complete.
        *script.borrow_mut() = input(vec![0, 2, 3], Predicate::True);
        breaker.consume_impl(InputId::ONLY, keys(vec![2]));
        breaker.consume_impl(InputId::ONLY, keys(vec![3]));
        finish(&mut breaker, 2, true);
        let handed = sink.0.lock().expect("no hand-off panics");
        let held: Vec<Vec<i64>> = handed
            .iter()
            .map(|tile| match tile {
                Tile::DataFunction {
                    domain: ColumnValue::Ints(keys),
                    ..
                } => keys.clone(),
                other => panic!("an answer of keys: {other:?}"),
            })
            .collect();
        assert_eq!(held, [vec![0], vec![], vec![2, 3]], "one answer per epoch");
        assert_eq!(
            handed.iter().map(Tile::is_terminal).collect::<Vec<_>>(),
            [false, false, true],
            "only the last epoch's answer is terminal"
        );
        assert!(breaker.input_released(InputId::ONLY).is_universal());
    }

    /// A `main` output's breaker finishes its epochs in order, since its pipeline is ordered.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "a `main` output's pipeline is ordered")]
    fn a_main_output_finishing_an_earlier_epoch_is_refused() {
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let (spy, _, _) = ProjectionSpy::new(Tile::Scalar(ColumnValue::Ints(vec![3])), tiling);
        let producer: ProducerSlot = Rc::new(RefCell::new(Some(Box::new(spy))));
        let mut breaker = SinkBreaker::per_epoch(producer, Arc::new(Recording::default()));
        let dispatcher = crate::interpreter::dispatcher::Dispatcher::new(vec![vec![]], 1);
        let pipeline = crate::interpreter::dispatcher::PipelineId(0);
        breaker.consume_impl(InputId::ONLY, TileGuard::Scalar(TileGuard::leaf(true)));
        breaker.finish(&mut dispatcher.pushes_in(pipeline, 1), false);
        breaker.finish(&mut dispatcher.pushes_in(pipeline, 0), false);
    }
}
