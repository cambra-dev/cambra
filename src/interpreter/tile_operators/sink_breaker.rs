//! A sink as a pipeline breaker, for `crate::interpreter::dispatcher::run_program`.
//! See `src/interpreter/design-dispatcher.md`, "Running a compiled program".

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
}

/// When a [`SinkBreaker`] hands its sink what it pulled.
enum Hands {
    /// Each package's answer, as the package is consumed: a sink output's breaker.
    EachPackage,
    /// A `main` output's breaker, whose driver prints each answer as pull mode prints each
    /// pull's. Its pipeline is ordered (`Dispatcher::order`). At its finish it pulls the producer
    /// at the universal guard, which states what the producer states complete.
    Main {
        /// Whether it hands each package's answer as it consumes it, and at its finish the answer
        /// that states it complete where no answer before was terminal
        /// ([`SinkBreaker::hand_each_package`]); otherwise it merges the answers and hands them
        /// once, at its finish, as pull mode's one pull does.
        each_package: bool,
        /// The answers of the packages consumed, merged: all of them, or, where it hands each
        /// package's answer, in a debug build only, for the check that they add up to a terminal
        /// one.
        answer: Option<Box<Tile>>,
        /// Whether an answer handed so far was terminal.
        handed_terminal: bool,
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
        }
    }

    /// The breaker of a `main` output, which hands what it pulls of `producer` to `sink` once, at
    /// its finish ([`Hands::Main`]).
    pub(crate) fn main(producer: ProducerSlot, sink: Arc<dyn DataSink>) -> Self {
        Self {
            producer,
            sink,
            hands: Hands::Main {
                each_package: false,
                answer: None,
                handed_terminal: false,
                loop_beneath: false,
            },
        }
    }

    /// Have a `main` output hand each package's answer as it consumes it, and at its finish the
    /// answer that states it complete: a run over a live source finishes it only once every
    /// source yields everything.
    pub(crate) fn hand_each_package(&mut self) {
        if let Hands::Main { each_package, .. } = &mut self.hands {
            *each_package = true;
        }
    }

    /// Record that this `main` output reads a loop's scope: the pull at its finish reads, through
    /// that scope's store in pull mode, rows the loop's rounds have written. Each is final as it
    /// is written, and the producer states it complete.
    pub(crate) fn reads_a_loop(&mut self) {
        if let Hands::Main { loop_beneath, .. } = &mut self.hands {
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
            Hands::Main {
                each_package,
                answer,
                handed_terminal,
                ..
            } => {
                if *each_package {
                    *handed_terminal |= tile.is_terminal();
                    self.sink.process(&tile);
                    if !cfg!(debug_assertions) {
                        return;
                    }
                }
                match answer {
                    None => *answer = Some(Box::new(tile)),
                    Some(answer) => answer.merge(tile),
                }
            }
        }
    }

    fn finish(&mut self, _: &mut Pushes<'_>) {
        let Hands::Main {
            each_package,
            answer,
            handed_terminal,
            loop_beneath,
        } = &mut self.hands
        else {
            return;
        };
        let mut producer = Self::input(&self.producer);
        let tiling = producer.tiling().clone();
        let rest = producer.get(tiling.universal_guard()).closed_over(&tiling);
        producer.release(rest.to_guard());
        // The packages consumed all the producer holds, so the pull adds no key, except the rows
        // of a loop's rounds where the output reads a loop's scope (`reads_a_loop`).
        debug_assert!(
            rest.is_empty()
                || *loop_beneath
                    && matches!(&rest, Tile::DataFunction { domain_predicate, .. }
                        if rest.within(&Projection::admitting(domain_predicate.clone())).is_ok()),
            "the pull at the finish of a `main` output adds no key, unless it reads a loop's \
             scope, and then only keys the producer states complete: {rest:?}"
        );
        let merged = answer.take().map(|mut answer| {
            answer.merge(rest.clone());
            *answer
        });
        if *each_package {
            debug_assert!(
                merged.as_ref().is_none_or(Tile::is_terminal) || rest.is_terminal(),
                "the answers handed to a `main` output add up to a terminal one: {merged:?}"
            );
            // Handed even with no row where no answer handed before was terminal: it states the
            // output complete, as after a delivery of no key or a key a filter drops.
            if !*handed_terminal {
                self.sink.process(&rest);
            }
            return;
        }
        let answer = merged.unwrap_or(rest);
        debug_assert!(
            answer.is_terminal(),
            "a `main` output is handed a terminal answer at its finish"
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

    /// A `main` output over the scripted producer, its sink, and the producer's script: key 0
    /// complete through 0, then keys 0, 2 and 3 complete.
    fn main_over() -> (SinkBreaker, Arc<Recording>, Rc<RefCell<Tile>>) {
        let tiling = Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let (spy, script) = ProjectionSpy::scripted(input(vec![0], through(0)), tiling);
        let producer: ProducerSlot = Rc::new(RefCell::new(Some(Box::new(spy))));
        let sink = Arc::new(Recording::default());
        (SinkBreaker::main(producer, sink.clone()), sink, script)
    }

    fn input(keys: Vec<i64>, complete: Predicate) -> Tile {
        let values = keys.iter().map(|key| key * 10).collect();
        Tile::data_function(
            ColumnValue::Ints(keys),
            Box::new(Tile::Scalar(ColumnValue::Ints(values))),
            complete,
            bit_set::BitSet::new(),
        )
    }

    fn keys(keys: Vec<i64>) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(Predicate::from_column_value(
            &ColumnValue::Ints(keys),
        )))
    }

    fn through(key: i64) -> Predicate {
        Predicate::at_or_below(Value::Int(key))
    }

    /// Consume key 0, then keys 2 and 3 once the producer states everything complete, and
    /// finish: what the sink was handed, as each answer's keys and whether it is terminal.
    fn handed(
        mut breaker: SinkBreaker,
        sink: &Recording,
        script: &RefCell<Tile>,
    ) -> Vec<(Vec<i64>, bool)> {
        breaker.consume_impl(InputId::ONLY, keys(vec![0]));
        *script.borrow_mut() = input(vec![0, 2, 3], Predicate::True);
        breaker.consume_impl(InputId::ONLY, keys(vec![2]));
        breaker.consume_impl(InputId::ONLY, keys(vec![3]));
        let dispatcher = crate::interpreter::dispatcher::Dispatcher::new(vec![vec![]], 1);
        breaker.finish(&mut dispatcher.pushes(crate::interpreter::dispatcher::PipelineId(0)));
        assert!(breaker.input_released(InputId::ONLY).is_universal());
        let handed = sink.0.lock().expect("no hand-off panics");
        handed
            .iter()
            .map(|tile| match tile {
                Tile::DataFunction {
                    domain: ColumnValue::Ints(keys),
                    ..
                } => (keys.clone(), tile.is_terminal()),
                other => panic!("an answer of keys: {other:?}"),
            })
            .collect()
    }

    /// A `main` output's breaker merges its packages' answers and hands them once, at its finish,
    /// with what the producer states complete: a terminal answer.
    #[test]
    fn a_main_output_is_handed_its_merged_answers_at_its_finish() {
        let (breaker, sink, script) = main_over();
        assert_eq!(handed(breaker, &sink, &script), [(vec![0, 2, 3], true)]);
    }

    /// A `main` output's breaker that hands each package's answer hands each as it consumes it,
    /// then at its finish the answer that states it complete, since none before was terminal.
    #[test]
    fn a_main_output_handing_each_package_hands_its_answers_as_it_consumes_them() {
        let (mut breaker, sink, script) = main_over();
        breaker.hand_each_package();
        assert_eq!(
            handed(breaker, &sink, &script),
            [
                (vec![0], false),
                (vec![2], false),
                (vec![3], false),
                (vec![], true)
            ]
        );
    }
}
