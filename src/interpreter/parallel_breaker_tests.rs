//! The dispatcher's rounds over a breaker double: a recording [`Breaker`] that merges the keys of
//! the guard it is pulled at and pushes what a round merged.
//! See `src/interpreter/design-parallel.md`, "Pipeline breakers: sink, finalize and get".

// The shared-state check skips `#[cfg(test)]` items, and this file holds nothing else.
#[cfg(test)]
mod breakers {
    use std::collections::BTreeSet;
    use std::sync::{Arc, Mutex};

    use super::super::*;
    use crate::ccl::provenance::NodeId;
    use crate::interpreter::tile_operators::{
        Breaker, TileProducer, points, uint_keys_in, uint_range,
    };
    use crate::interpreter::{ColumnValue, FunctionGuard, Tile, Tiling, Value};

    /// What a double was asked to do, in order.
    #[derive(Debug, PartialEq)]
    enum Event {
        Pull(Vec<u64>),
        Round { terminal: bool, pushed: Vec<u64> },
    }

    /// How a double chooses what a round pushes.
    #[derive(Clone, Copy)]
    enum Pushing {
        /// The keys merged since the last round.
        Merged,
        /// The even keys merged since the last round.
        EvenOnly,
        /// The keys merged since the last round, pushed twice.
        Twice,
    }

    struct Double {
        log: Log,
        pushing: Pushing,
        state: Mutex<DoubleState>,
    }

    #[derive(Default)]
    struct DoubleState {
        held: BTreeSet<u64>,
        since_round: Vec<u64>,
        sinking: bool,
        terminal_seen: bool,
    }

    impl Double {
        fn new(pushing: Pushing) -> (Arc<Self>, Log) {
            let log = Log::default();
            let double = Arc::new(Self {
                log: log.clone(),
                pushing,
                state: Mutex::new(DoubleState::default()),
            });
            (double, log)
        }
    }

    type Log = Arc<Mutex<Vec<Event>>>;

    fn keys_of(region: &Predicate) -> Vec<u64> {
        uint_keys_in(region, u64::MAX)
            .into_iter()
            .map(|key| match key {
                Value::UInt(key) => key,
                other => panic!("a position, got {other:?}"),
            })
            .collect()
    }

    impl Breaker for Double {
        fn begin_sinking(&self) {
            let mut state = self.state.lock_now();
            assert!(!state.sinking, "a breaker begins sinking once");
            state.sinking = true;
        }

        fn pull_sink(&self, guard: TileGuard) {
            let mut state = self.state.lock_now();
            assert!(state.sinking, "a breaker is pulled after it begins sinking");
            assert!(!state.terminal_seen, "pull_sink after the terminal round");
            let TileGuard::Function(FunctionGuard::Domain(region)) = guard else {
                panic!("a morsel is a domain guard");
            };
            let keys = keys_of(&region);
            state.held.extend(&keys);
            state.since_round.extend(&keys);
            self.log.lock_now().push(Event::Pull(keys));
        }

        fn first_keys(&self, region: &Predicate, rows: u64) -> Vec<Value> {
            self.state
                .lock_now()
                .held
                .iter()
                .filter(|key| region.contains(&Value::UInt(**key)))
                .take(usize::try_from(rows).expect("a row count"))
                .map(|key| Value::UInt(*key))
                .collect()
        }

        fn held_keys(&self) -> usize {
            self.state.lock_now().held.len()
        }

        fn finalize(&self, round: Round, parents: &mut Pushes<'_>) {
            let mut state = self.state.lock_now();
            assert!(!state.terminal_seen, "no round after the terminal round");
            state.terminal_seen = round.terminal;
            let merged = std::mem::take(&mut state.since_round);
            drop(state);
            let pushed: Vec<u64> = match self.pushing {
                Pushing::Merged => merged,
                Pushing::Twice => merged,
                Pushing::EvenOnly => merged.into_iter().filter(|key| key % 2 == 0).collect(),
            };
            self.log.lock_now().push(Event::Round {
                terminal: round.terminal,
                pushed: pushed.clone(),
            });
            if !pushed.is_empty() {
                let region = points(
                    &pushed
                        .iter()
                        .map(|key| Value::UInt(*key))
                        .collect::<Vec<_>>(),
                );
                parents.push(&region);
                if matches!(self.pushing, Pushing::Twice) {
                    parents.push(&region);
                }
            }
        }
    }

    /// A worker that runs nothing: a breaker pipeline's morsels are the breaker's.
    struct NoWork;

    impl PoolWorker for NoWork {
        fn work(&mut self, _package: &WorkPackage) {
            panic!("a breaker pipeline's morsel runs through its breaker");
        }

        fn leave(&mut self, _pipeline: PipelineId) {}
    }

    /// A live source the test delivers keys to: the keys are ready when they are added.
    struct Arrivals {
        source: Arc<LiveSource>,
        ready: Arc<Mutex<Predicate>>,
    }

    impl Arrivals {
        fn new() -> Self {
            let ready = Arc::new(Mutex::new(Predicate::False));
            let read = ready.clone();
            Self {
                source: Arc::new(LiveSource::new(
                    move || read.lock_now().clone(),
                    uint_keys_in,
                )),
                ready,
            }
        }

        fn spec(&self, breaker: Option<BreakerHandle>) -> PipelineSpec {
            let source: Arc<dyn MorselSource> = self.source.clone();
            PipelineSpec {
                after: Vec::new(),
                streams_from: Vec::new(),
                source: Box::new(move || source.clone()),
                finalize: None,
                breaker,
            }
        }

        /// The keys `first..=last` arrive and are published to `pipeline`.
        fn deliver(&self, dispatcher: &Dispatcher, pipeline: usize, first: u64, last: u64) {
            let region = uint_range(first, last);
            {
                let mut ready = self.ready.lock_now();
                *ready = ready.union(&region);
            }
            dispatcher.publish(PipelineId(pipeline), &Projection::admitting(region));
        }
    }

    fn serve(dispatcher: &Dispatcher, state: &mut ServeState) {
        dispatcher.serve_until_wait(&mut NoWork, state);
    }

    fn rounds(log: &Arc<Mutex<Vec<Event>>>) -> Vec<(bool, Vec<u64>)> {
        log.lock_now()
            .iter()
            .filter_map(|event| match event {
                Event::Round { terminal, pushed } => Some((*terminal, pushed.clone())),
                Event::Pull(_) => None,
            })
            .collect()
    }

    fn pulled(log: &Arc<Mutex<Vec<Event>>>) -> Vec<u64> {
        let mut keys: Vec<u64> = log
            .lock_now()
            .iter()
            .flat_map(|event| match event {
                Event::Pull(keys) => keys.clone(),
                Event::Round { .. } => Vec::new(),
            })
            .collect();
        keys.sort_unstable();
        keys
    }

    /// One breaker pipeline over a live source, and its log.
    fn alone(pushing: Pushing) -> (Dispatcher, Arrivals, Log, Arc<Double>) {
        let arrivals = Arrivals::new();
        let (double, log) = Double::new(pushing);
        double.begin_sinking();
        let handle: BreakerHandle = double.clone();
        let dispatcher = Dispatcher::new(vec![arrivals.spec(Some(handle))], 2);
        (dispatcher, arrivals, log, double)
    }

    /// A round runs when the pipeline has drained after a morsel ran, once per drain, and not when
    /// no morsel ran since the last one, except the first, which is owed from the start; each
    /// round follows the morsels it merged.
    #[test]
    fn a_round_runs_when_a_pipeline_drains_and_not_when_it_ran_nothing() {
        let (dispatcher, arrivals, log, _double) = alone(Pushing::Merged);
        let mut state = dispatcher.serve_state();
        serve(&dispatcher, &mut state);
        assert_eq!(rounds(&log).len(), 1, "the first round is owed");
        arrivals.deliver(&dispatcher, 0, 0, 2);
        serve(&dispatcher, &mut state);
        serve(&dispatcher, &mut state);
        assert_eq!(
            log.lock_now()[1..],
            [
                Event::Pull(vec![0, 1]),
                Event::Pull(vec![2]),
                Event::Round {
                    terminal: false,
                    pushed: vec![0, 1, 2]
                },
            ],
            "the morsels of a drain, then one round"
        );
        arrivals.deliver(&dispatcher, 0, 3, 3);
        serve(&dispatcher, &mut state);
        assert_eq!(rounds(&log).len(), 3, "a second drain is a second round");
    }

    /// The terminal flag is set on the last round, exactly once, and a pipeline that ran nothing
    /// still has its terminal round.
    #[test]
    fn the_terminal_round_runs_once() {
        let (dispatcher, arrivals, log, _double) = alone(Pushing::Merged);
        let mut state = dispatcher.serve_state();
        arrivals.deliver(&dispatcher, 0, 0, 1);
        serve(&dispatcher, &mut state);
        dispatcher.close(PipelineId(0));
        serve(&dispatcher, &mut state);
        serve(&dispatcher, &mut state);
        let terminal: Vec<bool> = rounds(&log).iter().map(|(t, _)| *t).collect();
        assert_eq!(terminal, [false, true], "{:?}", log.lock_now());
        assert!(dispatcher.is_done(PipelineId(0)));

        let (dispatcher, _arrivals, log, _double) = alone(Pushing::Merged);
        let mut state = dispatcher.serve_state();
        dispatcher.close(PipelineId(0));
        serve(&dispatcher, &mut state);
        assert_eq!(
            rounds(&log),
            [(true, vec![])],
            "a pipeline that ran nothing has its terminal round"
        );
    }

    /// Two pipelines of breakers, the second a parent of the first, and a third that reads
    /// neither.
    fn family(pushing: Pushing) -> (Dispatcher, Arrivals, [Log; 3], Arrivals) {
        let first = Arrivals::new();
        let other = Arrivals::new();
        let ((a, a_log), (b, b_log), (c, c_log)) = (
            Double::new(pushing),
            Double::new(Pushing::Merged),
            Double::new(Pushing::Merged),
        );
        for double in [&a, &b, &c] {
            double.begin_sinking();
        }
        let a_handle: BreakerHandle = a.clone();
        let (b_handle, c_handle): (BreakerHandle, BreakerHandle) = (b.clone(), c.clone());
        let source = pushed_source(&a_handle);
        let parent = PipelineSpec {
            after: Vec::new(),
            streams_from: vec![PipelineId(0)],
            source: Box::new(move || source.clone()),
            finalize: None,
            breaker: Some(b_handle),
        };
        let dispatcher = Dispatcher::new(
            vec![
                first.spec(Some(a_handle)),
                parent,
                other.spec(Some(c_handle)),
            ],
            2,
        );
        (dispatcher, first, [a_log, b_log, c_log], other)
    }

    /// A push reaches the pipelines that stream from the breaker's pipeline and no other, and the
    /// parent claims each pushed key once.
    #[test]
    fn a_push_reaches_the_parents_and_no_other_pipeline() {
        let (dispatcher, first, [a_log, b_log, c_log], _other) = family(Pushing::Merged);
        let mut state = dispatcher.serve_state();
        first.deliver(&dispatcher, 0, 0, 4);
        serve(&dispatcher, &mut state);
        serve(&dispatcher, &mut state);
        assert_eq!(pulled(&a_log), [0, 1, 2, 3, 4]);
        assert_eq!(
            pulled(&b_log),
            [0, 1, 2, 3, 4],
            "the parent claims each pushed key once"
        );
        assert!(
            pulled(&c_log).is_empty(),
            "a pipeline that reads neither is not pushed to"
        );
    }

    /// The parent's morsels are cut from the keys pushed to it: the keys the breaker held and did
    /// not push are not claimed.
    #[test]
    fn a_parents_morsels_are_cut_from_pushed_keys_only() {
        let (dispatcher, first, [_a, b_log, _c], _other) = family(Pushing::EvenOnly);
        let mut state = dispatcher.serve_state();
        first.deliver(&dispatcher, 0, 0, 5);
        serve(&dispatcher, &mut state);
        serve(&dispatcher, &mut state);
        assert_eq!(pulled(&b_log), [0, 2, 4], "only the pushed keys");
    }

    /// A key is pushed once: a second push of it is refused, since the parent would never serve
    /// it, in every build.
    #[test]
    #[should_panic(expected = "a key is pushed in one round only")]
    fn a_key_pushed_twice_is_refused() {
        let (dispatcher, first, _logs, _other) = family(Pushing::Twice);
        let mut state = dispatcher.serve_state();
        first.deliver(&dispatcher, 0, 0, 1);
        serve(&dispatcher, &mut state);
        serve(&dispatcher, &mut state);
    }

    /// `pull_sink` is not called after the terminal round.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "pull_sink is not called after the terminal round")]
    fn pull_sink_is_not_called_after_the_terminal_round() {
        let (dispatcher, _arrivals, _log, _double) = alone(Pushing::Merged);
        let mut state = dispatcher.serve_state();
        dispatcher.close(PipelineId(0));
        serve(&dispatcher, &mut state);
        dispatcher.sink_morsel(&WorkPackage {
            pipeline: PipelineId(0),
            guard: TileGuard::Function(FunctionGuard::Domain(uint_range(0, 0))),
        });
    }

    /// The scheduler hands back the handle registered for an operator.
    #[test]
    fn the_scheduler_finds_a_breaker_by_its_operator() {
        let mut scheduler = Scheduler::default();
        let operator = NodeId::fresh();
        assert!(scheduler.breaker(operator).is_none());
        let (double, _log) = Double::new(Pushing::Merged);
        let handle: BreakerHandle = double;
        scheduler.register_breaker(operator, &handle);
        let found = scheduler.breaker(operator).expect("registered");
        assert!(Arc::ptr_eq(&found, &handle));
        assert!(scheduler.breaker(NodeId::fresh()).is_none());
    }

    /// A second registration for an operator replaces the first, live or not: the producer
    /// subscribed last is the one a run drives.
    #[test]
    fn a_second_registration_replaces_the_first() {
        let mut scheduler = Scheduler::default();
        let operator = NodeId::fresh();
        let (first, _) = Double::new(Pushing::Merged);
        let (second, _) = Double::new(Pushing::Merged);
        let (first, second): (BreakerHandle, BreakerHandle) = (first, second);
        scheduler.register_breaker(operator, &first);
        scheduler.register_breaker(operator, &second);
        let found = scheduler.breaker(operator).expect("registered");
        assert!(Arc::ptr_eq(&found, &second));
    }

    /// A breaker's first round runs when its pipeline first has nothing to claim, though no morsel
    /// ran: it may hold keys the parents have not been told.
    #[test]
    fn the_first_round_runs_before_any_morsel() {
        let (dispatcher, _arrivals, log, _double) = alone(Pushing::Merged);
        let mut state = dispatcher.serve_state();
        serve(&dispatcher, &mut state);
        assert_eq!(
            log.lock_now()
                .iter()
                .filter(|event| matches!(
                    event,
                    Event::Round {
                        terminal: false,
                        ..
                    }
                ))
                .count(),
            1
        );
        serve(&dispatcher, &mut state);
        assert_eq!(
            log.lock_now()
                .iter()
                .filter(|event| matches!(
                    event,
                    Event::Round {
                        terminal: false,
                        ..
                    }
                ))
                .count(),
            1,
            "no second round without a morsel"
        );
    }

    /// A pipeline that streams from two breaker pipelines is refused: its morsels are cut from one
    /// breaker's keys, and the other's would be lost.
    #[test]
    #[should_panic(expected = "a pipeline streams from one breaker pipeline")]
    fn a_pipeline_behind_two_breakers_is_refused() {
        let (first, second, parent) = (Arrivals::new(), Arrivals::new(), Arrivals::new());
        let ((a, _), (b, _), (c, _)) = (
            Double::new(Pushing::Merged),
            Double::new(Pushing::Merged),
            Double::new(Pushing::Merged),
        );
        let a_handle: BreakerHandle = a;
        let source = pushed_source(&a_handle);
        let mut behind = parent.spec(Some(c));
        behind.streams_from = vec![PipelineId(0), PipelineId(1)];
        behind.source = Box::new(move || source.clone());
        Dispatcher::new(
            vec![first.spec(Some(a_handle)), second.spec(Some(b)), behind],
            2,
        );
    }

    /// Two parents of one breaker each claim every key it pushes, once.
    #[test]
    fn two_parents_of_one_breaker_each_claim_every_pushed_key_once() {
        let first = Arrivals::new();
        let ((a, _), (b, b_log), (c, c_log)) = (
            Double::new(Pushing::Merged),
            Double::new(Pushing::Merged),
            Double::new(Pushing::Merged),
        );
        for double in [&a, &b, &c] {
            double.begin_sinking();
        }
        let a_handle: BreakerHandle = a;
        let parent = |breaker: BreakerHandle| {
            let source = pushed_source(&a_handle);
            PipelineSpec {
                after: Vec::new(),
                streams_from: vec![PipelineId(0)],
                source: Box::new(move || source.clone()),
                finalize: None,
                breaker: Some(breaker),
            }
        };
        let dispatcher = Dispatcher::new(
            vec![first.spec(Some(a_handle.clone())), parent(b), parent(c)],
            2,
        );
        let mut state = dispatcher.serve_state();
        first.deliver(&dispatcher, 0, 0, 4);
        serve(&dispatcher, &mut state);
        serve(&dispatcher, &mut state);
        assert_eq!(pulled(&b_log), [0, 1, 2, 3, 4]);
        assert_eq!(pulled(&c_log), [0, 1, 2, 3, 4]);
    }

    /// A breaker is called from one thread: a second thread's call is refused.
    #[test]
    fn a_breaker_pipeline_is_driven_by_one_thread() {
        let (dispatcher, _arrivals, _log, _double) = alone(Pushing::Merged);
        let package = || WorkPackage {
            pipeline: PipelineId(0),
            guard: TileGuard::Function(FunctionGuard::Domain(uint_range(0, 0))),
        };
        dispatcher.sink_morsel(&package());
        let refused = std::thread::scope(|scope| {
            scope
                .spawn(|| dispatcher.sink_morsel(&package()))
                .join()
                .is_err()
        });
        assert!(refused);
    }

    /// A `Memo` over a scripted input, subscribed, switched to sink mode and reached through the
    /// scheduler's registry; its producer answers `get`.
    fn memo_over(tile: Tile) -> (BreakerHandle, Box<dyn TileProducer>, Tiling) {
        use crate::interpreter::tile_operators::test_helpers::ProjectionSpyOp;
        use crate::interpreter::tile_operators::{Memo, TileOperator};
        use crate::interpreter::{BaseType, Extent};
        let tiling = Tiling::data_function(
            Extent::uint_range(8),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let (input, _, _) = ProjectionSpyOp::new(tile, tiling.clone());
        let mut memo = Memo::new(Box::new(input));
        let mut scheduler = Scheduler::new();
        let producer = memo.subscribe(tiling.empty_guard(), Box::new(|| {}), &mut scheduler);
        let handle = scheduler
            .breaker(memo.operator_id().expect("an operator has an identity"))
            .expect("a memo registers its breaker when it is subscribed");
        handle.begin_sinking();
        (handle, producer, tiling)
    }

    /// A memo pipeline over a live source and a parent over the memo's pushed keys.
    fn memo_and_parent(tile: Tile) -> (Dispatcher, Arrivals, Log, Box<dyn TileProducer>, Tiling) {
        let (handle, producer, tiling) = memo_over(tile);
        let arrivals = Arrivals::new();
        let (parent, log) = Double::new(Pushing::Merged);
        parent.begin_sinking();
        let parent: BreakerHandle = parent;
        let source = pushed_source(&handle);
        let spec = PipelineSpec {
            after: Vec::new(),
            streams_from: vec![PipelineId(0)],
            source: Box::new(move || source.clone()),
            finalize: None,
            breaker: Some(parent),
        };
        let dispatcher = Dispatcher::new(vec![arrivals.spec(Some(handle)), spec], 2);
        (dispatcher, arrivals, log, producer, tiling)
    }

    fn complete_at(tile: &Tile, key: u64) -> bool {
        let Tile::DataFunction {
            domain_predicate, ..
        } = tile
        else {
            panic!("a collection, got {tile:?}");
        };
        domain_predicate.contains(&Value::UInt(key))
    }

    /// A memo pipeline pushes the keys it merged each round, its parent claims them, and the
    /// whole output is complete only after the terminal round.
    #[test]
    fn a_memo_pipeline_pushes_each_round_and_completes_at_the_terminal_round() {
        use crate::interpreter::tile_operators::test_helpers::ints_by_position;
        let values: Vec<i64> = (0..8).collect();
        let (dispatcher, arrivals, log, mut memo, tiling) =
            memo_and_parent(ints_by_position(&values, true));
        let mut state = dispatcher.serve_state();
        arrivals.deliver(&dispatcher, 0, 0, 3);
        serve(&dispatcher, &mut state);
        serve(&dispatcher, &mut state);
        assert_eq!(
            pulled(&log),
            [0, 1, 2, 3],
            "the parent reads the first round's keys"
        );
        let first = memo.get(tiling.universal_guard());
        assert!(
            complete_at(&first, 3) && !complete_at(&first, 5),
            "{first:?}"
        );

        arrivals.deliver(&dispatcher, 0, 4, 7);
        dispatcher.close(PipelineId(0));
        serve(&dispatcher, &mut state);
        serve(&dispatcher, &mut state);
        serve(&dispatcher, &mut state);
        assert_eq!(
            pulled(&log),
            [0, 1, 2, 3, 4, 5, 6, 7],
            "each pushed key once"
        );
        let whole = memo.get(tiling.universal_guard());
        assert!(
            whole.is_terminal(),
            "complete after the terminal round: {whole:?}"
        );
        assert!(dispatcher.all_done());
    }

    /// A memo pushes keys with rows only: a key of its input that has none is not pushed.
    #[test]
    fn a_memo_pipeline_pushes_keys_with_rows_only() {
        let sparse = Tile::data_function(
            ColumnValue::UInts(vec![0, 2, 5]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 20, 50]))),
            Predicate::True,
            Default::default(),
        );
        let (dispatcher, arrivals, log, _memo, _tiling) = memo_and_parent(sparse);
        let mut state = dispatcher.serve_state();
        arrivals.deliver(&dispatcher, 0, 0, 7);
        serve(&dispatcher, &mut state);
        serve(&dispatcher, &mut state);
        assert_eq!(pulled(&log), [0, 2, 5]);
    }

    /// A memo that pulled keys before it switched pushes them to its parent with the keys the
    /// sink merges: the input released those keys, so no sink pull reads them again.
    #[test]
    fn review_adopted_keys_reach_the_parent() {
        use crate::interpreter::tile_operators::test_helpers::{ProjectionSpyOp, keys_between};
        use crate::interpreter::tile_operators::{Memo, TileOperator};
        use crate::interpreter::{BaseType, Extent};
        let tiling = Tiling::data_function(
            Extent::uint_range(8),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let values: Vec<i64> = (0..8).collect();
        let (input, _, _) = ProjectionSpyOp::new(
            crate::interpreter::tile_operators::test_helpers::ints_by_position(&values, true),
            tiling.clone(),
        );
        let mut memo = Memo::new(Box::new(input));
        let mut scheduler = Scheduler::new();
        let mut producer = memo.subscribe(tiling.empty_guard(), Box::new(|| {}), &mut scheduler);
        producer.get(keys_between(0, 3));
        let handle = scheduler
            .breaker(memo.operator_id().expect("an identity"))
            .expect("registered");
        handle.begin_sinking();

        let arrivals = Arrivals::new();
        let (parent, log) = Double::new(Pushing::Merged);
        parent.begin_sinking();
        let parent: BreakerHandle = parent;
        let source = pushed_source(&handle);
        let spec = PipelineSpec {
            after: Vec::new(),
            streams_from: vec![PipelineId(0)],
            source: Box::new(move || source.clone()),
            finalize: None,
            breaker: Some(parent),
        };
        let dispatcher = Dispatcher::new(vec![arrivals.spec(Some(handle)), spec], 2);
        let mut state = dispatcher.serve_state();
        arrivals.deliver(&dispatcher, 0, 0, 7);
        serve(&dispatcher, &mut state);
        serve(&dispatcher, &mut state);
        assert_eq!(pulled(&log), [0, 1, 2, 3, 4, 5, 6, 7]);
    }

    /// An aggregate in sink mode swallows what its input notifies, states its result terminal at the
    /// terminal round only, and wakes its consumer from that round.
    #[test]
    fn a_sinking_aggregate_is_terminal_and_notifies_at_the_terminal_round_only() {
        use crate::ccl::AggregateKind;
        use crate::interpreter::tile_operators::test_helpers::{
            NotifyingOp, ints_by_position, keys_between, notify_input,
        };
        use crate::interpreter::tile_operators::{Aggregate, TileOperator};
        use crate::interpreter::{BaseType, Extent, Projection};
        let tiling = Tiling::data_function(
            Extent::uint_range(8),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let values: Vec<i64> = (0..8).collect();
        let (input, notifier) = NotifyingOp::new(ints_by_position(&values, true), tiling.clone());
        let mut sum = Aggregate::new(Box::new(input), AggregateKind::Sum);
        let mut scheduler = Scheduler::new();
        let woken = Arc::new(Mutex::new(0usize));
        let counter = woken.clone();
        let mut producer = sum.subscribe(
            sum.tiling().empty_guard(),
            Box::new(move || *counter.lock_now() += 1),
            &mut scheduler,
        );
        let handle = scheduler
            .breaker(sum.operator_id().expect("an identity"))
            .expect("registered");
        handle.begin_sinking();
        notify_input(
            &notifier,
            &Projection::of(&keys_between(0, 3)).expect("keys"),
        );
        assert_eq!(
            *woken.lock_now(),
            0,
            "the input's notification is swallowed"
        );

        let arrivals = Arrivals::new();
        let dispatcher = Dispatcher::new(vec![arrivals.spec(Some(handle))], 2);
        let mut state = dispatcher.serve_state();
        arrivals.deliver(&dispatcher, 0, 0, 7);
        serve(&dispatcher, &mut state);
        assert_eq!(*woken.lock_now(), 0, "a round before the end wakes nobody");
        let universal = sum.tiling().universal_guard();
        assert!(!producer.get(universal.clone()).is_terminal());
        dispatcher.close(PipelineId(0));
        serve(&dispatcher, &mut state);
        assert_eq!(*woken.lock_now(), 1, "the terminal round woke the consumer");
        let tile = producer.get(universal);
        assert!(tile.is_terminal());
        let Tile::Aggregation { accumulator, .. } = tile else {
            panic!("an aggregation")
        };
        assert_eq!(
            *accumulator,
            Tile::Scalar(ColumnValue::Ints(vec![28]))
        );
    }

    /// The keys a memo adopted from its pull-mode cache reach the parent although no morsel is
    /// delivered and the source stays open: the memo's first round pushes them.
    #[test]
    fn adopted_keys_reach_the_parent_with_no_morsel_delivered() {
        use crate::interpreter::tile_operators::test_helpers::{ProjectionSpyOp, keys_between};
        use crate::interpreter::tile_operators::{Memo, TileOperator};
        use crate::interpreter::{BaseType, Extent};
        let tiling = Tiling::data_function(
            Extent::uint_range(8),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let values: Vec<i64> = (0..8).collect();
        let (input, _, _) = ProjectionSpyOp::new(
            crate::interpreter::tile_operators::test_helpers::ints_by_position(&values, true),
            tiling.clone(),
        );
        let mut memo = Memo::new(Box::new(input));
        let mut scheduler = Scheduler::new();
        let mut producer = memo.subscribe(tiling.empty_guard(), Box::new(|| {}), &mut scheduler);
        producer.get(keys_between(0, 3));
        let handle = scheduler
            .breaker(memo.operator_id().expect("an identity"))
            .expect("registered");
        handle.begin_sinking();

        let arrivals = Arrivals::new();
        let (parent, log) = Double::new(Pushing::Merged);
        parent.begin_sinking();
        let parent: BreakerHandle = parent;
        let source = pushed_source(&handle);
        let spec = PipelineSpec {
            after: Vec::new(),
            streams_from: vec![PipelineId(0)],
            source: Box::new(move || source.clone()),
            finalize: None,
            breaker: Some(parent),
        };
        let dispatcher = Dispatcher::new(vec![arrivals.spec(Some(handle)), spec], 2);
        let mut state = dispatcher.serve_state();
        for _ in 0..3 {
            serve(&dispatcher, &mut state);
        }
        assert_eq!(
            pulled(&log),
            [0, 1, 2, 3],
            "the pull-mode cache, no morsel delivered"
        );
    }

    /// A memo in sink mode swallows what its input notifies, and tells its consumer of a change
    /// when it finalizes, after the rows are merged.
    #[test]
    fn a_sinking_memo_notifies_its_consumer_from_finalize_only() {
        use crate::interpreter::tile_operators::test_helpers::{
            NotifyingOp, ints_by_position, keys_between, notify_input,
        };
        use crate::interpreter::tile_operators::{Memo, TileOperator};
        use crate::interpreter::{BaseType, Extent, Projection};
        let tiling = Tiling::data_function(
            Extent::uint_range(8),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let values: Vec<i64> = (0..8).collect();
        let (input, notifier) = NotifyingOp::new(ints_by_position(&values, true), tiling.clone());
        let mut memo = Memo::new(Box::new(input));
        let mut scheduler = Scheduler::new();
        let woken = Arc::new(Mutex::new(0usize));
        let counter = woken.clone();
        let _producer = memo.subscribe(
            tiling.empty_guard(),
            Box::new(move || *counter.lock_now() += 1),
            &mut scheduler,
        );
        let handle = scheduler
            .breaker(memo.operator_id().expect("an identity"))
            .expect("registered");
        handle.begin_sinking();
        let region = Projection::of(&keys_between(0, 3)).expect("keys");
        notify_input(&notifier, &region);
        assert_eq!(
            *woken.lock_now(),
            0,
            "the input's notification is swallowed"
        );

        let arrivals = Arrivals::new();
        let dispatcher = Dispatcher::new(vec![arrivals.spec(Some(handle))], 2);
        let mut state = dispatcher.serve_state();
        arrivals.deliver(&dispatcher, 0, 0, 3);
        serve(&dispatcher, &mut state);
        assert_eq!(
            *woken.lock_now(),
            1,
            "the round notified once, after the merge"
        );
    }

    /// A memo that is not a collection has no keys to push and is refused when it switches.
    #[test]
    #[should_panic(expected = "a memo that sinks is a collection")]
    fn a_memo_that_is_not_a_collection_does_not_sink() {
        use crate::interpreter::tile_operators::test_helpers::ProjectionSpyOp;
        use crate::interpreter::tile_operators::{Memo, TileOperator};
        use crate::interpreter::{BaseType, Extent};
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let (input, _, _) =
            ProjectionSpyOp::new(Tile::Scalar(ColumnValue::Ints(vec![3])), tiling.clone());
        let mut memo = Memo::new(Box::new(input));
        let mut scheduler = Scheduler::new();
        let _producer = memo.subscribe(tiling.empty_guard(), Box::new(|| {}), &mut scheduler);
        scheduler
            .breaker(memo.operator_id().expect("an identity"))
            .expect("registered")
            .begin_sinking();
    }
}
