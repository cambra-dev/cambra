//! A live source through the pool, end to end: the delivering thread, which stands in for the
//! source's input, appends rows and notifies, and the workers claim the arrivals and run
//! `LiveRows → MapResult(negate)` into the collecting breaker.
//! See `src/interpreter/design-parallel.md`, "The dispatcher".

// The shared-state check skips `#[cfg(test)]` items, and this file holds nothing else.
#[cfg(test)]
mod end_to_end {
    use std::collections::{BTreeMap, BTreeSet};
    use std::sync::mpsc;
    use std::time::Duration;

    use bit_set::BitSet;

    use super::super::*;
    use crate::interpreter::tile_operators::test_helpers::{int_entries, keys_between};
    use crate::interpreter::tile_operators::{
        Constant, LiveSource, MapResult, ProducerBase, impl_producer_base, uint_keys_in, uint_range,
    };
    use crate::interpreter::{
        BaseType, ColumnValue, CurryLevel, Extent, FunctionDef, UnaryOpKind, Value,
        operator_graph::InputEdgeSpec,
    };
    use crate::{pretty_graph::VizOptions, pretty_tree::InspectNode};

    /// The rows a live source holds, and what the pool did to them. The values are the rows' own;
    /// `None` marks a row a release reclaimed.
    struct LiveStore {
        rows: Mutex<BTreeMap<u64, Option<i64>>>,
        /// The positions whose rows are written, the source's yield predicate. A chunk's positions
        /// join it once its rows are written.
        ready: Arc<Mutex<Predicate>>,
        source: Arc<LiveSource>,
        /// The consumer each worker's chain subscribed with.
        consumers: Mutex<Vec<Box<dyn Consumer>>>,
        /// Positions a `get` answered.
        served: Mutex<BTreeSet<u64>>,
        /// Positions a release named.
        released: Mutex<BTreeSet<u64>>,
        closed: AtomicBool,
    }

    impl LiveStore {
        fn new() -> Arc<Self> {
            let ready = Arc::new(Mutex::new(Predicate::False));
            let read = ready.clone();
            Arc::new(Self {
                rows: Mutex::new(BTreeMap::new()),
                ready,
                source: Arc::new(LiveSource::new(
                    move || read.lock_wait().clone(),
                    uint_keys_in,
                )),
                consumers: Mutex::new(Vec::new()),
                served: Mutex::new(BTreeSet::new()),
                released: Mutex::new(BTreeSet::new()),
                closed: AtomicBool::new(false),
            })
        }

        /// Write `chunk`'s rows and add its positions to the yield predicate, then say which
        /// positions it took, or `None` for an empty chunk.
        fn append(&self, chunk: &Chunk) -> Option<(u64, u64)> {
            if chunk.values.is_empty() {
                return None;
            }
            let last = chunk.first + chunk.values.len() as u64 - 1;
            let mut rows = self.rows.lock_wait();
            for (offset, value) in chunk.values.iter().enumerate() {
                rows.insert(chunk.first + offset as u64, Some(*value));
            }
            // The rows are written before the positions arrive, and the positions before the
            // notify.
            let mut ready = self.ready.lock_wait();
            *ready = ready.union(&uint_range(chunk.first, last));
            Some((chunk.first, last))
        }

        /// How many positions are ready.
        fn ready_rows(&self) -> usize {
            uint_keys_in(&self.ready.lock_wait(), u64::MAX).len()
        }

        /// Notify every chain's consumer, as the delivering thread does.
        fn notify_all(&self, arrived: &Projection) {
            for consumer in self.consumers.lock_wait().iter_mut() {
                consumer.notify(arrived);
            }
        }

        /// The positions `region` names that are ready.
        fn positions(&self, region: &Projection) -> Vec<u64> {
            let ready = self.ready.lock_wait().clone();
            uint_keys_in(&ready, u64::MAX)
                .into_iter()
                .filter(|key| match region {
                    Projection::Everything | Projection::Fields(_) => true,
                    Projection::Nothing => false,
                    Projection::Keys(keys) => keys.contains(key),
                })
                .map(|key| key.as_uint())
                .collect()
        }
    }

    /// Rows `values` at the positions from `first`: what the delivering thread appends at once.
    #[derive(Clone)]
    struct Chunk {
        first: u64,
        values: Vec<i64>,
    }

    /// The source operator: positions to values, with the arrivals' positions claimable.
    struct LiveRows {
        store: Arc<LiveStore>,
        tiling: Tiling,
    }

    impl LiveRows {
        fn new(store: Arc<LiveStore>) -> Self {
            Self {
                store,
                tiling: Tiling::data_function(
                    Extent::Base(BaseType::UInt),
                    Tiling::Scalar(Extent::Base(BaseType::Int)),
                ),
            }
        }
    }

    impl TileOperator for LiveRows {
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}

        fn tiling(&self) -> &Tiling {
            &self.tiling
        }

        fn morsel_source(&self) -> Option<Arc<dyn MorselSource>> {
            Some(self.store.source.clone())
        }

        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            self.store.consumers.lock_wait().push(consumer);
            Box::new(LiveRowsProducer {
                base: ProducerBase::unowned(LiveRowsProducer::alloc_id(), &self.tiling),
                store: self.store.clone(),
            })
        }
    }

    struct LiveRowsProducer {
        base: ProducerBase,
        store: Arc<LiveStore>,
    }

    impl TileProducer for LiveRowsProducer {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        /// The rows of the projection that have arrived and were not released to this producer,
        /// stating the positions that have arrived complete, or all of them once the source is
        /// closed.
        fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
            let projection = projection_guard.projection(&self.name());
            let rows = self.store.rows.lock_wait();
            let wanted = self.store.positions(&projection);
            let mut served = self.store.served.lock_wait();
            let mut values = Vec::with_capacity(wanted.len());
            for &position in &wanted {
                assert!(
                    served.insert(position),
                    "position {position} was answered twice"
                );
                values.push(rows[&position].expect("a row answered after it was reclaimed"));
            }
            // A source that is open decides the positions it holds: no further row arrives in
            // one. Once it is closed it decides every position.
            let decided = match self.store.closed.load(Ordering::Acquire) {
                true => Predicate::True,
                false => self.store.ready.lock_wait().clone(),
            };
            let mut tile = Tile::data_function(
                ColumnValue::from_uints(wanted),
                Box::new(Tile::Scalar(ColumnValue::Ints(values))),
                decided,
                BitSet::new(),
            );
            tile.remove_guarded(self.obsolete_guard().clone());
            tile.compact();
            tile.restrict_to(&projection, self.tiling());
            tile
        }

        /// Reclaim the rows a worker finished with. A row is released only after a `get` answered
        /// it and a claim handed it out, and once.
        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            let region = Projection::of(&obsolete_guard).expect("a release names keys");
            let positions = self.store.positions(&region);
            let claimed = self.store.source.claimed();
            // The order `get_impl` takes them in.
            let mut rows = self.store.rows.lock_wait();
            let served = self.store.served.lock_wait();
            let mut released = self.store.released.lock_wait();
            for position in positions {
                assert!(
                    claimed.contains(&Value::UInt(position)),
                    "position {position} was released before a worker claimed it"
                );
                assert!(
                    served.contains(&position),
                    "position {position} was released before a worker pulled it"
                );
                assert!(
                    released.insert(position),
                    "position {position} was released twice"
                );
                rows.insert(position, None);
            }
        }
    }

    fn negate() -> Constant {
        Constant::new(
            Value::ComputableFunction(FunctionDef::UnaryOp(UnaryOpKind::Neg)),
            Extent::Function {
                domain: Box::new(Extent::Base(BaseType::Int)),
                codomain: Box::new(Extent::Base(BaseType::Int)),
            },
        )
    }

    /// How the delivering thread paces its arrivals.
    #[derive(Clone, Copy)]
    enum Pace {
        /// One arrival right after another.
        Flat,
        /// A yield after each arrival, and a pause after every third.
        Interleaved,
        /// The next arrival waits until the workers have pulled every row so far, so the rows are
        /// consumed while the source is open and only a wake-up lets a parked worker see them.
        Lockstep,
    }

    /// The chain `LiveRows → MapResult(negate)` over a fresh store, and the delivering thread
    /// that appends `chunks` to the store in the order given and notifies, waiting for the workers
    /// as `pace` says.
    ///
    /// Before it delivers the chunk at position 0 after another, it waits until the workers have
    /// pulled every row that arrived, which they can only do if a later chunk is claimable while
    /// an earlier one is missing.
    fn setup(
        chunks: Vec<Chunk>,
        threads: usize,
        pace: Pace,
    ) -> (Arc<LiveStore>, MapResult, DeliveringThread<'static>) {
        let store = LiveStore::new();
        let map = MapResult::new_at(
            Box::new(LiveRows::new(store.clone())),
            Box::new(negate()),
            CurryLevel::new(1),
        );
        let delivered = store.clone();
        let delivery: DeliveringThread<'static> = Box::new(move |handle, _scheduler| {
            for (n, chunk) in chunks.iter().enumerate() {
                if let Pace::Lockstep = pace {
                    // Every worker waits, so the publish below has to wake one.
                    wait_for_every_worker_to_park(&handle.dispatcher, threads);
                }
                if chunk.first == 0 && !chunk.values.is_empty() && delivered.ready_rows() > 0 {
                    wait_until_pulled(
                        &delivered,
                        "no later chunk was claimable while position 0 was missing",
                    );
                }
                // An empty arrival cannot name its region: the source notifies everything.
                let region = match delivered.append(chunk) {
                    Some((first, last)) => {
                        Projection::of(&keys_between(first, last)).expect("keys")
                    }
                    None => Projection::Everything,
                };
                delivered.notify_all(&region);
                match pace {
                    Pace::Flat => {}
                    Pace::Interleaved => {
                        std::thread::yield_now();
                        if n % 3 == 2 {
                            std::thread::sleep(Duration::from_micros(200));
                        }
                    }
                    Pace::Lockstep => wait_until_pulled(
                        &delivered,
                        "the workers did not pull the rows that arrived: a lost wake-up",
                    ),
                }
            }
            // `run_pipeline` closes the source once this returns.
            delivered.closed.store(true, Ordering::Release);
        });
        (store, map, delivery)
    }

    /// Wait until the workers have pulled every row that is ready, failing with `cause` when
    /// they do not within thirty seconds.
    fn wait_until_pulled(store: &LiveStore, cause: &str) {
        let deadline = std::time::Instant::now() + Duration::from_secs(30);
        while store.served.lock_wait().len() < store.ready_rows() {
            assert!(std::time::Instant::now() < deadline, "{cause}");
            std::thread::yield_now();
        }
    }

    /// Wait until `threads` workers are parked: none is running a morsel or looking for one.
    fn wait_for_every_worker_to_park(dispatcher: &Dispatcher, threads: usize) {
        let deadline = std::time::Instant::now() + Duration::from_secs(30);
        while dispatcher.parked.load(Ordering::Acquire) < threads {
            assert!(
                std::time::Instant::now() < deadline,
                "every worker parked: a worker is stuck outside `park`"
            );
            std::thread::yield_now();
        }
    }

    fn collecting(map: &MapResult) -> PoolBreaker {
        PoolBreaker::Collect {
            collector: Mutex::new(map.tiling().empty_tile()),
        }
    }

    /// Deliver `chunks` to a live source and run `LiveRows → MapResult(negate)` into the
    /// collecting breaker on `threads` workers with morsels of `morsel_rows`. Returns what the
    /// breaker holds and the store, after every worker returned.
    fn run(
        chunks: Vec<Chunk>,
        threads: usize,
        morsel_rows: u64,
        pace: Pace,
    ) -> (Tile, Arc<LiveStore>) {
        let (store, mut map, delivery) = setup(chunks, threads, pace);
        let source = source_of(&map).expect("the chain reads one live source");
        let breaker = collecting(&map);
        let config = Config {
            threads,
            morsel_rows,
        };
        let tile = run_pipeline(
            &mut Scheduler::new(),
            &mut map,
            source,
            breaker,
            &config,
            Some(delivery),
        );
        (tile, store)
    }

    /// `run` with the first worker never serving: its chain still carries the pipeline's
    /// consumer, but no pull of it ever reopens a gate on the path from the source.
    fn run_without_the_first_worker(
        chunks: Vec<Chunk>,
        threads: usize,
        morsel_rows: u64,
    ) -> (Tile, Arc<LiveStore>) {
        let (store, mut map, delivery) = setup(chunks, threads - 1, Pace::Flat);
        let source = source_of(&map).expect("the chain reads one live source");
        let breaker = collecting(&map);
        let dispatcher = Arc::new(Dispatcher::new(
            vec![PipelineSpec {
                after: Vec::new(),
                source: Box::new(move || source.clone()),
                finalize: None,
            }],
            morsel_rows,
        ));
        let handle = PipelineHandle {
            dispatcher: dispatcher.clone(),
            pipeline: PipelineId(0),
        };
        let tiling = map.tiling().clone();
        let mut scheduler = Scheduler::new();
        let mut chains: Vec<Vec<Box<dyn TileProducer>>> = (0..threads)
            .map(|worker| {
                let head: Box<dyn Consumer> = match worker {
                    0 => Box::new(PipelineConsumer(handle.clone())),
                    _ => Box::new(|| {}),
                };
                vec![map.subscribe(tiling.universal_guard(), head, &mut scheduler)]
            })
            .collect();
        std::thread::scope(|scope| {
            let _fail = FailOnUnwind(&dispatcher);
            for worker_chains in chains.iter_mut().skip(1) {
                let (dispatcher, breaker) = (&dispatcher, &breaker);
                scope.spawn(move || run_worker(worker_chains, dispatcher, breaker));
            }
            delivery(handle.clone(), &mut scheduler);
            handle.close();
        });
        drop(chains);
        (breaker.finish(), store)
    }

    /// Run `body` on a thread of its own: a panic in it, a worker's included, is raised again
    /// here, and a run that does not finish within a minute fails as a lost wake-up.
    fn within_deadline<T: Send + 'static>(body: impl FnOnce() -> T + Send + 'static) -> T {
        let (done, finished) = mpsc::channel();
        let thread = std::thread::spawn(move || {
            let _ = done.send(body());
        });
        match finished.recv_timeout(Duration::from_secs(60)) {
            Ok(result) => result,
            Err(mpsc::RecvTimeoutError::Timeout) => {
                panic!("the pipeline did not finish: a lost wake-up leaves a worker parked")
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => match thread.join() {
                Err(panic) => std::panic::resume_unwind(panic),
                Ok(()) => unreachable!("the body sent its result before it returned"),
            },
        }
    }

    fn entries(tile: &Tile) -> Vec<(u64, i64)> {
        if tile.is_empty() {
            Vec::new()
        } else {
            int_entries(tile)
        }
    }

    /// Check a finished run against the serial answer and the release it owes: the sink holds
    /// every row once, mapped, and the source reclaimed every row a worker finished with, none
    /// before. Only the first chain's consumer is region-driven, which is the invariant of the
    /// path from the source to the pipeline's consumer.
    fn verify(chunks: &[Chunk], tile: &Tile, store: &LiveStore, context: &str) {
        let rows: BTreeMap<u64, i64> = chunks
            .iter()
            .flat_map(|chunk| {
                chunk
                    .values
                    .iter()
                    .enumerate()
                    .map(|(offset, value)| (chunk.first + offset as u64, *value))
            })
            .collect();
        let serial: Vec<(u64, i64)> = rows.iter().map(|(&position, v)| (position, -v)).collect();
        assert_eq!(entries(tile), serial, "{context}");
        let everything: BTreeSet<u64> = rows.keys().copied().collect();
        assert_eq!(
            *store.served.lock_wait(),
            everything,
            "every row pulled once"
        );
        assert_eq!(
            *store.released.lock_wait(),
            everything,
            "every row released once"
        );
        assert!(
            store.rows.lock_wait().values().all(Option::is_none),
            "the source reclaimed every row"
        );
        let covered = match (rows.keys().next(), rows.keys().last()) {
            (Some(&first), Some(&last)) => uint_range(first, last),
            _ => Predicate::False,
        };
        assert_eq!(
            store.source.claimed(),
            covered,
            "the claims cover every row, each once"
        );
        let consumers = store.consumers.lock_wait();
        assert!(
            consumers[0].region_driven(),
            "the consumer the source holds for the first chain is region-driven"
        );
        assert!(
            consumers[1..]
                .iter()
                .all(|consumer| !consumer.region_driven()),
            "the other chains' consumers ignore the region"
        );
    }

    fn check(chunks: Vec<Chunk>, threads: usize, morsel_rows: u64, pace: Pace) {
        let expected = chunks.clone();
        let (tile, store) = within_deadline(move || run(chunks, threads, morsel_rows, pace));
        verify(
            &expected,
            &tile,
            &store,
            &format!("{threads} workers, {morsel_rows}-row morsels"),
        );
    }

    /// Chunks of the given sizes, in position order, with values that are not their positions.
    fn chunks(sizes: &[usize]) -> Vec<Chunk> {
        let mut first = 0u64;
        sizes
            .iter()
            .map(|&size| {
                let values = (0..size as u64)
                    .map(|p| ((first + p) as i64 + 1) * 7 % 101)
                    .collect();
                let chunk = Chunk { first, values };
                first += size as u64;
                chunk
            })
            .collect()
    }

    /// `chunks` last to first: the chunk at position 0 is delivered after every other.
    fn reversed(mut chunks: Vec<Chunk>) -> Vec<Chunk> {
        chunks.reverse();
        chunks
    }

    /// `chunks` in a fixed pseudo-random order that does not deliver the chunk at position 0
    /// first.
    fn shuffled(mut chunks: Vec<Chunk>, seed: u64) -> Vec<Chunk> {
        let mut state = seed | 1;
        for i in (1..chunks.len()).rev() {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            chunks.swap(i, (state % (i as u64 + 1)) as usize);
        }
        if chunks[0].first == 0 {
            let last = chunks.len() - 1;
            chunks.swap(0, last);
        }
        chunks
    }

    const WORKERS: [usize; 4] = [1, 2, 4, 8];

    #[test]
    fn rows_that_arrive_in_bursts_are_mapped_once_and_released() {
        for threads in WORKERS {
            for morsel_rows in [1, 4, 64] {
                check(
                    chunks(&[50, 0, 1, 1, 200, 0, 3]),
                    threads,
                    morsel_rows,
                    Pace::Flat,
                );
            }
        }
    }

    #[test]
    fn rows_that_arrive_one_at_a_time_are_mapped_once_and_released() {
        for threads in WORKERS {
            check(chunks(&[1; 100]), threads, 8, Pace::Interleaved);
        }
    }

    /// A worker parked for want of a morsel sees each arrival while the source is still open.
    #[test]
    fn a_parked_worker_consumes_each_arrival_before_the_source_closes() {
        for threads in WORKERS {
            check(chunks(&[1, 4, 0, 1, 16, 1]), threads, 3, Pace::Lockstep);
        }
    }

    #[test]
    fn empty_arrivals_publish_nothing_and_a_source_with_no_rows_finishes() {
        for threads in WORKERS {
            check(chunks(&[0, 0, 5, 0]), threads, 2, Pace::Flat);
            check(chunks(&[0, 0, 0]), threads, 2, Pace::Flat);
            check(Vec::new(), threads, 2, Pace::Flat);
        }
    }

    /// The same run, repeatedly, for the interleavings a single run misses.
    #[test]
    fn repeated_runs_agree_with_the_serial_answer() {
        for round in 0..200 {
            let pace = match round % 3 {
                0 => Pace::Flat,
                1 => Pace::Interleaved,
                _ => Pace::Lockstep,
            };
            check(chunks(&[3, 0, 7, 1, 1, 12, 0, 5]), 4, 3, pace);
        }
    }

    /// Chunks that arrive last to first are claimed as they arrive, ahead of the missing chunk at
    /// position 0, and every row is run once. The delivering thread waits for the workers to pull
    /// the rows of the later chunks before it delivers position 0, and fails if they cannot.
    #[test]
    fn chunks_that_arrive_in_reverse_are_claimed_ahead_of_the_missing_first_chunk() {
        for threads in WORKERS {
            for morsel_rows in [1, 3, 64] {
                check(
                    reversed(chunks(&[3, 5, 1, 8, 2, 4])),
                    threads,
                    morsel_rows,
                    Pace::Flat,
                );
            }
        }
    }

    #[test]
    fn chunks_that_arrive_shuffled_are_mapped_once_and_released() {
        for threads in WORKERS {
            for seed in [0x9e37_79b9_7f4a_7c15, 7, 123_456_789] {
                check(
                    shuffled(chunks(&[3, 5, 1, 8, 2, 4, 6, 2]), seed),
                    threads,
                    3,
                    Pace::Interleaved,
                );
            }
        }
    }

    /// Out of order and repeatedly, with the workers parked before each arrival.
    #[test]
    fn repeated_out_of_order_runs_agree_with_the_serial_answer() {
        for round in 0..200u64 {
            let pace = match round % 3 {
                0 => Pace::Flat,
                1 => Pace::Interleaved,
                _ => Pace::Lockstep,
            };
            let order = match round % 2 {
                0 => reversed(chunks(&[2, 6, 1, 9, 3, 4])),
                _ => shuffled(chunks(&[2, 6, 1, 9, 3, 4]), round + 11),
            };
            check(order, 4, 3, pace);
        }
    }

    /// The notification path does not depend on the first worker: its chain is subscribed and
    /// never pulled, and the arrivals still reach the pipeline and are run by the others.
    #[test]
    fn notifications_reach_the_pipeline_when_the_first_worker_never_claims() {
        for threads in [2, 4] {
            let rows = chunks(&[1, 4, 0, 1, 16, 1]);
            let owned = rows.clone();
            let (tile, store) =
                within_deadline(move || run_without_the_first_worker(owned, threads, 3));
            verify(
                &rows,
                &tile,
                &store,
                &format!("{threads} chains, the first idle"),
            );
        }
    }
}
