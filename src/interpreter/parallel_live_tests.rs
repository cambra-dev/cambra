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
        BreakerOutput, Constant, LiveSource, MapResult, ProducerBase, impl_producer_base,
        uint_keys_in, uint_range,
    };
    use crate::interpreter::{
        BaseType, ColumnValue, CurryLevel, Extent, FunctionDef, FunctionGuard, Materialized,
        Predicate, UnaryOpKind, Value, operator_graph::InputEdgeSpec,
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
        /// Makes the next `get` panic, as a worker that fails does.
        explodes: AtomicBool,
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
                explodes: AtomicBool::new(false),
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
        fn visit_inputs_mut(&mut self, _visit: &mut dyn FnMut(&mut Box<dyn TileOperator>)) {}

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
            assert!(
                !self.store.explodes.load(Ordering::Acquire),
                "a worker panicked"
            );
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
        let delivery = setup_delivery(store.clone(), chunks, threads, pace);
        (store, map, delivery)
    }

    /// The delivering thread of `setup`, over an existing store.
    fn setup_delivery(
        delivered: Arc<LiveStore>,
        chunks: Vec<Chunk>,
        threads: usize,
        pace: Pace,
    ) -> DeliveringThread<'static> {
        Box::new(move |handle, _scheduler| {
            for (n, chunk) in chunks.iter().enumerate() {
                if let Pace::Lockstep = pace {
                    // Every worker waits, so the publish below has to wake one.
                    wait_for_every_worker_to_park(&handle.dispatcher, threads);
                }
                if chunk.first == 0 && !chunk.values.is_empty() && delivered.ready_rows() > 0 {
                    wait_until_pulled(
                        &delivered,
                        &handle.dispatcher,
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
                        &handle.dispatcher,
                        "the workers did not pull the rows that arrived: a lost wake-up",
                    ),
                }
            }
            // `run_pipeline` closes the source once this returns.
            delivered.closed.store(true, Ordering::Release);
        })
    }

    /// Poll `condition` until it holds, failing with `cause` after thirty seconds, or at once when
    /// the dispatcher failed: a worker panicked, and nothing will make the condition hold.
    fn wait_for(cause: &str, dispatcher: &Dispatcher, condition: impl Fn() -> bool) {
        let deadline = std::time::Instant::now() + Duration::from_secs(30);
        while !condition() {
            assert!(
                !dispatcher.failed.load(Ordering::Acquire),
                "a worker failed while waiting: {cause}"
            );
            assert!(std::time::Instant::now() < deadline, "{cause}");
            std::thread::yield_now();
        }
    }

    /// Wait until the workers have pulled every row that is ready.
    fn wait_until_pulled(store: &LiveStore, dispatcher: &Dispatcher, cause: &str) {
        wait_for(cause, dispatcher, || {
            store.served.lock_wait().len() >= store.ready_rows()
        });
    }

    /// Wait until `threads` workers are parked: none is running a morsel or looking for one.
    fn wait_for_every_worker_to_park(dispatcher: &Dispatcher, threads: usize) {
        wait_for(
            "every worker parked: a worker is stuck outside `park`",
            dispatcher,
            || dispatcher.parked.load(Ordering::Acquire) >= threads,
        );
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

    /// Keeps the rows of the even positions: the keys a chain filters out are in the region it
    /// answers and have no row.
    struct EveryOther {
        base: OperatorBase,
        input: Box<dyn TileOperator>,
    }

    impl TileOperator for EveryOther {
        crate::interpreter::tile_operators::impl_operator_base!();

        fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
            visit(crate::interpreter::operator_graph::value(
                "input",
                &*self.input,
            ));
        }

        fn visit_inputs_mut(&mut self, visit: &mut dyn FnMut(&mut Box<dyn TileOperator>)) {
            visit(&mut self.input);
        }

        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            consumer: Box<dyn Consumer>,
            scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            let input =
                self.input
                    .subscribe(self.input.tiling().universal_guard(), consumer, scheduler);
            Box::new(EveryOtherProducer {
                base: ProducerBase::new(
                    EveryOtherProducer::alloc_id(),
                    self.tiling(),
                    &self.base,
                    scheduler,
                ),
                input,
            })
        }
    }

    struct EveryOtherProducer {
        base: ProducerBase,
        input: Box<dyn TileProducer>,
    }

    impl TileProducer for EveryOtherProducer {
        impl_producer_base!();

        fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
            visit("input", &*self.input);
        }

        fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
            let mut tile = self.input.get(projection_guard);
            let odd = match &tile {
                Tile::DataFunction { domain, .. } => (0..domain.len())
                    .map(|row| domain.index_at(row))
                    .filter(|key| key.as_uint() % 2 == 1)
                    .fold(Predicate::False, |all, key| {
                        all.union(&Predicate::point(key))
                    }),
                other => panic!("a collection, got {other:?}"),
            };
            tile.remove_guarded(TileGuard::Function(FunctionGuard::Domain(odd)));
            tile.compact();
            tile
        }

        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            self.input.release(obsolete_guard);
        }
    }

    /// `LiveRows → MapResult(negate) → Materialize` into `readers` pipelines
    /// `BreakerOutput → MapResult(negate) → Collect`, over `store`, on `threads` workers: the
    /// rows as delivered, negated twice. With `filtering` the first pipeline keeps the even
    /// positions only. Returns what each reading pipeline's breaker holds, the store and the
    /// breaker's output once every worker returned.
    fn run_breaker(
        delivery: impl FnOnce(&Arc<LiveStore>, &Arc<Materialized>) -> DeliveringThread<'static>,
        store: Arc<LiveStore>,
        threads: usize,
        morsel_rows: u64,
        readers: usize,
        filtering: bool,
    ) -> (Tile, Vec<Tile>, Arc<LiveStore>, Arc<Materialized>) {
        let rows: Box<dyn TileOperator> = match filtering {
            false => Box::new(LiveRows::new(store.clone())),
            true => {
                let live = LiveRows::new(store.clone());
                Box::new(EveryOther {
                    base: OperatorBase::new(live.tiling().clone()),
                    input: Box::new(live),
                })
            }
        };
        let mut upstream = MapResult::new_at(rows, Box::new(negate()), CurryLevel::new(1));
        let output = Materialized::new(upstream.tiling().clone());
        let mut downstreams: Vec<MapResult> = (0..readers)
            .map(|_| {
                MapResult::new_at(
                    Box::new(BreakerOutput::new(
                        output.clone(),
                        upstream.tiling().clone(),
                        false,
                        None,
                    )),
                    Box::new(negate()),
                    CurryLevel::new(1),
                )
            })
            .collect();
        let delivery = delivery(&store, &output);
        let up_source = source_of(&upstream).expect("the chain reads one live source");
        let mut runs = vec![PipelineRun {
            keyed: false,
            inherits: Vec::new(),
            chain: &mut upstream,
            source: up_source,
            breaker: PoolBreaker::Materialize {
                output: output.clone(),
            },
            head: Head::Source,
            after: Vec::new(),
            streams_from: Vec::new(),
        }];
        for downstream in &mut downstreams {
            runs.push(PipelineRun {
                keyed: false,
                inherits: Vec::new(),
                source: source_of(&*downstream).expect("the chain reads the breaker's output"),
                breaker: collecting(downstream),
                chain: downstream,
                head: Head::Breaker,
                after: Vec::new(),
                streams_from: vec![PipelineId(0)],
            });
        }
        let config = Config {
            threads,
            morsel_rows,
        };
        let mut tiles = run_pipelines(&mut Scheduler::new(), runs, &config, Some(delivery));
        let upstream = tiles.remove(0);
        (upstream, tiles, store, output)
    }

    /// [`run_breaker`] with one reading pipeline: what its breaker holds.
    fn run_two_pipelines(
        delivery: impl FnOnce(&Arc<LiveStore>, &Arc<Materialized>) -> DeliveringThread<'static>,
        store: Arc<LiveStore>,
        threads: usize,
        morsel_rows: u64,
    ) -> (Tile, Arc<LiveStore>, Arc<Materialized>) {
        let (_, mut tiles, store, output) =
            run_breaker(delivery, store, threads, morsel_rows, 1, false);
        (tiles.pop().expect("one reader"), store, output)
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
                streams_from: Vec::new(),
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
                    0 => Box::new(PipelineConsumer {
                        pipeline: handle.clone(),
                        keyed: false,
                    }),
                    _ => Box::new(|| {}),
                };
                vec![map.subscribe(tiling.universal_guard(), head, &mut scheduler)]
            })
            .collect();
        std::thread::scope(|scope| {
            let _fail = FailOnUnwind(&dispatcher);
            for worker_chains in chains.iter_mut().skip(1) {
                let (dispatcher, breakers) = (&dispatcher, std::slice::from_ref(&breaker));
                scope.spawn(move || run_worker(worker_chains, dispatcher, breakers));
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
    fn verify(chunks: &[Chunk], tile: &Tile, store: &LiveStore, sign: i64, context: &str) {
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
        let serial: Vec<(u64, i64)> = rows
            .iter()
            .map(|(&position, v)| (position, sign * v))
            .collect();
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
            -1,
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

    /// The answer of a two-pipeline run against the serial composition, and what the output owes:
    /// every row it held was released by the pipeline that read it, and it is complete.
    fn check_two_pipelines(chunks: Vec<Chunk>, threads: usize, morsel_rows: u64, pace: Pace) {
        let expected = chunks.clone();
        let (tile, store, output) = within_deadline(move || {
            run_two_pipelines(
                move |store, _| setup_delivery(store.clone(), chunks, threads, pace),
                LiveStore::new(),
                threads,
                morsel_rows,
            )
        });
        verify(
            &expected,
            &tile,
            &store,
            1,
            &format!("{threads} workers, {morsel_rows}-row morsels, two pipelines"),
        );
        assert!(
            output.is_complete(),
            "the breaker completed when its pipeline finished"
        );
        assert!(
            entries(&output.snapshot(&output.tiling().universal_guard())).is_empty(),
            "the pipeline behind the breaker released every row"
        );
    }

    /// `LiveRows → MapResult → Materialize → BreakerOutput → MapResult → Collect`, on one to
    /// eight workers, with arrivals in bursts: the answer is the serial composition, the source
    /// reclaimed every row once, and the breaker's output is empty and complete.
    #[test]
    fn a_pipeline_behind_a_breaker_equals_the_serial_composition() {
        for threads in WORKERS {
            for morsel_rows in [1, 4, 64] {
                check_two_pipelines(
                    chunks(&[50, 0, 1, 1, 200, 0, 3]),
                    threads,
                    morsel_rows,
                    Pace::Flat,
                );
            }
        }
    }

    /// The same under paced and out-of-order arrivals, where a key arrives ahead of an earlier
    /// one and the pipeline behind claims the keys the breaker has published, in any order.
    #[test]
    fn a_pipeline_behind_a_breaker_reads_arrivals_in_any_order() {
        for threads in WORKERS {
            check_two_pipelines(
                reversed(chunks(&[8, 8, 8, 8, 8])),
                threads,
                4,
                Pace::Interleaved,
            );
            check_two_pipelines(
                shuffled(chunks(&[5, 3, 9, 1, 12]), 7),
                threads,
                2,
                Pace::Flat,
            );
        }
    }

    /// Two operators read one breaker's output, each with a source and a consumer of its own:
    /// both answer the serial composition, and the rows leave once both have released them.
    #[test]
    fn two_pipelines_reading_one_breaker_each_see_every_row() {
        for threads in WORKERS {
            let rows = chunks(&[30, 0, 7, 100]);
            let expected = rows.clone();
            let (_, tiles, store, output) = within_deadline(move || {
                run_breaker(
                    move |store, _| setup_delivery(store.clone(), rows, threads, Pace::Flat),
                    LiveStore::new(),
                    threads,
                    4,
                    2,
                    false,
                )
            });
            assert_eq!(tiles.len(), 2);
            for tile in &tiles {
                verify(
                    &expected,
                    tile,
                    &store,
                    1,
                    &format!("{threads} workers, two readers"),
                );
            }
            assert!(output.is_complete());
            assert!(
                entries(&output.snapshot(&output.tiling().universal_guard())).is_empty(),
                "both readers released every row"
            );
        }
    }

    /// The result of a pipeline that ends in `Materialize` is its output once the pipelines that
    /// read it have released every row: empty, and complete.
    #[test]
    fn the_result_of_a_materializing_pipeline_is_its_released_output() {
        let rows = chunks(&[20, 5]);
        let (upstream, _, _, output) = within_deadline(move || {
            run_breaker(
                move |store, _| setup_delivery(store.clone(), rows, 2, Pace::Flat),
                LiveStore::new(),
                2,
                4,
                1,
                false,
            )
        });
        assert!(entries(&upstream).is_empty(), "{upstream:?}");
        assert!(upstream.is_terminal(), "{upstream:?}");
        assert!(output.is_complete());
    }

    /// A pipeline over a breaker's output that streams from none is refused, whatever it holds.
    #[test]
    #[should_panic(expected = "a pipeline over a breaker's output streams from the pipeline of")]
    fn a_breaker_headed_pipeline_that_streams_from_none_is_rejected() {
        let mut map = MapResult::new_at(
            Box::new(LiveRows::new(LiveStore::new())),
            Box::new(negate()),
            CurryLevel::new(1),
        );
        let runs = vec![PipelineRun {
            keyed: false,
            inherits: Vec::new(),
            source: source_of(&map).expect("a source"),
            breaker: collecting(&map),
            chain: &mut map,
            head: Head::Breaker,
            after: Vec::new(),
            streams_from: Vec::new(),
        }];
        let config = Config {
            threads: 1,
            morsel_rows: 4,
        };
        run_pipelines(&mut Scheduler::new(), runs, &config, None);
    }

    /// A pipeline over a data source that streams from another is refused: the dispatcher would
    /// wait on a region nothing publishes to it.
    #[test]
    #[should_panic(expected = "a pipeline over a data source streams from none")]
    fn a_source_headed_pipeline_that_streams_from_one_is_rejected() {
        let mut first = MapResult::new_at(
            Box::new(LiveRows::new(LiveStore::new())),
            Box::new(negate()),
            CurryLevel::new(1),
        );
        let mut second = MapResult::new_at(
            Box::new(LiveRows::new(LiveStore::new())),
            Box::new(negate()),
            CurryLevel::new(1),
        );
        let runs = vec![
            PipelineRun {
                keyed: false,
                inherits: Vec::new(),
                source: source_of(&first).expect("a source"),
                breaker: collecting(&first),
                chain: &mut first,
                head: Head::Source,
                after: Vec::new(),
                streams_from: Vec::new(),
            },
            PipelineRun {
                keyed: false,
                inherits: Vec::new(),
                source: source_of(&second).expect("a source"),
                breaker: collecting(&second),
                chain: &mut second,
                head: Head::Source,
                after: Vec::new(),
                streams_from: vec![PipelineId(0)],
            },
        ];
        let config = Config {
            threads: 1,
            morsel_rows: 4,
        };
        run_pipelines(&mut Scheduler::new(), runs, &config, None);
    }

    /// An upstream that delivers nothing: the pipeline behind starts when the one before
    /// finishes, reads an empty output, and finishes; the breaker completes.
    #[test]
    fn a_pipeline_behind_an_empty_breaker_reads_nothing_and_finishes() {
        for threads in WORKERS {
            check_two_pipelines(Vec::new(), threads, 4, Pace::Flat);
            check_two_pipelines(chunks(&[0, 0]), threads, 4, Pace::Flat);
        }
    }

    /// A chain that filters keys out publishes a region that names them: they have no row in the
    /// output, no morsel names them, and the pipeline behind reads exactly the rows that passed.
    /// The source reclaims every row it held, the filtered ones included.
    #[test]
    fn a_region_naming_filtered_out_keys_publishes_only_the_rows_that_passed() {
        for threads in WORKERS {
            let rows = chunks(&[40, 1, 25]);
            let expected = rows.clone();
            let (_, tiles, store, output) = within_deadline(move || {
                run_breaker(
                    move |store, _| setup_delivery(store.clone(), rows, threads, Pace::Flat),
                    LiveStore::new(),
                    threads,
                    4,
                    1,
                    true,
                )
            });
            let serial: Vec<(u64, i64)> = expected
                .iter()
                .flat_map(|chunk| {
                    chunk
                        .values
                        .iter()
                        .enumerate()
                        .map(|(offset, value)| (chunk.first + offset as u64, *value))
                })
                .filter(|(position, _)| position % 2 == 0)
                .collect();
            assert_eq!(entries(&tiles[0]), serial, "{threads} workers");
            assert_eq!(
                store.released.lock_wait().len(),
                66,
                "the source reclaimed every row it held"
            );
            assert!(output.is_complete());
        }
    }

    /// A worker of the pipeline before the breaker panics: the dispatcher fails, every worker
    /// returns, and the run re-raises the panic instead of hanging.
    #[test]
    fn a_panicking_worker_fails_a_two_pipeline_run() {
        for threads in WORKERS {
            let message = within_deadline(move || {
                let store = LiveStore::new();
                store.explodes.store(true, Ordering::Release);
                let rows = chunks(&[16, 16]);
                let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    run_two_pipelines(
                        move |store, _| setup_delivery(store.clone(), rows, threads, Pace::Flat),
                        store,
                        threads,
                        4,
                    )
                }));
                match outcome {
                    Ok(_) => None,
                    Err(panic) => panic.downcast_ref::<&str>().map(|m| m.to_string()),
                }
            });
            assert_eq!(
                message.as_deref(),
                Some("a worker panicked"),
                "{threads} workers"
            );
        }
    }

    /// A pipeline that waits on another and reads a source of its own is seeded and closed when
    /// the run starts, though it follows the other: the dispatcher keeps what was published until
    /// the pipeline starts, and the run finishes with every row of both.
    #[test]
    fn a_pipeline_that_follows_another_over_its_own_source_is_seeded_and_closed() {
        for threads in WORKERS {
            let (first_rows, second_rows) = (chunks(&[20, 5]), chunks(&[3, 40]));
            let (first, second) = (LiveStore::new(), LiveStore::new());
            for (store, rows) in [(&first, &first_rows), (&second, &second_rows)] {
                for chunk in rows {
                    store.append(chunk);
                }
                store.closed.store(true, Ordering::Release);
            }
            let (mut one, mut two) = (
                MapResult::new_at(
                    Box::new(LiveRows::new(first.clone())),
                    Box::new(negate()),
                    CurryLevel::new(1),
                ),
                MapResult::new_at(
                    Box::new(LiveRows::new(second.clone())),
                    Box::new(negate()),
                    CurryLevel::new(1),
                ),
            );
            let tiles = within_deadline(move || {
                let runs = vec![
                    PipelineRun {
                        keyed: false,
                        inherits: Vec::new(),
                        source: source_of(&one).expect("a source"),
                        breaker: collecting(&one),
                        chain: &mut one,
                        head: Head::Source,
                        after: Vec::new(),
                        streams_from: Vec::new(),
                    },
                    PipelineRun {
                        keyed: false,
                        inherits: Vec::new(),
                        source: source_of(&two).expect("a source"),
                        breaker: collecting(&two),
                        chain: &mut two,
                        head: Head::Source,
                        after: vec![PipelineId(0)],
                        streams_from: Vec::new(),
                    },
                ];
                let config = Config {
                    threads,
                    morsel_rows: 4,
                };
                run_pipelines(&mut Scheduler::new(), runs, &config, None)
            });
            for (tile, rows) in tiles.iter().zip([first_rows, second_rows]) {
                let serial: Vec<(u64, i64)> = rows
                    .iter()
                    .flat_map(|chunk| {
                        chunk
                            .values
                            .iter()
                            .enumerate()
                            .map(|(offset, value)| (chunk.first + offset as u64, -value))
                    })
                    .collect();
                assert_eq!(entries(tile), serial, "{threads} workers");
            }
        }
    }

    /// A morsel of the pipeline behind the breaker runs, and its rows are released, while the
    /// pipeline before it is still open: the first chunk passes through both pipelines before
    /// the delivering thread closes the source, and the breaker is not complete until then.
    #[test]
    fn a_morsel_behind_the_breaker_runs_before_the_pipeline_before_it_finishes() {
        let chunk = chunks(&[16]).remove(0);
        let last = chunk.values.len() as u64 - 1;
        let expected = vec![chunk.clone()];
        let (tile, store, output) = within_deadline(move || {
            run_two_pipelines(
                move |store, output| {
                    let (store, output) = (store.clone(), output.clone());
                    Box::new(move |handle, _scheduler| {
                        let region = store.append(&chunk).expect("a chunk with rows");
                        store.notify_all(
                            &Projection::of(&keys_between(region.0, region.1)).unwrap(),
                        );
                        wait_for(
                            "the pipeline behind the breaker released the first chunk",
                            &handle.dispatcher,
                            || {
                                output.ready().contains(&Value::UInt(last))
                                    && entries(&output.snapshot(&keys_between(0, last))).is_empty()
                            },
                        );
                        assert!(
                            !output.is_complete(),
                            "the pipeline before the breaker is still open"
                        );
                        store.closed.store(true, Ordering::Release);
                    })
                },
                LiveStore::new(),
                2,
                4,
            )
        });
        verify(
            &expected,
            &tile,
            &store,
            1,
            "the first chunk, then the close",
        );
        assert!(output.is_complete());
    }

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
                -1,
                &format!("{threads} chains, the first idle"),
            );
        }
    }
}
