//! A real data source through the pool, end to end: `[x + 1 for x in source1()]` is compiled
//! over a `TestDataSource`, whose keys are sparse and arrive out of order in chunks. The calling
//! thread delivers them, writing rows and the yield predicate to the source and telling the
//! scheduler, and the workers claim, map and release them into the collecting breaker.
//! See `src/interpreter/design-parallel.md`, "The dispatcher".

// The shared-state check skips `#[cfg(test)]` items, and this file holds nothing else.
#[cfg(test)]
mod source_end_to_end {
    use std::sync::mpsc;
    use std::time::{Duration, Instant};

    use intervalsets::{Interval, IntervalSet};

    use super::super::*;
    use crate::ccl::context::{GlobalContext, compile_program};
    use crate::ccl::load::LoadedProgram;
    use crate::interpreter::tile_operators::points;
    use crate::interpreter::{BaseType, ColumnValue, Extent, Predicate, TestDataSource, Value};

    /// The key and the value a row holds.
    #[derive(Clone)]
    struct Row {
        key: Value,
        value: i64,
    }

    /// Rows that are delivered together.
    type Chunk = Vec<Row>;

    /// How the calling thread paces its deliveries.
    #[derive(Clone, Copy)]
    enum Pace {
        /// One delivery right after another.
        Flat,
        /// Every worker is parked before a delivery, and a delivery that adds rows without making
        /// them ready is given time to show that nothing claims them. The next delivery waits for
        /// the workers to release what is ready.
        Lockstep,
    }

    fn int_rows(keys: &[i64]) -> Chunk {
        keys.iter()
            .map(|&key| Row {
                key: Value::Int(key),
                value: key * 3 % 17,
            })
            .collect()
    }

    fn string_rows(keys: &[&str]) -> Chunk {
        keys.iter()
            .enumerate()
            .map(|(n, key)| Row {
                key: Value::String((*key).into()),
                value: 5 * n as i64 + 2,
            })
            .collect()
    }

    fn sorted(mut rows: Vec<(Value, i64)>) -> Vec<(Value, i64)> {
        rows.sort_by(|a, b| a.0.partial_cmp(&b.0).expect("keys of one extent compare"));
        rows
    }

    /// What the sink holds: each key with the value it was mapped to.
    fn entries(tile: &Tile) -> Vec<(Value, i64)> {
        if tile.is_empty() {
            return Vec::new();
        }
        let Tile::DataFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("a collection, got {tile:?}");
        };
        let Tile::Scalar(ColumnValue::Ints(values)) = &**codomain else {
            panic!("integer values, got {codomain:?}");
        };
        sorted(
            (0..domain.len())
                .map(|row| (domain.index_at(row), values[row]))
                .collect(),
        )
    }

    /// Wait for the source to hold nothing, which only a worker that claimed, pulled, merged and
    /// released every row can bring about. A pool that failed stops the wait, and the worker's
    /// panic is the one raised.
    fn wait_until_released(source: &Mutex<TestDataSource>, dispatcher: &Dispatcher, cause: &str) {
        let deadline = Instant::now() + Duration::from_secs(30);
        while source.lock_wait().retained_keys() > 0 {
            assert!(
                !dispatcher.failed.load(Ordering::Acquire),
                "a worker failed while waiting: {cause}"
            );
            assert!(Instant::now() < deadline, "{cause}");
            std::thread::yield_now();
        }
    }

    fn wait_for_every_worker_to_park(dispatcher: &Dispatcher, threads: usize) {
        let deadline = Instant::now() + Duration::from_secs(30);
        while dispatcher.parked.load(Ordering::Acquire) < threads {
            assert!(
                !dispatcher.failed.load(Ordering::Acquire),
                "a worker failed while the others were parked"
            );
            assert!(
                Instant::now() < deadline,
                "every worker parked: a worker is stuck outside `park`"
            );
            std::thread::yield_now();
        }
    }

    /// What the yield predicate is made of.
    #[derive(Clone, Copy)]
    enum Yield {
        /// Exactly the keys that arrived.
        Points,
        /// The interval from the smallest key to the largest that arrived, which is complete
        /// where no key arrives out of order.
        Prefix,
    }

    fn new_source(key_extent: Extent) -> Arc<Mutex<TestDataSource>> {
        Arc::new(Mutex::new(
            TestDataSource::new(
                "source1",
                crate::ccl::Type::Base(BaseType::Int),
                Extent::Base(BaseType::Int),
            )
            .with_key_extent(key_extent),
        ))
    }

    /// Compile `[x + 1 for x in source1()]` over a source of `key_extent` keys, deliver `chunks` in
    /// the order given while `threads` workers run, and return what the sink holds and the source.
    ///
    /// A chunk is delivered in two steps, as a real source's rows precede its yield predicate: the
    /// rows are written and the scheduler told, and then the chunk's keys join the yield
    /// predicate and the scheduler is told again. Before the chunk that holds the smallest key is
    /// delivered after another, the workers must have released everything delivered so far,
    /// which they can only have done by claiming a later chunk while an earlier one was missing.
    fn run(
        chunks: Vec<Chunk>,
        key_extent: Extent,
        threads: usize,
        morsel_rows: u64,
        pace: Pace,
        yield_as: Yield,
    ) -> (Tile, Arc<Mutex<TestDataSource>>) {
        let source = new_source(key_extent);
        let tile = run_over(source.clone(), chunks, threads, morsel_rows, pace, yield_as);
        (tile, source)
    }

    /// [`run`] over a source the caller made.
    fn run_over(
        source: Arc<Mutex<TestDataSource>>,
        chunks: Vec<Chunk>,
        threads: usize,
        morsel_rows: u64,
        pace: Pace,
        yield_as: Yield,
    ) -> Tile {
        run_program_over(
            "[x + 1 for x in source1()]",
            source,
            chunks,
            threads,
            morsel_rows,
            pace,
            yield_as,
        )
    }

    /// [`run_over`] for the program `code`, which reads `source1()`.
    fn run_program_over(
        code: &str,
        source: Arc<Mutex<TestDataSource>>,
        chunks: Vec<Chunk>,
        threads: usize,
        morsel_rows: u64,
        pace: Pace,
        yield_as: Yield,
    ) -> Tile {
        let mut ctx = GlobalContext::default();
        ctx.register_source(source.clone());
        let loaded = LoadedProgram::test(code);
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let mut compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
        let smallest = chunks
            .iter()
            .flatten()
            .map(|row| row.key.clone())
            .min_by(|a, b| a.partial_cmp(b).expect("keys compare"));

        let delivered = source.clone();
        let delivery: DeliveringThread<'_> = Box::new(move |handle, scheduler| {
            let mut ready = Predicate::False;
            let mut arrived: Vec<Value> = Vec::new();
            for chunk in &chunks {
                let keys: Vec<Value> = chunk.iter().map(|row| row.key.clone()).collect();
                if let Pace::Lockstep = pace {
                    wait_for_every_worker_to_park(&handle.dispatcher, threads);
                }
                if smallest.as_ref().is_some_and(|k| keys.contains(k)) && !ready.is_false() {
                    wait_until_released(
                        &delivered,
                        &handle.dispatcher,
                        "no later chunk was claimable while the smallest key was missing",
                    );
                }
                // The rows arrive and the source says so; their keys are not yet in its yield
                // predicate, so nothing may claim them.
                delivered.lock_wait().add_data(
                    &chunk
                        .iter()
                        .map(|row| (row.key.clone(), Value::Int(row.value)))
                        .collect::<Vec<_>>(),
                );
                scheduler.check_for_notifications();
                if let Pace::Lockstep = pace {
                    std::thread::sleep(Duration::from_millis(10));
                    assert!(
                        delivered.lock_wait().retained_keys() >= chunk.len(),
                        "a row was claimed before its key was in the yield predicate"
                    );
                }
                // Now the keys are ready.
                ready = match yield_as {
                    Yield::Points => ready.union(&points(&keys)),
                    Yield::Prefix => {
                        arrived.extend(keys.iter().cloned());
                        let largest = arrived
                            .iter()
                            .max_by(|a, b| a.partial_cmp(b).expect("keys compare"))
                            .expect("a chunk holds a key");
                        Predicate::intervals(IntervalSet::from(Interval::closed(
                            smallest.clone().expect("a key arrived"),
                            largest.clone(),
                        )))
                    }
                };
                delivered.lock_wait().set_yield_predicate(ready.clone());
                // The delivering thread knows the keys it wrote, so it names them: the region
                // reaches the pipeline's head through operators that keep keys.
                scheduler.notify_source_consumers("source1", &Projection::admitting(points(&keys)));
                if let Pace::Lockstep = pace {
                    wait_until_released(
                        &delivered,
                        &handle.dispatcher,
                        "the workers did not release the rows that arrived: a lost wake-up",
                    );
                }
            }
        });
        let config = Config {
            threads,
            morsel_rows,
        };
        run_main_delivering(&mut ctx, &mut compiled, &mut None, &config, Some(delivery))
            .expect("the program is a morsel pipeline")
    }

    /// Run on a thread of its own: a panic in it, a worker's included, is raised again here, and a
    /// run that does not finish within a minute fails as a lost wake-up.
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

    /// Check a run against the serial answer and the release it owes: the sink holds every row
    /// once, mapped, and the source reclaimed every key a worker finished with.
    fn check(chunks: Vec<Chunk>, key_extent: Extent, threads: usize, morsel_rows: u64, pace: Pace) {
        check_yielding(
            chunks,
            key_extent,
            threads,
            morsel_rows,
            pace,
            Yield::Points,
        );
    }

    fn check_yielding(
        chunks: Vec<Chunk>,
        key_extent: Extent,
        threads: usize,
        morsel_rows: u64,
        pace: Pace,
        yield_as: Yield,
    ) {
        let expected = sorted(
            chunks
                .iter()
                .flatten()
                .map(|row| (row.key.clone(), row.value + 1))
                .collect(),
        );
        let (tile, source) =
            within_deadline(move || run(chunks, key_extent, threads, morsel_rows, pace, yield_as));
        assert_eq!(
            entries(&tile),
            expected,
            "{threads} workers, {morsel_rows}-key morsels"
        );
        assert_eq!(
            source.lock_wait().retained_keys(),
            0,
            "the source reclaimed every key the sink acknowledged"
        );
    }

    /// A value the program names and reads is a breaker between two pipelines, and the serial
    /// chain the program subscribed when it compiled holds release records with the source: the
    /// pool drops it when it cuts, so the source ends with no record and no retained key, under
    /// delivery that waits for the workers to release each chunk as well as under delivery that
    /// does not.
    #[test]
    fn a_shared_value_over_a_source_leaves_no_record_and_no_key() {
        for pace in [Pace::Flat, Pace::Lockstep] {
            for threads in [1, 2, 4] {
                let chunks = vec![int_rows(&[1, 2, 3]), int_rows(&[7, 8]), int_rows(&[5])];
                let expected = sorted(
                    chunks
                        .iter()
                        .flatten()
                        .map(|row| (row.key.clone(), (row.value + 1) * 2))
                        .collect(),
                );
                let source = new_source(Extent::Base(BaseType::Int));
                let held = source.clone();
                let tile = within_deadline(move || {
                    run_program_over(
                        "xs = [x + 1 for x in source1()]\n[a * 2 for a in xs]",
                        source,
                        chunks,
                        threads,
                        1,
                        pace,
                        Yield::Points,
                    )
                });
                assert_eq!(entries(&tile), expected, "{threads} workers");
                assert_eq!(held.lock_wait().retained_keys(), 0, "{threads} workers");
                assert_eq!(
                    held.lock_wait().release_records(),
                    0,
                    "{threads} workers: no record is left with the source"
                );
            }
        }
    }

    /// A filter over a source reads each key's value twice, at the iterated key: a keyed read of
    /// the memo the source's rows fill. On four workers with one-key morsels and chunks that arrive
    /// out of order, under both paces, the sink holds the rows the filter keeps, mapped, and the
    /// source ends with no record and no retained key.
    #[test]
    fn a_keyed_read_over_a_source_runs_on_four_workers() {
        for pace in [Pace::Flat, Pace::Lockstep] {
            for threads in [1, 4] {
                let chunks = vec![int_rows(&[1, 2, 3]), int_rows(&[7, 8]), int_rows(&[5])];
                let expected = sorted(
                    chunks
                        .iter()
                        .flatten()
                        .filter(|row| row.value > 5)
                        .map(|row| (row.key.clone(), row.value * 2))
                        .collect(),
                );
                let source = new_source(Extent::Base(BaseType::Int));
                let held = source.clone();
                let tile = within_deadline(move || {
                    run_program_over(
                        "xs = source1()\n[y * 2 for y in xs if y > 5]",
                        source,
                        chunks,
                        threads,
                        1,
                        pace,
                        Yield::Points,
                    )
                });
                assert_eq!(entries(&tile), expected, "{threads} workers");
                assert_eq!(held.lock_wait().retained_keys(), 0, "{threads} workers");
                assert_eq!(
                    held.lock_wait().release_records(),
                    0,
                    "{threads} workers: no record is left with the source"
                );
            }
        }
    }

    fn reversed(mut chunks: Vec<Chunk>) -> Vec<Chunk> {
        chunks.reverse();
        chunks
    }

    /// `chunks` in a fixed pseudo-random order that does not deliver the chunk of the smallest key
    /// first, whatever the type of the keys.
    fn shuffled(mut chunks: Vec<Chunk>, seed: u64) -> Vec<Chunk> {
        let smallest = chunks
            .iter()
            .flatten()
            .map(|row| row.key.clone())
            .min_by(|a, b| a.partial_cmp(b).expect("keys compare"))
            .expect("a chunk holds a key");
        let mut state = seed | 1;
        for i in (1..chunks.len()).rev() {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            chunks.swap(i, (state % (i as u64 + 1)) as usize);
        }
        if chunks[0].iter().any(|row| row.key == smallest) {
            let last = chunks.len() - 1;
            chunks.swap(0, last);
        }
        chunks
    }

    const WORKERS: [usize; 4] = [1, 2, 4, 8];

    fn sparse_int_chunks() -> Vec<Chunk> {
        vec![
            int_rows(&[10, 20]),
            int_rows(&[35]),
            int_rows(&[41, 90]),
            int_rows(&[120, 7_000]),
        ]
    }

    fn string_chunks() -> Vec<Chunk> {
        vec![
            string_rows(&["apple", "banana"]),
            string_rows(&["kiwi"]),
            string_rows(&["pear", "plum"]),
            string_rows(&["zucchini"]),
        ]
    }

    #[test]
    fn sparse_integer_keys_that_arrive_in_order_are_mapped_once_and_released() {
        for threads in WORKERS {
            for morsel_rows in [1, 2, 64] {
                check(
                    sparse_int_chunks(),
                    Extent::Base(BaseType::Int),
                    threads,
                    morsel_rows,
                    Pace::Flat,
                );
            }
        }
    }

    /// The chunk of the smallest keys arrives last, so the workers claim the others first.
    #[test]
    fn sparse_integer_keys_that_arrive_in_reverse_are_claimed_ahead_of_the_missing_first_chunk() {
        for threads in WORKERS {
            for morsel_rows in [1, 2, 64] {
                check(
                    reversed(sparse_int_chunks()),
                    Extent::Base(BaseType::Int),
                    threads,
                    morsel_rows,
                    Pace::Flat,
                );
            }
        }
    }

    #[test]
    fn sparse_integer_keys_that_arrive_shuffled_are_mapped_once_and_released() {
        for threads in WORKERS {
            for seed in [0x9e37_79b9_7f4a_7c15, 7, 123_456_789] {
                check(
                    shuffled(sparse_int_chunks(), seed),
                    Extent::Base(BaseType::Int),
                    threads,
                    2,
                    Pace::Flat,
                );
            }
        }
    }

    /// A second key type: strings, which are ordered and not positions.
    #[test]
    fn string_keys_that_arrive_out_of_order_are_mapped_once_and_released() {
        for threads in WORKERS {
            for order in [reversed(string_chunks()), shuffled(string_chunks(), 99)] {
                check(
                    order,
                    Extent::Base(BaseType::String),
                    threads,
                    2,
                    Pace::Flat,
                );
            }
        }
    }

    /// Every worker is parked before a delivery, so the notification has to wake one, and rows
    /// that are written before their keys are ready claim nothing.
    #[test]
    fn a_parked_worker_wakes_for_each_delivery_and_claims_nothing_that_is_not_ready() {
        for threads in WORKERS {
            check(
                reversed(sparse_int_chunks()),
                Extent::Base(BaseType::Int),
                threads,
                2,
                Pace::Lockstep,
            );
            check(
                string_chunks(),
                Extent::Base(BaseType::String),
                threads,
                1,
                Pace::Lockstep,
            );
        }
    }

    /// The same run, repeatedly, for the interleavings a single run misses.
    #[test]
    fn repeated_runs_agree_with_the_serial_answer() {
        for round in 0..200u64 {
            let pace = if round % 3 == 2 {
                Pace::Lockstep
            } else {
                Pace::Flat
            };
            let order = match round % 2 {
                0 => reversed(sparse_int_chunks()),
                _ => shuffled(sparse_int_chunks(), round + 3),
            };
            check(order, Extent::Base(BaseType::Int), 4, 2, pace);
        }
    }

    /// A yield predicate that is an interval, as a source reports it by position, and not the
    /// keys that arrived: the chunks arrive in order, so what the interval covers is complete.
    #[test]
    fn a_yield_predicate_of_intervals_is_claimed_like_one_of_points() {
        for threads in WORKERS {
            check_yielding(
                sparse_int_chunks(),
                Extent::Base(BaseType::Int),
                threads,
                2,
                Pace::Flat,
                Yield::Prefix,
            );
        }
    }

    /// A source that says it cannot cut morsels is refused by the pool, and the program then runs
    /// on the compiling thread through the scheduler loop and answers as a serial run does.
    #[test]
    fn a_source_that_cannot_cut_morsels_runs_serially_and_answers() {
        let source = Arc::new(Mutex::new(
            TestDataSource::new(
                "source1",
                crate::ccl::Type::Base(BaseType::Int),
                Extent::Base(BaseType::Int),
            )
            .declining_morsels(),
        ));
        source.lock_wait().add_data(&[
            (Value::UInt(1), Value::Int(10)),
            (Value::UInt(2), Value::Int(20)),
            (Value::UInt(3), Value::Int(30)),
        ]);
        source.lock_wait().set_yield_predicate(Predicate::True);
        let mut ctx = GlobalContext::default();
        ctx.register_source(source);
        let loaded = LoadedProgram::test("[x + 1 for x in source1()]");
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let mut compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
        let config = Config {
            threads: 2,
            morsel_rows: 2,
        };
        let refused = run_main(&mut ctx, &mut compiled, &config)
            .expect_err("a source that cannot cut morsels is not a morsel pipeline");
        assert!(
            refused.to_string().contains("cut into morsels"),
            "{refused}"
        );

        let producer = compiled
            .main_mut()
            .and_then(|output| output.producer.as_mut())
            .expect("the program keeps the producer the scheduler loop drives");
        let tile = crate::interpreter::pull_laps(ctx.scheduler(), producer.as_mut(), 8, |tile| {
            !tile.is_empty()
        });
        assert_eq!(
            entries(&tile),
            [
                (Value::UInt(1), 11),
                (Value::UInt(2), 21),
                (Value::UInt(3), 31)
            ]
        );
    }

    /// A worker that fails reading the source stops the pool without an abort, the panic is the
    /// worker's own, and the pool's release records are gone.
    #[test]
    fn a_worker_that_fails_to_read_the_source_surfaces_its_panic_and_retires_the_records() {
        let source = new_source(Extent::Base(BaseType::Int));
        source.lock_wait().fail_to_get();
        let delivered = source.clone();
        let failure = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            within_deadline(move || {
                run_over(
                    delivered,
                    sparse_int_chunks(),
                    4,
                    1,
                    Pace::Flat,
                    Yield::Points,
                )
            })
        }))
        .expect_err("a worker's panic fails the run");
        let message = failure
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| failure.downcast_ref::<&str>().map(|s| (*s).to_string()))
            .expect("a panic message");
        assert!(
            message.contains("the source failed to read source1"),
            "the worker's own panic, not a join failure: {message}"
        );
        assert_eq!(
            source.lock_wait().release_records(),
            0,
            "the pool's release records retired with the pool"
        );
    }
}
