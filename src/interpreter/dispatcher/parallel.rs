//! Experimental whole-pipeline execution. See `src/interpreter/design-parallel-dispatcher.md`,
//! "Ownership and execution". This harness is not selected by the compiled-program planner.

use std::sync::mpsc::{self, SyncSender};
use std::thread;

use super::{Dispatcher, Next, PipelineId, WorkPackage};
use crate::interpreter::TileGuard;

/// An exclusive runtime instance. Implementations read their inputs and release through their
/// own producer wrappers; the coordinator receives no input or output tiles.
trait Pipeline: Send {
    fn consume(&mut self, guard: &TileGuard);
}

struct Job {
    claim: WorkPackage,
    instance: Box<dyn Pipeline>,
}

struct Completed {
    slot: usize,
    job: Job,
    failed: bool,
}

/// Keep a separate slot per worker so capacity remains bounded, including returned instances.
fn worker(slot: usize, jobs: mpsc::Receiver<Job>, done: SyncSender<Completed>) {
    for mut job in jobs {
        let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            super::in_a_run(|| job.instance.consume(&job.claim.guard));
        }))
        .is_err();
        if done.send(Completed { slot, job, failed }).is_err() {
            break;
        }
    }
}

/// Run a finite, already-admitted prototype graph. Publication and finish remain serialized.
/// Instances are returned even on failure so teardown never races a worker still using them.
fn run(
    dispatcher: &Dispatcher,
    instances: &mut [Vec<Box<dyn Pipeline>>],
    workers: usize,
    mut publish: impl FnMut(PipelineId, &TileGuard, bool),
) -> Result<(), &'static str> {
    assert!(workers > 0);
    thread::scope(|scope| {
        let (done_tx, done_rx) = mpsc::sync_channel(workers);
        let mut senders = Vec::new();
        for slot in 0..workers {
            let (tx, rx) = mpsc::sync_channel(1);
            let done = done_tx.clone();
            scope.spawn(move || worker(slot, rx, done));
            senders.push(tx);
        }
        drop(done_tx);
        let mut idle: Vec<_> = (0..workers).collect();
        let mut active = 0;
        let mut failed = false;
        loop {
            if dispatcher.failed.load(std::sync::atomic::Ordering::SeqCst) {
                failed = true;
            }
            while let Ok(completed) = done_rx.try_recv() {
                if dispatcher.failed.load(std::sync::atomic::Ordering::SeqCst) {
                    failed = true;
                }
                let Completed {
                    slot,
                    job,
                    failed: error,
                } = completed;
                active -= 1;
                instances[job.claim.pipeline.0].push(job.instance);
                idle.push(slot);
                if error
                    || !failed
                        && std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            publish(job.claim.pipeline, &job.claim.guard, false);
                            if !dispatcher.failed.load(std::sync::atomic::Ordering::SeqCst) {
                                dispatcher.acknowledge(job.claim);
                            }
                        }))
                        .is_err()
                {
                    failed = true;
                    dispatcher.fail();
                }
            }
            if dispatcher.failed.load(std::sync::atomic::Ordering::SeqCst) {
                failed = true;
            }
            if failed && active == 0 {
                break;
            }
            if !failed && !idle.is_empty() {
                let next = instances
                    .iter()
                    .enumerate()
                    .filter(|(_, available)| !available.is_empty())
                    .find_map(|(p, _)| dispatcher.claim_from(p))
                    .map(Next::Package)
                    .or_else(|| {
                        (0..instances.len()).find_map(|p| {
                            dispatcher.try_begin_finish(p).then(|| Next::Finish {
                                pipeline: PipelineId(p),
                                consumed: dispatcher.states[p].queue.region(),
                            })
                        })
                    })
                    .unwrap_or_else(|| {
                        if dispatcher.failed.load(std::sync::atomic::Ordering::SeqCst) {
                            Next::Failed
                        } else if dispatcher
                            .unfinished
                            .load(std::sync::atomic::Ordering::Acquire)
                            == 0
                        {
                            Next::Done
                        } else {
                            Next::Wait(super::Generation(
                                dispatcher
                                    .generation
                                    .load(std::sync::atomic::Ordering::SeqCst),
                            ))
                        }
                    });
                match next {
                    Next::Package(claim) => {
                        if let Some(instance) = instances[claim.pipeline.0].pop() {
                            let slot = idle.pop().expect("a worker is available");
                            senders[slot]
                                .send(Job { claim, instance })
                                .unwrap_or_else(|_| {
                                    panic!("a live prototype worker accepts its job")
                                });
                            active += 1;
                            continue;
                        }
                        unreachable!("admission reserves an available instance");
                    }
                    Next::Finish { pipeline, consumed } => {
                        let guard = consumed
                            .unwrap_or(TileGuard::Scalar(crate::interpreter::Predicate::False));
                        if std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            publish(pipeline, &guard, true);
                            if !dispatcher.failed.load(std::sync::atomic::Ordering::SeqCst) {
                                dispatcher.finish(dispatcher.pushes(pipeline));
                            }
                        }))
                        .is_err()
                        {
                            failed = true;
                            dispatcher.fail();
                        }
                        continue;
                    }
                    Next::Done => break,
                    Next::Failed => {
                        failed = true;
                    }
                    Next::Wait(_) => {}
                }
            }
            if active != 0 {
                let completed = done_rx.recv().expect("active workers report completion");
                active -= 1;
                instances[completed.job.claim.pipeline.0].push(completed.job.instance);
                idle.push(completed.slot);
                if dispatcher.failed.load(std::sync::atomic::Ordering::SeqCst) {
                    failed = true;
                }
                if completed.failed
                    || !failed
                        && std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            publish(
                                completed.job.claim.pipeline,
                                &completed.job.claim.guard,
                                false,
                            );
                            if !dispatcher.failed.load(std::sync::atomic::Ordering::SeqCst) {
                                dispatcher.acknowledge(completed.job.claim);
                            }
                        }))
                        .is_err()
                {
                    failed = true;
                    dispatcher.fail();
                }
            } else if !failed {
                dispatcher.fail();
                failed = true;
            }
        }
        drop(senders);
        if failed {
            Err("parallel pipeline failed or stalled")
        } else {
            Ok(())
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::keys_between;
    use crate::interpreter::{ColumnValue, FunctionGuard, Tile, Value};
    use intervalsets::Bounding;
    use std::collections::{BTreeMap, HashMap};
    use std::sync::{Arc, Barrier, Mutex};
    use std::time::Instant;

    /// Retained positional integer rows. Readers exchange Tiles and release exact regions.
    /// This prototype supports one logical reader, split into disjoint claim-local instances.
    #[derive(Default)]
    struct Rows(Mutex<BTreeMap<u64, i64>>);

    impl Rows {
        fn get(&self, guard: &TileGuard) -> Tile {
            let TileGuard::Function(FunctionGuard::Domain(region)) = guard else {
                panic!("the prototype reads positional domain guards")
            };
            let (first, last) = bounds(guard);
            let rows = self.0.lock().unwrap();
            let (keys, values): (Vec<_>, Vec<_>) = rows
                .range(first..=last)
                .map(|(key, value)| (*key, *value))
                .unzip();
            Tile::data_function(
                ColumnValue::UInts(keys),
                Box::new(Tile::Scalar(ColumnValue::Ints(values))),
                region.clone(),
                Default::default(),
            )
        }

        fn insert(&self, tile: Tile) {
            let (keys, values) = unpack(tile);
            let mut rows = self.0.lock().unwrap();
            for (key, value) in keys.into_iter().zip(values) {
                assert!(
                    rows.insert(key, value).is_none(),
                    "each input position is applied once"
                );
            }
        }

        fn release(&self, guard: &TileGuard) {
            let (first, last) = bounds(guard);
            let mut rows = self.0.lock().unwrap();
            let keys: Vec<_> = rows.range(first..=last).map(|(key, _)| *key).collect();
            for key in keys {
                rows.remove(&key);
            }
        }
    }

    fn bounds(guard: &TileGuard) -> (u64, u64) {
        let TileGuard::Function(FunctionGuard::Domain(crate::interpreter::Predicate::Intervals(
            region,
        ))) = guard
        else {
            panic!("the prototype supports a closed contiguous UInt range")
        };
        let (Some(Value::UInt(first)), Some(Value::UInt(last))) = (region.lval(), region.rval())
        else {
            panic!("bounded UInt range")
        };
        assert_eq!(
            guard,
            &keys_between(*first, *last),
            "the range is exact and closed"
        );
        (*first, *last)
    }

    fn unpack(tile: Tile) -> (Vec<u64>, Vec<i64>) {
        let Tile::DataFunction {
            domain: ColumnValue::UInts(keys),
            codomain,
            ..
        } = tile
        else {
            panic!("a positional integer tile")
        };
        let Tile::Scalar(ColumnValue::Ints(values)) = *codomain else {
            panic!("integer values")
        };
        (keys, values)
    }

    trait Input: Send {
        fn get(&mut self, guard: &TileGuard) -> Tile;
        fn release(&mut self, guard: &TileGuard);
    }

    struct Reader(Arc<Rows>);
    impl Input for Reader {
        fn get(&mut self, guard: &TileGuard) -> Tile {
            self.0.get(guard)
        }
        fn release(&mut self, guard: &TileGuard) {
            self.0.release(guard);
        }
    }

    /// An owned inline operator. The caller traverses Reader → Map in its own worker.
    struct Map {
        input: Box<dyn Input>,
        iterations: usize,
        rendezvous: Option<Arc<Barrier>>,
        panic: bool,
    }
    impl Input for Map {
        fn get(&mut self, guard: &TileGuard) -> Tile {
            if let Some(barrier) = self.rendezvous.take() {
                barrier.wait();
            }
            assert!(!self.panic, "injected pipeline failure");
            let mut tile = self.input.get(guard);
            let Tile::DataFunction { codomain, .. } = &mut tile else {
                unreachable!()
            };
            let Tile::Scalar(ColumnValue::Ints(values)) = &mut **codomain else {
                unreachable!()
            };
            for value in values {
                for _ in 0..self.iterations {
                    *value = value.wrapping_mul(1664525).wrapping_add(1013904223);
                }
                *value &= 0x7fff;
            }
            tile
        }
        fn release(&mut self, guard: &TileGuard) {
            self.input.release(guard);
        }
    }

    struct Memo {
        input: Box<dyn Input>,
        output: Arc<Rows>,
    }
    impl Pipeline for Memo {
        fn consume(&mut self, guard: &TileGuard) {
            let tile = self.input.get(guard);
            self.output.insert(tile);
            self.input.release(guard);
        }
    }

    #[derive(Default)]
    struct Groups(Mutex<HashMap<u64, i64>>);
    struct GroupSum {
        input: Box<dyn Input>,
        output: Arc<Groups>,
    }
    impl Pipeline for GroupSum {
        fn consume(&mut self, guard: &TileGuard) {
            let (keys, values) = unpack(self.input.get(guard));
            {
                let mut groups = self.output.0.lock().unwrap();
                for (key, value) in keys.into_iter().zip(values) {
                    *groups.entry(key % 64).or_default() += value;
                }
            }
            self.input.release(guard);
        }
    }

    fn experiment(
        rows: usize,
        work: usize,
        workers: usize,
        barrier: bool,
        fail: bool,
    ) -> (Result<(), &'static str>, HashMap<u64, i64>, usize, usize) {
        let source = Arc::new(Rows(Mutex::new(
            (0..rows as u64).map(|key| (key, key as i64)).collect(),
        )));
        let memo = Arc::new(Rows::default());
        let groups = Arc::new(Groups::default());
        let rendezvous = barrier.then(|| Arc::new(Barrier::new(workers)));
        let mut instances: Vec<Vec<Box<dyn Pipeline>>> = vec![Vec::new(), Vec::new()];
        for _ in 0..workers {
            instances[0].push(Box::new(Memo {
                input: Box::new(Map {
                    input: Box::new(Reader(source.clone())),
                    iterations: work,
                    rendezvous: rendezvous.clone(),
                    panic: fail,
                }),
                output: memo.clone(),
            }));
            instances[1].push(Box::new(GroupSum {
                input: Box::new(Reader(memo.clone())),
                output: groups.clone(),
            }));
        }
        let dispatcher = Dispatcher::new(vec![vec![], vec![0]], 1024);
        // Explicit morsels make this experiment independent of shape construction on workers.
        for start in (0..rows).step_by(1024) {
            dispatcher.notify(
                PipelineId(0),
                &keys_between(start as u64, (start + 1024).min(rows) as u64 - 1),
            );
        }
        dispatcher.close(PipelineId(0));
        let result = run(
            &dispatcher,
            &mut instances,
            workers,
            |pipeline, guard, finishing| {
                if pipeline.0 == 0 && !finishing {
                    let mut pushes = dispatcher.pushes(pipeline);
                    pushes.push(guard, |guard, _| vec![guard.clone()]);
                    dispatcher.land(pushes);
                }
            },
        );
        let answer = groups.0.lock().unwrap().clone();
        let retained = source.0.lock().unwrap().len() + memo.0.lock().unwrap().len();
        (
            result,
            answer,
            retained,
            instances.iter().map(Vec::len).sum(),
        )
    }

    #[test]
    fn whole_chains_overlap_and_match_serial_with_exact_release() {
        let serial = experiment(16384, 8, 1, false, false);
        let parallel = experiment(16384, 8, 4, true, false);
        assert_eq!(serial.0, Ok(()));
        assert_eq!(parallel.0, Ok(()));
        assert_eq!(parallel.1, serial.1);
        assert_eq!(parallel.2, 0);
        assert_eq!(parallel.3, 8);
        assert_eq!(
            serial.1.values().sum::<i64>(),
            (0..16384_i64)
                .map(|mut value| {
                    for _ in 0..8 {
                        value = value.wrapping_mul(1664525).wrapping_add(1013904223);
                    }
                    value & 0x7fff
                })
                .sum::<i64>()
        );
    }

    #[test]
    fn failure_returns_every_instance_and_stops_without_replay() {
        let result = experiment(16384, 8, 4, false, true);
        assert!(result.0.is_err());
        assert!(result.1.is_empty());
        assert_eq!(result.3, 8);
    }

    #[test]
    fn empty_graph_finishes_without_worker_claims() {
        let result = experiment(0, 0, 2, false, false);
        assert_eq!(result.0, Ok(()));
        assert!(result.1.is_empty());
        assert_eq!(result.3, 4);
    }

    struct Meet(Arc<Barrier>);
    impl Pipeline for Meet {
        fn consume(&mut self, _: &TileGuard) {
            self.0.wait();
        }
    }

    #[test]
    fn one_instance_per_pipeline_does_not_block_independent_work() {
        let dispatcher = Dispatcher::new(vec![vec![], vec![]], 1);
        let meet = Arc::new(Barrier::new(2));
        let mut instances: Vec<Vec<Box<dyn Pipeline>>> = (0..2)
            .map(|_| vec![Box::new(Meet(meet.clone())) as Box<dyn Pipeline>])
            .collect();
        for p in 0..2 {
            for key in 0..4 {
                dispatcher.notify(PipelineId(p), &keys_between(key, key));
            }
            dispatcher.close(PipelineId(p));
        }
        assert_eq!(run(&dispatcher, &mut instances, 2, |_, _, _| {}), Ok(()));
        assert_eq!(instances.iter().map(Vec::len).sum::<usize>(), 2);
    }

    #[test]
    fn publication_failure_drains_and_returns_active_instances() {
        let dispatcher = Dispatcher::new(vec![vec![], vec![]], 1);
        let meet = Arc::new(Barrier::new(2));
        let mut instances: Vec<Vec<Box<dyn Pipeline>>> = (0..2)
            .map(|_| vec![Box::new(Meet(meet.clone())) as Box<dyn Pipeline>])
            .collect();
        for p in 0..2 {
            dispatcher.notify(PipelineId(p), &keys_between(0, 0));
            dispatcher.close(PipelineId(p));
        }
        assert!(
            run(&dispatcher, &mut instances, 2, |_, _, _| panic!(
                "publication failed"
            ))
            .is_err()
        );
        assert_eq!(instances.iter().map(Vec::len).sum::<usize>(), 2);
        assert!(matches!(dispatcher.try_claim(None), Next::Failed));
    }

    struct Count(Arc<std::sync::atomic::AtomicUsize>);
    impl Pipeline for Count {
        fn consume(&mut self, _: &TileGuard) {
            self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        }
    }

    #[test]
    fn failed_dispatcher_admits_no_work() {
        let dispatcher = Dispatcher::new(vec![vec![]], 1);
        dispatcher.notify(PipelineId(0), &keys_between(0, 0));
        dispatcher.close(PipelineId(0));
        dispatcher.fail();
        let calls = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let mut instances = vec![vec![Box::new(Count(calls.clone())) as Box<dyn Pipeline>]];
        assert!(run(&dispatcher, &mut instances, 1, |_, _, _| {}).is_err());
        assert_eq!(calls.load(std::sync::atomic::Ordering::SeqCst), 0);
        assert_eq!(instances[0].len(), 1);
    }

    #[test]
    fn silent_control_failure_stops_publication_and_admission() {
        let dispatcher = Dispatcher::new(vec![vec![]], 1);
        for key in 0..8 {
            dispatcher.notify(PipelineId(0), &keys_between(key, key));
        }
        dispatcher.close(PipelineId(0));
        let calls = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let mut instances = vec![vec![Box::new(Count(calls.clone())) as Box<dyn Pipeline>]];
        let mut published = 0;
        assert!(
            run(&dispatcher, &mut instances, 1, |_, _, _| {
                published += 1;
                dispatcher.fail();
            })
            .is_err()
        );
        assert_eq!(calls.load(std::sync::atomic::Ordering::SeqCst), 1);
        assert_eq!(published, 1);
        assert_eq!(instances[0].len(), 1);
    }

    #[test]
    #[ignore = "manual small benchmark; prints elapsed wall time"]
    fn benchmark_whole_pipeline() {
        for (rows, work) in [(16384, 1), (16384, 256), (65536, 256)] {
            let mut expected = None;
            for workers in [1, 2, 4] {
                let mut samples = Vec::new();
                for _ in 0..3 {
                    let start = Instant::now();
                    let (result, answer, retained, _) =
                        experiment(rows, work, workers, false, false);
                    samples.push(start.elapsed().as_secs_f64());
                    assert_eq!(result, Ok(()));
                    assert_eq!(retained, 0);
                    if let Some(expected) = &expected {
                        assert_eq!(&answer, expected);
                    } else {
                        expected = Some(answer);
                    }
                }
                samples.sort_by(f64::total_cmp);
                println!(
                    "parallel-prototype rows={rows} work={work} workers={workers} median_s={:.6}",
                    samples[1]
                );
            }
        }
    }
}
