//! The dispatcher of `crate::interpreter::dispatcher` shared by worker threads that run scripted
//! work: each worker claims packages and finalizes, and records what it did in plain data. The
//! breakers are not `Send`, so no breaker runs on a worker; the single-threaded run the results
//! are compared with drives breakers that follow the same script.
//!
//! Every scenario runs under a watchdog, so a deadlock fails the test instead of hanging it, and
//! a failing scenario prints its seed and thread count.

use std::cell::RefCell;
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering::SeqCst};
use std::sync::{Mutex, mpsc};
use std::thread;
use std::time::Duration;

use super::growing::{Rng, predicate, same_region};
use super::test_helpers::keys_between;
use super::*;
use crate::interpreter::dispatcher::{
    BreakerHandle, Dispatcher, Event, Next, PipelineId, WorkPackage, run,
};
use crate::interpreter::{BaseType, Extent};

/// The keys a scripted guard names: `0..64`, so the keys of a guard fit one `u64` mask.
const UNIVERSE: u64 = 64;

/// How long a scenario may run before the test reads it as a deadlock.
const WATCHDOG: Duration = Duration::from_secs(30);

const THREADS: [usize; 5] = [1, 2, 4, 8, 16];

fn keys_tiling(positions: u64) -> Tiling {
    Tiling::data_function(
        Extent::uint_range(positions),
        Tiling::Scalar(Extent::Base(BaseType::Int)),
    )
}

/// The keys of the universe `guard` names, as a mask.
fn mask_of(guard: &TileGuard) -> u64 {
    let predicate = predicate(guard);
    (0..UNIVERSE)
        .filter(|key| predicate.contains(&Value::UInt(*key)))
        .fold(0, |mask, key| mask | 1 << key)
}

/// The guard naming the keys of `mask`, one run of keys at a time.
fn guard_of(mask: u64) -> TileGuard {
    let mut guard = keys_tiling(UNIVERSE).empty_guard();
    let mut key = 0;
    while key < UNIVERSE {
        if mask & 1 << key == 0 {
            key += 1;
            continue;
        }
        let first = key;
        while key < UNIVERSE && mask & 1 << key != 0 {
            key += 1;
        }
        guard = guard.union(&keys_between(first, key - 1));
    }
    guard
}

/// `guard` cut before every `rows`-th key it names, as a breaker cuts at its held keys.
fn cut(guard: &TileGuard, rows: usize) -> Vec<TileGuard> {
    let mask = mask_of(guard);
    let keys: Vec<u64> = (0..UNIVERSE).filter(|key| mask & 1 << key != 0).collect();
    let cuts: Vec<Value> = keys
        .iter()
        .skip(rows)
        .step_by(rows)
        .map(|key| Value::UInt(*key))
        .collect();
    cut_before(&predicate(guard), &cuts, &Extent::uint_range(UNIVERSE))
}

/// The keys of `consumed` a pipeline that keeps every `keep`-th key holds: none for `keep` 0.
fn kept(consumed: u64, keep: u64) -> u64 {
    match keep {
        0 => 0,
        _ => {
            (0..UNIVERSE)
                .filter(|key| key % keep == 0)
                .fold(0, |mask, key| mask | 1 << key)
                & consumed
        }
    }
}

/// What every pipeline does, in plain data a worker thread can read.
#[derive(Clone, Debug)]
struct Script {
    reads: Vec<Vec<usize>>,
    rows: usize,
    ordered: Vec<bool>,
    /// The positions of each source pipeline's input; unused for a pipeline that reads one.
    positions: Vec<u64>,
    /// Each pipeline holds every `keep`-th key it consumed when it finalizes, and none for 0.
    keep: Vec<u64>,
}

impl Script {
    fn count(&self) -> usize {
        self.reads.len()
    }

    /// The pipelines that read `pipeline`.
    fn readers(&self, pipeline: usize) -> Vec<usize> {
        (0..self.count())
            .filter(|p| self.reads[*p].contains(&pipeline))
            .collect()
    }

    fn dispatcher(&self) -> Dispatcher {
        let mut dispatcher = Dispatcher::new(self.reads.clone(), self.rows);
        for (pipeline, ordered) in self.ordered.iter().enumerate() {
            if *ordered {
                dispatcher.order(PipelineId(pipeline));
            }
        }
        dispatcher
    }

    fn start(&self, dispatcher: &Dispatcher) {
        for pipeline in (0..self.count()).filter(|p| self.reads[*p].is_empty()) {
            dispatcher.start_source(PipelineId(pipeline), &keys_tiling(self.positions[pipeline]));
        }
    }

    /// Chains of `lengths` pipelines, numbered upward along each chain, every one unordered and
    /// keeping every key.
    fn chains(lengths: &[usize], rows: usize, positions: u64) -> Self {
        let mut reads = Vec::new();
        for length in lengths {
            let first = reads.len();
            for at in 0..*length {
                reads.push(match at {
                    0 => vec![],
                    _ => vec![first + at - 1],
                });
            }
        }
        let count = reads.len();
        Script {
            reads,
            rows,
            ordered: vec![false; count],
            positions: vec![positions; count],
            keep: vec![1; count],
        }
    }

    /// A random forest of chains over up to `most` pipelines, numbered in a random order.
    fn random(rng: &mut Rng, most: u64) -> Self {
        let count = 1 + rng.below(most) as usize;
        let mut order: Vec<usize> = (0..count).collect();
        for at in (1..count).rev() {
            order.swap(at, rng.below(at as u64 + 1) as usize);
        }
        let mut reads = vec![Vec::new(); count];
        for pair in order.windows(2) {
            if rng.below(3) > 0 {
                reads[pair[1]] = vec![pair[0]];
            }
        }
        Self::random_over(rng, reads)
    }

    /// A random forest of trees over up to `most` pipelines, numbered in a random order: each
    /// pipeline reads at most one that comes before it, and a pipeline may have several readers.
    fn random_trees(rng: &mut Rng, most: u64) -> Self {
        let count = 1 + rng.below(most) as usize;
        let mut order: Vec<usize> = (0..count).collect();
        for at in (1..count).rev() {
            order.swap(at, rng.below(at as u64 + 1) as usize);
        }
        let mut reads = vec![Vec::new(); count];
        for at in 1..count {
            if rng.below(3) > 0 {
                reads[order[at]] = vec![order[rng.below(at as u64) as usize]];
            }
        }
        Self::random_over(rng, reads)
    }

    /// A script over the pipelines `reads` describes, with random morsels, order, inputs and keys.
    fn random_over(rng: &mut Rng, reads: Vec<Vec<usize>>) -> Self {
        let count = reads.len();
        let rows = match rng.below(6) {
            0 => UNIVERSE as usize,
            rows => rows as usize,
        };
        Script {
            reads,
            rows,
            ordered: (0..count).map(|_| rng.below(3) == 0).collect(),
            positions: (0..count).map(|_| rng.below(41)).collect(),
            keep: (0..count).map(|_| rng.below(4)).collect(),
        }
    }
}

/// What the workers observe while they run, shared by them all.
struct Observed {
    /// Per pipeline, the keys of the packages consumed so far.
    consumed: Vec<AtomicU64>,
    /// Per pipeline, the keys queued for it: every key for a source, and what its child pushed.
    queued: Vec<AtomicU64>,
    finalizes: Vec<AtomicUsize>,
    finished: Vec<AtomicBool>,
    /// Per ordered pipeline, whether a worker is consuming one of its packages.
    busy: Vec<AtomicBool>,
    /// Per ordered pipeline, one past the highest key it has consumed.
    next_key: Vec<AtomicU64>,
    /// How many packages have been consumed, across pipelines.
    packages: AtomicUsize,
}

impl Observed {
    fn of(script: &Script) -> Self {
        let count = script.count();
        let sources = |p: usize| match script.reads[p].is_empty() {
            true => u64::MAX,
            false => 0,
        };
        Observed {
            consumed: (0..count).map(|_| AtomicU64::new(0)).collect(),
            queued: (0..count).map(|p| AtomicU64::new(sources(p))).collect(),
            finalizes: (0..count).map(|_| AtomicUsize::new(0)).collect(),
            finished: (0..count).map(|_| AtomicBool::new(false)).collect(),
            busy: (0..count).map(|_| AtomicBool::new(false)).collect(),
            next_key: (0..count).map(|_| AtomicU64::new(0)).collect(),
            packages: AtomicUsize::new(0),
        }
    }
}

/// How a worker thread runs.
#[derive(Clone, Copy)]
struct Plan {
    seed: u64,
    preferred: Option<PipelineId>,
    /// Whether it blocks in `claim` rather than calling `try_claim` and `wait` itself, with a
    /// pause between the two.
    blocking: bool,
    /// The most packages and finalizes it takes before it stops.
    budget: usize,
    /// It panics while consuming the package with this index across all workers.
    panics_at: Option<usize>,
}

/// What a worker did.
enum Record {
    Consumed(WorkPackage),
    Finalized {
        pipeline: usize,
        held: TileGuard,
        pushed: Vec<TileGuard>,
    },
}

/// A pause of random length, often none, where another thread may run.
fn jitter(rng: &mut Rng) {
    match rng.below(8) {
        0 => thread::sleep(Duration::from_micros(rng.below(200))),
        1 | 2 => thread::yield_now(),
        _ => {}
    }
}

fn work(
    dispatcher: &Dispatcher,
    script: &Script,
    observed: &Observed,
    worker: Plan,
) -> Vec<Record> {
    let _worker = dispatcher.worker();
    let mut rng = Rng(worker.seed | 1);
    let mut records = Vec::new();
    while records.len() < worker.budget {
        let next = match worker.blocking {
            true => dispatcher.claim(worker.preferred),
            false => dispatcher.try_claim(worker.preferred),
        };
        match next {
            Next::Package(package) => {
                consume(script, observed, &package, &mut rng, worker.panics_at);
                records.push(Record::Consumed(package.clone()));
                dispatcher.acknowledge(package);
            }
            Next::Finalize {
                pipeline, consumed, ..
            } => {
                jitter(&mut rng);
                records.push(finalize(dispatcher, script, observed, pipeline, consumed));
            }
            Next::Wait(epoch) => {
                jitter(&mut rng);
                dispatcher.wait(epoch);
            }
            Next::Done | Next::Failed => break,
        }
    }
    records
}

fn consume(
    script: &Script,
    observed: &Observed,
    package: &WorkPackage,
    rng: &mut Rng,
    panics_at: Option<usize>,
) {
    let p = package.pipeline.0;
    let mask = mask_of(&package.guard);
    let ordered = script.ordered[p];
    if ordered {
        assert!(
            !observed.busy[p].swap(true, SeqCst),
            "ordered pipeline {p} has one package in flight"
        );
        assert!(
            mask == 0 || u64::from(mask.trailing_zeros()) >= observed.next_key[p].load(SeqCst),
            "ordered pipeline {p} consumes its packages in queue order"
        );
    }
    jitter(rng);
    if panics_at == Some(observed.packages.fetch_add(1, SeqCst)) {
        panic!("a scripted worker panics while it consumes a package");
    }
    let before = observed.consumed[p].fetch_or(mask, SeqCst);
    assert_eq!(before & mask, 0, "pipeline {p} consumes each key once");
    if ordered && mask != 0 {
        observed.next_key[p].store(u64::from(64 - mask.leading_zeros()), SeqCst);
    }
    if ordered {
        observed.busy[p].store(false, SeqCst);
    }
}

/// A scripted finalize, which checks what a finalize rests on as the worker sees it.
fn finalize(
    dispatcher: &Dispatcher,
    script: &Script,
    observed: &Observed,
    pipeline: PipelineId,
    consumed: Option<TileGuard>,
) -> Record {
    let p = pipeline.0;
    assert_eq!(
        observed.finalizes[p].fetch_add(1, SeqCst),
        0,
        "pipeline {p} finalizes once"
    );
    for child in &script.reads[p] {
        assert!(
            observed.finished[*child].load(SeqCst),
            "pipeline {p} finalizes after pipeline {child}, which it reads, finished"
        );
    }
    let consumed = consumed.as_ref().map_or(0, mask_of);
    assert_eq!(
        observed.consumed[p].load(SeqCst),
        observed.queued[p].load(SeqCst),
        "pipeline {p} finalizes after consuming every key queued for it"
    );
    assert_eq!(
        consumed,
        observed.consumed[p].load(SeqCst),
        "pipeline {p} finalizes with every package it consumed recorded"
    );
    let held = guard_of(kept(consumed, script.keep[p]));
    let mut pushes = dispatcher.pushes(pipeline);
    let mut pushed = Vec::new();
    pushes.push(&held, |guard, rows| {
        pushed = cut(guard, rows);
        pushed.clone()
    });
    let keys = pushed.iter().fold(0, |keys, morsel| keys | mask_of(morsel));
    for reader in script.readers(p) {
        observed.queued[reader].store(keys, SeqCst);
    }
    observed.finished[p].store(true, SeqCst);
    dispatcher.finish(pushes);
    Record::Finalized {
        pipeline: p,
        held,
        pushed,
    }
}

/// A breaker that follows a script: it records the keys it consumes, its input releases
/// everything, and it holds every `keep`-th key it consumed.
struct ScriptBreaker {
    base: ProducerBase,
    input: Tiling,
    keep: u64,
    consumed: u64,
}

impl TileProducer for ScriptBreaker {
    impl_producer_base!();

    fn get_impl(&mut self, _guard: TileGuard) -> Tile {
        self.tiling().empty_tile()
    }

    fn release_impl(&mut self, _guard: TileGuard) {}
}

impl BreakingProducer for ScriptBreaker {
    fn consume_impl(&mut self, guard: TileGuard) {
        self.consumed |= mask_of(&guard);
    }

    fn input_tiling(&self) -> Tiling {
        self.input.clone()
    }

    fn input_released(&self) -> TileGuard {
        self.input.universal_guard()
    }

    fn held(&self) -> TileGuard {
        guard_of(kept(self.consumed, self.keep))
    }

    fn morsels(&self, guard: &TileGuard, rows: usize) -> Vec<TileGuard> {
        cut(guard, rows)
    }

    fn offer_impl(&mut self, _guard: TileGuard) -> Tile {
        self.tiling().empty_tile()
    }
}

/// What a run did: per pipeline, the guards it consumed, and the guard it held when it
/// finalized.
struct Outcome {
    consumed: Vec<Vec<TileGuard>>,
    held: Vec<TileGuard>,
}

/// The single-threaded run of breakers that follow `script`.
fn single_threaded(script: &Script) -> (Outcome, usize) {
    let breakers: Vec<BreakerHandle> = (0..script.count())
        .map(|p| {
            let input = match script.reads[p].is_empty() {
                true => keys_tiling(script.positions[p]),
                false => keys_tiling(UNIVERSE),
            };
            let breaker: BreakerHandle = Rc::new(RefCell::new(ScriptBreaker {
                base: ProducerBase::unowned(ScriptBreaker::alloc_id(), &keys_tiling(UNIVERSE)),
                input,
                keep: script.keep[p],
                consumed: 0,
            }));
            breaker
        })
        .collect();
    let dispatcher = script.dispatcher();
    run(&dispatcher, &breakers);
    let events = dispatcher.into_events();
    let mut consumed = vec![Vec::new(); script.count()];
    for event in &events {
        if let Event::Consume { pipeline, guard } = event {
            consumed[pipeline.0].push(guard.clone());
        }
    }
    let held = breakers.iter().map(|b| b.borrow().held()).collect();
    (Outcome { consumed, held }, events.len())
}

/// The workers' records, and the dispatcher's events, of a run of `workers` over `script`.
fn threaded(script: &Script, workers: &[Plan]) -> (Vec<thread::Result<Vec<Record>>>, Vec<Event>) {
    let dispatcher = script.dispatcher();
    let results = on_workers(&dispatcher, script, workers);
    (results, dispatcher.into_events())
}

/// The workers' records of a run of `workers` over `script` on `dispatcher`.
fn on_workers(
    dispatcher: &Dispatcher,
    script: &Script,
    workers: &[Plan],
) -> Vec<thread::Result<Vec<Record>>> {
    let observed = Observed::of(script);
    script.start(dispatcher);
    thread::scope(|scope| {
        let handles: Vec<_> = workers
            .iter()
            .map(|worker| scope.spawn(|| work(dispatcher, script, &observed, *worker)))
            .collect();
        handles.into_iter().map(|h| h.join()).collect()
    })
}

/// The outcome the workers' records describe.
fn outcome_of(script: &Script, records: impl IntoIterator<Item = Record>) -> Outcome {
    let mut consumed = vec![Vec::new(); script.count()];
    let mut held = vec![None; script.count()];
    for record in records {
        match record {
            Record::Consumed(package) => consumed[package.pipeline.0].push(package.guard),
            Record::Finalized {
                pipeline,
                held: guard,
                ..
            } => {
                assert!(held[pipeline].replace(guard).is_none(), "one finalize each");
            }
        }
    }
    Outcome {
        consumed,
        held: held
            .into_iter()
            .map(|h| h.expect("every pipeline finalized"))
            .collect(),
    }
}

/// Whether `a` and `b` hold the same guards, each as often, compared by the region they name.
fn same_guards(a: &[TileGuard], b: &[TileGuard]) -> bool {
    let mut rest: Vec<&TileGuard> = b.iter().collect();
    a.len() == b.len()
        && a.iter().all(|guard| {
            let at = rest
                .iter()
                .position(|other| same_region(&predicate(guard), &predicate(other)));
            at.map(|at| rest.swap_remove(at)).is_some()
        })
}

fn assert_same_outcome(threaded: &Outcome, single: &Outcome) {
    for (p, (a, b)) in threaded.consumed.iter().zip(&single.consumed).enumerate() {
        assert!(
            same_guards(a, b),
            "pipeline {p} consumes what the single-threaded run consumes: {a:?} against {b:?}"
        );
    }
    for (p, (a, b)) in threaded.held.iter().zip(&single.held).enumerate() {
        assert_eq!(
            mask_of(a),
            mask_of(b),
            "pipeline {p} holds what the single-threaded run holds"
        );
    }
}

/// The order of the dispatcher's events: every pipeline finalizes once, after every package it
/// consumed and after the pipeline it reads finalized; a parent consumes only after its child
/// finalized, exactly the morsels the child pushed; an ordered pipeline consumes its packages in
/// ascending key order.
fn assert_ordered_events(script: &Script, events: &[Event], records: &[Record]) {
    let finalized: Vec<usize> = (0..script.count())
        .map(|p| {
            let at: Vec<usize> = (0..events.len())
                .filter(|at| events[*at] == Event::Finalize(PipelineId(p)))
                .collect();
            assert_eq!(at.len(), 1, "pipeline {p} finalizes once");
            at[0]
        })
        .collect();
    let mut next_key = vec![0; script.count()];
    for (at, event) in events.iter().enumerate() {
        let Event::Consume { pipeline, guard } = event else {
            continue;
        };
        let p = pipeline.0;
        assert!(
            at < finalized[p],
            "pipeline {p} consumes before it finalizes"
        );
        for child in &script.reads[p] {
            assert!(
                finalized[*child] < at,
                "pipeline {p} consumes after pipeline {child} finalized"
            );
        }
        let mask = mask_of(guard);
        if script.ordered[p] && mask != 0 {
            assert!(
                u64::from(mask.trailing_zeros()) >= next_key[p],
                "ordered pipeline {p} consumes in queue order"
            );
            next_key[p] = u64::from(64 - mask.leading_zeros());
        }
    }
    for p in 0..script.count() {
        for child in &script.reads[p] {
            assert!(
                finalized[*child] < finalized[p],
                "{child} finalizes before {p}"
            );
        }
    }
    for record in records {
        let Record::Finalized {
            pipeline, pushed, ..
        } = record
        else {
            continue;
        };
        for reader in script.readers(*pipeline) {
            let consumed: Vec<TileGuard> = events
                .iter()
                .filter_map(|event| match event {
                    Event::Consume {
                        pipeline: at,
                        guard,
                    } if *at == PipelineId(reader) => Some(guard.clone()),
                    _ => None,
                })
                .collect();
            assert!(
                same_guards(&consumed, pushed),
                "pipeline {reader} consumes exactly the morsels pipeline {pipeline} pushed"
            );
        }
    }
}

/// Run `scenario` on a thread of its own and wait at most [`WATCHDOG`] for it; `what` names
/// the scenario, its seed and thread count, in the failure.
fn within<T: Send + 'static>(what: String, scenario: impl FnOnce() -> T + Send + 'static) -> T {
    let (done, finished) = mpsc::channel();
    let handle = thread::spawn(move || {
        let result = catch_unwind(AssertUnwindSafe(scenario));
        let _ = done.send(());
        result
    });
    match finished.recv_timeout(WATCHDOG) {
        Ok(()) => match handle.join().expect("the scenario's panic is caught") {
            Ok(value) => value,
            Err(panic) => {
                eprintln!("failing scenario: {what}");
                resume_unwind(panic)
            }
        },
        Err(_) => panic!("{what}: no end within {WATCHDOG:?}, a deadlock"),
    }
}

/// `threads` workers, half of them blocking in `claim` and each preferring a pipeline of its
/// own where `prefer` says so.
fn workers(threads: usize, seed: u64, count: usize, prefer: bool) -> Vec<Plan> {
    (0..threads)
        .map(|at| Plan {
            seed: seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ (at as u64 + 1) << 32,
            preferred: (prefer && at % 2 == 0).then_some(PipelineId(at % count)),
            blocking: at % 2 == 1,
            budget: usize::MAX,
            panics_at: None,
        })
        .collect()
}

/// Run `script` on `workers` and the single-threaded driver; check the order of the events, what
/// each finalize rested on, and that the two runs agree.
fn agrees_with_the_single_threaded_run(script: Script, workers: Vec<Plan>, what: String) {
    within(what, move || {
        let (single, _) = single_threaded(&script);
        let (results, events) = threaded(&script, &workers);
        let records: Vec<Record> = results
            .into_iter()
            .flat_map(|result| result.unwrap_or_else(|panic| resume_unwind(panic)))
            .collect();
        assert_ordered_events(&script, &events, &records);
        assert_same_outcome(&outcome_of(&script, records), &single);
    });
}

/// The dispatcher can be shared by threads.
#[test]
fn the_dispatcher_is_sync() {
    fn sync<T: Sync>() {}
    sync::<Dispatcher>();
}

/// Random forests of chains, at every thread count: every package is consumed exactly once,
/// each pipeline finalizes once after its preconditions, and the run consumes and holds what the
/// single-threaded run does.
#[test]
fn random_scripts_match_the_single_threaded_run() {
    for seed in 1..=40u64 {
        let script = Script::random(&mut Rng(seed.wrapping_mul(0x2545_f491_4f6c_dd1d)), 8);
        for threads in THREADS {
            let workers = workers(threads, seed, script.count(), seed % 2 == 0);
            let what = format!("seed {seed}, {threads} threads, {script:?}");
            agrees_with_the_single_threaded_run(script.clone(), workers, what);
        }
    }
}

/// Random forests of chains with the event log off, so no test-only lock orders the
/// acknowledgements: each worker still checks every package is consumed once and every finalize's
/// preconditions, and the run consumes and holds what the single-threaded run does.
#[test]
fn random_scripts_without_the_event_log_match_the_single_threaded_run() {
    for seed in 1..=40u64 {
        let script = Script::random(&mut Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15)), 8);
        for threads in THREADS {
            let workers = workers(threads, seed, script.count(), seed % 2 == 1);
            let what = format!("seed {seed}, {threads} threads, {script:?}");
            let script = script.clone();
            within(what, move || {
                let (single, _) = single_threaded(&script);
                let dispatcher = script.dispatcher().unrecorded();
                let records: Vec<Record> = on_workers(&dispatcher, &script, &workers)
                    .into_iter()
                    .flat_map(|result| result.unwrap_or_else(|panic| resume_unwind(panic)))
                    .collect();
                assert_same_outcome(&outcome_of(&script, records), &single);
            });
        }
    }
}

/// Threads that acknowledge one package at once: exactly one acknowledgement is recorded, and
/// the run fails, so a later claim answers `Failed`.
#[test]
fn one_package_acknowledged_on_many_threads_at_once_is_recorded_once() {
    for iteration in 1..=200 {
        within(format!("iteration {iteration}"), move || {
            let script = Script::chains(&[1], 64, 4);
            let dispatcher = script.dispatcher();
            script.start(&dispatcher);
            let Next::Package(package) = dispatcher.try_claim(None) else {
                panic!("the source's one package");
            };
            let start = std::sync::Barrier::new(8);
            let panicked = thread::scope(|scope| {
                let handles: Vec<_> = (0..8)
                    .map(|_| {
                        let package = package.clone();
                        let (dispatcher, start) = (&dispatcher, &start);
                        scope.spawn(move || {
                            start.wait();
                            dispatcher.acknowledge(package);
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|h| h.join())
                    .filter(Result::is_err)
                    .count()
            });
            assert!(
                panicked >= 1,
                "an acknowledgement after the first is refused"
            );
            assert!(matches!(dispatcher.try_claim(None), Next::Failed));
            let consumed = dispatcher
                .into_events()
                .iter()
                .filter(|event| matches!(event, Event::Consume { .. }))
                .count();
            assert_eq!(consumed, 1, "one acknowledgement is recorded");
        });
    }
}

/// Two threads that finish one pipeline at once: exactly one finish is recorded and the other is
/// refused.
#[test]
fn one_pipeline_finished_on_two_threads_at_once_finishes_once() {
    for iteration in 1..=200 {
        within(format!("iteration {iteration}"), move || {
            let script = Script::chains(&[1], 64, 4);
            let dispatcher = script.dispatcher();
            script.start(&dispatcher);
            let Next::Package(package) = dispatcher.try_claim(None) else {
                panic!("the source's one package");
            };
            dispatcher.acknowledge(package);
            let Next::Finalize { pipeline, .. } = dispatcher.try_claim(None) else {
                panic!("the source finalizes");
            };
            let start = std::sync::Barrier::new(2);
            let panicked = thread::scope(|scope| {
                let handles: Vec<_> = (0..2)
                    .map(|_| {
                        let (dispatcher, start) = (&dispatcher, &start);
                        scope.spawn(move || {
                            let pushes = dispatcher.pushes(pipeline);
                            start.wait();
                            dispatcher.finish(pushes);
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|h| h.join())
                    .filter(Result::is_err)
                    .count()
            });
            assert_eq!(panicked, 1, "the second finish is refused");
            let finished = dispatcher
                .into_events()
                .iter()
                .filter(|event| matches!(event, Event::Finalize(_)))
                .count();
            assert_eq!(finished, 1, "one finish is recorded");
        });
    }
}

/// Random forests of trees, where a pipeline may have several readers, at every thread count:
/// each reader consumes exactly what the pipeline it reads pushed, after it finalized.
#[test]
fn random_trees_match_the_single_threaded_run() {
    let mut fanned = 0;
    for seed in 1..=40u64 {
        let script = Script::random_trees(&mut Rng(seed.wrapping_mul(0x5851_f42d_4c95_7f2d)), 10);
        fanned += usize::from((0..script.count()).any(|p| script.readers(p).len() > 1));
        for threads in THREADS {
            let workers = workers(threads, seed, script.count(), seed % 2 == 0);
            let what = format!("seed {seed}, {threads} threads, {script:?}");
            agrees_with_the_single_threaded_run(script.clone(), workers, what);
        }
    }
    assert!(
        fanned >= 10,
        "the trees read a pipeline twice in {fanned} of 40 scripts"
    );
}

/// One source read by six pipelines, two of them ordered, at morsels of one row: the readers'
/// claims race each other on every thread count.
#[test]
fn a_pipeline_read_by_six_runs_on_many_threads() {
    for seed in 1..=10 {
        for threads in THREADS {
            let mut script = Script::chains(&[1], 1, 30);
            script.reads.extend((0..6).map(|_| vec![0]));
            script.ordered = vec![false, true, false, false, true, false, false];
            script.positions = vec![30; 7];
            script.keep = vec![1, 1, 2, 1, 3, 1, 0];
            let workers = workers(threads, seed, script.count(), seed % 2 == 0);
            let what = format!("seed {seed}, {threads} threads");
            agrees_with_the_single_threaded_run(script, workers, what);
        }
    }
}

/// Many packages over many threads: no package is lost or consumed twice.
#[test]
fn every_package_is_consumed_exactly_once() {
    for threads in THREADS {
        let script = Script::chains(&[1; 6], 1, 40);
        let workers = workers(threads, 7, script.count(), false);
        agrees_with_the_single_threaded_run(script, workers, format!("{threads} threads"));
    }
}

/// Chains of two to six pipelines finish in dependency order, and each parent consumes exactly
/// the morsels its child pushed.
#[test]
fn chains_finish_in_dependency_order() {
    for length in 2..=6 {
        for rows in [1, 3, 64] {
            for threads in THREADS {
                let script = Script::chains(&[length], rows, 24);
                let workers = workers(threads, length as u64, script.count(), true);
                let what = format!("a chain of {length} at {rows} rows, {threads} threads");
                agrees_with_the_single_threaded_run(script, workers, what);
            }
        }
    }
}

/// Eight chains of two at morsels of one row: a child's finalize pushes while other threads
/// claim and consume the packages of the other chains.
#[test]
fn pushes_from_a_finalize_race_claims_on_other_threads() {
    for seed in 1..=10 {
        for threads in [4, 8, 16] {
            let script = Script::chains(&[2; 8], 1, 8);
            let workers = workers(threads, seed, script.count(), seed % 2 == 0);
            let what = format!("seed {seed}, {threads} threads");
            agrees_with_the_single_threaded_run(script, workers, what);
        }
    }
}

/// An ordered pipeline that every worker prefers has one package in flight at a time and
/// consumes its packages in queue order; so does its ordered parent.
#[test]
fn an_ordered_pipeline_has_one_package_in_flight_in_queue_order() {
    for seed in 1..=10 {
        for threads in THREADS {
            let mut script = Script::chains(&[2, 1], 1, 40);
            script.ordered = vec![true, true, false];
            let mut workers = workers(threads, seed, script.count(), false);
            for (at, worker) in workers.iter_mut().enumerate() {
                worker.preferred = Some(PipelineId(at % 2));
            }
            let what = format!("seed {seed}, {threads} threads");
            agrees_with_the_single_threaded_run(script, workers, what);
        }
    }
}

/// Workers that take one package or finalize each and then stop: every step of the run is
/// taken by a worker woken from a wait by the step before it, with a pause between a claim that
/// answered `Wait` and the wait, so a change made in that pause is not missed.
#[test]
fn a_waiting_worker_is_woken_by_every_change() {
    for seed in 1..=20 {
        let script = Script::chains(&[3], 2, 8);
        let (_, steps) = single_threaded(&script);
        let workers: Vec<Plan> = (0..steps + 4)
            .map(|at| Plan {
                seed: seed * 1000 + at as u64,
                preferred: None,
                blocking: false,
                budget: 1,
                panics_at: None,
            })
            .collect();
        agrees_with_the_single_threaded_run(script, workers, format!("seed {seed}"));
    }
}

/// A worker that panics while it consumes a package ends the run: every other worker stops
/// without waiting for the package it claimed, and a later claim answers `Failed`.
#[test]
fn a_panicking_worker_ends_the_run_for_every_other() {
    for seed in 1..=20u64 {
        for threads in [2, 4, 8, 16] {
            let what = format!("seed {seed}, {threads} threads");
            within(what, move || {
                let script = Script::chains(&[3, 2], 1, 20);
                let mut workers = workers(threads, seed, script.count(), false);
                for worker in &mut workers {
                    worker.panics_at = Some(seed as usize % 12);
                }
                let dispatcher = script.dispatcher();
                let observed = Observed::of(&script);
                script.start(&dispatcher);
                let results: Vec<_> = thread::scope(|scope| {
                    let handles: Vec<_> = workers
                        .iter()
                        .map(|w| scope.spawn(|| work(&dispatcher, &script, &observed, *w)))
                        .collect();
                    handles.into_iter().map(|h| h.join()).collect()
                });
                let panicked = results.iter().filter(|r| r.is_err()).count();
                assert_eq!(panicked, 1, "the scripted worker panics, and no other");
                assert!(matches!(dispatcher.try_claim(None), Next::Failed));
            });
        }
    }
}

/// What `claim` answers on each of `threads - 1` threads, asleep in it while the source of a
/// chain of two has its one package in flight. `then` gets that package once every one of them
/// sleeps inside `wait`.
fn with_sleepers(threads: usize, then: impl FnOnce(&Dispatcher, WorkPackage)) -> Vec<Next> {
    let script = Script::chains(&[2], 64, 4);
    let dispatcher = script.dispatcher();
    script.start(&dispatcher);
    let Next::Package(package) = dispatcher.try_claim(None) else {
        panic!("the source's one package");
    };
    thread::scope(|scope| {
        let sleepers: Vec<_> = (1..threads)
            .map(|_| scope.spawn(|| dispatcher.claim(None)))
            .collect();
        while dispatcher.waiting() < threads - 1 {
            thread::yield_now();
        }
        then(&dispatcher, package);
        sleepers
            .into_iter()
            .map(|sleeper| sleeper.join().expect("a sleeper returns"))
            .collect()
    })
}

/// Threads asleep in `wait` for the one package a worker holds wake when that worker panics,
/// and answer `Failed`.
#[test]
fn a_failure_wakes_every_waiting_worker() {
    for threads in [2, 4, 8, 16] {
        within(format!("{threads} threads"), move || {
            let woken = with_sleepers(threads, |dispatcher, package| {
                let holder = thread::scope(|scope| {
                    scope
                        .spawn(|| {
                            let _worker = dispatcher.worker();
                            drop(package);
                            panic!("a scripted worker panics while it holds the only package");
                        })
                        .join()
                });
                assert!(holder.is_err());
            });
            assert!(woken.iter().all(|next| matches!(next, Next::Failed)));
        });
    }
}

/// A worker that acknowledges a package no claim handed out wakes every thread asleep in `wait`,
/// and they answer `Failed`.
#[test]
fn a_refused_acknowledgement_wakes_every_waiting_worker() {
    for threads in [2, 4, 8, 16] {
        within(format!("{threads} threads"), move || {
            let woken = with_sleepers(threads, |dispatcher, package| {
                let misuse = thread::scope(|scope| {
                    scope
                        .spawn(|| {
                            let _worker = dispatcher.worker();
                            dispatcher.acknowledge(WorkPackage {
                                pipeline: PipelineId(1),
                                epoch: 0,
                                ..package
                            });
                        })
                        .join()
                });
                assert!(misuse.is_err(), "pipeline 1 claimed no package");
            });
            assert!(woken.iter().all(|next| matches!(next, Next::Failed)));
        });
    }
}

/// A thread without a worker handle that acknowledges a package no claim handed out fails the
/// run as well: every thread asleep in `wait` wakes, and a later claim answers `Failed`.
#[test]
fn a_refusal_without_a_worker_handle_fails_the_run() {
    for threads in [2, 4, 8] {
        within(format!("{threads} threads"), move || {
            let woken = with_sleepers(threads, |dispatcher, package| {
                let misuse = thread::scope(|scope| {
                    scope
                        .spawn(|| {
                            dispatcher.acknowledge(WorkPackage {
                                pipeline: PipelineId(1),
                                epoch: 0,
                                ..package
                            });
                        })
                        .join()
                });
                assert!(misuse.is_err(), "pipeline 1 claimed no package");
                assert!(matches!(dispatcher.try_claim(None), Next::Failed));
            });
            assert!(woken.iter().all(|next| matches!(next, Next::Failed)));
        });
    }
}

/// A claim before a source has started finalizes nothing: it waits, and the workers spawned
/// before the sources start consume every package once they do.
#[test]
fn workers_spawned_before_the_sources_start_wait_for_them() {
    let script = Script::chains(&[2], 64, 4);
    let dispatcher = script.dispatcher();
    assert!(matches!(dispatcher.try_claim(None), Next::Wait(_)));
    for threads in THREADS {
        let what = format!("{threads} threads");
        within(what, move || {
            let script = Script::chains(&[2, 1, 3], 2, 10);
            let (single, _) = single_threaded(&script);
            let dispatcher = script.dispatcher();
            let observed = Observed::of(&script);
            let plans = workers(threads, 17, script.count(), true);
            let records: Vec<Record> = thread::scope(|scope| {
                let handles: Vec<_> = plans
                    .iter()
                    .map(|plan| scope.spawn(|| work(&dispatcher, &script, &observed, *plan)))
                    .collect();
                thread::sleep(Duration::from_millis(5));
                script.start(&dispatcher);
                handles
                    .into_iter()
                    .flat_map(|h| h.join().unwrap_or_else(|panic| resume_unwind(panic)))
                    .collect()
            });
            assert_same_outcome(&outcome_of(&script, records), &single);
        });
    }
}

/// A child that pushes nothing, because it holds nothing or keeps no key: its parent consumes
/// no package and still finishes.
#[test]
fn a_parent_of_a_child_that_pushes_nothing_still_finishes() {
    for threads in THREADS {
        let mut script = Script::chains(&[3, 2, 2], 1, 10);
        script.keep = vec![0, 1, 1, 1, 0, 2, 0];
        script.positions[5] = 0;
        let workers = workers(threads, 3, script.count(), true);
        agrees_with_the_single_threaded_run(script, workers, format!("{threads} threads"));
    }
}

#[test]
fn a_single_pipeline_runs_on_many_threads() {
    for threads in THREADS {
        let script = Script::chains(&[1], 1, 40);
        let workers = workers(threads, 5, 1, true);
        agrees_with_the_single_threaded_run(script, workers, format!("{threads} threads"));
    }
}

#[test]
fn many_independent_pipelines_run_on_many_threads() {
    for threads in THREADS {
        let script = Script::chains(&[1; 32], 2, 12);
        let workers = workers(threads, 11, script.count(), true);
        agrees_with_the_single_threaded_run(script, workers, format!("{threads} threads"));
    }
}

#[test]
fn a_long_chain_at_morsels_of_one_row() {
    for threads in THREADS {
        let script = Script::chains(&[12], 1, 30);
        let workers = workers(threads, 13, script.count(), true);
        agrees_with_the_single_threaded_run(script, workers, format!("{threads} threads"));
    }
}

/// One racy scenario, two hundred times: three chains of mixed order at morsels of one row on
/// eight threads.
#[test]
fn a_racy_scenario_holds_over_many_iterations() {
    for iteration in 1..=200u64 {
        let mut script = Script::chains(&[3, 2, 1], 1, 16);
        script.ordered = vec![false, true, false, true, false, false];
        script.keep = vec![1, 2, 1, 1, 3, 1];
        let workers = workers(8, iteration, script.count(), iteration % 2 == 0);
        agrees_with_the_single_threaded_run(script, workers, format!("iteration {iteration}"));
    }
}

/// A wait for an epoch a change has already advanced past returns at once.
#[test]
fn a_wait_after_a_change_returns_at_once() {
    within("one thread".to_string(), || {
        let script = Script::chains(&[2], 64, 4);
        let dispatcher = script.dispatcher();
        script.start(&dispatcher);
        let Next::Package(package) = dispatcher.try_claim(None) else {
            panic!("the source's one package");
        };
        let Next::Wait(epoch) = dispatcher.try_claim(None) else {
            panic!("nothing to claim while the package is in flight");
        };
        dispatcher.acknowledge(package);
        dispatcher.wait(epoch);
        assert!(matches!(
            dispatcher.try_claim(None),
            Next::Finalize {
                pipeline: PipelineId(0),
                ..
            }
        ));
    });
}

/// One claim hands a pipeline's finalize out; the next answers `Wait` until it finishes.
#[test]
fn a_finalize_is_handed_out_once() {
    let script = Script::chains(&[1], 64, 4);
    let dispatcher = script.dispatcher();
    script.start(&dispatcher);
    let Next::Package(package) = dispatcher.try_claim(None) else {
        panic!("the source's one package");
    };
    dispatcher.acknowledge(package);
    let Next::Finalize { pipeline, .. } = dispatcher.try_claim(None) else {
        panic!("the source finalizes");
    };
    assert!(matches!(dispatcher.try_claim(None), Next::Wait(_)));
    dispatcher.finish(dispatcher.pushes(pipeline));
    assert!(matches!(dispatcher.try_claim(None), Next::Done));
}

/// A claim takes the preferred pipeline's package where it has one, and the lowest pipeline's
/// otherwise.
#[test]
fn a_claim_prefers_the_pipeline_it_is_given() {
    let script = Script::chains(&[1, 1, 1], 64, 4);
    let dispatcher = script.dispatcher();
    script.start(&dispatcher);
    let claimed = |preferred| match dispatcher.try_claim(preferred) {
        Next::Package(package) => package.pipeline,
        other => panic!("a package, got {other:?}"),
    };
    assert_eq!(claimed(Some(PipelineId(2))), PipelineId(2));
    assert_eq!(claimed(Some(PipelineId(2))), PipelineId(0));
    assert_eq!(claimed(None), PipelineId(1));
}

/// After a failure every claim answers `Failed`, packages queued or not.
#[test]
fn a_claim_after_a_failure_answers_failed() {
    let script = Script::chains(&[1], 1, 4);
    let dispatcher = script.dispatcher();
    script.start(&dispatcher);
    dispatcher.fail();
    assert!(matches!(dispatcher.try_claim(None), Next::Failed));
    assert!(matches!(dispatcher.claim(None), Next::Failed));
}

/// A notifying thread queues a source's input in runs and seals an epoch every few runs, into a
/// window of two epochs, while workers claim. Each epoch's finish of the source pushes what it
/// consumed in that epoch to the reader. Every key is consumed once by each, every pipeline
/// finishes every epoch once, and the reader claims a package of an epoch only after the source
/// finished it. An ordered source claims an epoch's packages only after it finished the epoch
/// before.
#[test]
fn epochs_sealed_while_workers_claim() {
    for iteration in 1..=60u64 {
        for threads in [1, 2, 8, 16] {
            let what = format!("iteration {iteration}, {threads} threads");
            within(what, move || sealed_while_claimed(iteration, threads));
        }
    }
}

fn sealed_while_claimed(seed: u64, threads: usize) {
    let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], 1 + (seed % 3) as usize);
    dispatcher.window(2);
    if seed.is_multiple_of(2) {
        dispatcher.order(PipelineId(0));
    }
    let consumed = [AtomicU64::new(0), AtomicU64::new(0)];
    let finishes = Mutex::new(Vec::new());
    // Each claim of a package, logged after the claim returns, and each finish, logged before
    // the finish lets a reader claim: (pipeline, epoch, whether it is a finish).
    let log = Mutex::new(Vec::new());
    let sealed = AtomicU64::new(0);
    thread::scope(|scope| {
        let (dispatcher, consumed, finishes, log, sealed) =
            (&dispatcher, &consumed, &finishes, &log, &sealed);
        scope.spawn(move || {
            let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15));
            let mut key = 0;
            while key < UNIVERSE {
                let last = (key + rng.below(6)).min(UNIVERSE - 1);
                dispatcher.notify(PipelineId(0), &keys_between(key, last));
                key = last + 1;
                if rng.below(3) == 0 {
                    dispatcher.seal();
                    sealed.fetch_add(1, SeqCst);
                }
                jitter(&mut rng);
            }
            dispatcher.close(PipelineId(0));
        });
        for at in 0..threads {
            scope.spawn(move || {
                let _worker = dispatcher.worker();
                let mut rng = Rng(seed ^ (at as u64 + 1) << 32);
                loop {
                    match dispatcher.claim(None) {
                        Next::Package(package) => {
                            let p = package.pipeline.0;
                            log.lock()
                                .expect("no worker panics")
                                .push((p, package.epoch, false));
                            let mask = mask_of(&package.guard);
                            jitter(&mut rng);
                            let before = consumed[p].fetch_or(mask, SeqCst);
                            assert_eq!(before & mask, 0, "pipeline {p} consumes each key once");
                            dispatcher.acknowledge(package);
                        }
                        Next::Finalize {
                            pipeline,
                            epoch,
                            consumed: region,
                            ..
                        } => {
                            finishes
                                .lock()
                                .expect("no worker panics")
                                .push((pipeline.0, epoch));
                            log.lock()
                                .expect("no worker panics")
                                .push((pipeline.0, epoch, true));
                            let mut pushes = dispatcher.pushes_in(pipeline, epoch);
                            if let (PipelineId(0), Some(region)) = (pipeline, &region) {
                                pushes.push(region, cut);
                            }
                            dispatcher.finish(pushes);
                        }
                        Next::Done => return,
                        Next::Failed => panic!("the run failed"),
                        Next::Wait(_) => unreachable!("a blocking claim waits itself"),
                    }
                }
            });
        }
    });
    assert_eq!(
        consumed.each_ref().map(|keys| keys.load(SeqCst)),
        [u64::MAX; 2]
    );
    let mut finishes = finishes.into_inner().expect("no worker panics");
    let epochs = sealed.load(SeqCst) + 1;
    finishes.sort();
    let expected: Vec<_> = (0..2)
        .flat_map(|p| (0..epochs).map(move |epoch| (p, epoch)))
        .collect();
    assert_eq!(
        finishes, expected,
        "every pipeline finishes every epoch once"
    );
    let log = log.into_inner().expect("no worker panics");
    for (at, &(p, epoch, finish)) in log.iter().enumerate() {
        let finished_before = |q, e| log[..at].contains(&(q, e, true));
        if p == 1 && !finish {
            assert!(
                finished_before(0, epoch),
                "the reader claims a package of epoch {epoch} after the source finished it"
            );
        }
        if p == 0 && !finish && seed.is_multiple_of(2) && epoch > 0 {
            assert!(
                finished_before(0, epoch - 1),
                "the ordered source claims in epoch {epoch} after it finished the epoch before"
            );
        }
    }
}

/// Two threads notify one source, each half of its keys, while a third seals epochs into a
/// window of two and closes the source once the notifies are done, and workers claim. A notify
/// that read the current epoch before a seal moved past it lands in a later epoch. Every key is
/// consumed once, and the source finishes every epoch once. The races of a notify with a seal and
/// with an acknowledgement are a few instructions wide, so the test runs them without forcing
/// either.
#[test]
fn a_source_notified_from_two_threads_while_a_third_seals() {
    for iteration in 1..=60u64 {
        for threads in [1, 2, 8] {
            let what = format!("iteration {iteration}, {threads} threads");
            within(what, move || notified_while_sealed(iteration, threads));
        }
    }
}

fn notified_while_sealed(seed: u64, threads: usize) {
    let mut dispatcher = Dispatcher::new(vec![vec![]], 1 + (seed % 3) as usize);
    dispatcher.window(2);
    let consumed = AtomicU64::new(0);
    let finishes = Mutex::new(Vec::new());
    let notified = AtomicUsize::new(0);
    let sealed = AtomicU64::new(0);
    thread::scope(|scope| {
        let (dispatcher, consumed, finishes, notified, sealed) =
            (&dispatcher, &consumed, &finishes, &notified, &sealed);
        for half in 0..2 {
            scope.spawn(move || {
                let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ half);
                let end = (half + 1) * UNIVERSE / 2;
                let mut key = half * UNIVERSE / 2;
                while key < end {
                    let last = (key + rng.below(6)).min(end - 1);
                    dispatcher.notify(PipelineId(0), &keys_between(key, last));
                    key = last + 1;
                    jitter(&mut rng);
                }
                notified.fetch_add(1, SeqCst);
            });
        }
        scope.spawn(move || {
            let mut rng = Rng(seed ^ 0x5ea1);
            while notified.load(SeqCst) < 2 {
                dispatcher.seal();
                sealed.fetch_add(1, SeqCst);
                jitter(&mut rng);
            }
            dispatcher.close(PipelineId(0));
        });
        for at in 0..threads {
            scope.spawn(move || {
                let _worker = dispatcher.worker();
                let mut rng = Rng(seed ^ (at as u64 + 1) << 32);
                loop {
                    match dispatcher.claim(None) {
                        Next::Package(package) => {
                            let mask = mask_of(&package.guard);
                            jitter(&mut rng);
                            let before = consumed.fetch_or(mask, SeqCst);
                            assert_eq!(before & mask, 0, "the source consumes each key once");
                            dispatcher.acknowledge(package);
                        }
                        Next::Finalize {
                            pipeline, epoch, ..
                        } => {
                            finishes.lock().expect("no worker panics").push(epoch);
                            dispatcher.finish(dispatcher.pushes_in(pipeline, epoch));
                        }
                        Next::Done => return,
                        Next::Failed => panic!("the run failed"),
                        Next::Wait(_) => unreachable!("a blocking claim waits itself"),
                    }
                }
            });
        }
    });
    assert_eq!(consumed.load(SeqCst), u64::MAX);
    let mut finishes = finishes.into_inner().expect("no worker panics");
    finishes.sort();
    assert_eq!(
        finishes,
        (0..sealed.load(SeqCst) + 1).collect::<Vec<_>>(),
        "the source finishes every epoch once"
    );
}

/// A notifying thread of a limited source waits for the workers: after each of its notifies of
/// one key, at most `limit` packages are outstanding, and every key is consumed once.
#[test]
fn a_limited_source_holds_its_notifying_thread_back() {
    for iteration in 1..=40u64 {
        for threads in [1, 2, 8] {
            let what = format!("iteration {iteration}, {threads} threads");
            within(what, move || limited(iteration, threads));
        }
    }
}

fn limited(seed: u64, threads: usize) {
    let limit = 1 + (seed % 3) as usize;
    let mut dispatcher = Dispatcher::new(vec![vec![]], 1);
    dispatcher.limit(PipelineId(0), limit);
    let consumed = AtomicU64::new(0);
    thread::scope(|scope| {
        let (dispatcher, consumed) = (&dispatcher, &consumed);
        scope.spawn(move || {
            for key in 0..UNIVERSE {
                dispatcher.notify(PipelineId(0), &keys_between(key, key));
                let outstanding = dispatcher.outstanding(PipelineId(0));
                assert!(
                    outstanding <= limit,
                    "{outstanding} outstanding past {limit}"
                );
            }
            dispatcher.close(PipelineId(0));
        });
        for at in 0..threads {
            scope.spawn(move || {
                let _worker = dispatcher.worker();
                let mut rng = Rng(seed ^ (at as u64 + 1) << 32);
                loop {
                    match dispatcher.claim(None) {
                        Next::Package(package) => {
                            jitter(&mut rng);
                            let mask = mask_of(&package.guard);
                            assert_eq!(consumed.fetch_or(mask, SeqCst) & mask, 0);
                            dispatcher.acknowledge(package);
                        }
                        Next::Finalize {
                            pipeline, epoch, ..
                        } => dispatcher.finish(dispatcher.pushes_in(pipeline, epoch)),
                        Next::Done => return,
                        Next::Failed => panic!("the run failed"),
                        Next::Wait(_) => unreachable!("a blocking claim waits itself"),
                    }
                }
            });
        }
    });
    assert_eq!(consumed.load(SeqCst), u64::MAX);
}

/// A notify waiting at its limit wakes and returns once the run fails, having queued nothing.
#[test]
fn a_notify_at_its_limit_returns_once_the_run_fails() {
    within("a waiting notify".to_string(), || {
        let mut dispatcher = Dispatcher::new(vec![vec![]], 1);
        dispatcher.limit(PipelineId(0), 1);
        dispatcher.notify(PipelineId(0), &keys_between(0, 0));
        thread::scope(|scope| {
            let dispatcher = &dispatcher;
            let waiting =
                scope.spawn(move || dispatcher.notify(PipelineId(0), &keys_between(1, 1)));
            while dispatcher.waiting() == 0 {
                thread::yield_now();
            }
            dispatcher.fail();
            waiting.join().expect("the notify returns");
        });
        assert_eq!(dispatcher.outstanding(PipelineId(0)), 1);
    });
}
