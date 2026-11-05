//! The dispatcher of `crate::interpreter::dispatcher` driving real breakers and scripted ones over
//! scripted inputs.

use std::cell::RefCell;
use std::rc::Rc;

use std::collections::BTreeSet;

use super::aggregate::{aggregate_over, extract_aggregate_over, map_aggregate_over};
use super::extract_final::extract_final_of;
use super::fanout::MemoProducer;
use super::growing::{
    Input, KEYS, NestedInput, ReadsBreaker, Rng, Shared, entries, ints, keys_predicate,
    nested_tiling, predicate, rows_of, same_region, source, value,
};
use super::test_helpers::{keys_between, push_to, wire};
use super::*;
use crate::ccl::AggregateKind;
use crate::interpreter::dispatcher::consume as hand_over;
use crate::interpreter::dispatcher::{
    BreakerHandle, Dispatcher, Event, Next, PipelineId, WorkPackage, finish_epoch, run,
};
use crate::interpreter::{
    BaseType, ColumnValue, Extent, WakeupQueue, domain_prefix, forwarding_consumer_tagging,
    shared_consumer,
};

/// A morsel size larger than any held collection: every guard is one morsel.
const UNBOUNDED: usize = usize::MAX;

/// A breaker the test keeps a typed handle on, and passes to the driver as a [`BreakerHandle`].
// shared-state-ok: the test reads the breaker through this handle after the driver has run it; no
// tile passes between operators through it.
type Held<T> = Rc<RefCell<T>>;

fn consume(pipeline: usize, guard: TileGuard) -> Event {
    Event::Consume {
        pipeline: PipelineId(pipeline),
        guard,
    }
}

fn finished(pipeline: usize) -> Event {
    Event::Finish(PipelineId(pipeline))
}

fn memo_over_rows(rows: std::ops::Range<u64>) -> Held<MemoProducer> {
    Rc::new(RefCell::new(MemoProducer::over(
        Box::new(Input::over(&source(rows))),
        &ints(),
    )))
}

fn memo_reading(read: &BreakerHandle) -> Held<MemoProducer> {
    Rc::new(RefCell::new(MemoProducer::over(
        Box::new(ReadsBreaker::of(read)),
        &ints(),
    )))
}

fn sum_tiling() -> Tiling {
    Tiling::Aggregation {
        kind: AggregateKind::Sum,
        accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
    }
}

/// The events of a run of `breakers` over the pipelines `reads` describes, one morsel per guard.
fn run_over(reads: Vec<Vec<usize>>, breakers: &[BreakerHandle]) -> Vec<Event> {
    run_cut(reads, breakers, UNBOUNDED)
}

/// The events of a run of `breakers` over the pipelines `reads` describes, in morsels of at most
/// `rows` held rows.
fn run_cut(reads: Vec<Vec<usize>>, breakers: &[BreakerHandle], rows: usize) -> Vec<Event> {
    wire(&reads, breakers);
    let dispatcher = Dispatcher::new(reads, rows);
    run(&dispatcher, breakers);
    dispatcher.into_events()
}

/// A breaker that holds what the test says, and drains its input at every consume unless it
/// keeps it.
struct Scripted {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    held: TileGuard,
    /// What each consume releases of its input.
    releases: Option<TileGuard>,
    /// The morsels it cuts any guard into, where the test names them.
    cut: Option<Vec<TileGuard>>,
}

impl Scripted {
    fn holding(held: TileGuard) -> Held<Scripted> {
        Self::new(held, true)
    }

    /// A breaker whose consume releases nothing of its input.
    fn keeping(held: TileGuard) -> Held<Scripted> {
        Self::new(held, false)
    }

    fn new(held: TileGuard, releases: bool) -> Held<Scripted> {
        let input = Input::over(&source(0..4));
        let releases = releases.then(|| input.tiling().universal_guard());
        Self::over(Box::new(input), held, releases)
    }

    /// A breaker over `input` whose consume releases `released` of it.
    fn releasing(input: Box<dyn TileProducer>, released: TileGuard) -> Held<Scripted> {
        Self::over(input, ints().universal_guard(), Some(released))
    }

    fn over(
        input: Box<dyn TileProducer>,
        held: TileGuard,
        releases: Option<TileGuard>,
    ) -> Held<Scripted> {
        Rc::new(RefCell::new(Scripted {
            base: ProducerBase::unowned(Self::alloc_id(), &ints()),
            input,
            held,
            releases,
            cut: None,
        }))
    }

    /// A breaker that holds `held` and cuts it into `cut`.
    fn cutting(held: TileGuard, cut: Vec<TileGuard>) -> Held<Scripted> {
        let scripted = Self::holding(held);
        scripted.borrow_mut().cut = Some(cut);
        scripted
    }
}

impl TileProducer for Scripted {
    impl_producer_base!();

    fn get_impl(&mut self, _guard: TileGuard) -> Tile {
        self.tiling().empty_tile()
    }

    fn release_impl(&mut self, _guard: TileGuard) {}
}

impl Breaker for Scripted {
    fn enter_consuming_mode(&mut self) {}

    fn consume_impl(&mut self, _: InputId, guard: TileGuard) {
        self.input.get(guard);
        if let Some(released) = &self.releases {
            self.input.release(released.clone());
        }
    }

    fn input_tiling(&self, _: InputId) -> Tiling {
        self.input.tiling().clone()
    }

    fn input_released(&self, _: InputId) -> TileGuard {
        self.input.obsolete_guard().clone()
    }

    fn as_producer(&self) -> Option<&dyn BreakingProducer> {
        Some(self)
    }
}

impl BreakingProducer for Scripted {
    fn held(&self) -> TileGuard {
        self.held.clone()
    }

    fn morsels(&self, guard: &TileGuard, _rows: usize) -> Vec<TileGuard> {
        self.cut.clone().unwrap_or_else(|| vec![guard.clone()])
    }

    fn offer_impl(&mut self, _guard: TileGuard) -> Tile {
        self.tiling().empty_tile()
    }
}

/// One pipeline consumes its input whole, then finishes, and pushes to no one.
#[test]
fn one_pipeline_consumes_everything_then_finishes() {
    let memo = memo_over_rows(0..6);
    let handle: BreakerHandle = memo.clone();
    let events = run_over(vec![vec![]], &[handle]);
    assert_eq!(
        events,
        vec![consume(0, ints().universal_guard()), finished(0)]
    );
    assert_eq!(
        entries(&memo.borrow_mut().get(ints().universal_guard())),
        rows_of(0..6)
    );
}

/// A memo read by a memo: the reader consumes exactly the guard the source pushed after its
/// consume, before the source finishes.
#[test]
fn a_reader_memo_consumes_the_guard_its_source_pushed() {
    let memo = memo_over_rows(0..6);
    let memo_handle: BreakerHandle = memo.clone();
    let reader = memo_reading(&memo_handle);
    let events = run_over(vec![vec![], vec![0]], &[memo_handle, reader.clone()]);
    // The source held everything and nothing was released when it pushed. The reader has
    // released the source's output since, so the source's pushed guard is read from the events.
    let pushed = ints().universal_guard();
    assert_eq!(
        events,
        vec![
            consume(0, ints().universal_guard()),
            consume(1, pushed),
            finished(0),
            finished(1),
        ]
    );
    assert_eq!(
        entries(&reader.borrow_mut().get(ints().universal_guard())),
        rows_of(0..6)
    );
}

/// A memo read by an aggregate: the aggregate folds what the memo pushed.
#[test]
fn an_aggregate_folds_what_the_memo_below_it_pushed() {
    let memo = memo_over_rows(0..6);
    let memo_handle: BreakerHandle = memo.clone();
    let sum = aggregate_over(Box::new(ReadsBreaker::of(&memo_handle)), &sum_tiling());
    let events = run_over(vec![vec![], vec![0]], &[memo_handle, sum.clone()]);
    assert_eq!(events[1], consume(1, ints().universal_guard()));
    assert!(
        memo.borrow().final_guard().is_empty(),
        "the aggregate released what it read"
    );
    let total: i64 = (0..6).map(value).sum();
    let Tile::Aggregation { accumulator, .. } =
        sum.borrow_mut().get(sum_tiling().universal_guard())
    else {
        panic!("an aggregation")
    };
    assert_eq!(*accumulator, Tile::Scalar(ColumnValue::Ints(vec![total])));
}

/// A breaker whose consumer released part of its state pushes only what is left.
#[test]
fn a_partly_released_breaker_pushes_only_what_is_left() {
    let memo = memo_over_rows(0..6);
    memo.borrow_mut().enter_consuming_mode();
    memo.borrow_mut()
        .consume_impl(InputId::ONLY, ints().universal_guard());
    memo.borrow_mut().release(keys_between(2, 3));
    push_to(&mut *memo.borrow_mut(), &[1]);
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        memo.borrow_mut().finish(pushes, true)
    });
    let package = dispatcher.pop().expect("one package for the reader");
    assert_eq!(package.pipeline, PipelineId(1));
    assert!(same_region(
        &predicate(&package.guard),
        &Predicate::True.minus(&keys_predicate(2, 3))
    ));
    assert_eq!(dispatcher.pop(), None, "one package");
}

/// Every pipeline reading a breaker is queued each morsel the breaker pushes, and finishes after
/// the breaker.
#[test]
fn a_breaker_read_by_several_pipelines_pushes_to_each() {
    let (low, high) = (
        keys_between(0, 1),
        TileGuard::Function(FunctionGuard::Domain(
            Predicate::True.minus(&keys_predicate(0, 1)),
        )),
    );
    let scripted = Scripted::cutting(ints().universal_guard(), vec![low.clone(), high.clone()]);
    let readers: Vec<BreakerHandle> = (0..2)
        .map(|_| -> BreakerHandle { Scripted::holding(ints().universal_guard()) })
        .collect();
    let breakers: Vec<BreakerHandle> = std::iter::once(scripted as BreakerHandle)
        .chain(readers)
        .collect();
    let events = run_over(vec![vec![], vec![0], vec![0]], &breakers);
    let finished_at = |p: usize| {
        events
            .iter()
            .position(|event| *event == finished(p))
            .expect("every pipeline finishes")
    };
    for reader in [1, 2] {
        assert!(
            finished_at(0) < finished_at(reader),
            "{reader} after the breaker it reads"
        );
        assert_eq!(
            consumed_by(&events, reader),
            vec![low.clone(), high.clone()]
        );
    }
}

/// A pipeline names each pipeline it reads once.
#[test]
#[should_panic(expected = "pipeline 1 reads pipeline 0 once")]
fn a_pipeline_reading_one_pipeline_twice_is_refused() {
    Dispatcher::new(vec![vec![], vec![0, 0]], UNBOUNDED);
}

/// The two halves of the integers' keys, held by two breakers.
fn halves() -> (TileGuard, TileGuard) {
    (
        keys_between(0, 1),
        TileGuard::Function(FunctionGuard::Domain(
            Predicate::True.minus(&keys_predicate(0, 1)),
        )),
    )
}

/// A pipeline that reads two consumes what each pushes, and finishes after both: its queue closes
/// at the finish of the last of them.
#[test]
fn a_reader_of_two_pipelines_consumes_both_and_finishes_after_both() {
    let (low, high) = halves();
    let breakers: Vec<BreakerHandle> = vec![
        Scripted::holding(low.clone()),
        Scripted::holding(high.clone()),
        Scripted::holding(ints().universal_guard()),
    ];
    let events = run_over(vec![vec![], vec![], vec![0, 1]], &breakers);
    let at = |event: &Event| {
        events
            .iter()
            .position(|seen| seen == event)
            .expect("happens")
    };
    assert!(at(&finished(0)) < at(&finished(2)) && at(&finished(1)) < at(&finished(2)));
    let consumed: BTreeSet<_> = consumed_by(&events, 2)
        .into_iter()
        .map(|guard| format!("{guard:?}"))
        .collect();
    assert_eq!(
        consumed,
        BTreeSet::from([format!("{low:?}"), format!("{high:?}")])
    );
}

/// A reader takes no push of a pipeline it follows, and no package before that pipeline has
/// finished the epoch: here pipeline 2 follows 1 and takes 0's pushes.
#[test]
fn a_reader_takes_nothing_before_the_pipeline_it_follows_finishes() {
    let (low, high) = halves();
    let breakers: Vec<BreakerHandle> = vec![
        Scripted::holding(low.clone()),
        Scripted::holding(high),
        Scripted::holding(ints().universal_guard()),
    ];
    let reads = vec![vec![], vec![], vec![0, 1]];
    wire(&reads, &breakers);
    let mut dispatcher = Dispatcher::new(reads, UNBOUNDED);
    dispatcher.follow(PipelineId(2), PipelineId(1));
    run(&dispatcher, &breakers);
    let events = dispatcher.into_events();
    let first = events
        .iter()
        .position(|event| {
            matches!(
                event,
                Event::Consume {
                    pipeline: PipelineId(2),
                    ..
                }
            )
        })
        .expect("pipeline 2 consumes");
    let built = events
        .iter()
        .position(|event| *event == finished(1))
        .expect("pipeline 1 finishes");
    assert!(built < first, "{events:?}");
    assert_eq!(consumed_by(&events, 2), vec![low]);
}

/// The driver consumes the lowest pipeline's package first and finishes only when nothing is
/// queued, which pins the order across two chains: pipeline 0's push lands as it consumes, and
/// pipeline 2 consumes it before any pipeline finishes.
#[test]
fn the_lowest_pipelines_package_goes_first_and_finishing_waits_for_an_empty_queue() {
    let (left, right) = (keys_between(0, 1), keys_between(2, 3));
    let breakers: Vec<BreakerHandle> = vec![
        Scripted::holding(left.clone()),
        Scripted::holding(right),
        Scripted::holding(ints().universal_guard()),
    ];
    let all = ints().universal_guard();
    let events = run_over(vec![vec![], vec![], vec![0]], &breakers);
    assert_eq!(
        events,
        vec![
            consume(0, all.clone()),
            consume(1, all),
            consume(2, left),
            finished(0),
            finished(1),
            finished(2),
        ]
    );
}

/// An empty final guard pushes nothing, and the pipeline that reads it still finishes.
#[test]
fn an_empty_final_guard_pushes_nothing_and_the_reader_finishes() {
    let breakers: Vec<BreakerHandle> = vec![
        Scripted::holding(ints().empty_guard()),
        Scripted::holding(ints().universal_guard()),
    ];
    let events = run_over(vec![vec![], vec![0]], &breakers);
    assert_eq!(
        events,
        vec![
            consume(0, ints().universal_guard()),
            finished(0),
            finished(1)
        ]
    );
}

#[test]
#[should_panic(expected = "pipeline 1 finishes after its queue is empty")]
fn finish_with_a_package_queued_panics() {
    let breakers: Vec<BreakerHandle> = vec![
        Scripted::holding(ints().universal_guard()),
        Scripted::holding(ints().universal_guard()),
    ];
    wire(&[vec![], vec![0]], &breakers);
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    breakers[0].borrow_mut().enter_consuming_mode();
    breakers[0]
        .borrow_mut()
        .consume_impl(InputId::ONLY, ints().universal_guard());
    dispatcher.close(PipelineId(0));
    finish_epoch(&dispatcher, &breakers, PipelineId(0));
    finish_epoch(&dispatcher, &breakers, PipelineId(1));
}

#[test]
#[should_panic(expected = "pipeline 1 finishes after every pipeline it reads has finished")]
fn finish_before_an_upstream_pipeline_finished_panics() {
    let breakers: Vec<BreakerHandle> = vec![
        Scripted::holding(ints().universal_guard()),
        Scripted::holding(ints().universal_guard()),
    ];
    finish_epoch(
        &Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED),
        &breakers,
        PipelineId(1),
    );
}

#[test]
#[should_panic(expected = "pipeline 1 finishes once")]
fn finish_twice_panics() {
    let breakers: Vec<BreakerHandle> = vec![
        Scripted::holding(ints().universal_guard()),
        Scripted::holding(ints().universal_guard()),
    ];
    wire(&[vec![], vec![0]], &breakers);
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    run(&dispatcher, &breakers);
    finish_epoch(&dispatcher, &breakers, PipelineId(1));
}

/// A source finishes once its input has released every region queued for it: one whose input
/// released less than its queue named would push what rests on rows the input has not stated.
#[test]
#[should_panic(
    expected = "pipeline 0 finishes after its input has released every guard the pipeline consumed"
)]
fn a_source_pipeline_finishes_after_its_input_released_what_was_queued() {
    let memo = memo_over_rows(0..6);
    let handle: BreakerHandle = memo.clone();
    let dispatcher = Dispatcher::new(vec![vec![]], UNBOUNDED);
    dispatcher.start_source(PipelineId(0), &ints(), &ints().empty_guard());
    let Next::Package(package) = dispatcher.try_claim(None) else {
        panic!("a started source hands out its package")
    };
    memo.borrow_mut().enter_consuming_mode();
    memo.borrow_mut()
        .consume_impl(InputId::ONLY, keys_between(0, 3));
    dispatcher.acknowledge(package);
    finish_epoch(&dispatcher, &[handle], PipelineId(0));
}

/// An input of `0..2 ⤇ 0..3 ⤇ Int` that answers nothing: a test names what it releases.
struct Positions {
    base: ProducerBase,
}

impl Positions {
    fn new() -> Self {
        let tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::data_function(
                Extent::uint_range(3),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        Positions {
            base: ProducerBase::unowned(Self::alloc_id(), &tiling),
        }
    }
}

impl TileProducer for Positions {
    impl_producer_base!();

    fn get_impl(&mut self, _guard: TileGuard) -> Tile {
        self.tiling().empty_tile()
    }

    fn release_impl(&mut self, _guard: TileGuard) {}
}

/// Finish source pipeline 0 after it consumed row 0 of a `Positions` input whole and the input
/// released everything at or below `path`.
fn finish_row_released_through(path: Vec<Value>) {
    let breaker = Scripted::releasing(Box::new(Positions::new()), domain_prefix(path));
    let breakers: Vec<BreakerHandle> = vec![breaker];
    let dispatcher = Dispatcher::new(vec![vec![]], UNBOUNDED);
    dispatcher.notify(PipelineId(0), &keys_between(0, 0));
    dispatcher.close(PipelineId(0));
    let Next::Package(package) = dispatcher.try_claim(None) else {
        panic!("a notified source hands out its package")
    };
    hand_over(&dispatcher, &breakers, package);
    finish_epoch(&dispatcher, &breakers, PipelineId(0));
}

/// An input that released a row through its last position has released the row: the row's paths
/// past it name no position of the row's range.
#[test]
fn a_pipeline_finishes_once_its_input_released_a_row_through_its_last_position() {
    finish_row_released_through(vec![Value::UInt(0), Value::UInt(2)]);
}

/// An input that released a row short of its last position has not released the row.
#[test]
#[should_panic(
    expected = "pipeline 0 finishes after its input has released every guard the pipeline consumed"
)]
fn a_pipeline_does_not_finish_while_its_input_holds_a_position_of_a_row_it_consumed() {
    finish_row_released_through(vec![Value::UInt(0), Value::UInt(1)]);
}

/// A reader whose input has not released a guard the reader consumed does not finish: what it
/// would push could rest on rows its input has not stated.
#[test]
#[should_panic(
    expected = "pipeline 1 finishes after its input has released every guard the pipeline consumed"
)]
fn a_reader_finishes_after_its_input_released_what_it_consumed() {
    let breakers: Vec<BreakerHandle> = vec![
        Scripted::holding(ints().universal_guard()),
        Scripted::keeping(ints().universal_guard()),
    ];
    wire(&[vec![], vec![0]], &breakers);
    run(
        &Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED),
        &breakers,
    );
}

/// A package whose guard is not of the tiling the breaker's input answers is refused.
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "pipeline 1 consumes a guard of the tiling its breaker's input answers")]
fn a_package_of_another_tiling_is_refused() {
    // The aggregate pushes a guard of its sum; the scripted breaker's input answers rows.
    let breakers: Vec<BreakerHandle> = vec![
        aggregate_over(Box::new(Input::over(&source(0..6))), &sum_tiling()),
        Scripted::holding(ints().universal_guard()),
    ];
    wire(&[vec![], vec![0]], &breakers);
    run(
        &Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED),
        &breakers,
    );
}

/// A pipeline that reads its input whole consumes that input in morsels that partition it once
/// the pipeline it reads finishes, whatever that pipeline pushes: here a guard of a sum, while
/// the scripted breaker's input answers rows.
#[test]
fn a_pipeline_reading_its_input_whole_consumes_it_in_morsels() {
    let breakers: Vec<BreakerHandle> = vec![
        aggregate_over(Box::new(Input::over(&source(0..6))), &sum_tiling()),
        Scripted::holding(ints().universal_guard()),
    ];
    let input = breakers[1].borrow().input_tiling(InputId::ONLY);
    wire(&[vec![], vec![0]], &breakers);
    let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], 2);
    dispatcher.read_whole(PipelineId(1), &input);
    run(&dispatcher, &breakers);
    let consumed = consumed_by(&dispatcher.into_events(), 1);
    assert!(
        consumed.len() > 1,
        "the rows in morsels of two: {consumed:?}"
    );
    assert_eq!(partition_gap(&input.universal_guard(), &consumed), None);
}

/// A source starts from its input, so it has no pipeline to read whole after.
#[test]
#[should_panic(expected = "pipeline 0 reads its input whole only after a pipeline it reads")]
fn a_source_read_whole_is_refused() {
    Dispatcher::new(vec![vec![]], UNBOUNDED).read_whole(PipelineId(0), &ints());
}

#[test]
#[should_panic(expected = "cycle")]
fn pipelines_that_read_each_other_are_refused() {
    Dispatcher::new(vec![vec![1], vec![0]], UNBOUNDED);
}

// ----------------------------------------------------------------------------------------------
// Morsels
// ----------------------------------------------------------------------------------------------

/// The keys a source holds, with holes, so a morsel's region reaches past the keys it holds.
const SPARSE: [u64; 8] = [0, 1, 3, 4, 5, 8, 10, 11];

fn sums_tiling() -> Tiling {
    Tiling::data_function(Extent::uint_range(KEYS), sum_tiling())
}

fn int() -> Tiling {
    Tiling::Scalar(Extent::Base(BaseType::Int))
}

/// The guards a pipeline consumed, in order.
fn consumed_by(events: &[Event], pipeline: usize) -> Vec<TileGuard> {
    events
        .iter()
        .filter_map(|event| match event {
            Event::Consume {
                pipeline: at,
                guard,
            } if *at == PipelineId(pipeline) => Some(guard.clone()),
            _ => None,
        })
        .collect()
}

/// The keys of `keys` a morsel names.
fn named(morsel: &TileGuard, keys: impl IntoIterator<Item = u64>) -> BTreeSet<u64> {
    keys.into_iter()
        .filter(|key| predicate(morsel).contains(&Value::UInt(*key)))
        .collect()
}

/// The breaker on top of a chain of pipelines over a memo of a source of [`SPARSE`] keys.
#[derive(Clone, Copy, Debug)]
enum Top {
    Memo,
    Sum,
    MapSum,
    Final,
    MemoThenSum,
    MapSumThenMemo,
}

/// A run of the chain `top` names at morsels of `rows`: the events, the source, the top breaker
/// and its tiling.
fn run_chain(top: Top, rows: usize) -> (Vec<Event>, Shared, BreakerHandle, Tiling) {
    let source = source(SPARSE);
    let base: BreakerHandle = match top {
        Top::MapSum | Top::MapSumThenMemo => Rc::new(RefCell::new(MemoProducer::over(
            Box::new(NestedInput::over(&source)),
            &nested_tiling(),
        ))),
        _ => Rc::new(RefCell::new(MemoProducer::over(
            Box::new(Input::over(&source)),
            &ints(),
        ))),
    };
    let reading = |read: &BreakerHandle| Box::new(ReadsBreaker::of(read));
    let mut breakers = vec![base.clone()];
    let (top, tiling) = match top {
        Top::Memo => (memo_reading(&base) as BreakerHandle, ints()),
        Top::Sum => (aggregate_over(reading(&base), &sum_tiling()), sum_tiling()),
        Top::MapSum => (
            map_aggregate_over(reading(&base), &sums_tiling(), AggregateKind::Sum),
            sums_tiling(),
        ),
        Top::Final => (extract_final_of(reading(&base), None, &int()), int()),
        Top::MemoThenSum => {
            let middle: BreakerHandle = memo_reading(&base);
            breakers.push(middle.clone());
            (
                aggregate_over(reading(&middle), &sum_tiling()),
                sum_tiling(),
            )
        }
        Top::MapSumThenMemo => {
            let (middle, tiling) = (
                map_aggregate_over(reading(&base), &sums_tiling(), AggregateKind::Sum),
                sums_tiling(),
            );
            breakers.push(middle.clone());
            let memo: BreakerHandle =
                Rc::new(RefCell::new(MemoProducer::over(reading(&middle), &tiling)));
            (memo, tiling)
        }
    };
    breakers.push(top.clone());
    let reads = (0..breakers.len())
        .map(|pipeline| match pipeline {
            0 => vec![],
            _ => vec![pipeline - 1],
        })
        .collect();
    let events = run_cut(reads, &breakers, rows);
    (events, source, top, tiling)
}

/// `tile` with every collection's statement cleared, so two tiles holding the same rows compare
/// equal however their statements are spelled; what the statements make releasable is compared
/// through `to_guard`. A merge drops an inner statement the level above covers, so a cache built
/// from morsels spells its completeness differently from one built at once.
fn rows_only(mut tile: Tile) -> Tile {
    fn clear(tile: &mut Tile) {
        match tile {
            Tile::DataFunction {
                codomain,
                domain_predicate,
                ..
            } => {
                *domain_predicate = Predicate::False;
                clear(codomain);
            }
            Tile::Record { fields, .. } => fields.values_mut().for_each(clear),
            _ => {}
        }
    }
    clear(&mut tile);
    tile
}

/// Every chain answers the same, and holds the same, at morsels of one row, three rows, and one
/// morsel per guard: the same rows, releasable at the same guard.
#[test]
fn every_chain_answers_the_same_at_every_morsel_size() {
    for top in [
        Top::Memo,
        Top::Sum,
        Top::MapSum,
        Top::Final,
        Top::MemoThenSum,
        Top::MapSumThenMemo,
    ] {
        let outcome = |rows| {
            let (_, _, breaker, tiling) = run_chain(top, rows);
            let held = breaker.borrow().final_guard();
            let answer = breaker.borrow_mut().get(tiling.universal_guard());
            (held, answer.to_guard(), rows_only(answer))
        };
        let whole = outcome(UNBOUNDED);
        for rows in [1, 3] {
            assert_eq!(outcome(rows), whole, "{top:?} at morsels of {rows}");
        }
    }
}

/// An aggregate over a memo becomes terminal at every morsel size: the morsels its input is
/// released at cover the whole input, keys the memo states absent included.
#[test]
fn an_aggregate_over_a_memo_becomes_terminal_at_every_morsel_size() {
    for rows in [1, 3, UNBOUNDED] {
        let (_, _, sum, _) = run_chain(Top::Sum, rows);
        let Tile::Aggregation {
            accumulator,
            terminal,
            ..
        } = sum.borrow_mut().get(sum_tiling().universal_guard())
        else {
            panic!("an aggregation")
        };
        let total = SPARSE.iter().copied().map(value).sum();
        assert_eq!(*accumulator, Tile::Scalar(ColumnValue::Ints(vec![total])));
        assert_eq!(
            terminal,
            ColumnValue::Bools(vec![true]),
            "at morsels of {rows}"
        );
    }
}

/// An extraction over a memo extracts at every morsel size.
#[test]
fn an_extraction_over_a_memo_extracts_at_every_morsel_size() {
    for rows in [1, 3, UNBOUNDED] {
        let (_, _, extract, _) = run_chain(Top::Final, rows);
        assert_eq!(
            extract.borrow_mut().get(int().universal_guard()),
            Tile::Scalar(ColumnValue::Ints(vec![value(11)])),
            "at morsels of {rows}"
        );
    }
}

/// A source over a finite range of positions starts with morsels of `rows` positions, the last
/// one partial when `rows` does not divide the range; each is consumed once, and the input is
/// pulled and released at each.
#[test]
fn a_source_over_a_range_starts_with_morsels_of_rows_positions() {
    let source = source(SPARSE);
    let memo: BreakerHandle = Rc::new(RefCell::new(MemoProducer::over(
        Box::new(Input::over(&source)),
        &ints(),
    )));
    let events = run_cut(vec![vec![]], &[memo], 5);
    let morsels = consumed_by(&events, 0);
    let positions: Vec<_> = morsels.iter().map(|m| named(m, 0..KEYS)).collect();
    assert_eq!(
        positions,
        vec![
            (0..5).collect::<BTreeSet<_>>(),
            (5..10).collect(),
            (10..KEYS).collect()
        ]
    );
    assert_eq!(partition_gap(&ints().universal_guard(), &morsels), None);
    assert_eq!(source.borrow().pulled, morsels, "one pull per morsel");
    assert_eq!(source.borrow().released, morsels, "one release per morsel");
}

/// A memo's morsels hold at most `rows` of its keys each and partition the guard it pushes:
/// keys it states absent ride in one morsel, and released keys are in none.
#[test]
fn a_memos_morsels_partition_its_final_guard_and_leave_out_released_keys() {
    let mut memo = MemoProducer::over(Box::new(Input::over(&source(SPARSE))), &ints());
    memo.enter_consuming_mode();
    memo.consume_impl(InputId::ONLY, ints().universal_guard());
    memo.release(keys_between(3, 3));
    memo.release(keys_between(8, 8));
    let guard = memo.final_guard();
    let morsels = memo.morsels(&guard, 2);
    assert_eq!(partition_gap(&guard, &morsels), None);
    let held = [0, 1, 4, 5, 10, 11];
    let rows: Vec<_> = morsels.iter().map(|m| named(m, held)).collect();
    assert_eq!(
        rows,
        vec![
            BTreeSet::from([0, 1]),
            BTreeSet::from([4, 5]),
            BTreeSet::from([10, 11])
        ]
    );
    for released in [3, 8] {
        assert!(morsels.iter().all(|m| named(m, [released]).is_empty()));
    }
    for absent in [2, 6, 7, 9] {
        let carrying = morsels.iter().filter(|m| !named(m, [absent]).is_empty());
        assert_eq!(carrying.count(), 1, "key {absent} rides in one morsel");
    }
}

/// A source whose reader released part of it pushes morsels over its unreleased keys only.
#[test]
fn a_partly_released_source_pushes_morsels_over_what_is_left() {
    let memo = memo_over_rows(0..6);
    memo.borrow_mut().enter_consuming_mode();
    memo.borrow_mut()
        .consume_impl(InputId::ONLY, ints().universal_guard());
    memo.borrow_mut().release(keys_between(2, 3));
    push_to(&mut *memo.borrow_mut(), &[1]);
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], 2);
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        memo.borrow_mut().finish(pushes, true)
    });
    let mut morsels = Vec::new();
    while let Some(package) = dispatcher.pop() {
        morsels.push(package.guard);
    }
    let rows: Vec<_> = morsels.iter().map(|m| named(m, 0..6)).collect();
    assert_eq!(rows, vec![BTreeSet::from([0, 1]), BTreeSet::from([4, 5])]);
}

/// A breaker whose output is one value pushes it as one morsel at any size.
#[test]
fn a_breaker_of_one_value_pushes_one_morsel() {
    let sum = aggregate_over(Box::new(Input::over(&source(SPARSE))), &sum_tiling());
    sum.borrow_mut().enter_consuming_mode();
    sum.borrow_mut()
        .consume_impl(InputId::ONLY, ints().universal_guard());
    push_to(&mut *sum.borrow_mut(), &[1]);
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], 1);
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        sum.borrow_mut().finish(pushes, true)
    });
    let package = dispatcher.pop().expect("one morsel");
    assert_eq!(package.guard, sum_tiling().universal_guard());
    assert_eq!(dispatcher.pop(), None, "one morsel");
}

fn source_rows(keys: &BTreeSet<u64>) -> Shared {
    source(keys.iter().copied())
}

/// Random held keys, releases and morsel sizes: the morsels partition the final guard, hold at
/// most `rows` held keys each and no released key, and a memo read by a sum folds the same total,
/// terminal, at that size as in one morsel.
#[test]
fn random_morsel_sizes_partition_and_answer_the_same() {
    for seed in 1..=300u64 {
        let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15));
        let keys: BTreeSet<u64> = (0..KEYS).filter(|_| rng.below(3) > 0).collect();
        let released: BTreeSet<u64> = keys.iter().copied().filter(|_| rng.below(4) == 0).collect();
        let rows = match rng.below(6) {
            0 => UNBOUNDED,
            n => n as usize,
        };
        let trace = format!("seed {seed}: keys {keys:?}, released {released:?}, rows {rows}");

        let mut memo = MemoProducer::over(Box::new(Input::over(&source_rows(&keys))), &ints());
        memo.enter_consuming_mode();
        memo.consume_impl(InputId::ONLY, ints().universal_guard());
        for key in &released {
            memo.release(keys_between(*key, *key));
        }
        let guard = memo.final_guard();
        let morsels = memo.morsels(&guard, rows);
        assert_eq!(partition_gap(&guard, &morsels), None, "{trace}");
        for morsel in &morsels {
            assert!(
                named(morsel, released.iter().copied()).is_empty(),
                "{trace}"
            );
            assert!(named(morsel, keys.iter().copied()).len() <= rows, "{trace}");
        }

        let total = |rows| {
            let memo: BreakerHandle = Rc::new(RefCell::new(MemoProducer::over(
                Box::new(Input::over(&source_rows(&keys))),
                &ints(),
            )));
            let sum = aggregate_over(Box::new(ReadsBreaker::of(&memo)), &sum_tiling());
            run_cut(vec![vec![], vec![0]], &[memo, sum.clone()], rows);
            sum.borrow_mut().get(sum_tiling().universal_guard())
        };
        assert_eq!(total(rows), total(UNBOUNDED), "{trace}");
    }
}

/// Morsels that overlap do not partition the guard they cut.
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "the morsels of a pushed guard partition it")]
fn overlapping_morsels_are_refused() {
    let cut = vec![keys_between(0, 5), ints().universal_guard()];
    let breaker = Scripted::cutting(ints().universal_guard(), cut);
    push_to(&mut *breaker.borrow_mut(), &[1]);
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], 1);
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        breaker.borrow_mut().finish(pushes, true)
    });
}

/// A pipeline that would consume a region twice is refused: a guard pushed twice names the region
/// twice.
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "the reader of pipeline 0 consumes each region once")]
fn a_region_consumed_twice_is_refused() {
    let all = ints().universal_guard();
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        for _ in 0..2 {
            pushes.push(&all, |guard, _| vec![guard.clone()]);
        }
    });
}

/// The pipelines of one breaker push into one record of what it pushed: a region one of them
/// pushed, the other pushing again would consume twice, which a debug build refuses.
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "the reader of pipeline 1 consumes each region once")]
fn the_pipelines_of_one_breaker_share_what_it_pushed() {
    let all = ints().universal_guard();
    let mut dispatcher = Dispatcher::new(vec![vec![], vec![], vec![0, 1]], UNBOUNDED);
    dispatcher.share_pushes(&[PipelineId(0), PipelineId(1)]);
    // Both sources closed, so the epoch is the run's last.
    dispatcher.close(PipelineId(1));
    for pipeline in [PipelineId(0), PipelineId(1)] {
        dispatcher.finish_by_hand(pipeline, |pushes| {
            pushes.push(&all, |guard, _| vec![guard.clone()]);
        });
    }
}

/// A breaker's final guard pushed twice pushes it once: the second push is of what the breaker
/// decided since, which is nothing.
#[test]
fn a_final_guard_pushed_twice_is_pushed_once() {
    let all = ints().universal_guard();
    let breakers: Vec<BreakerHandle> = vec![Scripted::holding(all.clone()), Scripted::holding(all)];
    wire(&[vec![], vec![0]], &breakers);
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        for _ in 0..2 {
            breakers[0].borrow_mut().finish(pushes, true);
        }
    });
    let pushed: Vec<_> = std::iter::from_fn(|| dispatcher.pop())
        .map(|package| package.guard)
        .collect();
    assert_eq!(pushed, vec![ints().universal_guard()]);
}

/// A guard naming part of what a memo holds is cut at the held keys it names, and no other.
#[test]
fn a_guard_naming_part_of_what_is_held_is_cut_at_the_keys_it_names() {
    let mut memo = MemoProducer::over(Box::new(Input::over(&source(0..8))), &ints());
    memo.enter_consuming_mode();
    memo.consume_impl(InputId::ONLY, ints().universal_guard());
    let guard = keys_between(3, 6);
    let morsels = memo.morsels(&guard, 2);
    assert_eq!(partition_gap(&guard, &morsels), None);
    let rows: Vec<_> = morsels.iter().map(|m| named(m, 0..8)).collect();
    assert_eq!(rows, vec![BTreeSet::from([3, 4]), BTreeSet::from([5, 6])]);
}

/// A collection whose keys have no order cannot be cut in key order, and says so.
#[test]
#[should_panic(expected = "a collection is cut into morsels in key order, which the key")]
fn keys_without_an_order_are_refused_a_cut() {
    let keys = vec![Value::Function(vec![]); 3];
    cut_at_keys(&ints().universal_guard(), keys, 1, &ints());
}

/// A `MapAggregate` read by a memo pushes one package per morsel of the groups it holds, one per
/// [`SPARSE`] key: each names at most `rows` of them, and together they name every one.
#[test]
fn a_map_aggregate_pushes_a_package_per_morsel_of_its_groups() {
    for (rows, expected) in [
        (
            1,
            vec![
                vec![0],
                vec![1],
                vec![3],
                vec![4],
                vec![5],
                vec![8],
                vec![10],
                vec![11],
            ],
        ),
        (3, vec![vec![0, 1, 3], vec![4, 5, 8], vec![10, 11]]),
        (UNBOUNDED, vec![SPARSE.to_vec()]),
    ] {
        let (events, _, _, _) = run_chain(Top::MapSumThenMemo, rows);
        assert!(read_after_finish(&events, 1, 2), "at morsels of {rows}");
        let packages = consumed_by(&events, 2);
        let named: Vec<Vec<u64>> = packages
            .iter()
            .map(|m| named(m, SPARSE).into_iter().collect())
            .collect();
        assert_eq!(named, expected, "at morsels of {rows}");
        assert_eq!(
            partition_gap(&sums_tiling().universal_guard(), &packages),
            None,
            "at morsels of {rows}"
        );
    }
}

/// Whether `reader` consumes nothing before `pipeline` has finished: the grouped breakers push
/// only at their finish ([`BreakingProducer::pushes_while_consuming`]).
fn read_after_finish(events: &[Event], pipeline: usize, reader: usize) -> bool {
    let finished = events.iter().position(|event| *event == finished(pipeline));
    let first = events.iter().position(
        |event| matches!(event, Event::Consume { pipeline, .. } if *pipeline == PipelineId(reader)),
    );
    finished.is_some_and(|finished| first.is_none_or(|first| first > finished))
}

/// The two morsels a scripted source pushes to an ordered reader, claimed by hand.
fn ordered_reader() -> (Dispatcher, Vec<BreakerHandle>) {
    let high = Predicate::True.minus(&keys_predicate(0, 1));
    let (low, high) = (
        keys_between(0, 1),
        TileGuard::Function(FunctionGuard::Domain(high)),
    );
    let scripted = Scripted::cutting(ints().universal_guard(), vec![low, high]);
    let breakers: Vec<BreakerHandle> = vec![scripted, Scripted::holding(ints().universal_guard())];
    wire(&[vec![], vec![0]], &breakers);
    let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.order(PipelineId(1));
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        breakers[0].borrow_mut().finish(pushes, true)
    });
    (dispatcher, breakers)
}

/// An ordered pipeline consumes the morsel claimed for it: a later one handed over first is
/// refused.
#[test]
#[should_panic(expected = "ordered pipeline 1 consumes the morsel claimed for it, in queue order")]
fn a_later_morsel_consumed_first_is_refused() {
    let (dispatcher, breakers) = ordered_reader();
    let first = dispatcher.pop().expect("the lower morsel");
    let later = WorkPackage {
        pipeline: first.pipeline,
        epoch: 0,
        guard: TileGuard::Function(FunctionGuard::Domain(
            Predicate::True.minus(&keys_predicate(0, 1)),
        )),
        index: 1,
    };
    hand_over(&dispatcher, &breakers, later);
}

/// An ordered pipeline has one morsel in flight at a time: a claim skips it while one is, and
/// takes the next once the first is acknowledged.
#[test]
fn a_claim_skips_an_ordered_pipeline_with_a_morsel_in_flight() {
    let (dispatcher, breakers) = ordered_reader();
    let first = dispatcher.pop().expect("the lower morsel");
    assert_eq!(dispatcher.pop(), None, "the later morsel waits");
    hand_over(&dispatcher, &breakers, first);
    assert!(dispatcher.pop().is_some(), "the later morsel");
}

/// An ordered pipeline consumes its morsels in the order they were queued, each claimed and
/// consumed before the next is claimed.
#[test]
fn an_ordered_pipeline_consumes_its_morsels_in_queue_order() {
    let (dispatcher, breakers) = ordered_reader();
    while let Some(package) = dispatcher.pop() {
        hand_over(&dispatcher, &breakers, package);
    }
    let high = TileGuard::Function(FunctionGuard::Domain(
        Predicate::True.minus(&keys_predicate(0, 1)),
    ));
    assert_eq!(
        dispatcher.into_events(),
        vec![
            finished(0),
            consume(1, keys_between(0, 1)),
            consume(1, high)
        ]
    );
}

/// A package handed over without being claimed is refused, ordered pipeline or not.
#[test]
#[should_panic(expected = "pipeline 1 consumes a package claimed for it")]
fn a_package_not_claimed_is_refused() {
    let breakers: Vec<BreakerHandle> = vec![
        Scripted::holding(ints().universal_guard()),
        Scripted::holding(ints().universal_guard()),
    ];
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    let package = WorkPackage {
        pipeline: PipelineId(1),
        epoch: 0,
        guard: ints().universal_guard(),
        index: 0,
    };
    hand_over(&dispatcher, &breakers, package);
}

/// A package acknowledged twice is refused: its flag in the queue is set at the first.
#[test]
#[should_panic(expected = "pipeline 0 consumes a package claimed for it")]
fn a_package_acknowledged_twice_is_refused() {
    let dispatcher = Dispatcher::new(vec![vec![]], UNBOUNDED);
    dispatcher.start_source(PipelineId(0), &ints(), &ints().empty_guard());
    let package = dispatcher.pop().expect("the source's one package");
    dispatcher.acknowledge(package.clone());
    dispatcher.acknowledge(package);
}

/// A start closes a source, which takes nothing more: a second start is refused.
#[test]
#[should_panic(expected = "pipeline 0 is queued nothing once it is closed")]
fn a_second_start_of_a_source_is_refused() {
    let dispatcher = Dispatcher::new(vec![vec![]], UNBOUNDED);
    dispatcher.start_source(PipelineId(0), &ints(), &ints().empty_guard());
    dispatcher.start_source(PipelineId(0), &ints(), &ints().empty_guard());
}

/// Every refusal fails the run before it panics, so a later claim answers `Failed` though no
/// worker handle was dropped.
#[test]
fn a_refusal_fails_the_run_before_it_panics() {
    type Misuse = fn(&Dispatcher);
    let misuses: [(&str, Misuse); 5] = [
        ("a second start", |dispatcher| {
            dispatcher.start_source(PipelineId(0), &ints(), &ints().empty_guard())
        }),
        (
            "a source start of a pipeline that reads one",
            |dispatcher| dispatcher.start_source(PipelineId(1), &ints(), &ints().empty_guard()),
        ),
        ("an acknowledgement for no pipeline", |dispatcher| {
            dispatcher.acknowledge(WorkPackage {
                pipeline: PipelineId(9),
                epoch: 0,
                guard: ints().universal_guard(),
                index: 0,
            })
        }),
        (
            "a finish before the package is acknowledged",
            |dispatcher| {
                dispatcher.begin_finish(PipelineId(0));
            },
        ),
        ("a finish of an epoch not begun", |dispatcher| {
            dispatcher.finish(dispatcher.pushes(PipelineId(0)))
        }),
    ];
    for (what, misuse) in misuses {
        let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
        dispatcher.start_source(PipelineId(0), &ints(), &ints().empty_guard());
        let refused =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| misuse(&dispatcher)));
        assert!(refused.is_err(), "{what} is refused");
        assert!(
            matches!(dispatcher.try_claim(None), Next::Failed),
            "{what} fails the run"
        );
    }
}

/// Claim and acknowledge every package `dispatcher` hands out for `pipeline` now: each one's
/// epoch and guard, in claim order.
fn drain(dispatcher: &Dispatcher, pipeline: usize) -> Vec<(u64, TileGuard)> {
    let mut consumed = Vec::new();
    while let Some(package) = dispatcher.claim_of(PipelineId(pipeline)) {
        consumed.push((package.epoch, package.guard.clone()));
        dispatcher.acknowledge(package);
    }
    consumed
}

/// The finish a claim hands out next, pushed `pushed` and finished: its pipeline, epoch, and
/// whether the epoch is the last.
fn finish_next(dispatcher: &Dispatcher, pushed: Option<TileGuard>) -> (usize, u64, bool) {
    let Next::Finish {
        pipeline,
        epoch,
        last,
        ..
    } = dispatcher.try_claim(None)
    else {
        panic!("a pipeline may finish an epoch")
    };
    let mut pushes = dispatcher.pushes_in(pipeline, epoch);
    if let Some(pushed) = &pushed {
        pushes.push(pushed, |guard, _| vec![guard.clone()]);
    }
    dispatcher.finish(pushes);
    (pipeline.0, epoch, last)
}

/// A source is queued each region it is notified of in the current epoch, cut every
/// `morsel_rows` positions, while the epoch runs; it finishes the epoch only once closed.
#[test]
fn a_notified_source_consumes_each_region_and_finishes_once_closed() {
    let dispatcher = Dispatcher::new(vec![vec![]], 2);
    dispatcher.notify(PipelineId(0), &keys_between(0, 4));
    assert_eq!(
        drain(&dispatcher, 0),
        vec![
            (0, keys_between(0, 1)),
            (0, keys_between(2, 3)),
            (0, keys_between(4, 4))
        ]
    );
    assert!(
        matches!(dispatcher.try_claim(None), Next::Wait(_)),
        "an open source waits for more of its input"
    );
    dispatcher.notify(PipelineId(0), &keys_between(5, 6));
    assert_eq!(drain(&dispatcher, 0), vec![(0, keys_between(5, 6))]);
    dispatcher.close(PipelineId(0));
    let Next::Finish { consumed, last, .. } = dispatcher.try_claim(None) else {
        panic!("a closed source whose packages are all acknowledged finishes")
    };
    assert_eq!((consumed, last), (Some(keys_between(0, 6)), true));
}

/// A notified region is cut every `morsel_rows` positions counted across its runs.
#[test]
fn a_notified_region_is_cut_every_rows_positions_across_its_runs() {
    let dispatcher = Dispatcher::new(vec![vec![]], 2);
    dispatcher.notify(
        PipelineId(0),
        &keys_between(0, 2).union(&keys_between(10, 12)),
    );
    let guards: Vec<_> = drain(&dispatcher, 0).into_iter().map(|(_, g)| g).collect();
    assert_eq!(
        guards,
        vec![
            keys_between(0, 1),
            keys_between(2, 2).union(&keys_between(10, 10)),
            keys_between(11, 12),
        ]
    );
}

/// A notified guard that names no finite run of positions is one package.
#[test]
fn a_notified_guard_of_no_positions_is_one_package() {
    let dispatcher = Dispatcher::new(vec![vec![]], 2);
    dispatcher.notify(PipelineId(0), &ints().universal_guard());
    assert_eq!(drain(&dispatcher, 0), vec![(0, ints().universal_guard())]);
}

/// A closed source takes no more of its input.
#[test]
#[should_panic(expected = "pipeline 0 is queued nothing once it is closed")]
fn a_source_notified_after_its_close_is_refused() {
    let dispatcher = Dispatcher::new(vec![vec![]], 2);
    dispatcher.close(PipelineId(0));
    dispatcher.notify(PipelineId(0), &keys_between(0, 1));
}

/// A pipeline that reads another is queued what that one pushes, not notified.
#[test]
#[should_panic(expected = "pipeline 1 is queued arrivals only as a source")]
fn a_reader_notified_is_refused() {
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], 2);
    dispatcher.notify(PipelineId(1), &keys_between(0, 1));
}

/// A source closes once.
#[test]
#[should_panic(expected = "pipeline 0 closes its queue once")]
fn a_second_close_is_refused() {
    let dispatcher = Dispatcher::new(vec![vec![]], 2);
    dispatcher.close(PipelineId(0));
    dispatcher.close(PipelineId(0));
}

/// A region notified twice in an epoch would be consumed twice, which a debug build refuses.
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "pipeline 0 consumes each region once")]
fn a_region_notified_twice_is_refused() {
    let dispatcher = Dispatcher::new(vec![vec![]], 2);
    dispatcher.notify(PipelineId(0), &keys_between(0, 3));
    dispatcher.notify(PipelineId(0), &keys_between(3, 4));
}

/// A sealed epoch finishes while the next runs: the source finishes epoch 0 and its reader
/// consumes what it pushed there and finishes epoch 0 too, while epoch 1's package is in flight.
#[test]
fn a_sealed_epoch_finishes_while_the_next_runs() {
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.notify(PipelineId(0), &keys_between(0, 1));
    dispatcher.seal();
    dispatcher.notify(PipelineId(0), &keys_between(2, 3));
    let first = dispatcher
        .claim_of(PipelineId(0))
        .expect("epoch 0's package");
    let second = dispatcher
        .claim_of(PipelineId(0))
        .expect("epoch 1's package");
    assert_eq!((first.epoch, second.epoch), (0, 1));
    dispatcher.acknowledge(first);
    assert_eq!(
        finish_next(&dispatcher, Some(keys_between(0, 1))),
        (0, 0, false)
    );
    assert_eq!(drain(&dispatcher, 1), vec![(0, keys_between(0, 1))]);
    assert_eq!(finish_next(&dispatcher, None), (1, 0, false));
    dispatcher.acknowledge(second);
}

/// A pipeline's epochs run in parallel and finish in any order: epoch 1 finishes first while
/// epoch 0's package is in flight, and epoch 0 after.
#[test]
fn a_pipelines_epochs_finish_in_any_order() {
    let dispatcher = Dispatcher::new(vec![vec![]], UNBOUNDED);
    dispatcher.notify(PipelineId(0), &keys_between(0, 1));
    dispatcher.seal();
    dispatcher.notify(PipelineId(0), &keys_between(2, 3));
    dispatcher.seal();
    let early = dispatcher
        .claim_of(PipelineId(0))
        .expect("epoch 0's package");
    let late = dispatcher
        .claim_of(PipelineId(0))
        .expect("epoch 1's package");
    assert_eq!((early.epoch, late.epoch), (0, 1));
    dispatcher.acknowledge(late);
    assert_eq!(finish_next(&dispatcher, None), (0, 1, false));
    dispatcher.acknowledge(early);
    assert_eq!(finish_next(&dispatcher, None), (0, 0, false));
}

/// A seal waits while the window's slot for the next epoch holds an epoch in flight, and opens
/// it once that epoch has retired.
#[test]
fn a_seal_waits_while_the_window_is_full() {
    let mut dispatcher = Dispatcher::new(vec![vec![]], UNBOUNDED);
    dispatcher.window(2);
    assert!(dispatcher.try_seal(), "epoch 1 has a slot of its own");
    assert!(
        !dispatcher.try_seal(),
        "epoch 2 takes epoch 0's slot, which is in flight"
    );
    assert_eq!(finish_next(&dispatcher, None), (0, 0, false));
    assert!(dispatcher.try_seal(), "epoch 0 has retired");
}

/// The run ends with its last epoch, once every source is closed: a source closed while another
/// is open finishes its epochs as they are sealed, and the epoch of the last close is the last.
#[test]
fn the_last_epoch_is_the_one_every_source_has_closed_in() {
    let dispatcher = Dispatcher::new(vec![vec![], vec![]], UNBOUNDED);
    dispatcher.close(PipelineId(0));
    assert!(
        matches!(dispatcher.try_claim(None), Next::Wait(_)),
        "epoch 0 is neither sealed nor known to be the last"
    );
    dispatcher.seal();
    assert_eq!(finish_next(&dispatcher, None), (0, 0, false));
    assert_eq!(finish_next(&dispatcher, None), (1, 0, false));
    dispatcher.close(PipelineId(1));
    assert_eq!(finish_next(&dispatcher, None), (0, 1, true));
    assert_eq!(finish_next(&dispatcher, None), (1, 1, true));
    assert!(matches!(dispatcher.try_claim(None), Next::Done));
}

/// An epoch a source is sealed in after every source closed has no epoch after it.
#[test]
#[should_panic(expected = "a seal opens an epoch while a source is open")]
fn a_seal_after_the_last_close_is_refused() {
    let dispatcher = Dispatcher::new(vec![vec![]], UNBOUNDED);
    dispatcher.close(PipelineId(0));
    dispatcher.seal();
}

/// A memo over a source notified in two epochs pushes in each epoch, as it consumes, only what
/// that epoch decided, and the reader consumes every key once.
#[test]
fn a_memo_pushes_in_each_epoch_what_it_decided_since_the_last() {
    let memo = MemoProducer::over(Box::new(Input::over(&source(0..6))), &ints());
    let memo = Rc::new(RefCell::new(memo));
    let reader = Scripted::holding(ints().empty_guard());
    let breakers: Vec<BreakerHandle> = vec![memo, reader];
    wire(&[vec![], vec![0]], &breakers);
    for breaker in &breakers {
        breaker.borrow_mut().enter_consuming_mode();
    }
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.notify(PipelineId(0), &keys_between(0, 2));
    dispatcher.seal();
    let package = dispatcher
        .claim_of(PipelineId(0))
        .expect("epoch 0's package");
    hand_over(&dispatcher, &breakers, package);
    let pushed = dispatcher
        .claim_of(PipelineId(1))
        .expect("the memo's push lands while epoch 0 runs");
    assert_eq!(pushed.epoch, 0);
    hand_over(&dispatcher, &breakers, pushed);
    let Next::Finish {
        pipeline, epoch, ..
    } = dispatcher.try_claim(None)
    else {
        panic!("the memo finishes epoch 0")
    };
    let mut pushes = dispatcher.pushes_in(pipeline, epoch);
    breakers[0].borrow_mut().finish(&mut pushes, false);
    dispatcher.finish(pushes);
    dispatcher.notify(PipelineId(0), &keys_between(3, 5));
    dispatcher.close(PipelineId(0));
    run_epochs(&dispatcher, &breakers);
    let events = dispatcher.into_events();
    let read: Vec<_> = events
        .iter()
        .filter_map(|event| match event {
            Event::Consume { pipeline, guard } if *pipeline == PipelineId(1) => Some(guard),
            _ => None,
        })
        .collect();
    assert_eq!(read.len(), 2, "one push per epoch: {read:?}");
    assert!(guard_minus(read[0], &keys_between(0, 2)).is_empty());
    assert!(guard_minus(read[1], &keys_between(3, 5)).is_empty());
}

/// Drive `breakers` through every epoch queued, as [`run`] drives one, without starting the
/// sources.
fn run_epochs(dispatcher: &Dispatcher, breakers: &[BreakerHandle]) {
    loop {
        match dispatcher.try_claim(None) {
            Next::Package(package) => hand_over(dispatcher, breakers, package),
            Next::Finish {
                pipeline,
                epoch,
                last,
                ..
            } => {
                let mut breaker = breakers[pipeline.0].borrow_mut();
                let mut pushes = dispatcher.pushes_in(pipeline, epoch);
                match last {
                    true => breaker.finish(&mut pushes, true),
                    false => pushes.push_final(&*breaker),
                }
                dispatcher.finish(pushes);
            }
            Next::Done => return,
            other => panic!("a run of queued epochs on one thread: {other:?}"),
        }
    }
}

/// An ordered pipeline runs its epochs one after another: an epoch's package waits while a
/// package of the epoch before is in flight, and until that epoch has finished.
#[test]
fn an_ordered_pipeline_runs_its_epochs_one_after_another() {
    let mut dispatcher = Dispatcher::new(vec![vec![]], UNBOUNDED);
    dispatcher.order(PipelineId(0));
    dispatcher.notify(PipelineId(0), &keys_between(0, 1));
    dispatcher.seal();
    dispatcher.notify(PipelineId(0), &keys_between(2, 3));
    let first = dispatcher
        .claim_of(PipelineId(0))
        .expect("epoch 0's package");
    assert!(
        dispatcher.claim_of(PipelineId(0)).is_none(),
        "epoch 1's package waits while epoch 0's is in flight"
    );
    dispatcher.acknowledge(first);
    assert!(
        dispatcher.claim_of(PipelineId(0)).is_none(),
        "epoch 1's package waits until epoch 0 has finished"
    );
    assert_eq!(finish_next(&dispatcher, None), (0, 0, false));
    let second = dispatcher
        .claim_of(PipelineId(0))
        .expect("epoch 1's package");
    assert_eq!(second.epoch, 1);
}

/// An ordered reader consumes its epochs in order, though the pipeline it reads finishes the
/// later epoch first.
#[test]
fn an_ordered_reader_consumes_its_epochs_in_order() {
    let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.order(PipelineId(1));
    dispatcher.notify(PipelineId(0), &keys_between(0, 1));
    dispatcher.seal();
    dispatcher.notify(PipelineId(0), &keys_between(2, 3));
    dispatcher.seal();
    let held = dispatcher
        .claim_of(PipelineId(0))
        .expect("epoch 0's package");
    assert_eq!(drain(&dispatcher, 0), vec![(1, keys_between(2, 3))]);
    assert_eq!(
        finish_next(&dispatcher, Some(keys_between(2, 3))),
        (0, 1, false)
    );
    assert!(
        dispatcher.claim_of(PipelineId(1)).is_none(),
        "epoch 1's push waits until the reader has finished epoch 0"
    );
    dispatcher.acknowledge(held);
    assert_eq!(
        finish_next(&dispatcher, Some(keys_between(0, 1))),
        (0, 0, false)
    );
    assert_eq!(drain(&dispatcher, 1), vec![(0, keys_between(0, 1))]);
    assert_eq!(finish_next(&dispatcher, None), (1, 0, false));
    assert_eq!(drain(&dispatcher, 1), vec![(1, keys_between(2, 3))]);
    assert_eq!(finish_next(&dispatcher, None), (1, 1, false));
}

/// The last epoch finishes only after every earlier epoch of the pipeline: a package of the
/// epoch before in flight holds the last epoch's finish back, though its own packages are
/// acknowledged.
#[test]
fn the_last_epoch_finishes_after_the_earlier_ones() {
    let dispatcher = Dispatcher::new(vec![vec![]], UNBOUNDED);
    dispatcher.notify(PipelineId(0), &keys_between(0, 1));
    dispatcher.seal();
    dispatcher.notify(PipelineId(0), &keys_between(2, 3));
    let held = dispatcher
        .claim_of(PipelineId(0))
        .expect("epoch 0's package");
    dispatcher.close(PipelineId(0));
    assert_eq!(drain(&dispatcher, 0), vec![(1, keys_between(2, 3))]);
    assert!(
        matches!(dispatcher.try_claim(None), Next::Wait(_)),
        "the last epoch waits for epoch 0's package"
    );
    dispatcher.acknowledge(held);
    assert_eq!(finish_next(&dispatcher, None), (0, 0, false));
    assert_eq!(finish_next(&dispatcher, None), (0, 1, true));
}

/// A package of an epoch that has retired is refused.
#[test]
#[should_panic(expected = "pipeline 0 consumes a package claimed for it")]
fn a_package_of_a_retired_epoch_is_refused() {
    let mut dispatcher = Dispatcher::new(vec![vec![]], UNBOUNDED);
    dispatcher.window(2);
    dispatcher.notify(PipelineId(0), &keys_between(0, 1));
    let package = dispatcher
        .claim_of(PipelineId(0))
        .expect("epoch 0's package");
    dispatcher.acknowledge(package.clone());
    dispatcher.seal();
    assert_eq!(finish_next(&dispatcher, None), (0, 0, false));
    assert!(
        dispatcher.try_seal(),
        "epoch 0 has retired, so its slot opens epoch 2"
    );
    dispatcher.acknowledge(package);
}

/// A window of one epoch would hold the epoch a seal opens in the slot of the one it seals.
#[test]
#[should_panic(expected = "a window holds the epoch a seal opens beside the one it seals")]
fn a_window_of_one_epoch_is_refused() {
    Dispatcher::new(vec![vec![]], UNBOUNDED).window(1);
}

/// A window replaces every epoch, so it is set before anything is queued.
#[test]
#[should_panic(expected = "a window is set before any notify, seal or close")]
fn a_window_set_after_a_notify_is_refused() {
    let mut dispatcher = Dispatcher::new(vec![vec![]], UNBOUNDED);
    dispatcher.notify(PipelineId(0), &keys_between(0, 1));
    dispatcher.window(2);
}

/// A window set after a seal would replace the epoch the seal opened.
#[test]
#[should_panic(expected = "a window is set before any notify, seal or close")]
fn a_window_set_after_a_seal_is_refused() {
    let mut dispatcher = Dispatcher::new(vec![vec![]], UNBOUNDED);
    dispatcher.seal();
    dispatcher.window(2);
}

/// A limited source takes a notify only while fewer packages than its limit are outstanding,
/// in every epoch, and takes more once one is acknowledged.
#[test]
fn a_limited_source_takes_a_notify_below_its_limit() {
    let mut dispatcher = Dispatcher::new(vec![vec![]], 1);
    dispatcher.limit(PipelineId(0), 2);
    assert!(dispatcher.try_notify(PipelineId(0), &keys_between(0, 0)));
    dispatcher.seal();
    assert!(dispatcher.try_notify(PipelineId(0), &keys_between(1, 1)));
    assert!(
        !dispatcher.try_notify(PipelineId(0), &keys_between(2, 2)),
        "two packages are outstanding, one in each epoch"
    );
    let package = dispatcher.claim_of(PipelineId(0)).expect("a package");
    assert!(
        !dispatcher.try_notify(PipelineId(0), &keys_between(2, 2)),
        "a claimed package is outstanding until it is acknowledged"
    );
    dispatcher.acknowledge(package);
    assert!(dispatcher.try_notify(PipelineId(0), &keys_between(2, 2)));
    assert_eq!(dispatcher.outstanding(PipelineId(0)), 2);
}

/// A notify admitted below the limit queues every morsel it cuts, and a notify of nothing
/// returns at once.
#[test]
fn a_notify_below_the_limit_queues_all_its_morsels() {
    let mut dispatcher = Dispatcher::new(vec![vec![]], 1);
    dispatcher.limit(PipelineId(0), 1);
    assert!(dispatcher.try_notify(PipelineId(0), &keys_between(0, 3)));
    dispatcher.notify(PipelineId(0), &ints().empty_guard());
    assert_eq!(dispatcher.outstanding(PipelineId(0)), 4);
}

/// A reader is queued what is pushed to it, which no limit holds back.
#[test]
#[should_panic(expected = "pipeline 1 is limited only as a source")]
fn a_limited_reader_is_refused() {
    Dispatcher::new(vec![vec![], vec![0]], 1).limit(PipelineId(1), 2);
}

/// A push lands only while its pipeline has not finished the epoch.
#[test]
#[should_panic(expected = "pipeline 0 lands its pushes in an epoch before it finishes there")]
fn a_push_landed_after_the_finish_is_refused() {
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.finish_by_hand(PipelineId(0), |_| {});
    let mut pushes = dispatcher.pushes_in(PipelineId(0), 0);
    pushes.push(&keys_between(0, 1), |guard, _| vec![guard.clone()]);
    dispatcher.land(pushes);
}

/// An aggregate read by an extraction pushes its value once, at the consume that makes it final
/// and before its finish: its accumulator is partial while the memo's morsels arrive one at a
/// time, and holds nothing until then.
#[test]
fn an_aggregate_pushes_its_value_once_it_is_final() {
    let memo: BreakerHandle = memo_over_rows(0..6);
    let sum = aggregate_over(Box::new(ReadsBreaker::of(&memo)), &sum_tiling());
    let scalar = Tiling::Scalar(Extent::Base(BaseType::Int));
    let extract = extract_aggregate_over(
        Box::new(ReadsBreaker::of(&sum)),
        &scalar,
        AggregateKind::Sum,
    );
    let breakers = [memo, sum, extract.clone()];
    let events = run_cut(vec![vec![], vec![0], vec![1]], &breakers, 1);
    assert_eq!(consumed_by(&events, 2).len(), 1, "one push: {events:?}");
    assert!(
        !read_after_finish(&events, 1, 2),
        "the extraction consumes before the aggregate finishes: {events:?}"
    );
    let total: i64 = (0..6).map(value).sum();
    assert_eq!(
        extract.borrow_mut().get(scalar.universal_guard()),
        Tile::Scalar(ColumnValue::Ints(vec![total]))
    );
}

/// A consumer that hands everything to the boxed consumer it holds, so a test can share one
/// behind an `Rc` as a breaker's push target.
struct Boxed(Box<dyn Consumer>);

impl Consumer for Boxed {
    fn notify(&mut self, arrived: &Projection) {
        self.0.notify(arrived);
    }

    fn push(
        &mut self,
        region: &Projection,
        landing: &mut crate::interpreter::dispatcher::Landing<'_>,
    ) {
        self.0.push(region, landing);
    }

    fn route(&mut self, routes: &mut crate::interpreter::dispatcher::Routes) {
        self.0.route(routes);
    }
}

/// The entry of pipeline 1 behind a gated consumer, as an operator between two breakers shares
/// one: the gate, which every pull clears and nothing pulls here, and the shared consumer.
fn gated_entry(input: &Tiling) -> (Gate, GatedConsumer) {
    let entry =
        crate::interpreter::dispatcher::Entry::new(PipelineId(1), input.clone(), Box::new(|| {}));
    let (shared, gate) = shared_consumer(Box::new(entry));
    (gate, shared)
}

/// The tiling of a collection keyed by a tagged union of `UInt` keys under tags `0` and `1`.
fn keyed_by_two_tags() -> Tiling {
    use crate::ccl::{FieldKey, TagMap};
    let uint = || Extent::Base(BaseType::UInt);
    Tiling::data_function(
        Extent::Union(TagMap::from_arms(vec![
            (FieldKey::Index(0), uint()),
            (FieldKey::Index(1), uint()),
        ])),
        Tiling::Scalar(Extent::Base(BaseType::Int)),
    )
}

/// The guard of `keys_by_tag`, each set of keys under its tag of [`keyed_by_two_tags`].
fn under_tags(keys_by_tag: Vec<(usize, Predicate)>) -> TileGuard {
    use crate::ccl::{FieldKey, TagMap};
    let arms = keys_by_tag
        .into_iter()
        .map(|(tag, keys)| (FieldKey::Index(tag), keys))
        .collect();
    TileGuard::Function(FunctionGuard::Domain(Predicate::tagged(
        TagMap::from_arms(arms),
        false,
    )))
}

/// A push climbs the reader's chain as each operator restates it: through the arm of a tagged
/// union it lands under the arm's tag, as a guard of the reader's input. Each morsel is a package:
/// a push passes the union's gate, which nothing pulls between the morsels.
#[test]
fn a_push_lands_restated_by_the_chain_and_past_the_gate() {
    use crate::ccl::FieldKey;
    let (low, high) = (
        keys_predicate(0, 1),
        Predicate::True.minus(&keys_predicate(0, 1)),
    );
    let domain = |keys: Predicate| TileGuard::Function(FunctionGuard::Domain(keys));
    let scripted = Scripted::cutting(
        ints().universal_guard(),
        vec![domain(low.clone()), domain(high.clone())],
    );
    let input = keyed_by_two_tags();
    let (_gate, shared) = gated_entry(&input);
    let arm = forwarding_consumer_tagging(&shared, &WakeupQueue::default(), FieldKey::Index(1));
    scripted
        .borrow_mut()
        .base_mut()
        .pushing_to(Rc::new(RefCell::new(Boxed(arm))));
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        scripted.borrow_mut().finish(pushes, true)
    });
    let queued: Vec<TileGuard> = std::iter::from_fn(|| dispatcher.pop())
        .map(|package| package.guard)
        .collect();
    assert_eq!(
        queued,
        vec![under_tags(vec![(1, low)]), under_tags(vec![(1, high)])]
    );
    assert!(
        queued.iter().all(|guard| guard.check_from(&input)),
        "each package is a guard of the reader's input: {queued:?}"
    );
}

/// A push whose region names every tag of the reader's input whole lands as the universal guard,
/// as a pull of every arm is answered.
#[test]
fn a_push_naming_every_tag_whole_lands_universal() {
    let input = keyed_by_two_tags();
    let every_tag = under_tags(vec![(0, Predicate::True), (1, Predicate::True)]);
    assert!(!every_tag.is_universal(), "{every_tag:?}");
    let scripted = Scripted::holding(every_tag);
    let (_gate, shared) = gated_entry(&input);
    let path = forwarding_consumer_keeping_keys(&shared, &WakeupQueue::default());
    scripted
        .borrow_mut()
        .base_mut()
        .pushing_to(Rc::new(RefCell::new(Boxed(path))));
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        scripted.borrow_mut().finish(pushes, true)
    });
    let queued: Vec<TileGuard> = std::iter::from_fn(|| dispatcher.pop())
        .map(|package| package.guard)
        .collect();
    assert_eq!(queued, vec![input.universal_guard()]);
}

/// A push that reaches one reader along two paths, as a filter reads one memo for its values and
/// its predicate, is queued once: what is queued for the reader in the epoch already is taken out.
#[test]
fn a_push_reaching_a_reader_twice_is_queued_once() {
    let scripted = Scripted::holding(ints().universal_guard());
    let (_gate, shared) = gated_entry(&ints());
    let wakeups = WakeupQueue::default();
    let paths = vec![
        forwarding_consumer_keeping_keys(&shared, &wakeups),
        forwarding_consumer_keeping_keys(&shared, &wakeups),
    ];
    scripted
        .borrow_mut()
        .base_mut()
        .pushing_to(Rc::new(RefCell::new(Paths(paths))));
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        scripted.borrow_mut().finish(pushes, true)
    });
    assert_eq!(
        dispatcher.pop().map(|package| package.guard),
        Some(ints().universal_guard())
    );
    assert_eq!(dispatcher.pop(), None, "one package for two paths");
}

/// A consumer with several paths to one reader: a push takes each.
struct Paths(Vec<Box<dyn Consumer>>);

impl Consumer for Paths {
    fn notify(&mut self, _arrived: &Projection) {}

    fn push(
        &mut self,
        region: &Projection,
        landing: &mut crate::interpreter::dispatcher::Landing<'_>,
    ) {
        for path in &mut self.0 {
            path.push(region, landing);
        }
    }

    fn route(&mut self, routes: &mut crate::interpreter::dispatcher::Routes) {
        for path in &mut self.0 {
            path.route(routes);
        }
    }
}

/// A route declares, per path, whether the consumers on it keep the pushing pipeline's keys: a
/// path through a widening consumer reaches the entry widened, and one through a consumer that
/// keeps keys reaches it with them kept. Nothing is pushed.
#[test]
fn a_route_declares_whether_each_path_keeps_its_keys() {
    let (_gate, shared) = gated_entry(&ints());
    let wakeups = WakeupQueue::default();
    let mut paths = Paths(vec![
        forwarding_consumer(&shared, &wakeups),
        forwarding_consumer_keeping_keys(&shared, &wakeups),
    ]);
    let mut routes = crate::interpreter::dispatcher::Routes::new();
    paths.route(&mut routes);
    let reached: Vec<_> = routes
        .reached()
        .into_iter()
        .map(|route| (route.pipeline, route.keeps_keys))
        .collect();
    assert_eq!(reached, [(PipelineId(1), false), (PipelineId(1), true)]);
}

/// A route declares, per path, whether its decided region names only part of what a row depends
/// on: a widening path's does, and so does a lookup operand's, which names rows by the key they
/// read whatever their input holds. A path that keeps its keys does not, and neither does an
/// outermost `Uncurry`'s, which widens a change but restates a decided region exactly.
#[test]
fn a_route_declares_whether_each_path_decides_part_of_a_row() {
    let (_gate, shared) = gated_entry(&ints());
    let wakeups = WakeupQueue::default();
    let mut paths = Paths(vec![
        forwarding_consumer(&shared, &wakeups),
        forwarding_consumer_keeping_keys(&shared, &wakeups),
        crate::interpreter::scheduler::widening_restating_decided(
            |region| region.clone(),
            forwarding_consumer_keeping_keys(&shared, &wakeups),
        ),
        crate::interpreter::scheduler::restating_lookup(
            Box::new(|region| region.clone()),
            forwarding_consumer_keeping_keys(&shared, &wakeups),
        ),
    ]);
    let mut routes = crate::interpreter::dispatcher::Routes::new();
    paths.route(&mut routes);
    let parts: Vec<_> = routes
        .reached()
        .into_iter()
        .map(|route| route.decides_part)
        .collect();
    assert_eq!(parts, [true, false, false, true]);
}

/// A read that reaches its reader along a path that drops a decided region and one that keeps it
/// decides the reader's input only once it is whole: a row reached along both depends on rows the
/// region does not name. Its decided push of some keys records nothing, where the same push of a
/// read with no such mark records those keys.
#[cfg(debug_assertions)]
#[test]
fn a_read_decided_only_whole_records_no_part() {
    use crate::interpreter::dispatcher::Decided;
    let recorded = |whole_only: bool| {
        let scripted = Scripted::holding(keys_between(0, 1));
        let (_gate, shared) = gated_entry(&ints());
        let wakeups = WakeupQueue::default();
        let paths = vec![
            forwarding_consumer(&shared, &wakeups),
            forwarding_consumer_keeping_keys(&shared, &wakeups),
        ];
        scripted
            .borrow_mut()
            .base_mut()
            .pushing_to(Rc::new(RefCell::new(Paths(paths))));
        let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
        dispatcher.park(PipelineId(1));
        if whole_only {
            dispatcher.decides_whole_only(PipelineId(1), PipelineId(0));
        }
        dispatcher.finish_by_hand(PipelineId(0), |pushes| {
            scripted.borrow_mut().finish(pushes, false)
        });
        dispatcher.decided_of(PipelineId(1), PipelineId(0))
    };
    assert!(matches!(recorded(true), Decided::Nothing));
    assert!(matches!(recorded(false), Decided::Region(_)));
}

/// A read decided only whole still records its whole push: once the pipeline it reads has decided
/// everything, each path's region is decided, whatever it was restated to on the way.
#[cfg(debug_assertions)]
#[test]
fn a_read_decided_only_whole_records_its_whole_push() {
    use crate::interpreter::dispatcher::Decided;
    let scripted = Scripted::holding(ints().universal_guard());
    let (_gate, shared) = gated_entry(&ints());
    let wakeups = WakeupQueue::default();
    let paths = vec![
        forwarding_consumer(&shared, &wakeups),
        forwarding_consumer_keeping_keys(&shared, &wakeups),
    ];
    scripted
        .borrow_mut()
        .base_mut()
        .pushing_to(Rc::new(RefCell::new(Paths(paths))));
    let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.park(PipelineId(1));
    dispatcher.decides_whole_only(PipelineId(1), PipelineId(0));
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        scripted.borrow_mut().finish(pushes, true)
    });
    assert!(matches!(
        dispatcher.decided_of(PipelineId(1), PipelineId(0)),
        Decided::Whole
    ));
}

/// A push widened to `Everything` on its way fails the run, since the reader could not tell which
/// of its keys it names: a reader reached that way reads the pushing pipeline once it finished.
#[test]
#[should_panic(
    expected = "a push of pipeline 0 is widened to `Everything` on its way to pipeline 1"
)]
fn a_push_widened_on_its_way_fails_the_run() {
    let scripted = Scripted::cutting(keys_between(0, 1), vec![keys_between(0, 1)]);
    let (_gate, shared) = gated_entry(&ints());
    let widening = forwarding_consumer(&shared, &WakeupQueue::default());
    scripted
        .borrow_mut()
        .base_mut()
        .pushing_to(Rc::new(RefCell::new(Boxed(widening))));
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        scripted.borrow_mut().finish(pushes, true)
    });
}

/// A push whose chain leads back into a consumer it is passing through fails the run: only a
/// store closes a cycle, and no pipeline runs a store.
#[test]
#[should_panic(expected = "a push of pipeline 0 re-enters a consumer it is passing through")]
fn a_push_that_re_enters_its_chain_fails_the_run() {
    /// A consumer whose push climbs `back`, a forwarder into the consumer this one sits behind.
    struct Cycle(test_helpers::InputConsumer);
    impl Consumer for Cycle {
        fn notify(&mut self, _arrived: &Projection) {}

        fn push(
            &mut self,
            region: &Projection,
            landing: &mut crate::interpreter::dispatcher::Landing<'_>,
        ) {
            if let Some(back) = self.0.borrow_mut().as_mut() {
                back.push(region, landing);
            }
        }
    }
    let back = Rc::new(RefCell::new(None));
    let (shared, _gate) = shared_consumer(Box::new(Cycle(back.clone())));
    *back.borrow_mut() = Some(forwarding_consumer_keeping_keys(
        &shared,
        &WakeupQueue::default(),
    ));
    let scripted = Scripted::cutting(keys_between(0, 1), vec![keys_between(0, 1)]);
    let path = forwarding_consumer_keeping_keys(&shared, &WakeupQueue::default());
    scripted
        .borrow_mut()
        .base_mut()
        .pushing_to(Rc::new(RefCell::new(Boxed(path))));
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        scripted.borrow_mut().finish(pushes, true)
    });
}

/// A push reaches every live slot of a fan-out, past the fan-out's own gate, so each pipeline
/// that reads a slot is queued every morsel.
#[test]
fn a_push_reaches_every_slot_of_a_fan_out() {
    use super::test_helpers::NotifyingOp;
    let (low, high) = (
        keys_between(0, 1),
        TileGuard::Function(FunctionGuard::Domain(
            Predicate::True.minus(&keys_predicate(0, 1)),
        )),
    );
    let scripted = Scripted::cutting(ints().universal_guard(), vec![low.clone(), high.clone()]);
    let (feed, input) = NotifyingOp::new(ints().empty_tile(), ints());
    let fan = FanOut::new(Box::new(feed));
    let mut cx = SubscribeContext::new();
    let _slots: Vec<_> = (1..=2)
        .map(|reader| {
            let entry = crate::interpreter::dispatcher::Entry::new(
                PipelineId(reader),
                ints(),
                Box::new(|| {}),
            );
            let mut slot = fan.slot();
            let guard = slot.tiling().universal_guard();
            slot.subscribe(guard, Box::new(entry), &mut cx)
        })
        .collect();
    scripted
        .borrow_mut()
        .base_mut()
        .pushing_to(Rc::new(RefCell::new(Through(input))));
    let dispatcher = Dispatcher::new(vec![vec![], vec![0], vec![0]], UNBOUNDED);
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        scripted.borrow_mut().finish(pushes, true)
    });
    let mut queued: Vec<(usize, TileGuard)> = std::iter::from_fn(|| dispatcher.pop())
        .map(|package| (package.pipeline.0, package.guard))
        .collect();
    queued.sort_by_key(|(pipeline, _)| *pipeline);
    assert_eq!(
        queued,
        vec![(1, low.clone()), (1, high.clone()), (2, low), (2, high)]
    );
}

/// The consumer an operator a test built hands its input: a push goes on to it.
struct Through(test_helpers::InputConsumer);

impl Consumer for Through {
    fn notify(&mut self, _arrived: &Projection) {}

    fn push(
        &mut self,
        region: &Projection,
        landing: &mut crate::interpreter::dispatcher::Landing<'_>,
    ) {
        self.0
            .borrow_mut()
            .as_mut()
            .expect("the operator was subscribed")
            .push(region, landing);
    }

    fn route(&mut self, routes: &mut crate::interpreter::dispatcher::Routes) {
        self.0
            .borrow_mut()
            .as_mut()
            .expect("the operator was subscribed")
            .route(routes);
    }
}

/// A source whose input was released whole, as a scalar a run before a pause or a reload took, is
/// queued no package when a later run starts it, and finishes once claimed.
#[test]
fn a_source_started_over_an_input_released_whole_is_queued_nothing() {
    let scalar = Tiling::Scalar(Extent::Base(BaseType::Int));
    let dispatcher = Dispatcher::new(vec![vec![]], UNBOUNDED);
    dispatcher.start_source(PipelineId(0), &scalar, &scalar.universal_guard());
    assert!(
        matches!(
            dispatcher.try_claim(None),
            Next::Finish { consumed: None, .. }
        ),
        "nothing is queued, so the closed source finishes at once"
    );
}
