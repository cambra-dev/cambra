//! The dispatcher of `crate::interpreter::dispatcher` driving real breakers and scripted ones over
//! scripted inputs.

use std::cell::RefCell;
use std::rc::Rc;

use std::collections::BTreeSet;

use super::aggregate::{aggregate_over, map_aggregate_over};
use super::combinators::converse_of;
use super::extract_final::extract_final_of;
use super::fanout::MemoProducer;
use super::growing::{
    Input, KEYS, NestedInput, ReadsBreaker, Rng, Shared, entries, ints, keys_predicate,
    nested_tiling, predicate, rows_of, same_region, source, source_of, value,
};
use super::test_helpers::keys_between;
use super::*;
use crate::ccl::AggregateKind;
use crate::interpreter::dispatcher::consume as hand_over;
use crate::interpreter::dispatcher::{
    BreakerHandle, Dispatcher, Event, Next, PipelineId, WorkPackage, finalize, run,
};
use crate::interpreter::{BaseType, ColumnValue, Extent};

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

fn finalized(pipeline: usize) -> Event {
    Event::Finalize(PipelineId(pipeline))
}

fn memo_over_rows(rows: std::ops::Range<u64>) -> Held<MemoProducer> {
    Rc::new(RefCell::new(MemoProducer::over(
        Box::new(Input::over(&source(rows))),
        &ints(),
    )))
}

fn memo_reading(child: &BreakerHandle) -> Held<MemoProducer> {
    Rc::new(RefCell::new(MemoProducer::over(
        Box::new(ReadsBreaker::of(child)),
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
    releases: bool,
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
        Rc::new(RefCell::new(Scripted {
            base: ProducerBase::unowned(Self::alloc_id(), &ints()),
            input: Box::new(Input::over(&source(0..4))),
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

impl BreakingProducer for Scripted {
    fn consume_impl(&mut self, guard: TileGuard) {
        self.input.get(guard);
        if self.releases {
            self.input.release(self.input.tiling().universal_guard());
        }
    }

    fn input_tiling(&self) -> Tiling {
        self.input.tiling().clone()
    }

    fn input_released(&self) -> TileGuard {
        self.input.obsolete_guard().clone()
    }

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

/// One pipeline consumes its input whole, then finalizes, and pushes to no one.
#[test]
fn one_pipeline_consumes_everything_then_finalizes() {
    let memo = memo_over_rows(0..6);
    let handle: BreakerHandle = memo.clone();
    let events = run_over(vec![vec![]], &[handle]);
    assert_eq!(
        events,
        vec![consume(0, ints().universal_guard()), finalized(0)]
    );
    assert_eq!(
        entries(&memo.borrow_mut().get(ints().universal_guard())),
        rows_of(0..6)
    );
}

/// A memo read by a memo: the parent consumes exactly the guard the child finalized.
#[test]
fn a_parent_memo_consumes_the_guard_its_child_finalized() {
    let child = memo_over_rows(0..6);
    let child_handle: BreakerHandle = child.clone();
    let parent = memo_reading(&child_handle);
    let events = run_over(vec![vec![], vec![0]], &[child_handle, parent.clone()]);
    // The child held everything and nothing was released when it finalized. The parent has
    // released the child's output since, so the child's final guard is read from the events.
    let pushed = ints().universal_guard();
    assert_eq!(
        events,
        vec![
            consume(0, ints().universal_guard()),
            finalized(0),
            consume(1, pushed),
            finalized(1),
        ]
    );
    assert_eq!(
        entries(&parent.borrow_mut().get(ints().universal_guard())),
        rows_of(0..6)
    );
}

/// A memo read by an aggregate: the aggregate folds what the memo pushed.
#[test]
fn an_aggregate_folds_what_the_memo_below_it_pushed() {
    let child = memo_over_rows(0..6);
    let child_handle: BreakerHandle = child.clone();
    let sum = aggregate_over(Box::new(ReadsBreaker::of(&child_handle)), &sum_tiling());
    let events = run_over(vec![vec![], vec![0]], &[child_handle, sum.clone()]);
    assert_eq!(events[2], consume(1, ints().universal_guard()));
    assert!(
        child.borrow().final_guard().is_empty(),
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
    let child = memo_over_rows(0..6);
    child.borrow_mut().consume_impl(ints().universal_guard());
    child.borrow_mut().release(keys_between(2, 3));
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.finalize_by_hand(PipelineId(0), |pushes| child.borrow_mut().finalize(pushes));
    let package = dispatcher.pop().expect("one package for the parent");
    assert_eq!(package.pipeline, PipelineId(1));
    assert!(same_region(
        &predicate(&package.guard),
        &Predicate::True.minus(&keys_predicate(2, 3))
    ));
    assert_eq!(dispatcher.pop(), None, "one package");
}

/// Two pipelines reading one breaker need a `FanOut`: the release of one would remove rows the
/// other has still to read.
#[test]
#[should_panic(expected = "pipeline 0 is read by pipelines 1 and 2")]
fn a_breaker_read_by_two_pipelines_is_refused() {
    Dispatcher::new(vec![vec![], vec![0], vec![0]], UNBOUNDED);
}

/// A breaker has one input, so a pipeline reads at most one other.
#[test]
#[should_panic(expected = "pipeline 2 reads pipelines [0, 1]; a breaker has one input")]
fn a_pipeline_that_reads_two_pipelines_is_refused() {
    Dispatcher::new(vec![vec![], vec![], vec![0, 1]], UNBOUNDED);
}

/// The driver consumes the lowest pipeline's package first and finalizes only when nothing is
/// queued, which pins the order across two chains: a push to pipeline 2 waits behind the
/// packages queued below it.
#[test]
fn the_lowest_pipelines_package_goes_first_and_finalizing_waits_for_an_empty_queue() {
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
            finalized(0),
            consume(2, left),
            finalized(1),
            finalized(2),
        ]
    );
}

/// An empty final guard pushes nothing, and the pipeline that reads it still finishes.
#[test]
fn an_empty_final_guard_pushes_nothing_and_the_parent_finishes() {
    let breakers: Vec<BreakerHandle> = vec![
        Scripted::holding(ints().empty_guard()),
        Scripted::holding(ints().universal_guard()),
    ];
    let events = run_over(vec![vec![], vec![0]], &breakers);
    assert_eq!(
        events,
        vec![
            consume(0, ints().universal_guard()),
            finalized(0),
            finalized(1)
        ]
    );
}

#[test]
#[should_panic(expected = "pipeline 1 finalizes after its queue is empty")]
fn finalize_with_a_package_queued_panics() {
    let breakers: Vec<BreakerHandle> = vec![
        Scripted::holding(ints().universal_guard()),
        Scripted::holding(ints().universal_guard()),
    ];
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    breakers[0]
        .borrow_mut()
        .consume_impl(ints().universal_guard());
    dispatcher.close(PipelineId(0));
    finalize(&dispatcher, &breakers, PipelineId(0));
    finalize(&dispatcher, &breakers, PipelineId(1));
}

#[test]
#[should_panic(expected = "pipeline 1 finalizes after every pipeline it reads has finished")]
fn finalize_before_an_upstream_pipeline_finished_panics() {
    let breakers: Vec<BreakerHandle> = vec![
        Scripted::holding(ints().universal_guard()),
        Scripted::holding(ints().universal_guard()),
    ];
    finalize(
        &Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED),
        &breakers,
        PipelineId(1),
    );
}

#[test]
#[should_panic(expected = "pipeline 1 finalizes once")]
fn finalize_twice_panics() {
    let breakers: Vec<BreakerHandle> = vec![
        Scripted::holding(ints().universal_guard()),
        Scripted::holding(ints().universal_guard()),
    ];
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    run(&dispatcher, &breakers);
    finalize(&dispatcher, &breakers, PipelineId(1));
}

/// A source finalizes once its input has released every region queued for it: one whose input
/// released less than its queue named would push what rests on rows the input has not stated.
#[test]
#[should_panic(
    expected = "pipeline 0 finalizes after its input has released every guard the pipeline consumed"
)]
fn a_source_pipeline_finalizes_after_its_input_released_what_was_queued() {
    let memo = memo_over_rows(0..6);
    let handle: BreakerHandle = memo.clone();
    let dispatcher = Dispatcher::new(vec![vec![]], UNBOUNDED);
    dispatcher.start_source(PipelineId(0), &ints());
    let Next::Package(package) = dispatcher.try_claim(None) else {
        panic!("a started source hands out its package")
    };
    memo.borrow_mut().consume_impl(keys_between(0, 3));
    dispatcher.acknowledge(package);
    finalize(&dispatcher, &[handle], PipelineId(0));
}

/// A parent whose input has not released a guard the parent consumed does not finalize: what it
/// would push could rest on rows its input has not stated.
#[test]
#[should_panic(
    expected = "pipeline 1 finalizes after its input has released every guard the pipeline consumed"
)]
fn a_parent_finalizes_after_its_input_released_what_it_consumed() {
    let breakers: Vec<BreakerHandle> = vec![
        Scripted::holding(ints().universal_guard()),
        Scripted::keeping(ints().universal_guard()),
    ];
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
    let input = breakers[1].borrow().input_tiling();
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

/// The value of a key in a source a converse groups: three groups.
fn group_of(key: u64) -> i64 {
    (key % 3) as i64
}

fn groups_tiling() -> Tiling {
    Tiling::data_function(
        Extent::Base(BaseType::Int),
        Tiling::data_function(
            Extent::uint_range(KEYS),
            Tiling::Scalar(Extent::uint_range(KEYS)),
        ),
    )
}

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
    Converse,
    Final,
    MemoThenSum,
    MemoThenConverse,
    MapSumThenMemo,
    ConverseThenMemo,
}

/// A run of the chain `top` names at morsels of `rows`: the events, the source, the top breaker
/// and its tiling.
fn run_chain(top: Top, rows: usize) -> (Vec<Event>, Shared, BreakerHandle, Tiling) {
    let groups = matches!(
        top,
        Top::Converse | Top::MemoThenConverse | Top::ConverseThenMemo
    );
    let source = match groups {
        true => source_of(SPARSE, group_of),
        false => source(SPARSE),
    };
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
    let reading = |child: &BreakerHandle| Box::new(ReadsBreaker::of(child));
    let mut breakers = vec![base.clone()];
    let (top, tiling) = match top {
        Top::Memo => (memo_reading(&base) as BreakerHandle, ints()),
        Top::Sum => (aggregate_over(reading(&base), &sum_tiling()), sum_tiling()),
        Top::MapSum => (
            map_aggregate_over(reading(&base), &sums_tiling(), AggregateKind::Sum),
            sums_tiling(),
        ),
        Top::Converse => (
            converse_of(reading(&base), &groups_tiling()),
            groups_tiling(),
        ),
        Top::Final => (extract_final_of(reading(&base), None, &int()), int()),
        Top::MemoThenSum | Top::MemoThenConverse => {
            let middle: BreakerHandle = memo_reading(&base);
            breakers.push(middle.clone());
            match top {
                Top::MemoThenSum => (
                    aggregate_over(reading(&middle), &sum_tiling()),
                    sum_tiling(),
                ),
                _ => (
                    converse_of(reading(&middle), &groups_tiling()),
                    groups_tiling(),
                ),
            }
        }
        Top::MapSumThenMemo | Top::ConverseThenMemo => {
            let (middle, tiling) = match top {
                Top::MapSumThenMemo => (
                    map_aggregate_over(reading(&base), &sums_tiling(), AggregateKind::Sum),
                    sums_tiling(),
                ),
                _ => (
                    converse_of(reading(&base), &groups_tiling()),
                    groups_tiling(),
                ),
            };
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
        Top::Converse,
        Top::Final,
        Top::MemoThenSum,
        Top::MemoThenConverse,
        Top::MapSumThenMemo,
        Top::ConverseThenMemo,
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

/// A converse over a memo holds every group final at every morsel size: its input is released
/// whole, and each group holds the keys that carry its value.
#[test]
fn a_converse_over_a_memo_holds_every_group_final_at_every_morsel_size() {
    for rows in [1, 3, UNBOUNDED] {
        let (_, _, converse, _) = run_chain(Top::Converse, rows);
        assert!(
            converse.borrow().input_released().is_universal(),
            "the input is released whole at morsels of {rows}"
        );
        assert!(
            converse.borrow().final_guard().is_universal(),
            "every group is final at morsels of {rows}: {:?}",
            converse.borrow().final_guard()
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
    memo.consume_impl(ints().universal_guard());
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

/// A child whose reader released part of it pushes morsels over its unreleased keys only.
#[test]
fn a_partly_released_child_pushes_morsels_over_what_is_left() {
    let child = memo_over_rows(0..6);
    child.borrow_mut().consume_impl(ints().universal_guard());
    child.borrow_mut().release(keys_between(2, 3));
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], 2);
    dispatcher.finalize_by_hand(PipelineId(0), |pushes| child.borrow_mut().finalize(pushes));
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
    sum.borrow_mut().consume_impl(ints().universal_guard());
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], 1);
    dispatcher.finalize_by_hand(PipelineId(0), |pushes| sum.borrow_mut().finalize(pushes));
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
        memo.consume_impl(ints().universal_guard());
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
            let child: BreakerHandle = Rc::new(RefCell::new(MemoProducer::over(
                Box::new(Input::over(&source_rows(&keys))),
                &ints(),
            )));
            let sum = aggregate_over(Box::new(ReadsBreaker::of(&child)), &sum_tiling());
            run_cut(vec![vec![], vec![0]], &[child, sum.clone()], rows);
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
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], 1);
    dispatcher.finalize_by_hand(PipelineId(0), |pushes| {
        breaker.borrow_mut().finalize(pushes)
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
    dispatcher.finalize_by_hand(PipelineId(0), |pushes| {
        for _ in 0..2 {
            pushes.push(&all, |guard, _| vec![guard.clone()]);
        }
    });
}

/// A breaker's final guard pushed twice pushes it once: the second push is of what the breaker
/// decided since, which is nothing.
#[test]
fn a_final_guard_pushed_twice_is_pushed_once() {
    let all = ints().universal_guard();
    let breakers: Vec<BreakerHandle> = vec![Scripted::holding(all.clone()), Scripted::holding(all)];
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.finalize_by_hand(PipelineId(0), |pushes| {
        for _ in 0..2 {
            breakers[0].borrow_mut().finalize(pushes);
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
    memo.consume_impl(ints().universal_guard());
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

/// A `Converse` read by a memo pushes one package per morsel of the groups it holds, one per
/// value: `0`, `1` and `2`.
#[test]
fn a_converse_pushes_a_package_per_morsel_of_its_groups() {
    for (rows, expected) in [
        (1, vec![vec![0], vec![1], vec![2]]),
        (2, vec![vec![0, 1], vec![2]]),
        (3, vec![vec![0, 1, 2]]),
        (UNBOUNDED, vec![vec![0, 1, 2]]),
    ] {
        let (events, _, _, _) = run_chain(Top::ConverseThenMemo, rows);
        let packages = consumed_by(&events, 2);
        let named: Vec<Vec<i64>> = packages
            .iter()
            .map(|m| {
                (0..3)
                    .filter(|value| predicate(m).contains(&Value::Int(*value)))
                    .collect()
            })
            .collect();
        assert_eq!(named, expected, "at morsels of {rows}");
        assert_eq!(
            partition_gap(&groups_tiling().universal_guard(), &packages),
            None,
            "at morsels of {rows}"
        );
    }
}

/// The two morsels a scripted child pushes to an ordered parent, claimed by hand.
fn ordered_parent() -> (Dispatcher, Vec<BreakerHandle>) {
    let high = Predicate::True.minus(&keys_predicate(0, 1));
    let (low, high) = (
        keys_between(0, 1),
        TileGuard::Function(FunctionGuard::Domain(high)),
    );
    let child = Scripted::cutting(ints().universal_guard(), vec![low, high]);
    let breakers: Vec<BreakerHandle> = vec![child, Scripted::holding(ints().universal_guard())];
    let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.order(PipelineId(1));
    dispatcher.finalize_by_hand(PipelineId(0), |pushes| {
        breakers[0].borrow_mut().finalize(pushes)
    });
    (dispatcher, breakers)
}

/// An ordered pipeline consumes the morsel claimed for it: a later one handed over first is
/// refused.
#[test]
#[should_panic(expected = "ordered pipeline 1 consumes the morsel claimed for it, in queue order")]
fn a_later_morsel_consumed_first_is_refused() {
    let (dispatcher, breakers) = ordered_parent();
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
    let (dispatcher, breakers) = ordered_parent();
    let first = dispatcher.pop().expect("the lower morsel");
    assert_eq!(dispatcher.pop(), None, "the later morsel waits");
    hand_over(&dispatcher, &breakers, first);
    assert!(dispatcher.pop().is_some(), "the later morsel");
}

/// An ordered pipeline consumes its morsels in the order they were queued, each claimed and
/// consumed before the next is claimed.
#[test]
fn an_ordered_pipeline_consumes_its_morsels_in_queue_order() {
    let (dispatcher, breakers) = ordered_parent();
    while let Some(package) = dispatcher.pop() {
        hand_over(&dispatcher, &breakers, package);
    }
    let high = TileGuard::Function(FunctionGuard::Domain(
        Predicate::True.minus(&keys_predicate(0, 1)),
    ));
    assert_eq!(
        dispatcher.into_events(),
        vec![
            finalized(0),
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
    dispatcher.start_source(PipelineId(0), &ints());
    let package = dispatcher.pop().expect("the source's one package");
    dispatcher.acknowledge(package.clone());
    dispatcher.acknowledge(package);
}

/// A start closes a source, which takes nothing more: a second start is refused.
#[test]
#[should_panic(expected = "pipeline 0 is queued nothing once it is closed")]
fn a_second_start_of_a_source_is_refused() {
    let dispatcher = Dispatcher::new(vec![vec![]], UNBOUNDED);
    dispatcher.start_source(PipelineId(0), &ints());
    dispatcher.start_source(PipelineId(0), &ints());
}

/// Every refusal fails the run before it panics, so a later claim answers `Failed` though no
/// worker handle was dropped.
#[test]
fn a_refusal_fails_the_run_before_it_panics() {
    type Misuse = fn(&Dispatcher);
    let misuses: [(&str, Misuse); 5] = [
        ("a second start", |dispatcher| {
            dispatcher.start_source(PipelineId(0), &ints())
        }),
        (
            "a source start of a pipeline that reads one",
            |dispatcher| dispatcher.start_source(PipelineId(1), &ints()),
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
            "a finalize before the package is acknowledged",
            |dispatcher| {
                dispatcher.begin_finalize(PipelineId(0));
            },
        ),
        ("a finish before the finalize began", |dispatcher| {
            dispatcher.finish(dispatcher.pushes(PipelineId(0)))
        }),
    ];
    for (what, misuse) in misuses {
        let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
        dispatcher.start_source(PipelineId(0), &ints());
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
    let Next::Finalize {
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
    let Next::Finalize { consumed, last, .. } = dispatcher.try_claim(None) else {
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
#[should_panic(expected = "pipeline 1 is queued its input only as a source")]
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

/// A memo over a source notified in two epochs pushes in each epoch only what that epoch
/// decided, and the reader consumes every key once.
#[test]
fn a_memo_pushes_in_each_epoch_what_it_decided_since_the_last() {
    let memo = MemoProducer::over(Box::new(Input::over(&source(0..6))), &ints());
    let memo = Rc::new(RefCell::new(memo));
    let reader = Scripted::holding(ints().empty_guard());
    let breakers: Vec<BreakerHandle> = vec![memo, reader];
    let dispatcher = Dispatcher::new(vec![vec![], vec![0]], UNBOUNDED);
    dispatcher.notify(PipelineId(0), &keys_between(0, 2));
    dispatcher.seal();
    let package = dispatcher
        .claim_of(PipelineId(0))
        .expect("epoch 0's package");
    hand_over(&dispatcher, &breakers, package);
    let Next::Finalize {
        pipeline, epoch, ..
    } = dispatcher.try_claim(None)
    else {
        panic!("the memo finishes epoch 0")
    };
    let mut pushes = dispatcher.pushes_in(pipeline, epoch);
    pushes.push_final(&*breakers[0].borrow());
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
            Next::Finalize {
                pipeline,
                epoch,
                last,
                ..
            } => {
                let mut breaker = breakers[pipeline.0].borrow_mut();
                let mut pushes = dispatcher.pushes_in(pipeline, epoch);
                match last {
                    true => breaker.finalize(&mut pushes),
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
