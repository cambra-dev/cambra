//! A reader a reload rebuilds over a kept fan-out whose readers disagree about what
//! they have released.
//!
//! `FanOutSlot::subscribe` seeds a rebuilt reader's slot with the release of the
//! reader it replaces, read off that reader's slot, and the reader starts its own
//! release record there (`src/ccl/design/program-evolution.md`, "Where a rebuilt
//! reader picks up"). The intersection of every slot's release only reclaims, so a
//! sibling that lags does not move where the rebuilt reader starts.
//!
//! The binary case cuts a live feed between lines. The finite case checks collection reuse at
//! supported execution boundaries.
//!
//! `rebuilt_readers_state_the_prefix_their_predecessors_released_complete` reloads two sinks'
//! readers of a kept feed between dispatched runs and runs the program to its end.
//!
//! `a_replacement_held_behind_its_sibling_starts_at_its_predecessors_release`
//! drives two sinks whose readers share a kept feed's fan-out through four versions, so that
//! one reader's replacement starts behind the release its sibling's replacement reaches.
//!
//! A reload subscribes every replacement before a run releases anything, so no case here
//! releases between two replacements' subscriptions. The fan-out's unit tests
//! `retired_slots_hold_reclamation_back_until_the_handover_settles` and
//! `a_slot_that_dies_during_the_handover_holds_reclamation_back_until_it_settles` check that
//! order.

use indoc::{formatdoc, indoc};

use cambra::{
    ccl::{SourceDefinition, Type, context::GlobalContext},
    interpreter::{
        BaseType, ColumnValue, Extent, Predicate, TestDataSource, TestSink, Tile, Value,
    },
    live_program::{LiveProgram, MAIN_BRANCH},
};

use super::harness::{OneFile, stdin_across_reload};
use super::serving::no_main;

const ITEMS: &str = r#"["a", "b", "c", "d", "e", "f", "g", "h"]"#;

/// A feed of `n` over `source`, plus a second writer to the same feed that loops
/// over a collection that is always empty.
///
/// With `reads_n`, the second writer reads the final value of `n`. Its loop never
/// runs, so `MapResultToConst` never pulls that value (see the laziness comment in
/// `MapResultToConstProducer::get_impl`), and the `StoreDenseRead` under the
/// `ExtractFinal` reads the store's fan-out without taking anything. It releases once the
/// loop is done: `MapResultToConst` releases its constant when its consumer releases
/// everything.
///
/// `mark` is the edit: it changes only the second writer.
fn feed(source: &str, reads_n: bool, mark: &str) -> String {
    let second = if reads_n { "n + y" } else { "y" };
    format!(
        indoc! {r#"
            out: Feed(_)
            n := ""
            for x in {source}:
                n := n + x
                out << n
            for y in [z for z in ["q"] if z == "x"]:
                out << {second} + "{mark}"
            out
        "#},
        source = source,
        second = second,
        mark = mark,
    )
}

/// A subprocess reload of a feed with an edited empty writer starts the rebuilt tap reader
/// after the last value the old version printed. With `a` and `b` sent before the reload and
/// `c` after, the output is `["a", "ab", "abc"]`.
///
/// The store's recurrence has not released the last position when `--control` reloads, so the
/// intersection of every slot's release trails the tap reader's own; the rebuilt reader starts
/// at its predecessor's release, not at the intersection.
#[test]
fn a_stdin_feed_resumes_after_the_cut_when_its_other_writer_is_edited() {
    let (reply, out) = stdin_across_reload(
        &feed("stdin()", true, ""),
        &feed("stdin()", true, "!"),
        "a\nb",
        "c",
    );
    assert!(
        reply.contains("reloaded"),
        "the reload is accepted: {reply}"
    );
    // The driver prints each tile's `Debug` form, one string value per line of a `Strings`
    // column. A channel's arm tags print quoted too, outside any `Strings` column.
    let mut in_strings = false;
    let mut printed: Vec<&str> = out
        .lines()
        .map(str::trim)
        .filter_map(|l| {
            match l {
                "Strings(" => in_strings = true,
                "]," | "]" => in_strings = false,
                _ => {}
            }
            in_strings
                .then(|| l.strip_prefix('"')?.strip_suffix("\","))
                .flatten()
        })
        .collect();
    // A `main` output hands each package's answer as the package finishes, in no order, so the
    // values are compared sorted. Sorted, each value extends the one before it, as the
    // accumulation built them.
    printed.sort_unstable();
    assert!(
        printed.windows(2).all(|pair| pair[1].starts_with(pair[0])),
        "each value extends the one before it: {printed:?}"
    );
    assert_eq!(
        printed,
        vec!["a", "ab", "abc"],
        "each value prints once: {out}"
    );
}

/// The values a feed of [`DELIVERED`] over a live `source1()` emits when the items arrive one at
/// a time and a reload that edits the second writer comes before each batch named in `cuts`,
/// each run to a drained boundary at `morsel_rows` rows to a work package.
fn feed_across_reloads(reads_n: bool, cuts: &[usize], morsel_rows: usize) -> Vec<String> {
    let mut feed = LiveFeed::start(reads_n);
    let mut emitted = Vec::new();
    let mut reloads = 0;
    for at in 0..DELIVERED.len() {
        if cuts.contains(&at) {
            reloads += 1;
            feed.reload(MAIN_BRANCH, &"!".repeat(reloads));
        }
        feed.deliver(at);
        emitted.extend(feed.run(MAIN_BRANCH, morsel_rows));
    }
    feed.complete();
    emitted.extend(feed.run(MAIN_BRANCH, morsel_rows));
    emitted
}

/// The items a [`LiveFeed`] delivers, one per position of `source1()`.
const DELIVERED: [&str; 8] = ["a", "b", "c", "d", "e", "f", "g", "h"];

/// A [`feed`] over a live `source1()` that delivers [`DELIVERED`] one at a time, and the branches
/// running it, each run to a drained boundary.
struct LiveFeed {
    ctx: GlobalContext,
    live: LiveProgram,
    source: SourceDefinition<TestDataSource>,
    reads_n: bool,
}

impl LiveFeed {
    /// The feed's first version over a `source1()` that has delivered nothing.
    fn start(reads_n: bool) -> Self {
        use cambra::ccl::Type;
        use cambra::interpreter::{BaseType, Extent, TestDataSource};
        let mut ctx = GlobalContext::default();
        let source = TestDataSource::new(
            "source1",
            Type::Base(BaseType::String),
            Extent::Base(BaseType::String),
        );
        ctx.register_source(source.clone());
        let live = LiveProgram::start_text(&mut ctx, &feed("source1()", reads_n, ""), &no_main)
            .expect("v1 compiles");
        Self {
            ctx,
            live,
            source,
            reads_n,
        }
    }

    /// Deliver the item at position `at` and yield every position through it.
    fn deliver(&mut self, at: usize) {
        use cambra::interpreter::{Predicate, Value};
        let mut source = self
            .source
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        source.add_data(&[(
            Value::uint_from_row(at),
            Value::String(DELIVERED[at].into()),
        )]);
        source.set_yield_predicate(Predicate::at_or_below(Value::uint_from_row(at)));
    }

    /// Yield every position, so the source completes.
    fn complete(&mut self) {
        self.source
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .set_yield_predicate(Predicate::True);
    }

    /// Reload `branch` with the second writer marked `mark`.
    fn reload(&mut self, branch: &str, mark: &str) {
        self.live
            .reload_text(
                &mut self.ctx,
                branch,
                &feed("source1()", self.reads_n, mark),
                &no_main,
            )
            .expect("only the second writer changed");
    }

    /// Run `branch` to a drained boundary at `morsel_rows` rows to a work package, and return
    /// what its `main` emitted.
    fn run(&mut self, branch: &str, morsel_rows: usize) -> Vec<String> {
        struct Pause;
        impl cambra::interpreter::dispatcher::RunObserver for Pause {
            fn drained(&mut self, _: bool) -> std::ops::ControlFlow<()> {
                std::ops::ControlFlow::Break(())
            }
        }
        let output = std::sync::Arc::new(Emitted::default());
        self.live
            .run_branch(branch, morsel_rows, &|_| output.clone(), &mut Pause)
            .expect("the branch dispatches");
        output.0.lock().unwrap().clone()
    }
}

/// A sink that keeps every string value a run emitted, in order.
#[derive(Default)]
struct Emitted(std::sync::Mutex<Vec<String>>);

impl cambra::interpreter::DataSink for Emitted {
    fn process(&self, tile: &Tile) {
        let Tile::DataFunction {
            codomain, deleted, ..
        } = tile
        else {
            return;
        };
        let Tile::Scalar(ColumnValue::Strings(values)) = codomain.as_ref() else {
            return;
        };
        self.0.lock().unwrap().extend(
            values
                .iter()
                .enumerate()
                .filter(|(i, _)| !deleted.contains(*i))
                .map(|(_, v)| v.to_string()),
        );
    }
}

/// Every running value of `n`, once each.
fn every_value_once() -> Vec<String> {
    [
        "a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh",
    ]
    .map(String::from)
    .to_vec()
}

/// A feed whose tap reader a reload rebuilds while a sibling of it lags, the second writer
/// that takes nothing (`reads_n`) or the recurrence a position behind (`!reads_n`), emits each
/// value once at every cut, after one reload and after two. The rebuilt reader starts at its
/// predecessor's release, not at the intersection the lagging sibling holds back.
#[rstest::rstest]
#[case::before_the_first_item(vec![0])]
#[case::partway(vec![3])]
#[case::before_the_last_item(vec![7])]
#[case::twice(vec![2, 5])]
#[case::twice_in_a_row(vec![4, 5])]
fn a_feed_resumes_after_each_cut_while_a_sibling_lags(
    #[case] cuts: Vec<usize>,
    #[values(false, true)] reads_n: bool,
    #[values(1, usize::MAX)] morsel_rows: usize,
) {
    assert_eq!(
        feed_across_reloads(reads_n, &cuts, morsel_rows),
        every_value_once(),
        "cuts {cuts:?}, reads_n {reads_n}, morsel_rows {morsel_rows}"
    );
}

/// A loop added at a drained finite boundary reads the complete fixed collection, before or
/// after the existing fold finishes. Mid-pull cuts are not execution boundaries.
#[test]
fn a_loop_added_over_a_finite_collection_reads_its_whole_prefix() {
    let fold = |added: &str, result: &str| {
        format!(
            indoc! {r#"
                items = {items}
                n := ""
                for x in items:
                    n := n + x
                {added}{result}
            "#},
            items = ITEMS,
            added = added,
            result = result,
        )
    };
    let added = indoc! {r#"
        p := ""
        for y in items:
            p := p + y
    "#};
    let mut changed = Vec::new();
    for completed in [false, true] {
        let mut ctx = GlobalContext::default();
        let mut live =
            LiveProgram::start_text(&mut ctx, &fold("", "n"), &no_main).expect("compiles");
        if completed {
            super::serving::run_branch_to_idle(&mut live, MAIN_BRANCH);
        }
        live.reload_text(
            &mut ctx,
            MAIN_BRANCH,
            &fold(added, r#"n + "|" + p"#),
            &no_main,
        )
        .expect("a loop over a list literal is a collection this version can build again");
        let value = drive_to_terminal(&mut ctx, &mut live);
        // The added loop folds `items` from the element the kept fold is on.
        let pinned = "abcdefgh|abcdefgh";
        if value != pinned {
            changed.push(format!(
                "completed={completed}: actual {value}, pinned {pinned}"
            ));
        }
    }
    assert!(
        changed.is_empty(),
        "the added loop's fold changed. If the lost prefix was fixed, pin the correct \
         abcdefgh|abcdefgh at every cut instead:\n  {}",
        changed.join("\n  "),
    );
}

fn drive_to_terminal(_ctx: &mut GlobalContext, live: &mut LiveProgram) -> String {
    let Tile::Scalar(ColumnValue::Strings(values)) =
        super::serving::run_branch_to_idle(live, MAIN_BRANCH)
    else {
        panic!("a final string")
    };
    values[0].to_string()
}

/// The most names one slot answers to, over the fan-outs `branch` holds.
fn most_names_held_by(live: &LiveProgram, branch: &str) -> usize {
    live.held_operators(branch)
        .expect("the branch exists")
        .iter()
        .filter_map(std::sync::Weak::upgrade)
        .map(|fan| fan.most_names_of_a_slot())
        .max()
        .unwrap_or(0)
}

/// A reader kept across reloads answers to the names of the versions still held. A branch
/// created from `main` holds an older version while `main` reloads six times. After each reload a
/// kept slot answers to three names: the version `main` runs, the version it replaced, whose names
/// go at the next compaction, and the branch's. Without dropping the names of versions no longer
/// held, the count grows by one each reload. Reloading the branch finds its predecessors by the
/// branch's own names, so its feed emits each value it had not emitted once. Once the branch is
/// deleted and `main` reloads again, a slot answers to two names. `main`'s feed emits each value
/// once throughout.
#[test]
fn reloads_beside_a_kept_branch_keep_only_the_names_of_versions_still_held() {
    let mut feed = LiveFeed::start(false);
    feed.deliver(0);
    let mut emitted = feed.run(MAIN_BRANCH, usize::MAX);
    feed.live
        .create_branch_text(
            &mut feed.ctx,
            "old",
            MAIN_BRANCH,
            &self::feed("source1()", false, ""),
            &no_main,
        )
        .expect("the branch compiles");
    let mut most = Vec::new();
    for at in 1..=6 {
        feed.reload(MAIN_BRANCH, &"!".repeat(at));
        most.push(most_names_held_by(&feed.live, MAIN_BRANCH));
        feed.deliver(at);
        emitted.extend(feed.run(MAIN_BRANCH, usize::MAX));
    }
    assert_eq!(
        most, [3; 6],
        "a kept slot's names stay bounded across reloads"
    );
    feed.reload("old", "#");
    let old = feed.run("old", usize::MAX);
    assert_eq!(
        old,
        every_value_once()[1..7],
        "the branch branched after `a`"
    );
    feed.live
        .delete_branch(&mut feed.ctx, "old")
        .expect("the branch is deleted");
    feed.reload(MAIN_BRANCH, "?");
    assert_eq!(
        most_names_held_by(&feed.live, MAIN_BRANCH),
        2,
        "deleting the branch drops its version's names"
    );
    feed.deliver(7);
    feed.complete();
    emitted.extend(feed.run(MAIN_BRANCH, usize::MAX));
    assert_eq!(emitted, every_value_once());
}

/// Two sinks read the feed `f` through one kept fan-out. Version `k` writes `v * k` to each,
/// and a sink marked as waiting adds the sum of a source that has not completed, so its
/// reader takes nothing from the fan-out while it waits.
fn two_readers_of_a_feed(k: i64, a_waits: bool, b_waits: bool) -> String {
    let wait = |waits: bool, source: &str| {
        if waits {
            format!(" + sum({source}())")
        } else {
            String::new()
        }
    };
    formatdoc! {r#"
        a = test_sink()
        b = test_sink()
        f: Feed(_)
        n := 0
        for x in nums():
            n := n + x
            f << n
        for v in f:
            a << v * {k}{a_wait}
        for v in f:
            b << v * {k}{b_wait}
    "#,
        a_wait = wait(a_waits, "hold_a"),
        b_wait = wait(b_waits, "hold_b"),
    }
}

/// A test source of integers named `name`, registered with `ctx`.
fn int_source(ctx: &mut GlobalContext, name: &str) -> SourceDefinition<TestDataSource> {
    let source = TestDataSource::new(name, Type::Base(BaseType::Int), Extent::Base(BaseType::Int));
    ctx.register_source(source.clone());
    source
}

/// Add rows `from..=to` of `nums`, row `i` holding `i + 1`, and declare every row up to `to`
/// complete.
fn add_nums(nums: &SourceDefinition<TestDataSource>, from: u64, to: u64) {
    let rows: Vec<(Value, Value)> = (from..=to)
        .map(|i| {
            (
                Value::UInt(i),
                Value::Int(i64::try_from(i).expect("fits") + 1),
            )
        })
        .collect();
    let mut nums = nums
        .write()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    nums.add_data(&rows);
    nums.set_yield_predicate(Predicate::at_or_below(Value::UInt(to)));
}

/// Run every branch to a drained boundary, so every sink has taken what the program decided.
fn run_to_drained(live: &mut LiveProgram) {
    struct Pause;
    impl cambra::interpreter::dispatcher::RunObserver for Pause {
        fn drained(&mut self, _: bool) -> std::ops::ControlFlow<()> {
            std::ops::ControlFlow::Break(())
        }
    }
    let output = std::sync::Arc::new(Emitted::default());
    live.run(1, &|_| output.clone(), &mut Pause)
        .expect("the program dispatches");
}

/// What `sink` holds, as the value written at each position of `nums`, in position order.
fn by_position(sink: &TestSink) -> Vec<(u64, i64)> {
    let Value::Function(bindings) = sink.value().expect("the sink is complete") else {
        panic!("a feed reads as a function");
    };
    let mut written: Vec<(u64, i64)> = bindings
        .iter()
        .map(|b| match (&b.input, &b.output) {
            (Value::UInt(position), Value::Int(value)) => (*position, *value),
            other => panic!("a position and an integer, got {other:?}"),
        })
        .collect();
    written.sort_unstable();
    written
}

/// Readers that two reloads rebuild over a kept feed state the positions their predecessors
/// released complete, so the run to the program's end finishes and each sink holds each position
/// once, written by the version that decided it. Version `k` writes `v * k`, and each version
/// decides two positions.
///
/// A rebuilt reader's slot starts at its predecessor's release, and the fan-out's input pushes only
/// the positions it still holds. The slot announces the inherited region to its reader, so the
/// memo above it states that region complete. Without the announcement, the memo states only the
/// positions it read, and the run-end check fails.
#[test]
fn rebuilt_readers_state_the_prefix_their_predecessors_released_complete() {
    let mut ctx = GlobalContext::default();
    let nums = int_source(&mut ctx, "nums");
    let a = ctx.register_test_sink("a");
    let b = ctx.register_test_sink("b");
    let mut live =
        LiveProgram::start_text(&mut ctx, &two_readers_of_a_feed(1, false, false), &no_main)
            .expect("v1 compiles");
    add_nums(&nums, 0, 1);
    run_to_drained(&mut live);
    for (k, through) in [(2, 3), (3, 5)] {
        live.reload_text(
            &mut ctx,
            MAIN_BRANCH,
            &two_readers_of_a_feed(k, false, false),
            &no_main,
        )
        .expect("only the writes changed");
        add_nums(&nums, through - 1, through);
        run_to_drained(&mut live);
    }
    add_nums(&nums, 6, 7);
    nums.write()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .set_yield_predicate(Predicate::True);
    run_to_drained(&mut live);
    assert!(live.poll_finished(), "both sinks complete");
    let each_position_once = [
        (0, 1),
        (1, 3),
        (2, 12),
        (3, 20),
        (4, 45),
        (5, 63),
        (6, 84),
        (7, 108),
    ];
    assert_eq!(by_position(&a), each_position_once, "`a`");
    assert_eq!(by_position(&b), each_position_once, "`b`");
}

/// A replacement whose predecessor was held behind its sibling starts at its predecessor's
/// release, and its sibling's replacement releasing further reclaims nothing it still reads.
/// Each sink holds each position's value once, written by the version that decided it:
///
/// ```text
/// a: 1, 3 (v1)  12, 20 (v2)  60, 84, 112, 144 (v4)
/// b: 1, 3 (v1)  24, 40, 60, 84, 112, 144 (v4)
/// ```
///
/// The four versions place the cut. Version 1 has both readers release through position 1.
/// Version 2 holds `b` back, and `a` releases through 3. Version 3 holds both back while the
/// fold decides positions 4 and 5. Version 4 releases `a`, so `a`'s replacement can take
/// positions 4 and 5 and release through 5 while `b`'s replacement starts at its predecessor's
/// release, through 1 (`src/ccl/design/program-evolution.md`, "Where a rebuilt reader picks
/// up").
#[test]
fn a_replacement_held_behind_its_sibling_starts_at_its_predecessors_release() {
    let mut ctx = GlobalContext::default();
    let nums = int_source(&mut ctx, "nums");
    int_source(&mut ctx, "hold_a");
    let hold_b = int_source(&mut ctx, "hold_b");
    let a = ctx.register_test_sink("a");
    let b = ctx.register_test_sink("b");
    let mut live =
        LiveProgram::start_text(&mut ctx, &two_readers_of_a_feed(1, false, false), &no_main)
            .expect("v1 compiles");
    add_nums(&nums, 0, 1);
    run_to_drained(&mut live);
    for (k, a_waits, b_waits, through) in [(2, false, true, 3), (3, true, true, 5)] {
        live.reload_text(
            &mut ctx,
            MAIN_BRANCH,
            &two_readers_of_a_feed(k, a_waits, b_waits),
            &no_main,
        )
        .expect("only the writes changed");
        add_nums(&nums, through - 1, through);
        run_to_drained(&mut live);
    }
    live.reload_text(
        &mut ctx,
        MAIN_BRANCH,
        &two_readers_of_a_feed(4, false, true),
        &no_main,
    )
    .expect("only the writes changed");
    add_nums(&nums, 6, 7);
    nums.write()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .set_yield_predicate(Predicate::True);
    {
        let mut hold_b = hold_b
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        hold_b.add_data(&[(Value::UInt(0), Value::Int(0))]);
        hold_b.set_yield_predicate(Predicate::True);
    }
    run_to_drained(&mut live);
    assert!(live.poll_finished(), "both sinks complete");
    assert_eq!(
        by_position(&a),
        [
            (0, 1),
            (1, 3),
            (2, 12),
            (3, 20),
            (4, 60),
            (5, 84),
            (6, 112),
            (7, 144)
        ],
        "`a` holds each position once"
    );
    assert_eq!(
        by_position(&b),
        [
            (0, 1),
            (1, 3),
            (2, 24),
            (3, 40),
            (4, 60),
            (5, 84),
            (6, 112),
            (7, 144)
        ],
        "`b`'s replacement starts after position 1"
    );
}
