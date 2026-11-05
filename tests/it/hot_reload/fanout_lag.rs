//! A reader a reload rebuilds over a kept fan-out starts at its predecessor's release
//! (`FanOut::slot_read_by`), not at the intersection of every subscriber's release, so a
//! reload replays no output where the fan-out's readers disagree about what they have
//! released.
//!
//! Every feed case here reads a `defer` feed whose other writer the reload edits.
//! That edit rebuilds the `out` binding, and with it the `StoreDenseRead` that reads
//! the feed's tap off the store. The loop is unchanged, so the store and its fan-out
//! are kept, and the store's other readers release less than the tap reader did.
//!
//! The last test is a pinned failure: it asserts the wrong output the runtime produces
//! today, so it passes now and turns red on any change to that output. Its doc comment
//! gives the correct output. A change that fixes it should replace the pinned value with
//! the correct one and rename the test to state the behavior it then pins.

use indoc::indoc;

use cambra::{
    ccl::context::GlobalContext,
    interpreter::{ColumnValue, FunctionGuard, Tile, TileGuard},
    live_program::{LiveProgram, MAIN_BRANCH},
};

use super::harness::{OneFile, stdin_across_reload};
use super::serving::no_main;

const ITEMS: &str = r#"["a", "b", "c", "d", "e", "f", "g", "h"]"#;

/// Every running value `n` takes over [`ITEMS`], which is what a correct feed emits
/// once each.
const EXPECTED: [&str; 8] = [
    "a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh",
];

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

/// Pull `main` once and release what it delivered, as the binary's driver does
/// (`run_program` in `src/main.rs`).
fn pull(ctx: &mut GlobalContext, live: &mut LiveProgram) -> (Vec<String>, bool) {
    ctx.scheduler().check_for_notifications();
    let producer = live
        .main_producer_mut(MAIN_BRANCH)
        .expect("the program's value is `out`");
    let tile = producer.get(producer.tiling().universal_guard());
    let Tile::DataFunction {
        codomain,
        deleted,
        domain_predicate,
        ..
    } = &tile
    else {
        panic!("a feed is a function, got {tile:?}");
    };
    let Tile::Scalar(ColumnValue::Strings(values)) = codomain.as_ref() else {
        panic!("the feed carries strings, got {codomain:?}");
    };
    let emitted = values
        .iter()
        .enumerate()
        .filter(|(i, _)| !deleted.contains(*i))
        .map(|(_, v)| v.to_string())
        .collect();
    let guard = TileGuard::Function(FunctionGuard::Domain(domain_predicate.clone()));
    let done = guard.is_universal();
    producer.release(guard);
    (emitted, done)
}

/// Run the feed over [`ITEMS`] for `pulls` pulls, reload with the second writer
/// edited, drive to the end, and return everything `main` emitted.
fn emitted_across_reload(reads_n: bool, pulls: usize) -> Vec<String> {
    emitted_across_reloads(reads_n, pulls, &["!"])
}

/// Run the feed over [`ITEMS`] for `pulls` pulls, then reload to the second writer marked with
/// each of `marks` in turn, pulling once between two reloads, drive to the end, and return
/// everything `main` emitted. A mark equal to the one before keeps the second writer.
fn emitted_across_reloads(reads_n: bool, pulls: usize, marks: &[&str]) -> Vec<String> {
    let mut ctx = GlobalContext::default();
    let mut live = LiveProgram::start_text(&mut ctx, &feed(ITEMS, reads_n, ""), &no_main)
        .expect("v1 compiles");
    let mut all = Vec::new();
    for _ in 0..pulls {
        all.extend(pull(&mut ctx, &mut live).0);
    }
    for (at, mark) in marks.iter().enumerate() {
        if at > 0 {
            all.extend(pull(&mut ctx, &mut live).0);
        }
        live.reload_text(&mut ctx, MAIN_BRANCH, &feed(ITEMS, reads_n, mark), &no_main)
            .expect("only the second writer changed");
    }
    for _ in 0..100 {
        let (emitted, done) = pull(&mut ctx, &mut live);
        all.extend(emitted);
        if done {
            return all;
        }
    }
    panic!("the feed never finished: {all:?}");
}

/// What `main` emits across a reload at each cut from 0 to 10 pulls. Two pulls
/// decide the first position; eight more finish the fold.
fn emitted_at_each_cut(reads_n: bool) -> Vec<Vec<String>> {
    (0..=10)
        .map(|pulls| emitted_across_reload(reads_n, pulls))
        .collect()
}

/// Assert that every cut emits each value of [`EXPECTED`] once, and name every cut that does
/// not.
fn assert_every_cut_emits_each_value_once(actual: &[Vec<String>]) {
    let wrong: Vec<String> = actual
        .iter()
        .enumerate()
        .filter(|(_, emitted)| **emitted != strings(&EXPECTED))
        .map(|(pulls, emitted)| format!("{pulls} pulls: {emitted:?}"))
        .collect();
    assert!(
        wrong.is_empty(),
        "each value once at every cut:\n  {}",
        wrong.join("\n  ")
    );
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|v| v.to_string()).collect()
}

/// Each value is emitted once at every cut from 0 to 10 pulls, though the second writer
/// reads `n` without taking anything (see [`feed`]): its release is the recurrence's, a position
/// behind the tap reader's, and the rebuilt tap reader starts at its own predecessor's release.
#[test]
fn a_feed_read_by_a_sibling_that_takes_nothing_emits_each_value_once_at_every_cut() {
    assert_every_cut_emits_each_value_once(&emitted_at_each_cut(true));
}

/// Each value is emitted once at every cut from 0 to 10 pulls. The induction driver's
/// recurrence slot reads each key at the store's frontier, the position before the one it feeds,
/// so its release trails the tap reader's by one position; the rebuilt tap reader starts at its
/// own predecessor's release, not at the driver's.
#[test]
fn a_feed_the_recurrence_still_reads_emits_each_value_once_at_every_cut() {
    assert_every_cut_emits_each_value_once(&emitted_at_each_cut(false));
}

/// Each value is emitted once at every cut from 0 to 10 pulls across two reloads: one that keeps
/// the tap reader and one that rebuilds it, then two that rebuild it. A slot a kept region holds
/// stays recorded under the node of the version that built it, so the reader the second reload
/// rebuilds starts at that slot's release only because the operator map carries the node across
/// the first.
#[rstest::rstest]
fn a_feed_across_two_reloads_emits_each_value_once_at_every_cut(
    #[values(false, true)] reads_n: bool,
    #[values(["", "!"], ["!", "?"])] marks: [&str; 2],
) {
    let emitted: Vec<_> = (0..=10)
        .map(|pulls| emitted_across_reloads(reads_n, pulls, &marks))
        .collect();
    assert_every_cut_emits_each_value_once(&emitted);
}

/// Through the real binary, over `stdin`, reloaded through `--control` at a quiet point
/// between lines: with `a` and `b` sent before the reload and `c` after, each value is printed
/// once, in pull mode as dispatched. The program is that of
/// [`a_feed_read_by_a_sibling_that_takes_nothing_emits_each_value_once_at_every_cut`].
#[rstest::rstest]
fn a_stdin_feed_prints_each_value_once_when_its_other_writer_is_edited(
    #[values("0", "1")] dispatch: &str,
) {
    let (reply, out) = stdin_across_reload(
        &feed("stdin()", true, ""),
        &feed("stdin()", true, "!"),
        "a\nb",
        "c",
        dispatch,
    );
    assert!(
        reply.contains("reloaded"),
        "the reload is accepted: {reply}"
    );
    // The driver prints each tile's `Debug` form, one string value per line.
    let printed: Vec<&str> = out
        .lines()
        .map(str::trim)
        .filter_map(|l| l.strip_prefix('"')?.strip_suffix("\","))
        .collect();
    assert_eq!(printed, ["a", "ab", "abc"], "{out}");
}

/// PINNED FAILURE of a related bug: lost input, not replay. A loop the reload adds
/// over a list-literal binding misses the prefix the existing fold had consumed.
///
/// Correct at every cut from 0 to 10 pulls, as
/// `a_loop_added_over_a_folded_collection_reads_it_whole` pins for a finished fold:
///
/// ```text
/// abcdefgh|abcdefgh
/// ```
///
/// Pinned: cuts 0, 1, 9 and 10 are correct. At 9 and 10 the fold has finished, so
/// `items` is released in full and rebuilt. Cuts 2 to 8 lose one more element each:
///
/// ```text
/// 2 pulls: abcdefgh|bcdefgh
/// 3 pulls: abcdefgh|cdefgh
/// 8 pulls: abcdefgh|h
/// ```
///
/// `bind_let` rebuilds a binding only when it is released in full. A partially
/// released `items` is kept, and the new loop's reader is seeded with the kept
/// fan-out's intersection, which is `n`'s frontier.
#[test]
fn a_loop_added_over_a_collection_caught_mid_fold_loses_its_prefix() {
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
    for pulls in 0..=10 {
        let mut ctx = GlobalContext::default();
        let mut live =
            LiveProgram::start_text(&mut ctx, &fold("", "n"), &no_main).expect("compiles");
        for _ in 0..pulls {
            let producer = live
                .main_producer_mut(MAIN_BRANCH)
                .expect("the value is `n`");
            let _ = producer.get(producer.tiling().universal_guard());
            ctx.scheduler().check_for_notifications();
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
        let pinned = match pulls {
            2..=8 => format!("abcdefgh|{}", &"abcdefgh"[pulls - 1..]),
            _ => "abcdefgh|abcdefgh".to_string(),
        };
        if value != pinned {
            changed.push(format!("{pulls} pulls: actual {value}, pinned {pinned}"));
        }
    }
    assert!(
        changed.is_empty(),
        "the added loop's fold changed. If the lost prefix was fixed, pin the correct \
         abcdefgh|abcdefgh at every cut instead:\n  {}",
        changed.join("\n  "),
    );
}

fn drive_to_terminal(ctx: &mut GlobalContext, live: &mut LiveProgram) -> String {
    for _ in 0..500 {
        ctx.scheduler().check_for_notifications();
        let producer = live
            .main_producer_mut(MAIN_BRANCH)
            .expect("the value is a string");
        let tile = producer.get(producer.tiling().universal_guard());
        if tile.is_terminal() {
            let Tile::Scalar(ColumnValue::Strings(v)) = tile else {
                panic!("a string value, got {tile:?}");
            };
            return v[0].to_string();
        }
    }
    panic!("the fold never settled");
}
