//! A reload replays output when a rebuilt reader subscribes to a kept fan-out
//! whose readers disagree about what they have released.
//!
//! `FanOutBranch::subscribe` seeds every new subscriber with `FanOutShared::released`,
//! the intersection of all subscribers' releases, not with the release of the
//! subscriber it replaces. A reader the reload rebuilds therefore starts at the
//! slowest sibling's frontier and receives again every position between that
//! frontier and the one its predecessor had reached.
//!
//! Every feed case here reads a `defer` feed whose other writer the reload edits.
//! That edit rebuilds the `out` binding, and with it the `StoreDenseRead` that reads
//! the feed's tap off the store. The loop is unchanged, so the store and its fan-out
//! are kept.
//!
//! Every test here is a pinned failure: it asserts the wrong output the runtime
//! produces today, so it passes now and turns red on any change to that output. Each
//! test's doc comment gives the correct output. A change that fixes the bug should
//! replace the pinned value with the correct one and rename the test to state the
//! behavior it then pins.

use indoc::indoc;

use cambra::{
    ccl::context::GlobalContext,
    interpreter::{ColumnValue, FunctionGuard, Tile, TileGuard},
    live_program::LiveProgram,
};

use crate::harness::stdin_across_reload;
use crate::serving::no_main;

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
/// `ExtractFinal` stays subscribed to the store's fan-out without ever releasing.
/// That binding is unchanged across the reload, so it is kept, and it pins the
/// fan-out's intersection at nothing.
///
/// `mark` is the edit: it changes only the second writer.
fn feed(source: &str, reads_n: bool, mark: &str) -> String {
    let second = if reads_n { "n + y" } else { "y" };
    format!(
        indoc! {r#"
            out = defer()
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
        .main_producer_mut()
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
    let mut ctx = GlobalContext::default();
    let mut live =
        LiveProgram::start(&mut ctx, &feed(ITEMS, reads_n, ""), &no_main).expect("v1 compiles");
    let mut all = Vec::new();
    for _ in 0..pulls {
        all.extend(pull(&mut ctx, &mut live).0);
    }
    live.reload(&mut ctx, &feed(ITEMS, reads_n, "!"), &no_main)
        .expect("only the second writer changed");
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

/// Assert that each cut's output is the pinned buggy output, and name every cut
/// that differs.
fn assert_cuts_pinned(actual: &[Vec<String>], pinned: &[Vec<String>]) {
    let changed: Vec<String> = actual
        .iter()
        .zip(pinned)
        .enumerate()
        .filter(|(_, (actual, pinned))| actual != pinned)
        .map(|(pulls, (actual, pinned))| {
            format!("{pulls} pulls:\n    actual: {actual:?}\n    pinned: {pinned:?}")
        })
        .collect();
    assert!(
        changed.is_empty(),
        "the feed's output across a reload changed. If the replay was fixed, pin the \
         correct output from this test's doc comment instead.\n  {}",
        changed.join("\n  "),
    );
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|v| v.to_string()).collect()
}

/// PINNED FAILURE. Every value decided before the swap is emitted a second time
/// after it.
///
/// Correct at every cut from 0 to 10 pulls:
///
/// ```text
/// ["a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]
/// ```
///
/// Pinned: cuts 0 and 1 are correct, and cuts 2 to 10 replay the prefix. Three of
/// them:
///
/// ```text
/// 2 pulls:  ["a", "a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]
/// 4 pulls:  ["a", "ab", "abc", "a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]
/// 10 pulls: ["a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh",
///            "a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]
/// ```
///
/// The kept store's fan-out has a subscriber that never releases (see [`feed`]),
/// so `FanOutShared::released` stays empty. The rebuilt tap reader is seeded with
/// that, and the store has retained every tick, so the whole prefix is re-read.
#[test]
fn a_feed_replays_its_prefix_when_an_unpulled_sibling_holds_its_store() {
    let pinned: Vec<Vec<String>> = (0..=10)
        .map(|pulls| match pulls {
            0 | 1 => strings(&EXPECTED),
            // The values decided before the swap, then the whole feed again.
            _ => strings(&[&EXPECTED[..(pulls - 1).min(8)], &EXPECTED[..]].concat()),
        })
        .collect();
    assert_cuts_pinned(&emitted_at_each_cut(true), &pinned);
}

/// PINNED FAILURE. The value at the cut is emitted twice.
///
/// Correct at every cut from 0 to 10 pulls:
///
/// ```text
/// ["a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]
/// ```
///
/// Pinned: cuts 0 and 1 are correct. Each cut from 2 to 8 repeats the last value
/// decided before the swap, and cuts 9 and 10, after the fold finished, repeat the
/// last two:
///
/// ```text
/// 3 pulls:  ["a", "ab", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]
/// 8 pulls:  ["a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefg", "abcdefgh"]
/// 9 pulls:  ["a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh", "abcdefg", "abcdefgh"]
/// ```
///
/// In-process only: through the binary over `stdin` the recurrence has caught up at
/// the quiet point where `--control` reloads, and nothing is replayed.
///
/// No reader here is unpulled. The induction driver's recurrence branch reads the
/// store's previous tick, so its release trails the tap reader's by one tick, and
/// the rebuilt tap reader is seeded at the driver's frontier.
#[test]
fn a_feed_repeats_the_position_the_recurrence_still_reads() {
    let pinned: Vec<Vec<String>> = (0..=10)
        .map(|pulls| match pulls {
            0 | 1 => strings(&EXPECTED),
            // The value at the cut, `EXPECTED[pulls - 2]`, twice.
            2..=8 => strings(&[&EXPECTED[..pulls - 1], &EXPECTED[pulls - 2..]].concat()),
            // The finished feed, then its last two values again.
            _ => strings(&[&EXPECTED[..], &EXPECTED[6..]].concat()),
        })
        .collect();
    assert_cuts_pinned(&emitted_at_each_cut(false), &pinned);
}

/// PINNED FAILURE through the real binary. The new version prints the values the
/// old version already printed.
///
/// With `a` and `b` sent before the reload and `c` after, correct:
///
/// ```text
/// ["a", "ab", "abc"]
/// ```
///
/// Pinned:
///
/// ```text
/// ["a", "ab", "a", "ab", "abc"]
/// ```
///
/// The program of `a_feed_replays_its_prefix_when_an_unpulled_sibling_holds_its_store`,
/// over `stdin`, reloaded through `--control` at a quiet point between lines.
#[test]
fn a_stdin_feed_replays_when_its_other_writer_is_edited() {
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
    // The driver prints each tile's `Debug` form, one string value per line.
    let printed: Vec<&str> = out
        .lines()
        .map(str::trim)
        .filter_map(|l| l.strip_prefix('"')?.strip_suffix("\","))
        .collect();
    assert_eq!(
        printed,
        vec!["a", "ab", "a", "ab", "abc"],
        "the printed values changed. If the replay was fixed, pin the correct \
         [\"a\", \"ab\", \"abc\"] instead: {out}"
    );
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
        let mut live = LiveProgram::start(&mut ctx, &fold("", "n"), &no_main).expect("compiles");
        for _ in 0..pulls {
            let producer = live.main_producer_mut().expect("the value is `n`");
            let _ = producer.get(producer.tiling().universal_guard());
            ctx.scheduler().check_for_notifications();
        }
        live.reload(&mut ctx, &fold(added, r#"n + "|" + p"#), &no_main)
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
        let producer = live.main_producer_mut().expect("the value is a string");
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
