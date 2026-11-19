//! A reader a reload rebuilds over a kept fan-out whose readers disagree about what
//! they have released.
//!
//! `FanOutSlot::subscribe` seeds a rebuilt reader's slot with the release of the
//! reader it replaces, read off that reader's slot, and the reader starts its own
//! release record there (`src/ccl/design/program-evolution.md`, "Where a rebuilt
//! reader picks up"). The intersection of every slot's release only reclaims, so a
//! sibling that lags does not move where the rebuilt reader starts.
//!
//! Every feed case here reads a `defer` feed whose other writer the reload edits.
//! That edit rebuilds the `out` binding, and with it the `StoreDenseRead` that reads
//! the feed's tap off the store. The loop is unchanged, so the store and its fan-out
//! are kept.
//!
//! `a_loop_added_over_a_collection_caught_mid_fold_loses_its_prefix` is a pinned
//! failure: it asserts the wrong output the runtime produces today, so it turns red on
//! any change to that output, and its doc comment gives the correct output.

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
    pull_branch(ctx, live, MAIN_BRANCH)
}

/// [`pull`] of branch `branch`'s `main`.
fn pull_branch(
    ctx: &mut GlobalContext,
    live: &mut LiveProgram,
    branch: &str,
) -> (Vec<String>, bool) {
    ctx.scheduler().check_for_notifications();
    let producer = live
        .main_producer_mut(branch)
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
    emitted_across_reloads(reads_n, &[pulls])
}

/// Run the feed over [`ITEMS`], and before each count of pulls in `cuts` run that
/// many pulls and then reload with the second writer edited again; drive to the end,
/// and return everything `main` emitted.
fn emitted_across_reloads(reads_n: bool, cuts: &[usize]) -> Vec<String> {
    let mut ctx = GlobalContext::default();
    let mut live = LiveProgram::start_text(&mut ctx, &feed(ITEMS, reads_n, ""), &no_main)
        .expect("v1 compiles");
    let mut all = Vec::new();
    for (version, &pulls) in cuts.iter().enumerate() {
        for _ in 0..pulls {
            all.extend(pull(&mut ctx, &mut live).0);
        }
        let mark = "!".repeat(version + 1);
        live.reload_text(
            &mut ctx,
            MAIN_BRANCH,
            &feed(ITEMS, reads_n, &mark),
            &no_main,
        )
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

/// Assert that each cut's output is `expected`'s, and name every cut that differs.
fn assert_each_cut_emits(actual: &[Vec<String>], expected: &[Vec<String>]) {
    let changed: Vec<String> = actual
        .iter()
        .zip(expected)
        .enumerate()
        .filter(|(_, (actual, expected))| actual != expected)
        .map(|(pulls, (actual, expected))| {
            format!("{pulls} pulls:\n    actual: {actual:?}\n    expected: {expected:?}")
        })
        .collect();
    assert!(
        changed.is_empty(),
        "the feed's output across a reload is wrong at these cuts:\n  {}",
        changed.join("\n  "),
    );
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|v| v.to_string()).collect()
}

/// The feed emits each value once at every cut from 0 to 10 pulls:
///
/// ```text
/// ["a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]
/// ```
///
/// The second writer reads `n` without taking anything (see [`feed`]), and releases the
/// store's fan-out once its empty loop is done, so the kept fan-out's reclamation
/// intersection is what the recurrence has read, one position behind the tap reader. The
/// rebuilt tap reader starts at its predecessor's own release, read off that reader's slot,
/// not at the intersection (`src/ccl/design/program-evolution.md`, "Where a rebuilt reader
/// picks up").
#[test]
fn a_feed_read_by_a_sibling_that_takes_nothing_resumes_after_the_cut() {
    let expected = vec![strings(&EXPECTED); 11];
    assert_each_cut_emits(&emitted_at_each_cut(true), &expected);
}

/// The feed emits each value once at every cut from 0 to 10 pulls:
///
/// ```text
/// ["a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]
/// ```
///
/// The induction driver's recurrence slot reads each key at the store's frontier, the
/// position before the one it feeds, so its release trails the tap reader's by one position.
/// The rebuilt tap reader starts at its predecessor's own release, not at the driver's.
#[test]
fn a_feed_resumes_after_the_cut_while_the_recurrence_trails_it() {
    let expected = vec![strings(&EXPECTED); 11];
    assert_each_cut_emits(&emitted_at_each_cut(false), &expected);
}

/// A second reload starts the tap reader at the release of the reader the first
/// reload built, so the feed emits each value once across both cuts.
#[test]
fn a_feed_reloaded_twice_resumes_after_each_cut() {
    // Before the first position is decided, partway, and later, then at once and
    // partway into the second version.
    for first in [1, 3, 5] {
        for second in [0, 3] {
            for reads_n in [false, true] {
                assert_eq!(
                    emitted_across_reloads(reads_n, &[first, second]),
                    strings(&EXPECTED),
                    "cuts after {first} and {second} more pulls, reads_n {reads_n}"
                );
            }
        }
    }
}

/// A real-binary reload preserves the pull reader's release at the cut. A deferred release
/// from the store's recurrence settles before its mutable borrow ends, so the new version
/// starts after the last value the old version printed.
///
/// With `a` and `b` sent before the reload and `c` after, the output is
/// `["a", "ab", "abc"]`.
///
/// The program of
/// [`a_feed_read_by_a_sibling_that_takes_nothing_resumes_after_the_cut`], over
/// `stdin`, reloaded through `--control` at a quiet point between lines.
#[test]
fn a_stdin_feed_preserves_its_release_when_its_other_writer_is_edited() {
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
    let printed: Vec<&str> = out
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
    assert_eq!(
        printed,
        vec!["a", "ab", "abc"],
        "the rebuilt pull reader resumes after the cut: {out}"
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

/// The most names one slot answers to, over the fan-outs `branch` holds.
fn most_names_held_by(live: &LiveProgram, branch: &str) -> usize {
    live.held_operators(branch)
        .expect("the branch exists")
        .iter()
        .filter_map(std::rc::Weak::upgrade)
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
    let mut ctx = GlobalContext::default();
    let mut live =
        LiveProgram::start_text(&mut ctx, &feed(ITEMS, false, ""), &no_main).expect("v1 compiles");
    let mut all = pull(&mut ctx, &mut live).0;
    live.create_branch_text(
        &mut ctx,
        "old",
        MAIN_BRANCH,
        &feed(ITEMS, false, ""),
        &no_main,
    )
    .expect("the branch compiles");
    let mut most = Vec::new();
    for version in 1..=6 {
        all.extend(pull(&mut ctx, &mut live).0);
        live.reload_text(
            &mut ctx,
            MAIN_BRANCH,
            &feed(ITEMS, false, &"!".repeat(version)),
            &no_main,
        )
        .expect("only the second writer changed");
        most.push(most_names_held_by(&live, MAIN_BRANCH));
    }
    assert_eq!(
        most, [3; 6],
        "a kept slot's names stay bounded across reloads"
    );
    live.reload_text(&mut ctx, "old", &feed(ITEMS, false, "#"), &no_main)
        .expect("only the branch's second writer changed");
    let mut old = Vec::new();
    for _ in 0..100 {
        let (emitted, done) = pull_branch(&mut ctx, &mut live, "old");
        old.extend(emitted);
        if done {
            break;
        }
    }
    assert_eq!(
        old,
        strings(&EXPECTED[1..]),
        "the branch branched after `a`"
    );
    live.delete_branch(&mut ctx, "old")
        .expect("the branch is deleted");
    live.reload_text(&mut ctx, MAIN_BRANCH, &feed(ITEMS, false, "?"), &no_main)
        .expect("only the second writer changed");
    let after = most_names_held_by(&live, MAIN_BRANCH);
    assert_eq!(after, 2, "deleting the branch drops its version's names");
    for _ in 0..100 {
        let (emitted, done) = pull(&mut ctx, &mut live);
        all.extend(emitted);
        if done {
            assert_eq!(all, strings(&EXPECTED));
            return;
        }
    }
    panic!("the feed never finished: {all:?}");
}
