//! A reload replays output when a rebuilt reader subscribes to a kept fan-out
//! whose readers disagree about what they have released.
//!
//! `FanOutSlot::subscribe` seeds every new subscriber with `FanOutShared::released`,
//! the intersection of all subscribers' releases, not with the release of the
//! subscriber it replaces. A reader the reload rebuilds therefore starts at the
//! slowest sibling's frontier and receives again every position between that
//! frontier and the one its predecessor had reached.
//!
//! The binary case retains the deferred replay pin. The finite case checks collection reuse at
//! supported execution boundaries.

use indoc::indoc;

use cambra::{
    ccl::context::GlobalContext,
    interpreter::{ColumnValue, Tile},
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

/// A subprocess reload of a feed with an edited empty writer. Replay remains a deferred issue;
/// this test exercises the actual dispatcher and control port rather than manual producer reads.
#[rstest::rstest]
fn a_stdin_feed_repeats_the_value_at_the_cut_when_its_other_writer_is_edited() {
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
    let expected = vec!["a", "ab", "ab", "abc"];
    assert_eq!(
        printed, expected,
        "the printed values changed. If the replay was fixed, pin the correct \
         [\"a\", \"ab\", \"abc\"] in both modes: {out}"
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
