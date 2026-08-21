//! Replacing a running program with a new version of its source, over live HTTP
//! endpoints.
//!
//! # The programs
//!
//! Two base programs, each with variants that differ from it by one edit. Every
//! variant is named for the edit, so `diff`ing it against its base shows exactly
//! what a case is about.
//!
//! `guestbook` serves `/sign`, whose loop accumulates into a mutable variable,
//! and `/peek`, which holds no state. Both loops fall in one causal group, so
//! one `Transact` store carries them.
//!
//! `two-loops` serves `/a` and `/b`, each accumulating into its own mutable
//! variable. They are independent, so they get a store each — which is what
//! makes one adoptable while the other is rebuilt.
//!
//! # The sequences
//!
//! | From | To | Expected |
//! | --- | --- | --- |
//! | `guestbook` | `-stateless-edit` | Accepted. `/peek` changes. The edit is outside the store's recurrence, so the store is adopted and the guestbook's entries carry across untouched. |
//! | `guestbook` | `-stateful-edit` | Accepted. The edit is inside the store's recurrence, so the store is rebuilt and re-derives the whole retained history under the new rule: earlier entries come back reformatted. See the module note below. |
//! | `two-loops` | `-one-edited` | Accepted. `/a`'s store is adopted, entries and all; `/b` gets the new rule. |
//! | `two-loops` | itself, then `-one-edited` | Reuse is identical to making the edit directly, so it does not depend on how many updates came before. |
//! | `guestbook` | `-stateless-edit`, back, and again | Every update takes effect, including reverting. |
//! | `guestbook` | `-adds-route` | Refused: it opens an endpoint the running program does not hold. The program keeps serving. |
//! | `guestbook` | a program that does not parse | Refused. The program keeps serving. |
//!
//! Diffing is separately covered, and must leave the running program untouched
//! whichever stage it compares at.
//!
//! The distinction the two families exist for is store granularity: `guestbook`
//! puts both loops in one store, so an edit to either is an edit to that store's
//! recurrence, while `two-loops` gives each loop a store and so has one that
//! stays adoptable while the other is rebuilt. See
//! `src/ccl/design/live-update.md`, "Stores are bindings too".
//!
//! # Rebuilding a store resumes it, and stalls once the source has trimmed
//!
//! A rebuilt store resumes each variable from the value the retired version left
//! it holding, so an edit to a loop changes what happens next without discarding
//! what the loop had accumulated. See `src/ccl/design/live-update.md`,
//! "Rebuilding a store resumes it".
//!
//! These cases drive two or three requests before updating. That is the regime
//! where a rebuilt store works; past roughly five it produces nothing, and the
//! suite is green anyway. A passing run here is not evidence about that case —
//! see the same doc, "Unresolved: a rebuilt store stalls once its source has
//! trimmed".

use std::{sync::mpsc, thread, time::Duration};

use cambra::{ccl::context::CompileStage, interpreter::Consumer, live_program::UpdateReport};

use super::common::{drive_until, http_get, http_post, reserve_test_port, start_sink};

/// The main-output consumer a sink-only program never uses.
fn no_main() -> Box<dyn Consumer> {
    Box::new(|| {})
}

fn source(name: &str, port: u16) -> String {
    let text = match name {
        "guestbook" => include_str!("guestbook.cambra"),
        "guestbook-stateless-edit" => include_str!("guestbook-stateless-edit.cambra"),
        "guestbook-stateful-edit" => include_str!("guestbook-stateful-edit.cambra"),
        "guestbook-adds-route" => include_str!("guestbook-adds-route.cambra"),
        "two-loops" => include_str!("two-loops.cambra"),
        "two-loops-one-edited" => include_str!("two-loops-one-edited.cambra"),
        other => panic!("no such program: {other}"),
    };
    text.replace("{PORT}", &port.to_string())
}

/// Run `requests` on a client thread and pump the scheduler until they finish.
fn exchange<F>(ctx: &mut cambra::ccl::context::GlobalContext, requests: F) -> Vec<String>
where
    F: FnOnce() -> Vec<String> + Send + 'static,
{
    let (tx, rx) = mpsc::channel::<Vec<String>>();
    thread::spawn(move || tx.send(requests()).unwrap());
    drive_until(ctx, &rx, Duration::from_secs(5))
}

/// An update replaces the edited logic and leaves the untouched logic running,
/// with everything that logic has accumulated.
///
/// The guestbook is signed twice, `/peek` is edited, and the third signature
/// still returns all three entries.
///
/// Both loops of this program share one causal group, so the edit rebuilds their
/// store and the entries survive by being re-derived from the requests the reused
/// source operator still holds. `an_edit_to_one_accumulator_leaves_the_other_running`
/// is the case where the store itself is adopted.
#[test]
fn an_update_keeps_the_state_of_logic_it_did_not_change() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    let before = exchange(&mut ctx, move || {
        vec![
            http_post(port, "/sign", "alice: hi"),
            http_post(port, "/sign", "bob: hello"),
            http_get(port, "/peek"),
        ]
    });
    assert_eq!(
        before,
        vec!["alice: hi\n", "alice: hi\nbob: hello\n", "peek\n"],
    );

    let report: UpdateReport = live
        .update(
            &mut ctx,
            &source("guestbook-stateless-edit", port),
            &no_main,
        )
        .expect("the new version only changes logic between existing endpoints");

    let after = exchange(&mut ctx, move || {
        vec![
            http_get(port, "/peek"),
            http_post(port, "/sign", "carol: hey"),
        ]
    });
    assert_eq!(
        after,
        vec![
            // The edited binding was rebuilt.
            "peek edited\n",
            // The untouched one kept its accumulation across the swap.
            "alice: hi\nbob: hello\ncarol: hey\n",
        ],
    );

    let (reused, bound) = report.reuse;
    assert!(
        reused > 0 && reused < bound,
        "an edit to one of two independent bindings should reuse some and rebuild some, \
         got {reused}/{bound}",
    );
}

/// An edit to the accumulating loop itself takes effect.
///
/// The regression this pins: every mutable variable of a program lives in one
/// `Transact` store bound to `__reg`, and a read of one is a projection off that
/// binding. While the store was registered outside the conversion scope, `__reg`
/// was free in every such term and hashed by its bare spelling, so `sign_resps`
/// (`__reg.to_sign_resps_0`) hashed identically however the recurrence was
/// edited — and its operator was reused against a store that no longer computed
/// what it had. The edit was accepted, reported as a divergence, and silently
/// did nothing.
#[test]
fn an_edit_to_the_accumulating_loop_takes_effect() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    let before = exchange(&mut ctx, move || {
        vec![
            http_post(port, "/sign", "alice"),
            http_post(port, "/sign", "bob"),
        ]
    });
    assert_eq!(
        before,
        vec![
            "alice
",
            "alice
bob
"
        ]
    );

    live.update(&mut ctx, &source("guestbook-stateful-edit", port), &no_main)
        .expect("editing a loop body is a change between existing endpoints");

    let after = exchange(&mut ctx, move || vec![http_post(port, "/sign", "carol")]);
    assert_eq!(
        after,
        // The store is rebuilt, and resumes from the value the replaced version
        // had reached: the entries it already recorded stand as they were, and
        // the new rule governs from here.
        vec!["alice\nbob\n- carol\n"],
        "the new loop body must govern the response",
    );
}

/// Editing one of `two-loops`' two independent loops leaves the other's store
/// adopted, with its entries, and applies the new rule to the edited one.
#[test]
fn an_edit_to_one_accumulator_leaves_the_other_running() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("two-loops", port));

    let before = exchange(&mut ctx, move || {
        vec![http_post(port, "/a", "p"), http_post(port, "/b", "q")]
    });
    assert_eq!(before, vec!["p\n", "q\n"]);

    live.update(&mut ctx, &source("two-loops-one-edited", port), &no_main)
        .expect("editing one loop is a change between existing endpoints");

    let after = exchange(&mut ctx, move || {
        vec![http_post(port, "/a", "r"), http_post(port, "/b", "s")]
    });
    assert_eq!(
        after,
        vec![
            // Untouched: its store was adopted, entries and all.
            "p\nr\n",
            // Edited: its store was rebuilt but resumed from `q`, so the entry it
            // already held stands as recorded and the new rule governs from here.
            // `q` keeping its original form also shows the two loops'
            // accumulators do not collide — both are `acc0` within their own store.
            "q\n* s\n",
        ],
    );
}

/// How much an update reuses does not depend on how many updates came before it.
///
/// The regression this pins: while a binding's class was its identity hash when
/// adopted and a fresh value when built, a first compilation handed out classes
/// that no later one reproduced, so every binding reading another was rebuilt on
/// the first update and reuse only settled in on the second. A program is most
/// likely to be updated exactly once, which is the case that lost the most.
#[test]
fn reuse_does_not_depend_on_how_many_updates_came_before() {
    let first = {
        let port = reserve_test_port();
        let (mut ctx, mut live) = start_sink(&source("two-loops", port));
        live.update(&mut ctx, &source("two-loops-one-edited", port), &no_main)
            .expect("accepted")
            .reuse
    };
    let after_a_no_op = {
        let port = reserve_test_port();
        let (mut ctx, mut live) = start_sink(&source("two-loops", port));
        live.update(&mut ctx, &source("two-loops", port), &no_main)
            .expect("accepted");
        live.update(&mut ctx, &source("two-loops-one-edited", port), &no_main)
            .expect("accepted")
            .reuse
    };
    assert_eq!(
        first, after_a_no_op,
        "the same edit reused {first:?} as a program's first update and \
         {after_a_no_op:?} as its second",
    );
    let (reused, bound) = first;
    assert!(
        reused * 2 > bound,
        "editing one of two independent loops should leave most of the program \
         in place, got {reused}/{bound}",
    );
}

/// A version that opens an endpoint the running program does not hold is
/// rejected, and the running program keeps serving.
#[test]
fn an_update_may_not_open_a_new_endpoint() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    let errors = live
        .update(&mut ctx, &source("guestbook-adds-route", port), &no_main)
        .err()
        .expect("adding an http_serve route is not a change between existing endpoints");
    let rendered = format!("{errors:?}");
    assert!(
        rendered.contains("opens a new endpoint"),
        "expected the endpoint-set rejection, got: {rendered}",
    );

    let still_serving = exchange(&mut ctx, move || vec![http_get(port, "/peek")]);
    assert_eq!(still_serving, vec!["peek\n"]);
}

/// A version that does not compile is rejected before the running program is
/// touched.
#[test]
fn a_rejected_update_leaves_the_program_serving() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    live.update(&mut ctx, "x = = 1", &no_main)
        .err()
        .expect("a syntax error is not an update");

    let still_serving = exchange(&mut ctx, move || vec![http_get(port, "/peek")]);
    assert_eq!(still_serving, vec!["peek\n"]);
}

/// Diffing a running program against a new version opens nothing and changes
/// nothing — the endpoint set it compiles against is the one already bound.
///
/// The naive alternative, compiling the new version in a fresh context, would
/// try to bind a port this program holds.
#[test]
fn diffing_a_running_http_program_leaves_it_untouched() {
    let port = reserve_test_port();
    let (mut ctx, live) = start_sink(&source("guestbook", port));

    let identical = live
        .diff_against(&ctx, &source("guestbook", port), CompileStage::Channelized)
        .expect("the running source compiles against its own endpoints");
    assert!(
        identical.contains("no difference"),
        "a program should not differ from itself: {identical}",
    );

    let changed = live
        .diff_against(
            &ctx,
            &source("guestbook-stateless-edit", port),
            CompileStage::Channelized,
        )
        .expect("the new version compiles against the running endpoints");
    assert!(
        changed.contains("divergence"),
        "an edited program should report a divergence: {changed}",
    );

    let still_serving = exchange(&mut ctx, move || vec![http_get(port, "/peek")]);
    assert_eq!(still_serving, vec!["peek\n"]);
}

/// Every stage is available as a diff point, not only the default.
#[test]
fn every_stage_is_a_diff_point() {
    let port = reserve_test_port();
    let (ctx, live) = start_sink(&source("guestbook", port));

    for stage in [
        CompileStage::Lowered,
        CompileStage::Inferred,
        CompileStage::Inlined,
        CompileStage::Channelized,
        CompileStage::LambdaElim,
        CompileStage::Planned,
    ] {
        let rendered = live
            .diff_against(&ctx, &source("guestbook-stateless-edit", port), stage)
            .unwrap_or_else(|e| panic!("diff at {stage:?} failed: {e:?}"));
        assert!(
            rendered.contains("divergence"),
            "the edit should be visible at {stage:?}: {rendered}",
        );
    }
}

/// Repeated updates keep working, including switching back to a version that
/// already ran.
#[test]
fn a_program_can_be_updated_repeatedly() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    for (name, expected) in [
        ("guestbook-stateless-edit", "peek edited\n"),
        ("guestbook", "peek\n"),
        ("guestbook-stateless-edit", "peek edited\n"),
        // Twice in a row: an update to the version already running is a no-op
        // that must still leave it serving.
        ("guestbook-stateless-edit", "peek edited\n"),
    ] {
        live.update(&mut ctx, &source(name, port), &no_main)
            .unwrap_or_else(|e| panic!("update to {name} rejected: {e:?}"));
        let served = exchange(&mut ctx, move || vec![http_get(port, "/peek")]);
        assert_eq!(served, vec![expected], "after updating to {name}");
    }
}
