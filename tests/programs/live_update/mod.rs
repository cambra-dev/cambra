//! Replacing a running program with a new version of its source, against a
//! program that is actually running.
//!
//! # The programs
//!
//! Base programs with variants that differ from them by one edit. A variant is
//! named for its edit, so `diff`ing it against its base shows what a case is
//! about.
//!
//! | Base | Shape |
//! | --- | --- |
//! | `guestbook` | `POST /sign` accumulates into a mutable variable, `GET /peek` holds no state. Both loops fall in one causal group, so one `Transact` store carries them. |
//! | `two-loops` | `POST /a` and `POST /b` each accumulate into their own variable. Independent, so a store each — one stays adoptable while the other is rebuilt. |
//! | `two-accumulators` | One loop carrying two variables (`left` and `right`), for the cases about telling them apart. |
//! | `one-stateful-loop` | `POST /p` accumulates, `POST /q` does not — the pair a variable can move between. |
//! | `latest-write` | A transactional variable (`Mut(String, Txn)`) that `POST /set` overwrites and `GET /get` reads. |
//!
//! The `stdin` cases build their programs inline and drive the binary as a
//! subprocess ([`stdin_across_update`]), because a `main` output belongs to the
//! binary's own loop rather than to a sink a test can pump.
//!
//! # What an update may do
//!
//! | Change | Expected |
//! | --- | --- |
//! | Logic outside a store's recurrence | Accepted; the store is adopted and its variables are untouched |
//! | Logic inside one | Accepted; the store is rebuilt and each variable resumes from the value it held, so what was recorded stands and the new rule governs from here |
//! | An edit to one of two independent loops | Accepted; the other's store is adopted |
//! | A loop gains an accumulator | Accepted; the others resume, the new one starts at its init |
//! | An endpoint is added | Accepted; the route serves as soon as the swap completes |
//! | An endpoint is removed | Accepted; the route is retired and the address answers 404 |
//! | Repeats and reverts | Accepted; each takes effect |
//!
//! # What it may not
//!
//! | Change | Expected |
//! | --- | --- |
//! | A variable is no longer declared | Refused, naming it |
//! | A variable's type changes | Refused, naming both types |
//! | A variable moves to another loop, or to or from a transaction | Refused, naming where it went |
//! | The source does not compile | Refused |
//!
//! In every refusal the running program keeps serving. Diffing is covered
//! separately and must leave it untouched whichever stage it compares at.
//!
//! # Two properties worth stating
//!
//! How much an update reuses does not depend on how many updates came before it:
//! a binding is named by what it computes, not by whether the compilation before
//! this one happened to build it.
//!
//! A rebuilt store resumes rather than restarting, and resumes at the position
//! its source has reached rather than replaying it. Most cases here drive two or
//! three requests before updating, which is not enough to exercise a resuming
//! store's indexing — `a_store_resumes_however_far_its_source_has_advanced`
//! drives six for that reason.

use std::{
    sync::mpsc,
    thread,
    time::{Duration, Instant},
};

use cambra::{
    ccl::context::{CompileStage, ReuseTally},
    interpreter::Consumer,
    live_program::UpdateReport,
};

use super::common::{drive_until, http_get, http_post, raw_http, reserve_test_port, start_sink};

/// Run a `stdin`-sourced program under `--control`, feeding it `before`, then
/// swapping it for `updated` and feeding it `after`.
///
/// Driven as a subprocess because a `main` output belongs to the binary's own
/// loop, not to a sink a test can pump. Such a program is not short-lived: its
/// source is unbounded, so it keeps running and is as updatable as any other.
fn stdin_across_update(
    program: &str,
    updated: &str,
    before: &str,
    after: &str,
) -> (String, String) {
    use std::io::{BufRead, BufReader, Write};
    use std::process::{Command, Stdio};

    let control = reserve_test_port();
    let dir = std::env::temp_dir().join(format!("cambra-live-{control}"));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let v1 = dir.join("v1.cambra");
    let v2 = dir.join("v2.cambra");
    std::fs::write(&v1, program).expect("write v1");
    std::fs::write(&v2, updated).expect("write v2");

    let mut child = Command::new(env!("CARGO_BIN_EXE_cambra"))
        .arg(format!("--control={control}"))
        .arg(&v1)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn cambra");

    let mut input = child.stdin.take().expect("piped stdin");
    let out = child.stdout.take().expect("piped stdout");
    let collected = std::sync::Arc::new(std::sync::Mutex::new(String::new()));
    let sink = collected.clone();
    let reader = thread::spawn(move || {
        for line in BufReader::new(out).lines().map_while(Result::ok) {
            sink.lock().unwrap().push_str(&line);
            sink.lock().unwrap().push('\n');
        }
    });

    // The program binds its control port during compilation, before it reads a
    // line, so a write is only safe once the port answers.
    let deadline = Instant::now() + Duration::from_secs(10);
    while std::net::TcpStream::connect(("127.0.0.1", control)).is_err() {
        assert!(Instant::now() < deadline, "control port never opened");
        thread::sleep(Duration::from_millis(50));
    }

    writeln!(input, "{before}").expect("write before");
    input.flush().expect("flush");
    thread::sleep(Duration::from_millis(400));

    let body = std::fs::read_to_string(&v2).expect("read v2");
    let reply = raw_http(
        control,
        &format!(
            "POST /update HTTP/1.1\r\nHost: 127.0.0.1:{control}\r\nContent-Length: {}\r\n\
             Connection: close\r\n\r\n{body}",
            body.len()
        ),
    );
    writeln!(input, "{after}").expect("write after");
    input.flush().expect("flush");
    thread::sleep(Duration::from_millis(400));
    drop(input);

    let _ = child.wait();
    reader.join().expect("reader thread");
    let text = collected.lock().unwrap().clone();
    (reply, text)
}

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
        "guestbook-drops-state" => include_str!("guestbook-drops-state.cambra"),
        "guestbook-retypes-state" => include_str!("guestbook-retypes-state.cambra"),
        "guestbook-drops-route" => include_str!("guestbook-drops-route.cambra"),
        "two-loops" => include_str!("two-loops.cambra"),
        "two-loops-one-edited" => include_str!("two-loops-one-edited.cambra"),
        "two-accumulators" => include_str!("two-accumulators.cambra"),
        "two-accumulators-reordered" => include_str!("two-accumulators-reordered.cambra"),
        "two-accumulators-added" => include_str!("two-accumulators-added.cambra"),
        "one-stateful-loop" => include_str!("one-stateful-loop.cambra"),
        "one-stateful-loop-moved" => include_str!("one-stateful-loop-moved.cambra"),
        "latest-write" => include_str!("latest-write.cambra"),
        "latest-write-writer-edit" => include_str!("latest-write-writer-edit.cambra"),
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

    let ReuseTally { adopted, bound } = report.reuse;
    assert!(
        adopted > 0 && adopted < bound,
        "an edit to one of two independent bindings should adopt some and rebuild some, \
         got {adopted}/{bound}",
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

/// A store resumes correctly however far its source has advanced.
///
/// The regression this pins: the writer body is fed through a buffer this store
/// appends to, so a decision is indexed by the row that produced it — the *n*th
/// position *this store* drove. A store resuming a running program starts at the
/// source's frontier rather than at `0`, so looking a decision up by absolute
/// position found nothing and the drive stalled, silently: the update was
/// accepted, the program's other endpoints kept serving, and the resumed loop
/// answered nothing.
///
/// Six prior requests rather than the two or three the cases above use. That is
/// the whole point of this case: at one or two the row index and the absolute
/// position coincide often enough for the drive to stumble through, so the rest
/// of this suite passed throughout.
#[test]
fn a_store_resumes_however_far_its_source_has_advanced() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    let before = exchange(&mut ctx, move || {
        (1..=6)
            .map(|i| http_post(port, "/sign", &format!("e{i}")))
            .collect()
    });
    assert_eq!(before.len(), 6);
    assert_eq!(before[5], "e1\ne2\ne3\ne4\ne5\ne6\n");

    live.update(&mut ctx, &source("guestbook-stateful-edit", port), &no_main)
        .expect("editing a loop body is a change between existing endpoints");

    let after = exchange(&mut ctx, move || vec![http_post(port, "/sign", "e7")]);
    assert_eq!(
        after,
        // Six entries as they were recorded, and the seventh under the new rule.
        vec!["e1\ne2\ne3\ne4\ne5\ne6\n- e7\n"],
    );
}

/// Two accumulators of one loop keep their own values when the loop is
/// rewritten with them in the other order.
///
/// The regression this pins: a write set used to reach the store as an
/// unlabelled tuple, so an accumulator was known downstream only by its position
/// within its loop. Reordering two left both positions occupied and pointing at
/// each other, and resuming from them wrote each variable's history into the
/// other — `aaa|BBB` came back as `BBBa|aaaB`, which no assertion about a single
/// accumulator could have caught.
#[test]
fn reordering_two_accumulators_does_not_cross_their_state() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("two-accumulators", port));

    let before = exchange(&mut ctx, move || {
        (0..3).map(|_| http_post(port, "/bump", "x")).collect()
    });
    assert_eq!(before[2], "aaa|BBB\n");

    live.update(
        &mut ctx,
        &source("two-accumulators-reordered", port),
        &no_main,
    )
    .expect("reordering two accumulators is a change between existing endpoints");

    let after = exchange(&mut ctx, move || vec![http_post(port, "/bump", "x")]);
    assert_eq!(
        after,
        vec!["aaaa|BBBB\n"],
        "each accumulator keeps its own value"
    );
}

/// A version may add an accumulator to a loop: the ones already there resume and
/// the new one starts from its init.
///
/// The complement of dropping one, which is refused — a variable the new version
/// introduces has no value to lose.
#[test]
fn a_loop_may_gain_an_accumulator() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("two-accumulators", port));

    let before = exchange(&mut ctx, move || {
        (0..2).map(|_| http_post(port, "/bump", "x")).collect()
    });
    assert_eq!(before[1], "aa|BB\n");

    live.update(&mut ctx, &source("two-accumulators-added", port), &no_main)
        .expect("adding an accumulator loses nothing");

    let after = exchange(&mut ctx, move || vec![http_post(port, "/bump", "x")]);
    assert_eq!(
        after,
        // The two that were there carry; the added one starts empty.
        vec!["aaa|BBB|c\n"],
    );
}

/// Moving a variable to a different loop is refused, and says where it went.
///
/// A name matching is not the same variable: an accumulator's history came from
/// the inputs its loop read, so the value the old loop built is not a seed for a
/// loop over another source. Reported apart from a deletion because the two read
/// very differently to whoever wrote the edit.
#[test]
fn moving_a_variable_to_another_loop_is_refused() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("one-stateful-loop", port));

    let before = exchange(&mut ctx, move || vec![http_post(port, "/p", "x")]);
    assert_eq!(before, vec!["a\n"]);

    let errors = live
        .update(&mut ctx, &source("one-stateful-loop-moved", port), &no_main)
        .err()
        .expect("`n` accumulates over a different source in the new version");
    let rendered = format!("{errors:?}");
    assert!(
        rendered.contains("`n`") && rendered.contains("now belongs to"),
        "the rejection should say where the variable went: {rendered}",
    );

    let still_serving = exchange(&mut ctx, move || vec![http_post(port, "/p", "x")]);
    assert_eq!(still_serving, vec!["aa\n"], "state intact");
}

/// A transactional variable survives an edit to the writer that commits it.
///
/// The commit store is rebuilt, because the edit is inside its recurrence, and
/// resumes `latest` from the value the retired version had committed. The read
/// endpoint is untouched throughout, so a `GET` before any further write is
/// asking the resumed store directly.
///
/// The regression this pins: the commit store published its state and was
/// adopted when unchanged, but nothing seeded a rebuilt one, so editing a
/// transactional writer silently reset the variable to its declared init.
#[test]
fn a_transactional_variable_survives_an_edit_to_its_writer() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("latest-write", port));

    let before = exchange(&mut ctx, move || {
        vec![http_post(port, "/set", "bob"), http_get(port, "/get")]
    });
    assert_eq!(before, vec!["ok\n", "bob"]);

    live.update(
        &mut ctx,
        &source("latest-write-writer-edit", port),
        &no_main,
    )
    .expect("editing a transactional writer is a change between existing endpoints");

    let after = exchange(&mut ctx, move || {
        vec![
            // Committed before the swap, so it stands as committed.
            http_get(port, "/get"),
            http_post(port, "/set", "carol"),
            // Committed after, so the new rule governs it.
            http_get(port, "/get"),
        ]
    });
    assert_eq!(after, vec!["bob", "ok\n", "carol!"]);
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
            // `q` keeping its original form also shows the two loops' state does
            // not collide, each being scoped by the source its loop reads.
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
    let ReuseTally { adopted, bound } = first;
    assert!(
        adopted * 2 > bound,
        "editing one of two independent loops should leave most of the program \
         in place, got {adopted}/{bound}",
    );
}

/// A program whose output is its `main` value rather than a sink updates too.
///
/// Its source is `stdin`, which is unbounded, so the program keeps running and
/// the binary's own driver loop services the control port between pulls. The
/// line written before the swap is answered by the old version and the one after
/// by the new.
#[test]
fn a_main_output_program_over_stdin_updates() {
    let (reply, out) = stdin_across_update(
        "[\"> \" + line for line in stdin()]\n",
        "[\">> \" + line for line in stdin()]\n",
        "one",
        "two",
    );
    assert!(
        reply.contains("updated"),
        "the update should be accepted: {reply}"
    );
    assert!(
        out.contains("\"> one\""),
        "the first line predates the swap: {out}"
    );
    assert!(
        out.contains("\">> two\""),
        "the second line follows it: {out}"
    );
    assert!(
        !out.contains("\">> one\""),
        "the swap must not reprocess the line the old version answered: {out}"
    );
}

/// A pure element-wise transformation splits exactly at the swap: every element
/// is emitted once, by the version that was running when it arrived.
///
/// Eight lines with the swap after the fourth. Nothing here holds state, so what
/// is being checked is the seam itself — that the stream is neither replayed
/// through the new version nor has elements dropped at the handover.
#[test]
fn an_element_wise_transformation_splits_exactly_at_the_swap() {
    let (reply, out) = stdin_across_update(
        "[\"A\" + line for line in stdin()]\n",
        "[\"B\" + line for line in stdin()]\n",
        "L1\nL2\nL3\nL4",
        "L5\nL6\nL7\nL8",
    );
    assert!(
        reply.contains("updated"),
        "the update should be accepted: {reply}"
    );
    for want in ["AL1", "AL2", "AL3", "AL4", "BL5", "BL6", "BL7", "BL8"] {
        assert!(out.contains(want), "missing {want} from: {out}");
    }
    for unwanted in ["BL1", "BL2", "BL3", "BL4", "AL5", "AL6", "AL7", "AL8"] {
        assert!(
            !out.contains(unwanted),
            "{unwanted} means an element crossed the seam: {out}"
        );
    }
}

/// An accumulator in a `main`-output program carries across the swap, and each
/// half of the stream is counted by the rule in force when it arrived.
///
/// Four lines, the rule changing from `+1` to `+2` after the second: the value
/// at EOF is `6`, not `4` (the old rule throughout) and not `8` (the new one
/// applied retroactively). Nothing about a `main` output makes its state less
/// live than a sink program's — what a value like `n` here reports is decided by
/// when it is read, and reading it at the tail of the program means EOF.
#[test]
fn a_main_output_accumulator_carries_across_the_swap() {
    let (reply, out) = stdin_across_update(
        "n := 0\nfor line in stdin():\n    n := n + 1\nn\n",
        "n := 0\nfor line in stdin():\n    n := n + 2\nn\n",
        "a\nb",
        "c\nd",
    );
    assert!(
        reply.contains("updated"),
        "the update should be accepted: {reply}"
    );
    let flat: String = out.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(
        flat.contains("Ints([6,],)"),
        "want 1+1+2+2; the whole run was: {out}"
    );
}

/// A `main`-output program reports its accumulator *live* when it feeds one out,
/// and the feed shows the swap taking effect mid-stream.
///
/// `out << n` per line makes each step observable rather than only the value at
/// EOF, so the sequence `1, 2, 4, 6` is the accumulator itself: two steps of `+1`,
/// then the swap, then two of `+2` continuing from `2` rather than restarting.
#[test]
fn a_fed_accumulator_is_observable_across_the_swap() {
    let (reply, out) = stdin_across_update(
        "out = defer()\nn := 0\nfor line in stdin():\n    n := n + 1\n    out << n\nout\n",
        "out = defer()\nn := 0\nfor line in stdin():\n    n := n + 2\n    out << n\nout\n",
        "a\nb",
        "c\nd",
    );
    assert!(
        reply.contains("updated"),
        "the update should be accepted: {reply}"
    );
    let flat: String = out.chars().filter(|c| !c.is_whitespace()).collect();
    // `4` is the step that can only happen if the swap resumed from `2`; a
    // restart would report `2` again.
    assert!(flat.contains("Ints([4,],)"), "want a step to 4: {out}");
    assert!(flat.contains("Ints([6,],)"), "want a step to 6: {out}");
}

/// The state guard covers a `stdin`-sourced loop, not just an `http_serve` one.
///
/// A loop's accumulators are identified by the source the loop reads, and
/// nothing about that is HTTP-specific — the store id here is plainly `stdin`.
/// The value never reaches the program's output (a scalar read of an
/// accumulator over an unbounded source never finalizes), which is exactly why
/// the guard has to catch the change rather than leaving it to be noticed.
#[test]
fn the_state_guard_covers_a_stdin_sourced_loop() {
    let (reply, _) = stdin_across_update(
        "n := \"\"\nfor line in stdin():\n    n := n + line\nn\n",
        "n := 0\nfor line in stdin():\n    n := n + 1\nn\n",
        "a",
        "b",
    );
    assert!(
        reply.contains("`n`, of the loop over `stdin`") && reply.contains("Int"),
        "the rejection should name the stdin loop's variable and its new type: {reply}"
    );
}

/// A version may add an endpoint, and serves it as soon as the swap completes.
///
/// The endpoint set is not frozen: a route the registry already holds is bound
/// and one it does not is opened, in a replacement exactly as in a first
/// version. The endpoints that were already there keep working, state included.
#[test]
fn an_update_may_add_an_endpoint() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    let before = exchange(&mut ctx, move || vec![http_post(port, "/sign", "alice")]);
    assert_eq!(before, vec!["alice\n"]);

    live.update(&mut ctx, &source("guestbook-adds-route", port), &no_main)
        .expect("adding an endpoint is allowed");

    let after = exchange(&mut ctx, move || {
        vec![
            // The added route serves.
            http_get(port, "/added"),
            // The endpoints that were already there are unaffected, state and all.
            http_get(port, "/peek"),
            http_post(port, "/sign", "bob"),
        ]
    });
    assert_eq!(after, vec!["added\n", "peek\n", "alice\nbob\n"]);
}

/// A version that stops serving a route retires it, so the address answers 404.
///
/// The listener and its routing-table entry belong to the source/sink registry
/// and outlive the version that opened them, so a version that stops binding a
/// route has to say so. Left registered, the route keeps matching requests and
/// buffering them for a reader that no longer exists, and the client waits on a
/// reply nobody will compute — this test hangs rather than fails if that
/// regresses, because the request never comes back at all.
#[test]
fn a_version_that_stops_serving_a_route_retires_it() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    let before = exchange(&mut ctx, move || vec![http_get(port, "/peek")]);
    assert_eq!(before, vec!["peek\n"]);

    live.update(&mut ctx, &source("guestbook-drops-route", port), &no_main)
        .expect("dropping a stateless route is allowed");

    let after = exchange(&mut ctx, move || {
        vec![
            // Retired: the dispatcher answers rather than buffering.
            http_get(port, "/peek"),
            // The route that stayed is unaffected.
            http_post(port, "/sign", "alice"),
        ]
    });
    assert_eq!(after, vec!["Not Found", "alice\n"]);
}

/// A version that declares a held variable at a different type is rejected, and
/// the running program keeps serving.
///
/// The value cannot be the seed of a store built for another shape. Left to
/// proceed, the store is constructed around a constant of the wrong extent and
/// the process dies on the next pull (`Scalar(Strings([..])) vs Scalar(Int)`),
/// taking every endpoint with it — the update is not recoverable at that point,
/// so it has to be refused before the swap.
#[test]
fn an_update_may_not_change_the_type_of_held_state() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    let before = exchange(&mut ctx, move || vec![http_post(port, "/sign", "alice")]);
    assert_eq!(before, vec!["alice\n"]);

    let errors = live
        .update(&mut ctx, &source("guestbook-retypes-state", port), &no_main)
        .err()
        .expect("`entries` holds a String; the new version declares it an Int");
    let rendered = format!("{errors:?}");
    assert!(
        rendered.contains("`entries`") && rendered.contains("Int") && rendered.contains("String"),
        "the rejection should name the variable and both types: {rendered}",
    );

    let still_serving = exchange(&mut ctx, move || vec![http_post(port, "/sign", "bob")]);
    assert_eq!(still_serving, vec!["alice\nbob\n"], "state intact");
}

/// A version that stops declaring a variable the running program is holding a
/// value for is rejected, and the running program keeps serving.
///
/// This is the whole endpoint/state guard: dropping a value is the one outcome
/// an author cannot see having happened, since the program carries on answering
/// and only the accumulated history is gone.
#[test]
fn an_update_may_not_drop_state() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    let before = exchange(&mut ctx, move || vec![http_post(port, "/sign", "alice")]);
    assert_eq!(before, vec!["alice\n"]);

    let errors = live
        .update(&mut ctx, &source("guestbook-drops-state", port), &no_main)
        .err()
        .expect("a version that stops declaring `entries` would discard its value");
    let rendered = format!("{errors:?}");
    assert!(
        rendered.contains("cannot take over state") && rendered.contains("`entries`"),
        "the rejection should name the variable: {rendered}",
    );

    let still_serving = exchange(&mut ctx, move || vec![http_post(port, "/sign", "bob")]);
    assert_eq!(still_serving, vec!["alice\nbob\n"], "state intact");
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
