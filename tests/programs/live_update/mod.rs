//! Replacing a running program with a new version of its source, against a
//! program that is actually running.
//!
//! # The programs
//!
//! The gallery entry is one program and the version that replaces it:
//! `program.cambra` is a guestbook where `POST /sign` accumulates into a mutable
//! variable and `GET /peek` holds no state, and `updated.cambra` is the same
//! program with the accumulating loop edited. That pair is what a reader should
//! look at to see what an update *is*.
//!
//! Everything else the cases drive is scaffolding, and lives inline in
//! [`fixtures`]: variants that differ from a base by the single edit their case is
//! about, plus the shapes with no single base — a program on two ports, and the
//! `stdin`-sourced ones. The bases they vary:
//!
//! | Base | Shape |
//! | --- | --- |
//! | `guestbook` | The gallery program. Both its loops fall in one causal group, so one `Transact` store carries them. |
//! | `two-loops` | `POST /a` and `POST /b` each accumulate into their own variable. Independent, so a store each — one stays adoptable while the other is rebuilt. |
//! | `two-accumulators` | One loop carrying two variables (`left` and `right`), for the cases about telling them apart. |
//! | `one-stateful-loop` | `POST /p` accumulates, `POST /q` does not — the pair a variable can move between. |
//! | `latest-write` | A transactional variable (`Mut(String, Txn)`) that `POST /set` overwrites and `GET /get` reads. |
//! | `running-log` | A transactional variable that `POST /set` *appends* to, so every commit leaves a mark a replay would show. |
//! | `two-transactions` | Two transactional variables written and read from disjoint endpoint pairs, so they fall in different causal groups and each gets its own commit store. |
//!
//! The `stdin` cases drive the binary as a subprocess
//! ([`launch_under_control`]), because a `main` output belongs to the binary's own
//! loop rather than to a sink a test can pump. Those are also the only cases that
//! reach the control port over HTTP; every other case calls `LiveProgram`
//! directly.
//!
//! # What an update may do
//!
//! | Change | Expected |
//! | --- | --- |
//! | Logic outside a store's recurrence | Accepted; the store is adopted and its variables are untouched |
//! | Logic inside one | Accepted; the store is rebuilt and each variable resumes from the value it held, so what was recorded stands and the new rule governs from here |
//! | An edit to one of two independent loops | Accepted; the other's store is adopted |
//! | A loop gains an accumulator | Accepted; the others resume, the new one starts at its init |
//! | A variable moves to another loop, or to or from a transaction | Accepted; it seeds with the value it held and decides its new loop's positions from `0` |
//! | A loop reads another source — a port change, say | Accepted; same as above, and the port it left is released |
//! | Two loops swap which source they read | Accepted; each keeps its value and continues where its new source has got to |
//! | A variable moves to a loop over a fixed collection | Accepted; nothing is carried, since that fold is recomputed |
//! | An endpoint is added | Accepted; the route serves as soon as the swap completes |
//! | An endpoint is removed | Accepted; the route is retired and the address answers 404, unless it was the port's last route, in which case the port is released |
//! | Repeats and reverts | Accepted; each takes effect |
//!
//! # What it may not
//!
//! | Change | Expected |
//! | --- | --- |
//! | A variable is no longer declared | Refused, naming it |
//! | A variable's type changes | Refused, naming both types |
//! | The source does not compile | Refused |
//!
//! In every refusal the running program keeps serving. Diffing is covered
//! separately and must leave it untouched whichever phase it compares at, and
//! whatever the version it is compared against would have changed.
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
    ccl::context::{Phase, ReuseTally},
    interpreter::Consumer,
    live_program::UpdateReport,
};

use super::common::{
    drive_until, http_get, http_post, raw_http, raw_http_response, reserve_test_port, start_sink,
};

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
    use std::io::Write;

    let mut launched = launch_under_control(program);
    let control = launched.control;
    let v2 = launched.program.dir.join("v2.cambra");
    std::fs::write(&v2, updated).expect("write v2");
    let mut input = launched.input.take().expect("piped stdin");
    let collected = launched.collected.clone();
    let reader = launched.reader.take().expect("reader thread");

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

    launched.program.wait_for_exit(Duration::from_secs(10));
    reader.join().expect("reader thread");
    let text = collected.lock().unwrap().clone();
    (reply, text)
}

/// A program running under `--control`, with its control port already answering.
///
/// Split out of [`stdin_across_update`] because a test that only asks the control
/// port a question needs the launch and none of the feeding.
struct Launched {
    program: RunningProgram,
    control: u16,
    /// The program's `stdin`, for a test that feeds it. `None` once taken.
    input: Option<std::process::ChildStdin>,
    /// Every line the program has written, accumulated by [`reader`](Self::reader).
    collected: std::sync::Arc<std::sync::Mutex<String>>,
    reader: Option<thread::JoinHandle<()>>,
}

/// Spawn `program` under `--control` on a reserved port and wait for that port to
/// answer.
///
/// The wait is not optional: the program binds its control port during
/// compilation, so a request sent before then is refused rather than served.
fn launch_under_control(program: &str) -> Launched {
    use std::io::{BufRead, BufReader};
    use std::process::{Command, Stdio};

    let control = reserve_test_port();
    let dir = std::env::temp_dir().join(format!("cambra-live-{control}"));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let v1 = dir.join("v1.cambra");
    std::fs::write(&v1, program).expect("write v1");

    let mut program = RunningProgram {
        child: Command::new(env!("CARGO_BIN_EXE_cambra"))
            .arg(format!("--control={control}"))
            .arg(&v1)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn cambra"),
        dir,
    };

    let input = program.child.stdin.take().expect("piped stdin");
    let out = program.child.stdout.take().expect("piped stdout");
    let collected = std::sync::Arc::new(std::sync::Mutex::new(String::new()));
    let sink = collected.clone();
    let reader = thread::spawn(move || {
        for line in BufReader::new(out).lines().map_while(Result::ok) {
            sink.lock().unwrap().push_str(&line);
            sink.lock().unwrap().push('\n');
        }
    });

    let deadline = Instant::now() + Duration::from_secs(10);
    while std::net::TcpStream::connect(("127.0.0.1", control)).is_err() {
        assert!(Instant::now() < deadline, "control port never opened");
        thread::sleep(Duration::from_millis(50));
    }

    Launched {
        program,
        control,
        input: Some(input),
        collected,
        reader: Some(reader),
    }
}

/// A spawned program and its scratch directory, both cleaned up on drop.
///
/// Every assertion between the spawn and the last read can fail, and a program
/// left running holds the control port it bound. A port reservation's lock dies
/// with the process that took it, so the next run's allocator hands that port
/// out again and the bind fails.
struct RunningProgram {
    child: std::process::Child,
    dir: std::path::PathBuf,
}

impl RunningProgram {
    /// Give the program `within` to exit on its own once its input has closed.
    ///
    /// Polled rather than waited on: a program that never exits fails the test
    /// here instead of hanging the run.
    fn wait_for_exit(&mut self, within: Duration) {
        let deadline = Instant::now() + within;
        while Instant::now() < deadline {
            if self.child.try_wait().expect("wait on cambra").is_some() {
                return;
            }
            thread::sleep(Duration::from_millis(20));
        }
        panic!("the program did not exit when its input closed");
    }
}

impl Drop for RunningProgram {
    fn drop(&mut self) {
        // Both calls fail for a program that already exited, which is the
        // ordinary path; reaping it is what has to happen either way.
        let _ = self.child.kill();
        let _ = self.child.wait();
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

/// Wait for `port` to stop accepting connections.
///
/// Releasing a port is not synchronous with the update that stopped serving it:
/// dropping the last handle unblocks the dispatcher thread, and the socket closes
/// when that thread notices. The contract is that the port *is* released, not that
/// it is released before `update` returns.
fn assert_port_released(port: u16) {
    let deadline = Instant::now() + Duration::from_secs(5);
    while std::net::TcpStream::connect(("127.0.0.1", port)).is_ok() {
        assert!(
            Instant::now() < deadline,
            "port {port} is still accepting connections after its last route went",
        );
        thread::sleep(Duration::from_millis(20));
    }
}

/// The main-output consumer a sink-only program never uses.
fn no_main() -> Box<dyn Consumer> {
    Box::new(|| {})
}

/// The programs the cases below drive, other than the two the gallery keeps as
/// files.
///
/// Inline because they are scaffolding rather than demonstrations: each is one
/// base program's variant differing by the single edit its case is about, and a
/// gallery directory holds a program, not a fixture set. `{PORT}` is substituted
/// by [`source`].
mod fixtures {
    use indoc::indoc;

    pub const BUMP_OVER_SOURCE: &str = indoc! {r#"
        n := ""
        reqs, resps = http_serve("{PORT}", "POST", "/bump")
        for r in reqs:
            n := n + "a"
            resps << n + "\n"
    "#};

    pub const BUMP_OVER_A_FIXED_LIST: &str = indoc! {r#"
        n := ""
        reqs, resps = http_serve("{PORT}", "POST", "/bump")
        for x in ["y", "z"]:
            n := n + x
        for r in reqs:
            resps << n + "\n"
    "#};

    pub const GUESTBOOK_ADDS_ROUTE: &str = indoc! {r#"
        entries := ""

        sign_reqs, sign_resps = http_serve("{PORT}", "POST", "/sign")
        peek_reqs, peek_resps = http_serve("{PORT}", "GET", "/peek")
        added_reqs, added_resps = http_serve("{PORT}", "GET", "/added")

        for entry in sign_reqs:
            entries := entries + entry + "\n"
            sign_resps << entries

        for req in peek_reqs:
            peek_resps << "peek\n"

        for req in added_reqs:
            added_resps << "added\n"
    "#};

    pub const GUESTBOOK_DROPS_ROUTE: &str = indoc! {r#"
        entries := ""

        sign_reqs, sign_resps = http_serve("{PORT}", "POST", "/sign")

        for entry in sign_reqs:
            entries := entries + entry + "\n"
            sign_resps << entries
    "#};

    pub const GUESTBOOK_DROPS_STATE: &str = indoc! {r#"
        sign_reqs, sign_resps = http_serve("{PORT}", "POST", "/sign")
        peek_reqs, peek_resps = http_serve("{PORT}", "GET", "/peek")

        for entry in sign_reqs:
            sign_resps << entry + "\n"

        for req in peek_reqs:
            peek_resps << "peek\n"
    "#};

    pub const GUESTBOOK_RETYPES_STATE: &str = indoc! {r#"
        entries := 0

        sign_reqs, sign_resps = http_serve("{PORT}", "POST", "/sign")
        peek_reqs, peek_resps = http_serve("{PORT}", "GET", "/peek")

        for entry in sign_reqs:
            entries := entries + 1
            sign_resps << "signed\n"

        for req in peek_reqs:
            peek_resps << "peek\n"
    "#};

    pub const GUESTBOOK_STATELESS_EDIT: &str = indoc! {r#"
        entries := ""

        sign_reqs, sign_resps = http_serve("{PORT}", "POST", "/sign")
        peek_reqs, peek_resps = http_serve("{PORT}", "GET", "/peek")

        for entry in sign_reqs:
            entries := entries + entry + "\n"
            sign_resps << entries

        for req in peek_reqs:
            peek_resps << "peek edited\n"
    "#};

    pub const LATEST_WRITE: &str = indoc! {r#"
        set_reqs, set_resps = http_serve("{PORT}", "POST", "/set")
        get_reqs, get_resps = http_serve("{PORT}", "GET", "/get")

        latest: Mut(String, Txn) := "(none)"

        for msg in set_reqs:
            with begin():
                latest := msg
            set_resps << "ok\n"

        for req in get_reqs:
            with begin():
                get_resps << latest
    "#};

    pub const LATEST_WRITE_WRITER_EDIT: &str = indoc! {r#"
        set_reqs, set_resps = http_serve("{PORT}", "POST", "/set")
        get_reqs, get_resps = http_serve("{PORT}", "GET", "/get")

        latest: Mut(String, Txn) := "(none)"

        for msg in set_reqs:
            with begin():
                latest := msg + "!"
            set_resps << "ok\n"

        for req in get_reqs:
            with begin():
                get_resps << latest
    "#};

    pub const ONE_STATEFUL_LOOP: &str = indoc! {r#"
        n := ""
        p, pr = http_serve("{PORT}", "POST", "/p")
        q, qr = http_serve("{PORT}", "POST", "/q")
        for x in p:
            n := n + "a"
            pr << n + "\n"
        for y in q:
            qr << "q\n"
    "#};

    pub const ONE_STATEFUL_LOOP_BOTH: &str = indoc! {r#"
        n := ""
        m := ""
        p, pr = http_serve("{PORT}", "POST", "/p")
        q, qr = http_serve("{PORT}", "POST", "/q")
        for x in p:
            n := n + "a"
            pr << n + "\n"
        for y in q:
            m := m + "b"
            qr << m + "\n"
    "#};

    pub const ONE_STATEFUL_LOOP_MOVED: &str = indoc! {r#"
        n := ""
        p, pr = http_serve("{PORT}", "POST", "/p")
        q, qr = http_serve("{PORT}", "POST", "/q")
        for x in p:
            pr << "p\n"
        for y in q:
            n := n + "a"
            qr << n + "\n"
    "#};

    pub const RUNNING_LOG: &str = indoc! {r#"
        set_reqs, set_resps = http_serve("{PORT}", "POST", "/set")
        get_reqs, get_resps = http_serve("{PORT}", "GET", "/get")

        log: Mut(String, Txn) := ""

        for msg in set_reqs:
            with begin():
                log := log + msg
            set_resps << "ok\n"

        for req in get_reqs:
            with begin():
                get_resps << log
    "#};

    pub const RUNNING_LOG_WRITER_EDIT: &str = indoc! {r#"
        set_reqs, set_resps = http_serve("{PORT}", "POST", "/set")
        get_reqs, get_resps = http_serve("{PORT}", "GET", "/get")

        log: Mut(String, Txn) := ""

        for msg in set_reqs:
            with begin():
                log := log + "-" + msg
            set_resps << "ok\n"

        for req in get_reqs:
            with begin():
                get_resps << log
    "#};

    pub const TWO_ACCUMULATORS: &str = indoc! {r#"
        left := ""
        right := ""

        reqs, resps = http_serve("{PORT}", "POST", "/bump")

        for x in reqs:
            left := left + "a"
            right := right + "B"
            resps << left + "|" + right + "\n"
    "#};

    pub const TWO_ACCUMULATORS_ADDED: &str = indoc! {r#"
        left := ""
        right := ""
        extra := ""

        reqs, resps = http_serve("{PORT}", "POST", "/bump")

        for x in reqs:
            left := left + "a"
            right := right + "B"
            extra := extra + "c"
            resps << left + "|" + right + "|" + extra + "\n"
    "#};

    pub const TWO_ACCUMULATORS_REORDERED: &str = indoc! {r#"
        right := ""
        left := ""

        reqs, resps = http_serve("{PORT}", "POST", "/bump")

        for x in reqs:
            right := right + "B"
            left := left + "a"
            resps << left + "|" + right + "\n"
    "#};

    pub const TWO_LOOPS_SWAPPED: &str = indoc! {r#"
        a := ""
        b := ""

        a_reqs, a_resps = http_serve("{PORT}", "POST", "/a")
        b_reqs, b_resps = http_serve("{PORT}", "POST", "/b")

        for y in b_reqs:
            a := a + y + "\n"
            b_resps << a

        for x in a_reqs:
            b := b + x + "\n"
            a_resps << b
    "#};

    pub const TWO_LOOPS: &str = indoc! {r#"
        a := ""
        b := ""

        a_reqs, a_resps = http_serve("{PORT}", "POST", "/a")
        b_reqs, b_resps = http_serve("{PORT}", "POST", "/b")

        for x in a_reqs:
            a := a + x + "\n"
            a_resps << a

        for y in b_reqs:
            b := b + y + "\n"
            b_resps << b
    "#};

    pub const TWO_LOOPS_ONE_EDITED: &str = indoc! {r#"
        a := ""
        b := ""

        a_reqs, a_resps = http_serve("{PORT}", "POST", "/a")
        b_reqs, b_resps = http_serve("{PORT}", "POST", "/b")

        for x in a_reqs:
            a := a + x + "\n"
            a_resps << a

        for y in b_reqs:
            b := b + "* " + y + "\n"
            b_resps << b
    "#};

    pub const TWO_TRANSACTIONS: &str = indoc! {r#"
        set_a, ok_a = http_serve("{PORT}", "POST", "/a")
        set_b, ok_b = http_serve("{PORT}", "POST", "/b")
        get_a, out_a = http_serve("{PORT}", "GET", "/ga")
        get_b, out_b = http_serve("{PORT}", "GET", "/gb")

        x: Mut(String, Txn) := ""
        y: Mut(String, Txn) := ""

        for m in set_a:
            with begin():
                x := x + m
            ok_a << "ok\n"

        for r in get_a:
            with begin():
                out_a << x

        for m in set_b:
            with begin():
                y := y + m
            ok_b << "ok\n"

        for r in get_b:
            with begin():
                out_b << y
    "#};

    pub const TWO_TRANSACTIONS_ONE_WRITER_EDITED: &str = indoc! {r#"
        set_a, ok_a = http_serve("{PORT}", "POST", "/a")
        set_b, ok_b = http_serve("{PORT}", "POST", "/b")
        get_a, out_a = http_serve("{PORT}", "GET", "/ga")
        get_b, out_b = http_serve("{PORT}", "GET", "/gb")

        x: Mut(String, Txn) := ""
        y: Mut(String, Txn) := ""

        for m in set_a:
            with begin():
                x := x + "-" + m
            ok_a << "ok\n"

        for r in get_a:
            with begin():
                out_a << x

        for m in set_b:
            with begin():
                y := y + m
            ok_b << "ok\n"

        for r in get_b:
            with begin():
                out_b << y
    "#};
}

fn source(name: &str, port: u16) -> String {
    let text = match name {
        "guestbook" => include_str!("program.cambra"),
        "bump-over-source" => fixtures::BUMP_OVER_SOURCE,
        "bump-over-a-fixed-list" => fixtures::BUMP_OVER_A_FIXED_LIST,
        "guestbook-adds-route" => fixtures::GUESTBOOK_ADDS_ROUTE,
        "guestbook-drops-route" => fixtures::GUESTBOOK_DROPS_ROUTE,
        "guestbook-drops-state" => fixtures::GUESTBOOK_DROPS_STATE,
        "guestbook-retypes-state" => fixtures::GUESTBOOK_RETYPES_STATE,
        "guestbook-stateful-edit" => include_str!("updated.cambra"),
        "guestbook-stateless-edit" => fixtures::GUESTBOOK_STATELESS_EDIT,
        "latest-write" => fixtures::LATEST_WRITE,
        "latest-write-writer-edit" => fixtures::LATEST_WRITE_WRITER_EDIT,
        "one-stateful-loop" => fixtures::ONE_STATEFUL_LOOP,
        "one-stateful-loop-both" => fixtures::ONE_STATEFUL_LOOP_BOTH,
        "one-stateful-loop-moved" => fixtures::ONE_STATEFUL_LOOP_MOVED,
        "running-log" => fixtures::RUNNING_LOG,
        "running-log-writer-edit" => fixtures::RUNNING_LOG_WRITER_EDIT,
        "two-accumulators" => fixtures::TWO_ACCUMULATORS,
        "two-accumulators-added" => fixtures::TWO_ACCUMULATORS_ADDED,
        "two-accumulators-reordered" => fixtures::TWO_ACCUMULATORS_REORDERED,
        "two-loops" => fixtures::TWO_LOOPS,
        "two-loops-swapped" => fixtures::TWO_LOOPS_SWAPPED,
        "two-loops-one-edited" => fixtures::TWO_LOOPS_ONE_EDITED,
        "two-transactions" => fixtures::TWO_TRANSACTIONS,
        "two-transactions-one-writer-edited" => fixtures::TWO_TRANSACTIONS_ONE_WRITER_EDITED,
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

/// A variable that moves to another loop takes its value and starts counting
/// again.
///
/// The value is the variable's; the position belongs to the collection it was
/// counted in. `n` accumulated over `/p` and now accumulates over `/q`, so it
/// seeds with what it held and decides `/q`'s positions from `0` — none of which
/// its predecessor ever read, so none is decided twice and none is skipped.
#[test]
fn a_variable_that_moves_to_another_loop_takes_its_value_and_restarts() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("one-stateful-loop", port));

    let before = exchange(&mut ctx, move || {
        vec![http_post(port, "/p", "x"), http_post(port, "/p", "x")]
    });
    assert_eq!(before, vec!["a\n", "aa\n"]);

    live.update(&mut ctx, &source("one-stateful-loop-moved", port), &no_main)
        .expect("`n` is still declared, at the same type");

    let after = exchange(&mut ctx, move || {
        vec![http_post(port, "/q", "x"), http_post(port, "/p", "x")]
    });
    assert_eq!(
        after,
        vec!["aaa\n", "p\n"],
        "`n` carried its `aa` into the loop it moved to",
    );
}

/// A program that moves to another port keeps what it has accumulated.
///
/// The whole reason a value and its position are carried separately: the new
/// source shares nothing with the old one — different route, different buffer,
/// positions from `0` — so the position cannot follow. The value can, and an
/// author moving a service to another port means to keep the guestbook.
#[test]
fn moving_a_program_to_another_port_keeps_its_state() {
    let old_port = reserve_test_port();
    let new_port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", old_port));

    let before = exchange(&mut ctx, move || {
        vec![
            http_post(old_port, "/sign", "alice"),
            http_post(old_port, "/sign", "bob"),
        ]
    });
    assert_eq!(before, vec!["alice\n", "alice\nbob\n"]);

    live.update(&mut ctx, &source("guestbook", new_port), &no_main)
        .expect("`entries` is still declared, at the same type");

    let after = exchange(&mut ctx, move || {
        vec![http_post(new_port, "/sign", "carol")]
    });
    assert_eq!(
        after,
        vec!["alice\nbob\ncarol\n"],
        "the guestbook moved with the program",
    );

    // The old port served nothing after the swap, so it was released with its
    // last route.
    assert_port_released(old_port);
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

/// The control port answers `/diff` itself, at the phase the request names, and
/// rejects a phase it does not offer.
///
/// Every other case here calls `LiveProgram::diff_against` directly, so this is
/// what covers the wire: both ways of carrying the source, the leading `phase=`,
/// and the main loop servicing a `Diff` between ticks.
#[test]
fn the_control_port_answers_a_diff_request() {
    const V1: &str = "[\"> \" + line for line in stdin()]\n";
    const V2: &str = "[\">> \" + line for line in stdin()]\n";

    let launched = launch_under_control(V1);
    let control = launched.control;

    // The source is the body here, which is how a client sends a file. A space in
    // a request line would end the target, so the query form has to be encoded.
    let post = |query: &str, body: &str| {
        raw_http(
            control,
            &format!(
                "POST /diff{query} HTTP/1.1\r\nHost: 127.0.0.1:{control}\r\n\
                 Content-Length: {}\r\nConnection: close\r\n\r\n{body}",
                body.len()
            ),
        )
    };

    let same = post("", V1);
    assert!(
        same.contains("no difference"),
        "the running source does not differ from itself: {same}"
    );

    let edited = post("?phase=inferred&", V2);
    assert!(
        edited.contains("divergence"),
        "an edit is a divergence at the phase asked for: {edited}"
    );

    let bad = raw_http_response(
        control,
        &format!(
            "POST /diff?phase=nonsense& HTTP/1.1\r\nHost: 127.0.0.1:{control}\r\n\
             Content-Length: {}\r\nConnection: close\r\n\r\n{V1}",
            V1.len()
        ),
    );
    assert!(
        bad.starts_with("HTTP/1.1 400"),
        "an unoffered phase is a rejection, not a default: {bad}"
    );
    assert!(
        bad.contains("channelized"),
        "and the reply names the offered set: {bad}"
    );

    // The query form, which is what `percent_decode` and `split_phase_param` are
    // for. `+` is a space and every other non-alphanumeric byte is escaped, so the
    // program survives a request line.
    let encoded: String = V1
        .trim_end()
        .bytes()
        .map(|b| match b {
            b' ' => "+".to_string(),
            b if b.is_ascii_alphanumeric() => (b as char).to_string(),
            b => format!("%{b:02X}"),
        })
        .collect();
    let query_form = raw_http(
        control,
        &format!(
            "GET /diff?{encoded} HTTP/1.1\r\nHost: 127.0.0.1:{control}\r\n\
             Connection: close\r\n\r\n"
        ),
    );
    assert!(
        query_form.contains("no difference"),
        "the same source through the query string reads the same: {query_form}"
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
/// Nothing about the guard is HTTP-specific: it reads the variables a version
/// declares off its planned tree, and `stdin` declares them the same way.
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
        reply.contains("`n` is now Int"),
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
        .diff_against(&ctx, &source("guestbook", port), Phase::AsOfRead)
        .expect("the running source compiles against its own endpoints");
    assert!(
        identical.contains("no difference"),
        "a program should not differ from itself: {identical}",
    );

    let changed = live
        .diff_against(
            &ctx,
            &source("guestbook-stateless-edit", port),
            Phase::AsOfRead,
        )
        .expect("the new version compiles against the running endpoints");
    assert!(
        changed.contains("divergence"),
        "an edited program should report a divergence: {changed}",
    );

    let still_serving = exchange(&mut ctx, move || vec![http_get(port, "/peek")]);
    assert_eq!(still_serving, vec!["peek\n"]);
}

/// Two calls to one function, each carrying its own loop and its own accumulator,
/// keep their state apart across an update.
///
/// Inlining clones the function body per call site, so both accumulators are the
/// same source declaration — same spelling, same lexical position, no name of
/// their own to tell them apart. Nor can anything they compute: once `step` is
/// substituted the two stores differ *only* in their writer bodies, which is
/// exactly what the edit changes. Their identities are the spelling plus an index
/// among the variables of that spelling, which is why the edit carries and the
/// two do not cross.
#[test]
fn two_instantiations_of_one_function_keep_their_accumulators_apart() {
    let v1 = concat!(
        "def count_by(src, step) => Int:\n",
        "    total := 0\n",
        "    for x in src:\n",
        "        total := total + step\n",
        "    total\n",
        "\n",
        "lines = stdin()\n",
        "a = count_by(lines, 1)\n",
        "b = count_by(lines, 10)\n",
        "a * 1000 + b\n",
    );
    let v2 = v1.replace("total + step", "total + step * 2");
    let (reply, out) = stdin_across_update(v1, &v2, "m\nn", "o\np");
    assert!(
        reply.contains("updated"),
        "the update should be accepted: {reply}"
    );
    let flat: String = out.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(
        flat.contains("Ints([6060,],)"),
        "want a = 2 + 2*2 and b = 20 + 2*20; seeding either from the other reads 6042: {out}"
    );
}

/// Two causally independent transaction groups keep their state apart across an
/// update that rebuilds one of them.
///
/// A program has one commit store per causal group, not one commit store, so `x`
/// and `y` here live in different stores sequenced by the same `Txn` domain.
/// Their frontiers differ — `x` has taken four commits and `y` one — and the
/// store rebuilt for `x` has to resume at its own, which is why the resume
/// position hangs off each variable rather than off the recurrence.
#[test]
fn two_transaction_groups_resume_at_their_own_positions() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("two-transactions", port));

    let before = exchange(&mut ctx, move || {
        vec![
            http_post(port, "/a", "1"),
            http_post(port, "/a", "2"),
            http_post(port, "/a", "3"),
            http_post(port, "/a", "4"),
            http_post(port, "/b", "9"),
            http_get(port, "/ga"),
            http_get(port, "/gb"),
        ]
    });
    assert_eq!(
        before,
        vec!["ok\n", "ok\n", "ok\n", "ok\n", "ok\n", "1234", "9"],
    );

    live.update(
        &mut ctx,
        &source("two-transactions-one-writer-edited", port),
        &no_main,
    )
    .expect("editing one group's writer declares the same variables at the same types");

    let after = exchange(&mut ctx, move || {
        vec![
            http_get(port, "/ga"),
            http_get(port, "/gb"),
            http_post(port, "/a", "5"),
            http_post(port, "/b", "8"),
            http_get(port, "/ga"),
            http_get(port, "/gb"),
        ]
    });
    assert_eq!(
        after,
        vec!["1234", "9", "ok\n", "ok\n", "1234-5", "98"],
        "each group stands where it stood, and the new rule governs `x` from here",
    );
}

/// A request the retired version received but never answered is answered by the
/// replacement, once.
///
/// The end-to-end half of the release carry: a source hands a newly registered
/// producer everything it still holds, and `retire_version` records what the
/// retired producers had released so the replacement's do not start from the
/// oldest retained element. `UIntStreamBuffer`'s unit tests pin the buffer's side
/// of that; this pins the promise a client sees, which is that arriving before
/// the swap is not a way to be dropped.
///
/// The request is sent and left unanswered — nothing pumps the scheduler until
/// after the update — so the version that received it is gone before it could
/// have replied.
#[test]
fn a_request_that_arrived_before_the_swap_is_answered_after_it() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    let (tx, rx) = mpsc::channel::<Vec<String>>();
    thread::spawn(move || tx.send(vec![http_post(port, "/sign", "alice")]).unwrap());
    // Long enough for the dispatcher thread to have taken the request off the
    // socket. Nothing has pumped, so no operator has seen it and no reply exists.
    thread::sleep(Duration::from_millis(300));

    live.update(
        &mut ctx,
        &source("guestbook-stateless-edit", port),
        &no_main,
    )
    .expect("editing `/peek` leaves `/sign` alone");

    let answered = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(
        answered,
        vec!["alice\n"],
        "the replacement answers the request its predecessor received",
    );

    let next = exchange(&mut ctx, move || vec![http_post(port, "/sign", "bob")]);
    assert_eq!(
        next,
        vec!["alice\nbob\n"],
        "and counted it once: a replay would read `alice` twice",
    );
}

/// Diffing against a version that stops serving a route leaves the route serving.
///
/// A diff answers a question; only an update changes what the program serves. The
/// two compile against the same registry, so the compile that answers the
/// question must not act on the difference it finds — the route it would retire
/// belongs to the running program, and its listener is shared.
#[test]
fn diffing_against_a_version_that_drops_a_route_does_not_retire_it() {
    let port = reserve_test_port();
    let (mut ctx, live) = start_sink(&source("guestbook", port));

    let changed = live
        .diff_against(
            &ctx,
            &source("guestbook-drops-route", port),
            Phase::AsOfRead,
        )
        .expect("the new version compiles against the running endpoints");
    assert!(
        changed.contains("divergence"),
        "dropping a route is a difference: {changed}",
    );

    let still_serving = exchange(&mut ctx, move || vec![http_get(port, "/peek")]);
    assert_eq!(
        still_serving,
        vec!["peek\n"],
        "`/peek` is still the running program's route; only an update retires it",
    );
}

/// A port whose last route goes is released; one that keeps a route keeps serving.
///
/// A listener outlives the version that opened it, but not the program's interest
/// in the address. While a sibling route survives on the port, a retired route's
/// address answers 404 — there is still a server there. Once nothing is
/// registered, the port itself goes, so a program that moves its endpoints around
/// over a long life does not hold every port it ever served.
#[test]
fn a_port_whose_last_route_goes_is_released() {
    let kept = reserve_test_port();
    let dropped = reserve_test_port();
    let two_ports = format!(
        "a_reqs, a_resps = http_serve(\"{kept}\", \"GET\", \"/a\")\n\
         b_reqs, b_resps = http_serve(\"{dropped}\", \"GET\", \"/b\")\n\
         c_reqs, c_resps = http_serve(\"{kept}\", \"GET\", \"/c\")\n\
         for r in a_reqs:\n    a_resps << \"a\\n\"\n\
         for r in b_reqs:\n    b_resps << \"b\\n\"\n\
         for r in c_reqs:\n    c_resps << \"c\\n\"\n"
    );
    let one_port = format!(
        "a_reqs, a_resps = http_serve(\"{kept}\", \"GET\", \"/a\")\n\
         for r in a_reqs:\n    a_resps << \"a\\n\"\n"
    );

    let (mut ctx, mut live) = start_sink(&two_ports);
    assert_eq!(
        exchange(&mut ctx, move || vec![
            http_get(kept, "/a"),
            http_get(dropped, "/b")
        ]),
        vec!["a\n", "b\n"],
    );

    live.update(&mut ctx, &one_port, &no_main)
        .expect("dropping routes declares no state, so it is accepted");

    // `/c` shared the kept port, so its address is a 404 rather than a refusal:
    // the listener is still there for `/a`'s sake.
    let retired = exchange(&mut ctx, move || {
        vec![http_get(kept, "/a"), http_get(kept, "/c")]
    });
    assert_eq!(retired, vec!["a\n", "Not Found"]);

    // The other port lost its only route, so nothing is listening there.
    assert_port_released(dropped);
}

/// Every phase the control port offers is a working diff point, not only the
/// default. Driven off `OFFERED_PHASES` itself, so a phase added to the offered
/// set is covered here without anyone remembering to add it.
#[test]
fn every_offered_phase_is_a_diff_point() {
    let port = reserve_test_port();
    let (ctx, live) = start_sink(&source("guestbook", port));

    for (spelling, phase) in cambra::control_port::OFFERED_PHASES {
        let rendered = live
            .diff_against(&ctx, &source("guestbook-stateless-edit", port), *phase)
            .unwrap_or_else(|e| panic!("diff at {spelling} failed: {e:?}"));
        assert!(
            rendered.contains("divergence"),
            "the edit should be visible at {spelling}: {rendered}",
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

/// A transaction writer does not re-attempt the transactions it committed before
/// the swap.
///
/// The regression this pins: the drive named the item it was attempting by its
/// index among the source's *offered columns* and never released a finished one,
/// so the source went on offering every request and the replacement's drive
/// started again from the first. Six commits before the update were committed a
/// second time after it, under the new rule — visible here because each append
/// leaves a mark, and invisible to a last-write-wins variable however deep the
/// history.
#[test]
fn a_transaction_writer_does_not_replay_what_it_committed() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("running-log", port));

    let before = exchange(&mut ctx, move || {
        (1..=6)
            .map(|i| http_post(port, "/set", &i.to_string()))
            .collect()
    });
    assert_eq!(before.len(), 6);
    let logged = exchange(&mut ctx, move || vec![http_get(port, "/get")]);
    assert_eq!(logged, vec!["123456"]);

    live.update(&mut ctx, &source("running-log-writer-edit", port), &no_main)
        .expect("editing a transactional writer is a change between existing endpoints");

    let after = exchange(&mut ctx, move || {
        vec![http_post(port, "/set", "7"), http_get(port, "/get")]
    });
    // Six as they were committed, and the seventh under the new rule — not
    // `123456-1-2-3-4-5-6-7`.
    assert_eq!(after, vec!["ok\n", "123456-7"]);
}

/// Two loops swapping which source they read keep their values and pick up where
/// each source has got to.
///
/// Both variables change domain at once, so neither can resume at its
/// predecessor's frontier — and neither can start at `0` either, because both
/// sources have already delivered and released. Each starts where the source it
/// moved to will next offer a producer.
#[test]
fn two_loops_may_swap_which_source_they_read() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("two-loops", port));

    let before = exchange(&mut ctx, move || {
        vec![
            http_post(port, "/a", "1"),
            http_post(port, "/a", "2"),
            http_post(port, "/b", "9"),
        ]
    });
    assert_eq!(before, vec!["1\n", "1\n2\n", "9\n"]);

    live.update(&mut ctx, &source("two-loops-swapped", port), &no_main)
        .expect("both variables are still declared, at the same types");

    // `/a` now writes `b` and answers on `a_resps`; `/b` now writes `a`.
    let after = exchange(&mut ctx, move || {
        vec![http_post(port, "/a", "3"), http_post(port, "/b", "8")]
    });
    assert_eq!(
        after,
        vec!["9\n3\n", "1\n2\n8\n"],
        "each variable kept its value and continued on the source it moved to",
    );
}

/// A loop that gains an accumulator over a source the program was already reading
/// starts where that source has got to.
///
/// There is no predecessor to resume from — the variable is new — so this is the
/// case that has nothing carried at all and still cannot start at `0`. `/q` has
/// delivered and released a request, and a store based below that waits for an
/// element the source will not offer again.
#[test]
fn a_stateless_loop_may_gain_an_accumulator_over_an_advanced_source() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("one-stateful-loop", port));

    let before = exchange(&mut ctx, move || {
        vec![http_post(port, "/p", "x"), http_post(port, "/q", "x")]
    });
    assert_eq!(before, vec!["a\n", "q\n"]);

    live.update(&mut ctx, &source("one-stateful-loop-both", port), &no_main)
        .expect("`n` is unchanged and `m` is new");

    let after = exchange(&mut ctx, move || {
        vec![http_post(port, "/q", "x"), http_post(port, "/p", "x")]
    });
    assert_eq!(
        after,
        vec!["b\n", "aa\n"],
        "`m` starts empty at `/q`'s current position, and `n` carries",
    );
}

/// A variable that moves to a loop over a fixed collection is recomputed, not
/// seeded.
///
/// A fixed collection is part of the program rather than outside it, so the fold
/// over it is a pure function of what the new version declares. Carrying the value
/// in would count the elements the old version had already seen on top of the
/// ones this fold is about to. Accepted, and `n` reads as the new list alone
/// however many requests the old version answered.
#[test]
fn a_variable_that_moves_to_a_fixed_collection_is_recomputed() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("bump-over-source", port));

    let before = exchange(&mut ctx, move || {
        vec![http_post(port, "/bump", "x"), http_post(port, "/bump", "x")]
    });
    assert_eq!(before, vec!["a\n", "aa\n"]);

    live.update(&mut ctx, &source("bump-over-a-fixed-list", port), &no_main)
        .expect("`n` is still declared, at the same type");

    let after = exchange(&mut ctx, move || vec![http_post(port, "/bump", "x")]);
    assert_eq!(
        after,
        vec!["yz\n"],
        "the fold is the list's, not the list's on top of what the requests built",
    );
}
