//! Replacing a running program with a new version of its source, against a
//! program that is actually running.
//!
//! # The programs
//!
//! The gallery entry is one program and the version that replaces it:
//! `program.cambra` is a guestbook where `POST /sign` accumulates into a mutable
//! variable and `GET /peek` holds no state, and `reloaded.cambra` is the same
//! program with the accumulating loop edited. That pair is what a reader should
//! look at to see what a reload does.
//!
//! Everything else the cases drive is scaffolding. [`fixtures`] holds every
//! program the `{PORT}` substitution reaches — a base per shape, plus the
//! variants that differ from one by the single edit their case is about. A
//! program a case cannot express that way stays in the case: the `stdin`-sourced
//! ones, the two-port one in
//! `a_port_whose_last_route_goes_is_released`, and `nested_fold`, which is a
//! function because its two cases vary the step rather than the shape. The bases:
//!
//! | Base | Shape |
//! | --- | --- |
//! | `guestbook` | The gallery program. One stateful loop, so one `Transact` store with one key; `/peek`'s loop holds nothing. |
//! | `bump-over-source` | The smallest one: `POST /bump` accumulates into `n`. Varied by its declared init, for the rule that a carried value wins over one. |
//! | `record-accumulator` | A record-valued accumulator, varied by the type of one field — a retype no single program can express. |
//! | `bump-over-a-fixed-list` | A fold over `["y", "z"]` read by `POST /bump`. Varied by the body and by the collection, which are the two edits a fold tells apart. |
//! | `two-loops` | `POST /a` and `POST /b` each accumulate into their own variable. Independent, so a store each — one stays keepable while the other is rebuilt. |
//! | `two-accumulators` | One loop carrying two variables (`left` and `right`), for the cases about telling them apart. |
//! | `one-stateful-loop` | `POST /p` accumulates, `POST /q` does not — the pair a variable can move between. |
//! | `latest-write` | A transactional variable (`Mut(String, Txn)`) that `POST /set` overwrites and `GET /get` reads. |
//! | `running-log` | A transactional variable that `POST /set` appends to, so every commit leaves a mark a replay would show. |
//! | `one-transactional-loop` | `POST /a` commits into a transactional variable, `POST /b` holds nothing — the pair a transactional writer can be added to. |
//! | `two-transactions` | Two transactional variables written and read from disjoint endpoint pairs, so they fall in different causal groups and each gets its own commit store. |
//!
//! The `stdin` cases drive the binary as a subprocess
//! ([`launch_under_control`]), because a `main` output fed by `stdin` belongs to
//! the binary's own loop rather than to a sink a test can pump. Those are also the
//! only cases that reach the control port over HTTP; every other case calls
//! `LiveProgram` directly.
//!
//! Some cases pull a program's value itself instead
//! (`drive_main_to_terminal`). A fold over a fixed collection needs no
//! source, so pulling it is what makes the position a reload lands on nameable:
//! one pull decides one position, where a socket lands wherever the notification
//! round it arrives in reaches.
//!
//! # What a reload may do
//!
//! | Change | Expected |
//! | --- | --- |
//! | Logic outside a store's recurrence | Accepted; the store is kept and its variables are untouched |
//! | Logic inside one | Accepted; the store is rebuilt and each variable resumes from the value it held, so what was recorded stands and the new rule governs from here |
//! | An edit to one of two independent loops | Accepted; the other's store is kept |
//! | A loop gains an accumulator under a new name | Accepted; the others resume, the new one starts at its init |
//! | A route serving statelessly gains a transactional writer | Accepted; the writer commits from the next request rather than replaying the ones the route already answered |
//! | A variable is added whose name another already has | Accepted; the bindings enclosing each declaration tell them apart, so the existing one resumes and the added one starts at its init |
//! | A variable moves to another loop | Accepted; it seeds with the value it held and decides the positions its new loop's iteration still has |
//! | A variable moves to or from a transaction | Accepted either direction; the value carries, and a fold caught partway resumes at the cut so no element is folded twice |
//! | The same, onto a different collection | Accepted; the value carries and the new collection is folded whole, since the sequence its positions were counted in is gone |
//! | A loop reads another source — a port change, say | Accepted; same as above, and the port it left is released |
//! | Two loops, or two transaction writers, swap which source they read | Accepted; each keeps its value and continues where its new source has got to |
//! | A variable moves to a loop over a fixed collection | Accepted; same as above — the value seeds and the collection folds on top of it |
//! | The body of a loop over a fixed collection is edited | Accepted; the fold resumes at the position it had reached, so the new rule governs the elements left |
//! | The same, with the fold caught partway | Accepted; every element is folded once, and the cut falls at the position the retired version had reached |
//! | The collection itself is edited | Accepted; the edited collection is a different computation, so its iteration is rebuilt and the collection folded whole |
//! | The same, over a collection a filter narrows | Accepted; the cut falls on a position the filter kept, which is a position of the collection it filters |
//! | An endpoint is added | Accepted; the route serves as soon as the swap completes |
//! | An endpoint is removed | Accepted; the route is retired and the address answers 404, unless it was the port's last route, in which case the port is released |
//! | An endpoint is removed with a request already in flight to it | Accepted; that request is answered 404 too, rather than waiting for a reply no version will compute |
//! | Repeats and reverts | Accepted; each takes effect |
//! | A reload after one that kept a stateful binding whole | Accepted; the variable under the kept binding is still carried and still guarded |
//!
//! # What it may not
//!
//! | Change | Expected |
//! | --- | --- |
//! | A variable is no longer declared | Refused, naming it |
//! | A variable's type changes | Refused, naming both types |
//! | Two anonymous call sites of one stateful function are reordered, or a third inserted ahead | Refused, naming both declarations and saying to bind each call site to a name |
//! | The source does not compile | Refused |
//!
//! In every refusal the running program keeps serving. Diffing is covered
//! separately and must leave it untouched whichever phase it compares at, and
//! whatever the version it is compared against would have changed.
//!
//! # Two properties worth stating
//!
//! How much a reload reuses does not depend on how many reloads came before it:
//! a binding is named by what it computes, not by whether the compilation before
//! this one happened to build it.
//!
//! A rebuilt store resumes rather than restarting, and resumes at the position
//! its source has reached rather than replaying it. Most cases here drive two or
//! three requests before reloading, which is not enough to exercise a resuming
//! store's indexing — `a_store_resumes_however_far_its_source_has_advanced`
//! drives six for that reason.
//!
//! Neither property weakens with the number of reloads. Every `{PORT}` fixture
//! here binds its store at the top of the binding chain, where each compilation
//! registers it again; the two cases over `nested_fold` put a store under another
//! binding instead, which is the placement where keeping that binding is what
//! has to hand the store on.

use std::{
    sync::mpsc,
    thread,
    time::{Duration, Instant},
};

use indoc::indoc;
use rstest_log::rstest;

use cambra::{
    ccl::context::{GlobalContext, Phase, ReuseTally},
    interpreter::{Consumer, Tile, Value},
    live_program::{LiveProgram, ReloadReport},
};

use super::common::{
    drive_until, http_get, http_post, raw_http, raw_http_response, reserve_test_port, start_sink,
};

/// Run a `stdin`-sourced program under `--control`, feeding it `before`, then
/// swapping it for `reloaded` and feeding it `after`.
///
/// Driven as a subprocess because a `main` output belongs to the binary's own
/// loop, not to a sink a test can pump. Such a program is not short-lived: its
/// source is unbounded, so it keeps running and is as reloadable as any other.
fn stdin_across_reload(
    program: &str,
    reloaded: &str,
    before: &str,
    after: &str,
) -> (String, String) {
    use std::io::Write;

    let mut launched = launch_under_control(program);
    let control = launched.control;
    let v2 = launched.program.dir.join("v2.cambra");
    std::fs::write(&v2, reloaded).expect("write v2");
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
            "POST /reload HTTP/1.1\r\nHost: 127.0.0.1:{control}\r\nContent-Length: {}\r\n\
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
/// Split out of [`stdin_across_reload`] because a test that only asks the control
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
/// Releasing a port is not synchronous with the reload that stopped serving it:
/// dropping the last handle unblocks the dispatcher thread, and the socket closes
/// when that thread notices. The contract is that the port *is* released, not that
/// it is released before `reload` returns.
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

    /// `BUMP_OVER_SOURCE` with a different declared init, and nothing else
    /// changed — for the rule that a carried value wins over the init, which is
    /// only ever read on a fresh start.
    pub const BUMP_OVER_SOURCE_RESEEDED: &str = indoc! {r#"
        n := "seed"
        reqs, resps = http_serve("{PORT}", "POST", "/bump")
        for r in reqs:
            n := n + "a"
            resps << n + "\n"
    "#};

    /// A record-valued accumulator, and the same program with one field at
    /// another type — for the "records included" half of the retype refusal.
    /// Neither program can be written with the field at two types, so the change
    /// only exists between versions.
    pub const RECORD_ACCUMULATOR: &str = indoc! {r#"
        n := (a=0, b=1)
        reqs, resps = http_serve("{PORT}", "POST", "/bump")
        for r in reqs:
            n := (a=n.a + 1, b=n.b)
            resps << "ok\n"
    "#};

    pub const RECORD_ACCUMULATOR_RETYPED_FIELD: &str = indoc! {r#"
        n := (a=0, b="x")
        reqs, resps = http_serve("{PORT}", "POST", "/bump")
        for r in reqs:
            n := (a=n.a + 1, b=n.b)
            resps << "ok\n"
    "#};

    pub const BUMP_OVER_A_FIXED_LIST: &str = indoc! {r#"
        n := ""
        reqs, resps = http_serve("{PORT}", "POST", "/bump")
        for x in ["y", "z"]:
            n := n + x
        for r in reqs:
            resps << n + "\n"
    "#};

    pub const BUMP_OVER_A_MARKED_LIST: &str = indoc! {r#"
        n := ""
        reqs, resps = http_serve("{PORT}", "POST", "/bump")
        for x in ["y", "z"]:
            n := n + x + "!"
        for r in reqs:
            resps << n + "\n"
    "#};

    pub const BUMP_OVER_ANOTHER_FIXED_LIST: &str = indoc! {r#"
        n := ""
        reqs, resps = http_serve("{PORT}", "POST", "/bump")
        for x in ["p", "q"]:
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

    pub const ONE_TRANSACTIONAL_LOOP: &str = indoc! {r#"
        set_a, ok_a = http_serve("{PORT}", "POST", "/a")
        set_b, ok_b = http_serve("{PORT}", "POST", "/b")
        get_a, out_a = http_serve("{PORT}", "GET", "/ga")

        x: Mut(String, Txn) := ""

        for m in set_a:
            with begin():
                x := x + m
            ok_a << "ok\n"

        for r in get_a:
            with begin():
                out_a << x

        for m in set_b:
            ok_b << "b\n"
    "#};

    pub const ONE_TRANSACTIONAL_LOOP_BOTH: &str = indoc! {r#"
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

    pub const TWO_TRANSACTIONS_SWAPPED: &str = indoc! {r#"
        set_a, ok_a = http_serve("{PORT}", "POST", "/a")
        set_b, ok_b = http_serve("{PORT}", "POST", "/b")
        get_a, out_a = http_serve("{PORT}", "GET", "/ga")
        get_b, out_b = http_serve("{PORT}", "GET", "/gb")

        x: Mut(String, Txn) := ""
        y: Mut(String, Txn) := ""

        for m in set_b:
            with begin():
                x := x + m
            ok_b << "ok\n"

        for r in get_a:
            with begin():
                out_a << x

        for m in set_a:
            with begin():
                y := y + m
            ok_a << "ok\n"

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
        "bump-over-source-reseeded" => fixtures::BUMP_OVER_SOURCE_RESEEDED,
        "record-accumulator" => fixtures::RECORD_ACCUMULATOR,
        "record-accumulator-retyped-field" => fixtures::RECORD_ACCUMULATOR_RETYPED_FIELD,
        "bump-over-a-fixed-list" => fixtures::BUMP_OVER_A_FIXED_LIST,
        "bump-over-a-marked-list" => fixtures::BUMP_OVER_A_MARKED_LIST,
        "bump-over-another-fixed-list" => fixtures::BUMP_OVER_ANOTHER_FIXED_LIST,
        "guestbook-adds-route" => fixtures::GUESTBOOK_ADDS_ROUTE,
        "guestbook-drops-route" => fixtures::GUESTBOOK_DROPS_ROUTE,
        "guestbook-drops-state" => fixtures::GUESTBOOK_DROPS_STATE,
        "guestbook-retypes-state" => fixtures::GUESTBOOK_RETYPES_STATE,
        "guestbook-stateful-edit" => include_str!("reloaded.cambra"),
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
        "one-transactional-loop" => fixtures::ONE_TRANSACTIONAL_LOOP,
        "one-transactional-loop-both" => fixtures::ONE_TRANSACTIONAL_LOOP_BOTH,
        "two-transactions" => fixtures::TWO_TRANSACTIONS,
        "two-transactions-one-writer-edited" => fixtures::TWO_TRANSACTIONS_ONE_WRITER_EDITED,
        "two-transactions-swapped" => fixtures::TWO_TRANSACTIONS_SWAPPED,
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

/// A reload replaces the edited logic and leaves the untouched logic running,
/// with everything that logic has accumulated.
///
/// The guestbook is signed twice, `/peek` is edited, and the third signature
/// still returns all three entries.
///
/// Only the signing loop is stateful, so the program has one store with one key,
/// and `/peek`'s loop reaches no store at all. Editing `/peek` leaves the store's
/// term untouched, so the store is kept and the entries survive by being the
/// same accumulation rather than by being re-derived.
/// `an_edit_to_the_accumulating_loop_takes_effect` is the case that rebuilds it.
#[test]
fn a_reload_keeps_the_state_of_logic_it_did_not_change() {
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

    let report: ReloadReport = live
        .reload(
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

    let ReuseTally { kept, bound } = report.reuse;
    assert!(
        kept > 0 && kept < bound,
        "an edit to one of two independent bindings should keep some and rebuild some, \
         got {kept}/{bound}",
    );
}

/// An edit to the accumulating loop itself takes effect.
///
/// The regression this pins: every mutable variable of a causal group lives in
/// one `Transact` store bound to `__hist`, and a read of one is a projection off
/// that binding. While the store was registered outside the conversion scope,
/// `__hist` was free in every such term and hashed by its bare spelling, so
/// `sign_resps` (`__hist.to_sign_resps_0`) hashed identically however the
/// recurrence was edited, and its operator was reused against a store that no
/// longer computed what it had. The edit was accepted, reported as a divergence,
/// and silently did nothing.
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

    live.reload(&mut ctx, &source("guestbook-stateful-edit", port), &no_main)
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
/// position found nothing and the drive stalled, silently: the reload was
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

    live.reload(&mut ctx, &source("guestbook-stateful-edit", port), &no_main)
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

    live.reload(
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

    live.reload(&mut ctx, &source("two-accumulators-added", port), &no_main)
        .expect("adding an accumulator loses nothing");

    let after = exchange(&mut ctx, move || vec![http_post(port, "/bump", "x")]);
    assert_eq!(
        after,
        // The two that were there carry; the added one starts empty.
        vec!["aaa|BBB|c\n"],
    );
}

/// A variable that moves to another loop takes its value and counts what that
/// loop still has.
///
/// The value is the variable's; the position is the iteration's. `n` accumulated
/// over `/p` and now accumulates over `/q`, so it seeds with what it held and
/// decides the positions `/q` has not delivered — none of which its predecessor
/// ever read, so none is decided twice and none is skipped.
#[test]
fn a_variable_that_moves_to_another_loop_takes_its_value_and_restarts() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("one-stateful-loop", port));

    let before = exchange(&mut ctx, move || {
        vec![http_post(port, "/p", "x"), http_post(port, "/p", "x")]
    });
    assert_eq!(before, vec!["a\n", "aa\n"]);

    live.reload(&mut ctx, &source("one-stateful-loop-moved", port), &no_main)
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
/// Why a position is never carried: the new source shares nothing with the old
/// one — different route, different buffer, its own positions — so the loop over
/// it is a different iteration and says for itself where to start. The value is
/// the variable's and follows it, which is what an author moving a service to
/// another port means by keeping the guestbook.
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

    live.reload(&mut ctx, &source("guestbook", new_port), &no_main)
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
/// kept when unchanged, but nothing seeded a rebuilt one, so editing a
/// transactional writer silently reset the variable to its declared init.
#[test]
fn a_transactional_variable_survives_an_edit_to_its_writer() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("latest-write", port));

    let before = exchange(&mut ctx, move || {
        vec![http_post(port, "/set", "bob"), http_get(port, "/get")]
    });
    assert_eq!(before, vec!["ok\n", "bob"]);

    live.reload(
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
/// kept, with its entries, and applies the new rule to the edited one.
#[test]
fn an_edit_to_one_accumulator_leaves_the_other_running() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("two-loops", port));

    let before = exchange(&mut ctx, move || {
        vec![http_post(port, "/a", "p"), http_post(port, "/b", "q")]
    });
    assert_eq!(before, vec!["p\n", "q\n"]);

    let report = live
        .reload(&mut ctx, &source("two-loops-one-edited", port), &no_main)
        .expect("editing one loop is a change between existing endpoints");
    // Reuse is not observable in the values below: a rebuilt store resumes
    // from the value it carried, so it answers what a kept one answers. The
    // tally is the only thing that tells the two apart, so the claim that one
    // store was kept rests on it.
    let ReuseTally { kept, bound } = report.reuse;
    assert!(
        kept > 0 && kept < bound,
        "one loop's subgraph is unchanged and the other's is edited, so a reload \
         keeps some and rebuilds some, got {kept}/{bound}",
    );

    let after = exchange(&mut ctx, move || {
        vec![http_post(port, "/a", "r"), http_post(port, "/b", "s")]
    });
    assert_eq!(
        after,
        vec![
            // Untouched: its store was kept, entries and all.
            "p\nr\n",
            // Edited: its store was rebuilt but resumed from `q`, so the entry it
            // already held stands as recorded and the new rule governs from here.
            // `q` keeping its original form also shows the two loops' state does
            // not collide, each being scoped by the source its loop reads.
            "q\n* s\n",
        ],
    );
}

/// How much a reload reuses does not depend on how many reloads came before it.
///
/// The regression this pins: while a binding's class was its identity hash when
/// kept and a fresh value when built, a first compilation handed out classes
/// that no later one reproduced, so every binding reading another was rebuilt on
/// the first reload and reuse only settled in on the second. A program is most
/// likely to be reloaded exactly once, which is the case that lost the most.
#[test]
fn reuse_does_not_depend_on_how_many_reloads_came_before() {
    let first = {
        let port = reserve_test_port();
        let (mut ctx, mut live) = start_sink(&source("two-loops", port));
        live.reload(&mut ctx, &source("two-loops-one-edited", port), &no_main)
            .expect("accepted")
            .reuse
    };
    let after_a_no_op = {
        let port = reserve_test_port();
        let (mut ctx, mut live) = start_sink(&source("two-loops", port));
        live.reload(&mut ctx, &source("two-loops", port), &no_main)
            .expect("accepted");
        live.reload(&mut ctx, &source("two-loops-one-edited", port), &no_main)
            .expect("accepted")
            .reuse
    };
    assert_eq!(
        first, after_a_no_op,
        "the same edit reused {first:?} as a program's first reload and \
         {after_a_no_op:?} as its second",
    );
    let ReuseTally { kept, bound } = first;
    assert!(
        kept * 2 > bound,
        "editing one of two independent loops should leave most of the program \
         in place, got {kept}/{bound}",
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
    // for. Every non-alphanumeric byte is escaped, a space included: the query is
    // percent-encoded rather than form-encoded, so `+` stands for itself — see
    // `percent_decode`.
    let encoded: String = V1
        .trim_end()
        .bytes()
        .map(|b| match b {
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

/// A program whose output is its `main` value rather than a sink reloads too.
///
/// Its source is `stdin`, which is unbounded, so the program keeps running and
/// the binary's own driver loop services the control port between pulls. The
/// line written before the swap is answered by the old version and the one after
/// by the new.
#[test]
fn a_main_output_program_over_stdin_reloads() {
    let (reply, out) = stdin_across_reload(
        "[\"> \" + line for line in stdin()]\n",
        "[\">> \" + line for line in stdin()]\n",
        "one",
        "two",
    );
    assert!(
        reply.contains("reloaded"),
        "the reload should be accepted: {reply}"
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
    let (reply, out) = stdin_across_reload(
        "[\"A\" + line for line in stdin()]\n",
        "[\"B\" + line for line in stdin()]\n",
        "L1\nL2\nL3\nL4",
        "L5\nL6\nL7\nL8",
    );
    assert!(
        reply.contains("reloaded"),
        "the reload should be accepted: {reply}"
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
    let (reply, out) = stdin_across_reload(
        indoc! {r#"
            n := 0
            for line in stdin():
                n := n + 1
            n
        "#},
        indoc! {r#"
            n := 0
            for line in stdin():
                n := n + 2
            n
        "#},
        "a\nb",
        "c\nd",
    );
    assert!(
        reply.contains("reloaded"),
        "the reload should be accepted: {reply}"
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
    let (reply, out) = stdin_across_reload(
        indoc! {r#"
            out = defer()
            n := 0
            for line in stdin():
                n := n + 1
                out << n
            out
        "#},
        indoc! {r#"
            out = defer()
            n := 0
            for line in stdin():
                n := n + 2
                out << n
            out
        "#},
        "a\nb",
        "c\nd",
    );
    assert!(
        reply.contains("reloaded"),
        "the reload should be accepted: {reply}"
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
    let (reply, _) = stdin_across_reload(
        indoc! {r#"
            n := ""
            for line in stdin():
                n := n + line
            n
        "#},
        indoc! {r#"
            n := 0
            for line in stdin():
                n := n + 1
            n
        "#},
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
fn a_reload_may_add_an_endpoint() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    let before = exchange(&mut ctx, move || vec![http_post(port, "/sign", "alice")]);
    assert_eq!(before, vec!["alice\n"]);

    live.reload(&mut ctx, &source("guestbook-adds-route", port), &no_main)
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

/// A route the program stops serving can be served again.
///
/// The regression this pins: a source handle outlived the version that opened it
/// and nothing removed one, so re-opening the address minted a second source
/// under the same id and `Scheduler::add_source_handle` refused to register it
/// beside the stale one — a panic inside the second reload, after the running
/// program had already been torn down.
#[test]
fn a_route_a_version_retired_can_be_served_again() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));
    assert_eq!(
        exchange(&mut ctx, move || vec![http_get(port, "/peek")]),
        vec!["peek\n"],
    );

    live.reload(&mut ctx, &source("guestbook-drops-route", port), &no_main)
        .expect("dropping a route is allowed");
    live.reload(&mut ctx, &source("guestbook", port), &no_main)
        .expect("re-adding the route it dropped is allowed");

    assert_eq!(
        exchange(&mut ctx, move || vec![http_get(port, "/peek")]),
        vec!["peek\n"],
        "the re-added route serves again",
    );
}

/// A program that moves to another port can move back.
///
/// Same cause as `a_route_a_version_retired_can_be_served_again`, on the shape
/// the PR advertises: `moving_a_program_to_another_port_keeps_its_state` covers
/// the move out, and moving back re-opens an address the registry had retired.
#[test]
fn a_program_can_move_back_to_the_port_it_left() {
    let first = reserve_test_port();
    let second = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", first));
    assert_eq!(
        exchange(&mut ctx, move || vec![http_post(first, "/sign", "alice")]),
        vec!["alice\n"],
    );

    live.reload(&mut ctx, &source("guestbook", second), &no_main)
        .expect("moving to another port is allowed");
    assert_port_released(first);

    live.reload(&mut ctx, &source("guestbook", first), &no_main)
        .expect("moving back is allowed");
    assert_eq!(
        exchange(&mut ctx, move || vec![http_post(first, "/sign", "bob")]),
        vec!["alice\nbob\n"],
        "back on the first port, with the entries it had",
    );
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

    live.reload(&mut ctx, &source("guestbook-drops-route", port), &no_main)
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
/// taking every endpoint with it — the reload is not recoverable at that point,
/// so it has to be refused before the swap.
#[test]
fn a_reload_may_not_change_the_type_of_held_state() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    let before = exchange(&mut ctx, move || vec![http_post(port, "/sign", "alice")]);
    assert_eq!(before, vec!["alice\n"]);

    let errors = live
        .reload(&mut ctx, &source("guestbook-retypes-state", port), &no_main)
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
fn a_reload_may_not_drop_state() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    let before = exchange(&mut ctx, move || vec![http_post(port, "/sign", "alice")]);
    assert_eq!(before, vec!["alice\n"]);

    let errors = live
        .reload(&mut ctx, &source("guestbook-drops-state", port), &no_main)
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

/// A version naming a port it cannot bind is refused, and the running program
/// keeps serving.
///
/// The regression this pins: the guard's compile named an address it did not hold
/// rather than taking it, so a port already in use failed only in the compile
/// *after* the running graph was torn down — where the failure is documented as a
/// compiler bug and panics, taking every endpoint with it. A typo, the program's
/// own control port, and a port another process holds all reach it.
#[test]
fn a_version_naming_an_unbindable_port_is_refused() {
    let port = reserve_test_port();
    let taken = reserve_test_port();
    let held = std::net::TcpListener::bind(("0.0.0.0", taken)).expect("hold the port");

    let (mut ctx, mut live) = start_sink(&source("guestbook", port));
    assert_eq!(
        exchange(&mut ctx, move || vec![http_post(port, "/sign", "alice")]),
        vec!["alice\n"],
    );

    let adds_a_held_port = source("guestbook", port).replace(
        "for entry in sign_reqs:",
        indoc! {r#"
            other_reqs, other_resps = http_serve("{PORT}", "GET", "/other")

            for req in other_reqs:
                other_resps << "other\n"

            for entry in sign_reqs:
        "#}
        .replace("{PORT}", &taken.to_string())
        .trim_end(),
    );
    let err = live
        .reload(&mut ctx, &adds_a_held_port, &no_main)
        .err()
        .expect("the port is held, so the version cannot be installed");
    assert!(
        format!("{err:?}").contains("bind"),
        "the refusal says what it could not do: {err:?}",
    );

    assert_eq!(
        exchange(&mut ctx, move || vec![http_get(port, "/peek")]),
        vec!["peek\n"],
        "the running program is still serving",
    );
    drop(held);
}

/// Retyping one field of a record-valued variable is refused.
///
/// The "records included" half of the retype refusal, which nothing covered: the
/// only other retype fixture goes `String` → `Int` at the top level.
/// `state_conflicts` compares `Extent`s structurally, so a field is as much of a
/// change as the whole value — and the change only exists between versions,
/// because inference rejects a field at two types within one program.
#[test]
fn retyping_one_field_of_a_record_variable_is_refused() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("record-accumulator", port));
    assert_eq!(
        exchange(&mut ctx, move || vec![http_post(port, "/bump", "x")]),
        vec!["ok\n"],
    );

    let err = live
        .reload(
            &mut ctx,
            &source("record-accumulator-retyped-field", port),
            &no_main,
        )
        .err()
        .expect("`n`'s value cannot seed a store built for another shape");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("`n`"),
        "the refusal names the variable: {rendered}",
    );

    assert_eq!(
        exchange(&mut ctx, move || vec![http_post(port, "/bump", "x")]),
        vec!["ok\n"],
        "the refused reload left the program serving",
    );
}

/// A version that does not compile is rejected before the running program is
/// touched.""""""
#[test]
fn a_rejected_reload_leaves_the_program_serving() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    live.reload(&mut ctx, "x = = 1", &no_main)
        .err()
        .expect("a syntax error is not a reload");

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
/// keep their state apart across a reload.
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
    let (reply, out) = stdin_across_reload(v1, &v2, "m\nn", "o\np");
    assert!(
        reply.contains("reloaded"),
        "the reload should be accepted: {reply}"
    );
    let flat: String = out.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(
        flat.contains("Ints([6060,],)"),
        "want a = 2 + 2*2 and b = 20 + 2*20; seeding either from the other reads 6042: {out}"
    );
}

/// Two causally independent transaction groups keep their state apart across an
/// reload that rebuilds one of them.
///
/// A program has one commit store per causal group, not one commit store, so `x`
/// and `y` here live in different stores sequenced by the same `Txn` domain, and
/// an edit to one group's writer rebuilds that group's store alone.
///
/// Neither store hands on a position: a commit clock is private and restartable,
/// so a rebuilt store seeds tick `0` from the value its variable carried. What
/// this pins is that the two groups' *values* stay apart — the rebuilt one
/// resumes from what `x` held, and `y`'s store is untouched.
#[test]
fn two_transaction_groups_keep_their_state_apart() {
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

    live.reload(
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

/// A request in flight across a swap is answered exactly once.
///
/// What this pins is the count, not which version answers: the request is
/// accepted by the listener and nothing pumps the scheduler until after the
/// reload, so whether the retired version read it before going depends on the
/// dispatcher, and either way it must be answered and counted once. A replay
/// would read `alice` twice, which the second assertion catches.
///
/// It does not pin the release carry, despite reading like it should. Nothing has
/// pumped, so every producer's recorded release is `Predicate::False` and the
/// agreement `carry_to_new_producers` records is empty — the case cannot tell
/// carrying it from carrying nothing. The carry is pinned by
/// `a_store_resumes_however_far_its_source_has_advanced`,
/// `two_loops_may_swap_which_source_they_read`,
/// `a_stateless_loop_may_gain_an_accumulator_over_an_advanced_source`, and
/// `UIntStreamBuffer`'s unit tests. `a_version_installed_mid_fold_is_pulled_without_a_new_arrival`
/// is the case where the retired version demonstrably decided a prefix first.
#[test]
fn a_request_that_arrived_before_the_swap_is_answered_after_it() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    let (tx, rx) = mpsc::channel::<Vec<String>>();
    thread::spawn(move || tx.send(vec![http_post(port, "/sign", "alice")]).unwrap());
    // Long enough for the dispatcher thread to have taken the request off the
    // socket. Nothing has pumped, so no reply exists. One poll would finish this
    // request outright rather than catching it partway — `/sign` is one step —
    // which is why establishing that the retired version decided a prefix needs
    // the twenty-element fold `a_version_installed_mid_fold_is_pulled_without_a_new_arrival`
    // uses.
    thread::sleep(Duration::from_millis(300));
    assert!(rx.try_recv().is_err(), "no reply before the swap");

    live.reload(
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

/// A request that arrived before its route was retired is answered 404.
///
/// The regression this pins: a retired route's source is kept alive past the
/// route by the handover the retired version's operators sit in, so
/// a request already in flight was neither replied to nor dropped, and the
/// client waited for the life of the process. Retirement answers it instead,
/// with the same 404 the address now gives —
/// `a_version_that_stops_serving_a_route_retires_it` is the case where the
/// request arrives after.
///
/// The request is caught in the dispatcher's channel here, before the source has
/// accepted it, because nothing pumps between its arrival and the swap. That is
/// the stage a client can reach without cooperating with the test; the pending
/// map is the other one `answer_in_flight` drains.
#[test]
fn a_request_that_arrived_before_its_route_was_retired_is_answered() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));
    assert_eq!(
        exchange(&mut ctx, move || vec![http_get(port, "/peek")]),
        vec!["peek\n"],
        "`/peek` serves before the swap",
    );

    let (tx, rx) = mpsc::channel::<Vec<String>>();
    thread::spawn(move || tx.send(vec![http_get(port, "/peek")]).unwrap());
    // Long enough for the dispatcher to have taken the request off the socket.
    // Nothing pumps, so no version ever reads it.
    thread::sleep(Duration::from_millis(300));
    assert!(rx.try_recv().is_err(), "no reply before the swap");

    live.reload(&mut ctx, &source("guestbook-drops-route", port), &no_main)
        .expect("dropping a stateless route is allowed");

    let answered = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(
        answered,
        vec!["Not Found"],
        "the retired route answers the request it was holding",
    );
}

/// Diffing against a version that stops serving a route leaves the route serving.
///
/// A diff answers a question; only a reload changes what the program serves. The
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
        "`/peek` is still the running program's route; only a reload retires it",
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
    let two_ports = indoc! {r#"
        a_reqs, a_resps = http_serve("{KEPT}", "GET", "/a")
        b_reqs, b_resps = http_serve("{DROPPED}", "GET", "/b")
        c_reqs, c_resps = http_serve("{KEPT}", "GET", "/c")
        for r in a_reqs:
            a_resps << "a\n"
        for r in b_reqs:
            b_resps << "b\n"
        for r in c_reqs:
            c_resps << "c\n"
    "#}
    .replace("{KEPT}", &kept.to_string())
    .replace("{DROPPED}", &dropped.to_string());
    let one_port = indoc! {r#"
        a_reqs, a_resps = http_serve("{KEPT}", "GET", "/a")
        for r in a_reqs:
            a_resps << "a\n"
    "#}
    .replace("{KEPT}", &kept.to_string());

    let (mut ctx, mut live) = start_sink(&two_ports);
    assert_eq!(
        exchange(&mut ctx, move || vec![
            http_get(kept, "/a"),
            http_get(dropped, "/b")
        ]),
        vec!["a\n", "b\n"],
    );

    live.reload(&mut ctx, &one_port, &no_main)
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

/// Repeated reloads keep working, including switching back to a version that
/// already ran.
#[test]
fn a_program_can_be_reloaded_repeatedly() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("guestbook", port));

    for (name, expected) in [
        ("guestbook-stateless-edit", "peek edited\n"),
        ("guestbook", "peek\n"),
        ("guestbook-stateless-edit", "peek edited\n"),
        // Twice in a row: a reload to the version already running is a no-op
        // that must still leave it serving.
        ("guestbook-stateless-edit", "peek edited\n"),
    ] {
        live.reload(&mut ctx, &source(name, port), &no_main)
            .unwrap_or_else(|e| panic!("reload to {name} rejected: {e:?}"));
        let served = exchange(&mut ctx, move || vec![http_get(port, "/peek")]);
        assert_eq!(served, vec![expected], "after reloading to {name}");
    }
}

/// A second reload does not replay what the first one's version committed.
///
/// The regression this pins: a source's release records were keyed by producer
/// name and never removed, so the producers a reload dropped went on
/// constraining the agreement from wherever they stopped. The agreement handed to
/// the next version's producers was pinned there, and the request the middle
/// version had committed was offered again — visible here because each `/set`
/// appends, so a replay leaves a mark.
///
/// The record is handed back from the producer's `Drop`
/// (`DataSourceDomainExtentImpl::retire_producer`), so this passes only while a
/// retired version's operators are actually freed. Two back-edges used to keep
/// them alive: a fan-out's notification closure held its own shared state, and a
/// store's driver and writer owned the fan-out whose input chain contains them
/// (`FanHold`). `a_retired_producer_stops_holding_the_agreement` pins the
/// bookkeeping itself.
#[test]
fn a_second_reload_does_not_replay_what_the_first_committed() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("running-log", port));
    let _ = exchange(&mut ctx, move || vec![http_post(port, "/set", "1")]);

    live.reload(&mut ctx, &source("running-log-writer-edit", port), &no_main)
        .expect("editing the writer is allowed");
    let _ = exchange(&mut ctx, move || vec![http_post(port, "/set", "2")]);

    live.reload(&mut ctx, &source("running-log", port), &no_main)
        .expect("editing it back is allowed");
    let after = exchange(&mut ctx, move || {
        vec![http_post(port, "/set", "3"), http_get(port, "/get")]
    });
    assert_eq!(
        after,
        vec!["ok\n", "1-23"],
        "each request is committed once, by whichever version was running",
    );
}

/// A transaction over a fixed collection does not re-commit what it committed
/// before the swap.
///
/// The regression this pins: a transaction drive's cut comes from its source's
/// agreed release, which works because a source outlives the version and
/// withdraws what its retired producers finished. A fixed collection is rebuilt
/// with the version and has no release state, so the drive had neither cut and
/// replayed its whole input — every item committed twice, under both rules. What
/// carries the drive across is the iteration operator itself: the collection is
/// not rebuilt, so the drive reads where to start off the fan-out over it. The
/// commit *clock* still hands on no position.
///
/// Visible because each commit appends. For a last-write-wins variable the replay
/// is invisible however deep the history, the same asymmetry
/// `a_transaction_writer_does_not_replay_what_it_committed` turns on.
#[test]
fn a_transaction_over_a_fixed_collection_does_not_replay() {
    let program = |step: &str| {
        format!(
            indoc! {r#"
                log: Mut(String, Txn) := ""
                for m in ["a", "b", "c", "d", "e", "f", "g", "h"]:
                    with begin():
                        {step}
                await_final(log)
            "#},
            step = step
        )
    };
    let mut ctx = GlobalContext::default();
    let mut live =
        LiveProgram::start(&mut ctx, &program("log := log + m"), &no_main).expect("v1 compiles");

    // Partway: enough pulls to commit some of the eight, not all.
    for _ in 0..6 {
        let producer = live
            .main_producer_mut()
            .expect("the program's value is `log`");
        let guard = producer.tiling().universal_guard();
        let _ = producer.get(guard);
        ctx.scheduler().check_for_notifications();
    }

    live.reload(&mut ctx, &program(r#"log := log + m + "!""#), &no_main)
        .expect("`log` is still declared, at the same type");
    let value = drive_main_to_terminal(&mut ctx, &mut live);

    let committed: String = value.chars().filter(|c| *c != '!').collect();
    assert_eq!(
        committed, "abcdefgh",
        "each element is committed once, by whichever version was running: {value:?}",
    );
}

/// Two writers to one transactional variable each keep their own place across an
/// reload.
///
/// The coverage this adds: every transaction test above has one writer, and the
/// handover carried a drive's position per *variable*. A store with two writer
/// sites has an iteration source per site and one variable to carry, so it could
/// not say which site a carried position belonged to and handed on none — both
/// drives restarted and committed their whole collections a second time.
///
/// Nothing carries a position now. Each site's iteration is its own node, so each
/// drive reads where to start off the fan-out over its own source, and two sites
/// need no more machinery than one.
///
/// Asserted as a multiset because the two writers interleave: what must hold is
/// that every element is committed exactly once, which a replay breaks by
/// duplicating and a lost place breaks by dropping.
#[test]
fn two_writers_to_one_variable_each_keep_their_place() {
    let program = |step: &str| {
        format!(
            indoc! {r#"
                log: Mut(String, Txn) := ""
                for m in ["a", "b", "c", "d"]:
                    with begin():
                        log := log + m
                for m in ["p", "q", "r", "s"]:
                    with begin():
                        {step}
                await_final(log)
            "#},
            step = step
        )
    };
    let mut ctx = GlobalContext::default();
    let mut live =
        LiveProgram::start(&mut ctx, &program("log := log + m"), &no_main).expect("v1 compiles");

    // Partway: enough pulls to commit some of the eight, not all.
    for _ in 0..6 {
        let producer = live
            .main_producer_mut()
            .expect("the program's value is `log`");
        let guard = producer.tiling().universal_guard();
        let _ = producer.get(guard);
        ctx.scheduler().check_for_notifications();
    }

    live.reload(&mut ctx, &program(r#"log := log + m + "!""#), &no_main)
        .expect("`log` is still declared, at the same type");
    let value = drive_main_to_terminal(&mut ctx, &mut live);

    let mut committed: Vec<char> = value.chars().filter(|c| *c != '!').collect();
    committed.sort_unstable();
    assert_eq!(
        committed.iter().collect::<String>(),
        "abcdpqrs",
        "each element of each writer's collection is committed once: {value:?}",
    );
}

/// A transaction writer does not re-attempt the transactions it committed before
/// the swap.
///
/// The regression this pins: the drive named the item it was attempting by its
/// index among the source's *offered columns* and never released a finished one,
/// so the source went on offering every request and the replacement's drive
/// started again from the first. Six commits before the reload were committed a
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

    live.reload(&mut ctx, &source("running-log-writer-edit", port), &no_main)
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

    live.reload(&mut ctx, &source("two-loops-swapped", port), &no_main)
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

/// A route that has been serving statelessly may gain a transactional writer, and
/// the writer commits from the next request rather than replaying the ones the
/// route already answered.
///
/// The transactional counterpart of
/// `a_stateless_loop_may_gain_an_accumulator_over_an_advanced_source`, and the
/// case where a commit drive really is built fresh over an advanced source: `/b`
/// carried no writer before, so no iteration operator exists at that node to take
/// over. The drive starts at `0` while the source is six items past it, which a
/// commit drive tolerates because it attempts the lowest position its source
/// still offers rather than the one it was based at.
#[test]
fn a_stateless_route_may_gain_a_transactional_writer_over_an_advanced_source() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("one-transactional-loop", port));

    let before = exchange(&mut ctx, move || {
        (1..=6)
            .map(|i| http_post(port, "/b", &i.to_string()))
            .collect()
    });
    assert_eq!(before, vec!["b\n"; 6], "`/b` answers, and holds nothing");

    live.reload(
        &mut ctx,
        &source("one-transactional-loop-both", port),
        &no_main,
    )
    .expect("`x` is unchanged and `y` is new");

    let after = exchange(&mut ctx, move || {
        vec![http_post(port, "/b", "Z"), http_get(port, "/gb")]
    });
    assert_eq!(
        after,
        vec!["ok\n", "Z"],
        "`y` starts at its init and commits the one request that arrived after it existed",
    );
}

/// Two transaction writers swapping which source they read keep their values and
/// pick up on the source each moved to.
///
/// The commit-store counterpart of `two_loops_may_swap_which_source_they_read`,
/// and the position comes from elsewhere. Both stores are rebuilt, but each
/// source term still corresponds — it moved between writers rather than changing
/// — so each drive takes over the iteration operator of the source it moved to
/// and resumes one past what that iteration had released. The iteration follows
/// the source, not the writer reading it. Six items per route, because at one or
/// two a drive that took the wrong iteration would still land on an offered
/// position.
#[test]
fn two_transactions_may_swap_which_source_they_read() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("two-transactions", port));

    let before = exchange(&mut ctx, move || {
        let mut out = Vec::new();
        for i in 1..=6 {
            out.push(http_post(port, "/a", &i.to_string()));
            out.push(http_post(port, "/b", &(10 - i).to_string()));
        }
        out.push(http_get(port, "/ga"));
        out.push(http_get(port, "/gb"));
        out
    });
    assert_eq!(
        (&before[before.len() - 2], before.last().unwrap()),
        (&"123456".to_string(), &"987654".to_string()),
    );

    live.reload(
        &mut ctx,
        &source("two-transactions-swapped", port),
        &no_main,
    )
    .expect("both variables are still declared, at the same types");

    // `/b` now writes `x`, which `/ga` reads, and `/a` now writes `y`.
    let after = exchange(&mut ctx, move || {
        vec![
            http_post(port, "/a", "A"),
            http_post(port, "/b", "B"),
            http_get(port, "/ga"),
            http_get(port, "/gb"),
        ]
    });
    assert_eq!(
        after,
        vec!["ok\n", "ok\n", "123456B", "987654A"],
        "each variable kept its value and committed on the source it moved to",
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

    live.reload(&mut ctx, &source("one-stateful-loop-both", port), &no_main)
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

/// Changing a variable's declared init does not reseed it.
///
/// The init is what a variable reads on a fresh start, and a carried value is not
/// a fresh start. The store is rebuilt — the init is part of its term — and it
/// resumes from the value it held, so the new init is never read. Nothing else
/// covered this: every other fixture pair either leaves the init alone or changes
/// its type, which is refused.
#[test]
fn changing_a_declared_init_leaves_a_carried_value_alone() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("bump-over-source", port));

    let before = exchange(&mut ctx, move || {
        vec![http_post(port, "/bump", "x"), http_post(port, "/bump", "x")]
    });
    assert_eq!(before, vec!["a\n", "aa\n"]);

    live.reload(
        &mut ctx,
        &source("bump-over-source-reseeded", port),
        &no_main,
    )
    .expect("`n` is still declared, at the same type");

    let after = exchange(&mut ctx, move || vec![http_post(port, "/bump", "x")]);
    assert_eq!(
        after,
        vec!["aaa\n"],
        "the carried value wins; reading the new init would answer `seeda`",
    );
}

/// A variable that moves to a loop over a fixed collection keeps its value and
/// folds the collection on top of it."""
///
/// The move is the same one a variable makes between any two loops: the value
/// seeds, and the positions restart because they are counted in something else.
/// Nothing about the new sequence being a list rather than a source changes that
/// — `n` holds what the requests built, and the list's elements follow.
#[test]
fn a_variable_that_moves_to_a_fixed_collection_keeps_its_value() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("bump-over-source", port));

    let before = exchange(&mut ctx, move || {
        vec![http_post(port, "/bump", "x"), http_post(port, "/bump", "x")]
    });
    assert_eq!(before, vec!["a\n", "aa\n"]);

    live.reload(&mut ctx, &source("bump-over-a-fixed-list", port), &no_main)
        .expect("`n` is still declared, at the same type");

    let after = exchange(&mut ctx, move || vec![http_post(port, "/bump", "x")]);
    assert_eq!(
        after,
        vec!["aayz\n"],
        "the list folds on top of what the requests built",
    );
}

/// A fold over a fixed collection resumes where its predecessor stopped, so an
/// edit inside the loop governs the elements that are left rather than replaying
/// the ones already folded.
///
/// The version installed here appends `"!"` to every element. None is appended,
/// because the fold had already reached the end of the list: an element is
/// decided once, by whichever version was running when it came up.
#[test]
fn a_fold_over_a_fixed_collection_resumes_where_it_stopped() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("bump-over-a-fixed-list", port));

    let before = exchange(&mut ctx, move || vec![http_post(port, "/bump", "x")]);
    assert_eq!(before, vec!["yz\n"]);

    live.reload(&mut ctx, &source("bump-over-a-marked-list", port), &no_main)
        .expect("`n` is still declared, at the same type");

    let after = exchange(&mut ctx, move || vec![http_post(port, "/bump", "x")]);
    assert_eq!(
        after,
        vec!["yz\n"],
        "the new rule governs the elements left, and none are",
    );
}

/// Pull the program's value until it settles, and return it.
///
/// A fold's value is final once the tile is terminal, which for an induction
/// store means every position of its extent is decided.
fn drive_main_to_terminal(ctx: &mut GlobalContext, live: &mut LiveProgram) -> String {
    for _ in 0..500 {
        ctx.scheduler().check_for_notifications();
        let producer = live
            .main_producer_mut()
            .expect("the program's value is `n`");
        let guard = producer.tiling().universal_guard();
        let tile = producer.get(guard);
        if tile.is_terminal() {
            let Tile::Scalar(column) = tile else {
                panic!("a string fold's value is a scalar, got {tile:?}");
            };
            let Value::String(s) = column.index_at(0) else {
                panic!("a string fold's value is a string");
            };
            return s.to_string();
        }
    }
    panic!("the fold never settled");
}

/// The elements the two mid-fold cases fold. Twenty because the point is a fold
/// caught partway, and a shorter list finishes inside the notification round that
/// starts it.
const TWENTY: &str = r#"["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t"]"#;

/// A fold of [`TWENTY`] into `n` whose `step` is the loop body, ending in `n` as
/// the program's value. Built rather than inline because the two mid-fold cases
/// and their two edits are one program with one line varying.
fn fold_to_main(step: &str) -> String {
    format!(
        indoc! {r#"
            n := ""
            for x in {items}:
                {step}
            n
        "#},
        items = TWENTY,
        step = step,
    )
}

/// The same fold behind `POST /read`, which replies with `n`.
fn fold_behind_a_route(step: &str, port: u16) -> String {
    format!(
        indoc! {r#"
            n := ""
            reqs, resps = http_serve("{port}", "POST", "/read")
            for x in {items}:
                {step}
            for r in reqs:
                resps << n + "\n"
        "#},
        port = port,
        items = TWENTY,
        step = step,
    )
}

/// Every element of `reply`, with the ones the marking version decided flagged.
///
/// The reply is the fold's whole value, so it says which version decided which
/// element: an element the marking version folded is followed by `!`.
fn decided_by_the_new_version(reply: &str) -> Vec<bool> {
    let mut out = Vec::new();
    for c in reply.trim().chars() {
        if c == '!' {
            *out.last_mut().expect("a marker follows an element") = true;
        } else {
            out.push(false);
        }
    }
    out
}

/// A fold caught partway resumes at the position it had reached, at every cut the
/// fold admits.
///
/// `docs/operational-semantics/semantics.md`, "What a reload computes" gives a
/// reloaded term's terminal tile as each version restricted to the part of the
/// extent it decided.
/// Sweeping the cut pins that equation rather than one instance of it: at every
/// one, each element is folded exactly once, the retired version decided a prefix,
/// and the new version decided the rest.
///
/// Drives the program's value directly rather than through a sink, because that
/// is what makes the position the reload lands on nameable: one pull decides one
/// position, so pulling `k` times and then swapping puts the cut at `k - 1`
/// rather than wherever a socket happened to be serviced.
///
/// The sweep reaches both ends. Below two pulls nothing is decided and the new
/// version governs the whole list; past twenty every position is decided and it
/// governs none. Those two are the only cuts an unsplittable tiling admits on its
/// own, and the ones between are reachable because the cut is taken on the fold's
/// input, whose function tiling denotes a position as a `Domain` guard.
#[test]
fn a_fold_interrupted_partway_resumes_at_the_position_it_reached() {
    // One past the twenty elements, so the sweep covers a fold already finished
    // when the reload arrives.
    const CUTS: usize = 22;
    let mut wrong: Vec<String> = Vec::new();
    for pulls in 0..CUTS {
        let mut ctx = GlobalContext::default();
        let mut live =
            LiveProgram::start(&mut ctx, &fold_to_main("n := n + x"), &no_main).expect("compiles");
        for _ in 0..pulls {
            let producer = live
                .main_producer_mut()
                .expect("the program's value is `n`");
            let guard = producer.tiling().universal_guard();
            let _ = producer.get(guard);
            ctx.scheduler().check_for_notifications();
        }

        live.reload(&mut ctx, &fold_to_main(r#"n := n + x + "!""#), &no_main)
            .expect("`n` is still declared, at the same type");

        let value = drive_main_to_terminal(&mut ctx, &mut live);
        let decided = decided_by_the_new_version(&value);
        // `k` pulls decide `k - 1` positions, and a fold whose every position is
        // decided leaves the new version governing nothing.
        let decided_before = pulls.saturating_sub(1);
        let want = (decided_before < 20).then_some(decided_before);
        let resumed_at = decided.iter().position(|marked| *marked);
        if decided.len() != 20 {
            wrong.push(format!(
                "{pulls} pulls: {} elements, so one was folded twice or not at all: {value}",
                decided.len()
            ));
        } else if resumed_at != want {
            wrong.push(format!(
                "{pulls} pulls: cut at {resumed_at:?} rather than {want:?}: {value}"
            ));
        } else if !decided[decided_before.min(20)..]
            .iter()
            .all(|marked| *marked)
        {
            wrong.push(format!(
                "{pulls} pulls: the new rule governs only part of the suffix: {value}"
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "the composite is not each version over the part it decided:\n  {}",
        wrong.join("\n  "),
    );
}

/// A version installed while a fold is partway through is pulled without waiting
/// for a source to report new data.
///
/// An operator notifies from inside `subscribe` — an induction store does, to
/// start its loop — and a sink consumer whose producer slot is not filled yet
/// drops that notification. A first compile does not notice, because the source
/// that has data reports it as new on the next poll. A replacement does: the
/// version it replaces already took that report, so the request in flight here
/// went unanswered until another arrived.
///
/// Where the fold is cut is a property of one notification round rather than
/// anything the language promises, so this pins the invariant — every element
/// folded once, the new rule governing a suffix — and leaves the position to
/// `a_fold_interrupted_partway_resumes_at_the_position_it_reached`.
#[test]
fn a_version_installed_mid_fold_is_pulled_without_a_new_arrival() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&fold_behind_a_route("n := n + x", port));

    let (tx, rx) = mpsc::channel::<Vec<String>>();
    thread::spawn(move || tx.send(vec![http_post(port, "/read", "x")]).unwrap());
    // Let the request arrive, then advance the fold with one poll — which both
    // takes the source's report of new data and leaves the fold unfinished.
    thread::sleep(Duration::from_millis(400));
    ctx.scheduler().check_for_notifications();
    assert!(
        rx.try_recv().is_err(),
        "twenty elements outlast the round that starts them, so the reply is still pending",
    );

    live.reload(
        &mut ctx,
        &fold_behind_a_route(r#"n := n + x + "!""#, port),
        &no_main,
    )
    .expect("`n` is still declared, at the same type");

    let reply = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    let value = reply.first().expect("one request, one reply").clone();
    let decided = decided_by_the_new_version(&value);
    assert_eq!(
        decided.len(),
        20,
        "every element is folded exactly once: {value}"
    );
    let resumed_at = decided
        .iter()
        .position(|marked| *marked)
        .expect("the swap lands before the last element");
    assert!(
        decided[resumed_at..].iter().all(|marked| *marked),
        "the new rule governs every element from the frontier on: {value}",
    );
    // Without this the case degenerates into "a version installed before the
    // fold started is pulled", which the assertions above would still satisfy:
    // the single poll would have advanced nothing, every element would be the
    // new version's, and `resumed_at` would be `0`. The precondition it needs is
    // that the retired version decided something.
    assert!(
        resumed_at > 0,
        "the fold was caught partway, so the retired version decided a prefix: {value}",
    );
}

/// A fold of [`TWENTY`]'s later half into `n`, the elements reaching the loop
/// through a filter. `step` is the loop body, as in [`fold_to_main`].
fn filtered_fold_to_main(step: &str) -> String {
    format!(
        indoc! {r#"
            n := ""
            kept = [x for x in {items} if x > "q"]
            for x in kept:
                {step}
            n
        "#},
        items = TWENTY,
        step = step,
    )
}

/// A fold whose source is filtered resumes at the position it had reached, which
/// is a position of the *unfiltered* extent.
///
/// The elements the filter drops occupy no position in the recurrence, so the
/// positions it does decide are a subset of the collection's and are not
/// contiguous. The resume position is one of those, and the cut has to fall on it:
/// resuming at the position after the last one *decided* would skip an element
/// nothing has folded, and resuming by counting decided elements would land in the
/// wrong place entirely.
#[test]
fn a_filtered_fold_resumes_at_a_position_of_the_collection_it_filters() {
    const PULLS: usize = 2;
    let mut ctx = GlobalContext::default();
    let mut live = LiveProgram::start(&mut ctx, &filtered_fold_to_main("n := n + x"), &no_main)
        .expect("compiles");
    for _ in 0..PULLS {
        let producer = live
            .main_producer_mut()
            .expect("the program's value is `n`");
        let guard = producer.tiling().universal_guard();
        let _ = producer.get(guard);
        ctx.scheduler().check_for_notifications();
    }

    live.reload(
        &mut ctx,
        &filtered_fold_to_main(r#"n := n + x + "!""#),
        &no_main,
    )
    .expect("`n` is still declared, at the same type");

    let value = drive_main_to_terminal(&mut ctx, &mut live);
    assert_eq!(
        value, "rs!t!",
        "the filter keeps `r`, `s` and `t`; the first is the retired version's and \
         the rest are the new one's",
    );
}

/// A fold over a *different* fixed collection folds it from its first element.
///
/// `[0, 2]` is the extent of `["y", "z"]` and of `["p", "q"]` alike, so the extent
/// alone would have the second fold resume at the first's frontier and skip both
/// its elements. What rules that out is that the two collections are two nodes:
/// the iteration is rebuilt and offers every position. The value carries the way
/// it does between any two loops.
#[test]
fn a_fold_over_another_fixed_collection_starts_it_from_the_beginning() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source("bump-over-a-fixed-list", port));

    let before = exchange(&mut ctx, move || vec![http_post(port, "/bump", "x")]);
    assert_eq!(before, vec!["yz\n"]);

    live.reload(
        &mut ctx,
        &source("bump-over-another-fixed-list", port),
        &no_main,
    )
    .expect("`n` is still declared, at the same type");

    let after = exchange(&mut ctx, move || vec![http_post(port, "/bump", "x")]);
    assert_eq!(
        after,
        vec!["yzpq\n"],
        "the new list is folded whole, onto the value the old one built",
    );
}

/// A fold whose variable is declared inside a function body, so its store sits
/// under the `Let` that binds the call's result rather than at the top of the
/// binding chain.
///
/// That placement is what the two cases below are about: a store bound directly
/// (every `{PORT}` fixture here) is re-registered by every compilation, and one
/// under another binding is not when that binding is kept.
fn nested_fold(step: &str) -> String {
    format!(
        indoc! {r#"
            def fold_by(items) => String:
                n := ""
                for x in items:
                    n := n {step}
                n

            a = fold_by(["p", "q"])
            a + ""
        "#},
        step = step
    )
}

/// A variable keeps its value across a reload that kept the binding holding
/// its store.
///
/// The regression this pins: keeping a binding does not walk the bound term, so
/// a `Transact` under a kept binding reached no `bind_store` and dropped out of
/// the handover. The version after that one had no value to seed the variable
/// from and reseeded it from the declared init, silently — the one outcome the
/// state guard exists to prevent, arrived at by way of the guard not seeing the
/// variable either (`the_state_guard_survives_a_reload_that_kept_the_binding`).
///
/// The middle reload is the whole point. Without it the same edit resumes
/// correctly, which `a_fold_over_a_fixed_collection_resumes_where_it_stopped`
/// already covers.
#[test]
fn a_variable_survives_a_reload_that_kept_its_binding() {
    let mut ctx = GlobalContext::default();
    let mut live =
        LiveProgram::start(&mut ctx, &nested_fold("+ \"x\""), &no_main).expect("compiles");
    assert_eq!(drive_main_to_terminal(&mut ctx, &mut live), "xx");

    live.reload(&mut ctx, &nested_fold("+ \"x\""), &no_main)
        .expect("a reload to the running version is a no-op");
    assert_eq!(drive_main_to_terminal(&mut ctx, &mut live), "xx");

    live.reload(&mut ctx, &nested_fold("+ \"y\""), &no_main)
        .expect("`n` is still declared, at the same type");
    assert_eq!(
        drive_main_to_terminal(&mut ctx, &mut live),
        "xx",
        "the fold had reached the end of the list, so the new rule governs nothing",
    );
}

/// The state guard still names a variable whose binding an earlier reload
/// kept.
///
/// The other side of `a_variable_survives_a_reload_that_kept_its_binding`: a
/// variable absent from the handover is one `state_conflicts` does not walk, so
/// dropping it was accepted rather than refused.
#[test]
fn the_state_guard_survives_a_reload_that_kept_the_binding() {
    let mut ctx = GlobalContext::default();
    let mut live =
        LiveProgram::start(&mut ctx, &nested_fold("+ \"x\""), &no_main).expect("compiles");
    assert_eq!(drive_main_to_terminal(&mut ctx, &mut live), "xx");

    live.reload(&mut ctx, &nested_fold("+ \"x\""), &no_main)
        .expect("a reload to the running version is a no-op");

    let dropped = indoc! {r#"
        def fold_by(items) => String:
            "gone"

        a = fold_by(["p", "q"])
        a + ""
    "#};
    let err = live
        .reload(&mut ctx, dropped, &no_main)
        .err()
        .expect("`n` is no longer declared, so its value has nowhere to be seeded");
    assert!(
        format!("{err:?}").contains("`n`"),
        "the refusal names the variable it is about: {err:?}",
    );
}

/// Two named instantiations of one stateful function, in either declaration
/// order, so the cases below can move them and add to them.
///
/// Each declares a variable spelled `n`, which is what makes them the shapes a
/// `VarPath` has to tell apart: the spelling alone does not, and the two are
/// distinguished by the binding whose definition encloses each one.
fn two_instantiations(order: bool, step_a: &str, step_z: &str) -> String {
    let def = indoc! {r#"
        def fold_by(items, step) => String:
            n := ""
            for x in items:
                n := n + step
            n

    "#};
    let a = format!("a = fold_by([\"p\", \"q\"], \"{step_a}\")\n");
    let z = format!("z = fold_by([\"p\", \"q\", \"r\"], \"{step_z}\")\n");
    let body = "a + \"|\" + z\n";
    if order {
        format!("{def}{a}{z}{body}")
    } else {
        format!("{def}{z}{a}{body}")
    }
}

/// A stateful loop the reload adds ahead of an existing one starts at its init,
/// and the existing one keeps its value.
///
/// The regression this pins: state was addressed by the variable's spelling plus
/// its index among same-spelled variables in tree order, so the added `n` took
/// the index the existing one had — and with it that variable's value and its
/// frontier, reporting its predecessor's answer instead of folding its own list.
#[test]
fn a_loop_added_ahead_of_a_same_spelled_one_starts_at_its_init() {
    let only_a = indoc! {r#"
        def fold_by(items, step) => String:
            n := ""
            for x in items:
                n := n + step
            n

        a = fold_by(["p", "q"], "x")
        a
    "#};
    let mut ctx = GlobalContext::default();
    let mut live = LiveProgram::start(&mut ctx, only_a, &no_main).expect("v1 compiles");
    assert_eq!(drive_main_to_terminal(&mut ctx, &mut live), "xx");

    live.reload(&mut ctx, &two_instantiations(false, "x", "z"), &no_main)
        .expect("`a` is unchanged and `z` is new");
    assert_eq!(
        drive_main_to_terminal(&mut ctx, &mut live),
        "xx|zzz",
        "`a` keeps its value and the loop the reload added folds its own list",
    );
}

/// Reordering two same-spelled variables leaves each one's state with it.
///
/// The regression this pins: an index in tree order swaps when the two
/// declarations swap, so each variable seeded from the other. Both stores have to
/// be rebuilt for it to show — a reorder alone keeps both operators and looks
/// correct — so this edits both bodies.
#[test]
fn reordering_two_same_spelled_variables_keeps_their_state_apart() {
    let mut ctx = GlobalContext::default();
    let mut live = LiveProgram::start(&mut ctx, &two_instantiations(true, "x", "y"), &no_main)
        .expect("v1 compiles");
    assert_eq!(drive_main_to_terminal(&mut ctx, &mut live), "xx|yyy");

    live.reload(&mut ctx, &two_instantiations(false, "X", "Y"), &no_main)
        .expect("both are still declared, at the same type");
    assert_eq!(
        drive_main_to_terminal(&mut ctx, &mut live),
        "xx|yyy",
        "both folds had reached the end, so neither new rule governs anything",
    );
}

/// Two instantiations whose arguments are equal keep their accumulators apart.
///
/// The regression this pins: equal arguments make the two `Transact` terms
/// α-equivalent, so they share a [`ContentHash`], and a handover keyed by that
/// alone kept one of the two — the other variable left the handover and reseeded
/// from its init on the next edit. `two_instantiations_of_one_function_keep_their_accumulators_apart`
/// covers the same shape with *unequal* arguments, which is what made this one
/// easy to miss.
#[test]
fn two_instantiations_with_equal_arguments_keep_their_accumulators_apart() {
    let twin = |step: &str| {
        format!(
            indoc! {r#"
                def fold_by(items, step) => String:
                    n := ""
                    for x in items:
                        n := n + step
                    n

                a = fold_by(["p", "q"], "{step}")
                z = fold_by(["p", "q"], "{step}")
                a + "|" + z
            "#},
            step = step
        )
    };
    let mut ctx = GlobalContext::default();
    let mut live = LiveProgram::start(&mut ctx, &twin("x"), &no_main).expect("v1 compiles");
    assert_eq!(drive_main_to_terminal(&mut ctx, &mut live), "xx|xx");

    live.reload(&mut ctx, &twin("x"), &no_main)
        .expect("a reload to the running version is a no-op");

    live.reload(&mut ctx, &twin("y"), &no_main)
        .expect("both are still declared, at the same type");
    assert_eq!(
        drive_main_to_terminal(&mut ctx, &mut live),
        "xx|xx",
        "both folds had reached the end, so the new rule governs nothing",
    );
}

/// The two programs the transaction-boundary cases move a variable between.
///
/// One `log` folded over one collection, written inside a `with begin():` or not.
/// Two lines differ and both follow from the boundary: the write sits in a
/// transaction block, and the terminal read is `await_final`, which lowering
/// refuses on an induction accumulator
/// (`await_final_on_an_induction_accumulator_is_refused`).
fn boundary_pair(transactional: bool, items: &str, mark: &str) -> String {
    if transactional {
        format!(
            indoc! {r#"
                log: Mut(String, Txn) := ""
                for m in {items}:
                    with begin():
                        log := log + m + "{mark}"
                await_final(log)
            "#},
            items = items,
            mark = mark,
        )
    } else {
        format!(
            indoc! {r#"
                log := ""
                for m in {items}:
                    log := log + m + "{mark}"
                log
            "#},
            items = items,
            mark = mark,
        )
    }
}

/// Fold `program` two positions in, leaving the rest for the version that
/// replaces it.
fn drive_two_positions(ctx: &mut GlobalContext, live: &mut LiveProgram) {
    for _ in 0..2 {
        let producer = live
            .main_producer_mut()
            .expect("the program's value is `log`");
        let guard = producer.tiling().universal_guard();
        let _ = producer.get(guard);
        ctx.scheduler().check_for_notifications();
    }
}

const BOUNDARY_ITEMS: &str = r#"["a", "b", "c"]"#;

/// A variable may move out of a transaction, and the elements left are folded by
/// the new rule.
///
/// A transaction's commit clock hands on no position — it restarts with the store
/// that counts it. What says where the fold resumes is the iteration both sides
/// read: the collection is unchanged, so its operator is kept, and the induction
/// store the variable moves to takes its position off the same fan the
/// transaction's drive was reading. So it resumes at the cut rather than folding
/// an element twice, and the mark shows which rule decided which element.
#[test]
fn a_variable_may_move_out_of_a_transaction() {
    let mut ctx = GlobalContext::default();
    let mut live = LiveProgram::start(&mut ctx, &boundary_pair(true, BOUNDARY_ITEMS, ""), &no_main)
        .expect("a transactional fold compiles");
    drive_two_positions(&mut ctx, &mut live);

    live.reload(
        &mut ctx,
        &boundary_pair(false, BOUNDARY_ITEMS, "!"),
        &no_main,
    )
    .expect("`log` is still declared, at the same type");
    assert_eq!(
        drive_main_to_terminal(&mut ctx, &mut live),
        "ab!c!",
        "`a` was committed under the transaction and the rest folded by the loop, each once",
    );
}

/// A variable may move into a transaction, on the same terms.
///
/// The mirror of `a_variable_may_move_out_of_a_transaction`, and it needs nothing
/// of its own: the iteration is the same operator either way, so whichever
/// recurrence is built over it reads its position off the same fan.
#[test]
fn a_variable_may_move_into_a_transaction() {
    let mut ctx = GlobalContext::default();
    let mut live = LiveProgram::start(
        &mut ctx,
        &boundary_pair(false, BOUNDARY_ITEMS, ""),
        &no_main,
    )
    .expect("an induction fold compiles");
    drive_two_positions(&mut ctx, &mut live);

    live.reload(
        &mut ctx,
        &boundary_pair(true, BOUNDARY_ITEMS, "!"),
        &no_main,
    )
    .expect("`log` is still declared, at the same type");
    assert_eq!(
        drive_main_to_terminal(&mut ctx, &mut live),
        "ab!c!",
        "`a` was folded by the loop and the rest committed under the transaction, each once",
    );
}

/// Crossing the boundary onto a different collection carries the value and folds
/// the new collection whole.
///
/// The position does not carry, because the iteration it belonged to is gone: the
/// edited collection is a different computation, so its operator is rebuilt and
/// offers every position. Resuming at the old frontier would skip elements
/// nothing read. The value is the variable's rather than the iteration's, so it
/// stays.
#[test]
fn a_variable_leaving_a_transaction_for_another_collection_keeps_its_value() {
    let mut ctx = GlobalContext::default();
    let mut live = LiveProgram::start(&mut ctx, &boundary_pair(true, BOUNDARY_ITEMS, ""), &no_main)
        .expect("a transactional fold compiles");
    assert_eq!(drive_main_to_terminal(&mut ctx, &mut live), "abc");

    live.reload(
        &mut ctx,
        &boundary_pair(false, r#"["p", "q", "r"]"#, "!"),
        &no_main,
    )
    .expect("`log` is still declared, at the same type");
    assert_eq!(
        drive_main_to_terminal(&mut ctx, &mut live),
        "abcp!q!r!",
        "the carried value seeds the fold and every element of the new collection is folded",
    );
}

/// `await_final` is refused on an induction accumulator, naming how to read one.
///
/// This is why the two programs a boundary case moves between differ in their
/// terminal read as well as in the write: the read form follows from the domain,
/// so the pair cannot differ by the transaction alone.
#[test]
fn await_final_on_an_induction_accumulator_is_refused() {
    let mut ctx = GlobalContext::default();
    let program = indoc! {r#"
        log := ""
        for m in ["a", "b", "c"]:
            log := log + m
        await_final(log)
    "#};
    let rendered = match LiveProgram::start(&mut ctx, program, &no_main) {
        Ok(_) => panic!("`await_final` applies to a transactional variable"),
        Err(errors) => format!("{errors:?}"),
    };
    assert!(
        rendered.contains("not a transactional mutable variable"),
        "the error names what `await_final` applies to, got {rendered}",
    );
}

/// Two anonymous call sites of one stateful function, and the fold each holds.
///
/// Anonymous is the point: neither call site is bound to a name, so the only
/// thing telling the two `n`s apart is which comes first.
fn anonymous_sites(first: (&str, &str), second: (&str, &str)) -> String {
    format!(
        indoc! {r#"
            def fold_by(items, step) => String:
                n := ""
                for x in items:
                    n := n + step
                n

            fold_by({fi}, "{fs}") + "|" + fold_by({si}, "{ss}")
        "#},
        fi = first.0,
        fs = first.1,
        si = second.0,
        ss = second.1,
    )
}

const TWO_ITEMS: &str = r#"["p", "q"]"#;
const THREE_ITEMS: &str = r#"["p", "q", "r"]"#;

/// Swapping two anonymous call sites is refused, naming the two declarations and
/// how to tell them apart.
///
/// The bug this prevents: the two `n`s are told apart by position alone, so a
/// swap hands each one its neighbour's value and folds its own list on top —
/// `"xxzzz|zzzxx"` where `"zzz|xx"` is right. Both accumulators are wrong and the
/// program goes on answering, which is the one outcome the guard exists to stop.
/// Refused rather than followed because the source says nothing about which
/// declaration the value belongs to; `site_moved` is what notices, and naming the
/// call sites is what makes the same edit carry
/// (`reordering_two_same_spelled_variables_keeps_their_state_apart`).
#[test]
fn swapping_two_anonymous_call_sites_is_refused() {
    let mut ctx = GlobalContext::default();
    let mut live = LiveProgram::start(
        &mut ctx,
        &anonymous_sites((TWO_ITEMS, "x"), (THREE_ITEMS, "z")),
        &no_main,
    )
    .expect("v1 compiles");
    assert_eq!(drive_main_to_terminal(&mut ctx, &mut live), "xx|zzz");

    let rendered = match live.reload(
        &mut ctx,
        &anonymous_sites((THREE_ITEMS, "z"), (TWO_ITEMS, "x")),
        &no_main,
    ) {
        Ok(_) => panic!("neither declaration can be told from the other"),
        Err(errors) => format!("{errors:?}"),
    };
    assert!(
        rendered.contains("`n` and `n` (#1) are told apart only by where they appear"),
        "the refusal names both declarations, got {rendered}",
    );
    assert!(
        rendered.contains("Bind each of those declarations to its own name"),
        "and says what to do about it, got {rendered}",
    );

    let served = drive_main_to_terminal(&mut ctx, &mut live);
    assert_eq!(
        served, "xx|zzz",
        "the refused reload left the program running"
    );
}

/// A call site inserted ahead of an anonymous one is refused on the same ground.
///
/// The insertion shifts every later declaration of that spelling onto its
/// neighbour's position. Resolvable in principle — the surviving site's content
/// says where it went — but the value would still be moving between declarations
/// the source does not distinguish, so it is refused with the rest.
#[test]
fn inserting_ahead_of_an_anonymous_call_site_is_refused() {
    let mut ctx = GlobalContext::default();
    let mut live = LiveProgram::start(
        &mut ctx,
        &anonymous_sites((TWO_ITEMS, "x"), (THREE_ITEMS, "z")),
        &no_main,
    )
    .expect("v1 compiles");
    assert_eq!(drive_main_to_terminal(&mut ctx, &mut live), "xx|zzz");

    let with_insertion = format!(
        indoc! {r#"
            def fold_by(items, step) => String:
                n := ""
                for x in items:
                    n := n + step
                n

            fold_by(["m"], "w") + fold_by({two}, "x") + "|" + fold_by({three}, "z")
        "#},
        two = TWO_ITEMS,
        three = THREE_ITEMS,
    );
    assert!(
        live.reload(&mut ctx, &with_insertion, &no_main).is_err(),
        "the insertion shifts both existing declarations",
    );
}

/// A reload that leaves the anonymous call sites where they are is accepted.
///
/// The refusal is about the state moving between two indistinguishable
/// declarations, not about a program having them: a version that edits one site's
/// body carries both values, and so does one that changes nothing. A site whose
/// body was edited is gone from the new version rather than sitting under another
/// variable, which is what tells the two apart.
#[rstest]
#[case::unchanged("x", "z")]
#[case::one_site_edited("X", "z")]
#[case::both_sites_edited("X", "Z")]
fn editing_anonymous_call_sites_in_place_is_accepted(#[case] first: &str, #[case] second: &str) {
    let mut ctx = GlobalContext::default();
    let mut live = LiveProgram::start(
        &mut ctx,
        &anonymous_sites((TWO_ITEMS, "x"), (THREE_ITEMS, "z")),
        &no_main,
    )
    .expect("v1 compiles");
    assert_eq!(drive_main_to_terminal(&mut ctx, &mut live), "xx|zzz");

    live.reload(
        &mut ctx,
        &anonymous_sites((TWO_ITEMS, first), (THREE_ITEMS, second)),
        &no_main,
    )
    .expect("the declarations stay where they are, so both values carry");
    assert_eq!(
        drive_main_to_terminal(&mut ctx, &mut live),
        "xx|zzz",
        "each fold had already reached the end of its own collection",
    );
}

/// Two anonymous call sites that compute the same thing may be reordered.
///
/// Sites that hash equal are the same computation over the same inputs, so their
/// accumulators hold the same value at every position and which one holds which
/// does not matter. `site_moved` returns nothing for them and the reload is
/// accepted, which keeps the refusal to the case where it changes an answer.
#[test]
fn reordering_two_identical_anonymous_call_sites_is_accepted() {
    let mut ctx = GlobalContext::default();
    let mut live = LiveProgram::start(
        &mut ctx,
        &anonymous_sites((TWO_ITEMS, "x"), (TWO_ITEMS, "x")),
        &no_main,
    )
    .expect("v1 compiles");
    assert_eq!(drive_main_to_terminal(&mut ctx, &mut live), "xx|xx");

    live.reload(
        &mut ctx,
        &anonymous_sites((TWO_ITEMS, "x"), (TWO_ITEMS, "x")),
        &no_main,
    )
    .expect("interchangeable declarations need no telling apart");
    assert_eq!(drive_main_to_terminal(&mut ctx, &mut live), "xx|xx");
}
