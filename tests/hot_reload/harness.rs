//! What the cases drive: the programs, and the plumbing that runs one.
//!
//! Split from [`cases`](crate::cases) because it is the larger half — a running
//! program, a control port and a swap are more setup than any one case's
//! assertion. See `tests/hot_reload.rs` for what the programs are and what a
//! reload may do to them.

use std::{
    thread,
    time::{Duration, Instant},
};

use crate::serving::{raw_http, reserve_test_port};
/// Run a `stdin`-sourced program under `--control`, feeding it `before`, then
/// swapping it for `reloaded` and feeding it `after`.
///
/// Driven as a subprocess because a `main` output belongs to the binary's own
/// loop, not to a sink a test can pump. Such a program is not short-lived: its
/// source is unbounded, so it keeps running and is as reloadable as any other.
pub(crate) fn stdin_across_reload(
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
pub(crate) struct Launched {
    pub(crate) program: RunningProgram,
    pub(crate) control: u16,
    /// The program's `stdin`, for a test that feeds it. `None` once taken.
    pub(crate) input: Option<std::process::ChildStdin>,
    /// Every line the program has written, accumulated by [`reader`](Self::reader).
    pub(crate) collected: std::sync::Arc<std::sync::Mutex<String>>,
    pub(crate) reader: Option<thread::JoinHandle<()>>,
}

/// Spawn `program` under `--control` on a reserved port and wait for that port to
/// answer.
///
/// The wait is not optional: the program binds its control port during
/// compilation, so a request sent before then is refused rather than served.
pub(crate) fn launch_under_control(program: &str) -> Launched {
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
pub(crate) struct RunningProgram {
    pub(crate) child: std::process::Child,
    pub(crate) dir: std::path::PathBuf,
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
pub(crate) fn assert_port_released(port: u16) {
    let deadline = Instant::now() + Duration::from_secs(5);
    while std::net::TcpStream::connect(("127.0.0.1", port)).is_ok() {
        assert!(
            Instant::now() < deadline,
            "port {port} is still accepting connections after its last route went",
        );
        thread::sleep(Duration::from_millis(20));
    }
}

/// The programs the cases below drive, other than the two the gallery keeps as
/// files.
///
/// Inline because they are scaffolding rather than demonstrations: each is one
/// base program's variant differing by the single edit its case is about, and a
/// gallery directory holds a program, not a fixture set. `{PORT}` is substituted
/// by [`source`].
pub(crate) mod fixtures {
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

    /// `TWO_LOOPS` with each loop reading the other's route, so both
    /// variables keep their values and continue on the source they moved to.
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

    /// A loop folding a view over its own request source: `seen` is a
    /// comprehension over `bump_reqs`, so its elements are gone once answered.
    /// The base for the two cases about a loop that cannot read its collection
    /// from the start.
    pub(crate) const VIEW_FOLD: &str = indoc! {r#"
        bump_reqs, bump_resps = http_serve("{PORT}", "POST", "/bump")
        seen = [r + "!" for r in bump_reqs]
        n := ""
        for x in seen:
            n := n + x
            bump_resps << n
    "#};

    /// [`VIEW_FOLD`] with `n` moved to a loop of its own and the `seen` loop
    /// carrying a new variable instead. The `seen` loop then carries nothing, so
    /// it would read `seen` from the beginning — which is the refusal.
    pub(crate) const VIEW_FOLD_REVARIABLED: &str = indoc! {r#"
        bump_reqs, bump_resps = http_serve("{PORT}", "POST", "/bump")
        tick_reqs, tick_resps = http_serve("{PORT}", "POST", "/tick")
        seen = [r + "!" for r in bump_reqs]
        m := ""
        for x in seen:
            m := m + x
            bump_resps << m
        n := ""
        for z in tick_reqs:
            n := n + z
            tick_resps << n
    "#};

    /// [`VIEW_FOLD`] plus a loop over a second route. The added loop reads a
    /// source rather than a collection, so it starts where that source is.
    pub(crate) const VIEW_FOLD_SECOND_ROUTE: &str = indoc! {r#"
        bump_reqs, bump_resps = http_serve("{PORT}", "POST", "/bump")
        tick_reqs, tick_resps = http_serve("{PORT}", "POST", "/tick")
        seen = [r + "!" for r in bump_reqs]
        n := ""
        for x in seen:
            n := n + x
            bump_resps << n
        t := ""
        for z in tick_reqs:
            t := t + z
            tick_resps << t
    "#};
}

pub(crate) fn source(name: &str, port: u16) -> String {
    let text = match name {
        "guestbook" => include_str!("../programs/hot_reload/program.cambra"),
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
        "guestbook-stateful-edit" => include_str!("../programs/hot_reload/reloaded.cambra"),
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
        "view-fold" => fixtures::VIEW_FOLD,
        "view-fold-revariabled" => fixtures::VIEW_FOLD_REVARIABLED,
        "view-fold-second-route" => fixtures::VIEW_FOLD_SECOND_ROUTE,
        other => panic!("no such program: {other}"),
    };
    text.replace("{PORT}", &port.to_string())
}
