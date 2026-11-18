//! What the cases drive: the programs, and the plumbing that runs one.
//!
//! Split from [`cases`](super::cases) because it is the larger half — a running
//! program, a control port and a swap are more setup than any one case's
//! assertion. See `tests/it/hot_reload.rs` for what the programs are and what a
//! reload may do to them.

use std::{
    thread,
    time::{Duration, Instant},
};

use cambra::{
    ccl::context::{CompileError, GlobalContext, Phase},
    ccl::load::LoadedProgram,
    live_program::{
        BranchError, Created, DiffReport, LiveProgram, MainConsumerFactory, ReloadReport,
    },
};

use super::serving::{raw_http, reserve_test_port};
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
    let v2 = launched.spawned.program.dir.join("v2.cambra");
    std::fs::write(&v2, reloaded).expect("write v2");
    let mut input = launched.spawned.input.take().expect("piped stdin");
    let collected = launched.spawned.collected.clone();
    let reader = launched.spawned.reader.take().expect("reader thread");

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

    launched
        .spawned
        .program
        .wait_for_exit(Duration::from_secs(10));
    reader.join().expect("reader thread");
    let text = collected.lock().unwrap().clone();
    (reply, text)
}

/// A spawned `cambra` binary, with its `stdin` held open and its `stdout`
/// collected.
///
/// Every launch starts here. [`Launched`] adds a control port to it.
pub(crate) struct Spawned {
    pub(crate) program: RunningProgram,
    /// The program's `stdin`, for a test that feeds it. `None` once taken.
    pub(crate) input: Option<std::process::ChildStdin>,
    /// Every line the program has written, accumulated by [`reader`](Self::reader).
    pub(crate) collected: std::sync::Arc<std::sync::Mutex<String>>,
    pub(crate) reader: Option<thread::JoinHandle<()>>,
}

impl Spawned {
    /// Wait until the program has written every one of `needles`, failing the
    /// test after `within`.
    pub(crate) fn wait_for_output(&self, needles: &[&str], within: Duration) {
        let deadline = Instant::now() + within;
        loop {
            let out = self.collected.lock().unwrap().clone();
            if needles.iter().all(|n| out.contains(n)) {
                return;
            }
            assert!(
                Instant::now() < deadline,
                "the program never wrote all of {needles:?}: {out}"
            );
            thread::sleep(Duration::from_millis(20));
        }
    }
}

/// A program running under `--control`, with its control port already answering.
///
/// Split out of [`stdin_across_reload`] because a test that only asks the control
/// port a question needs the launch and none of the feeding.
pub(crate) struct Launched {
    pub(crate) spawned: Spawned,
    pub(crate) control: u16,
}

impl Launched {
    /// Wait until the program has finished, and return the control port's whole
    /// response to the first request it no longer serves.
    ///
    /// A program that ends prints its value and then leaves the driver loop, and
    /// the control port answers `200` until it has. So this waits for the value,
    /// then repeats `GET /branches` until the status is something else, failing
    /// the test after `within`. Each request has a read timeout: a control port
    /// that never answers fails the test rather than hanging it.
    pub(crate) fn wait_until_finished(&self, within: Duration) -> String {
        use std::io::{Read, Write};

        self.spawned.wait_for_output(&["Got value"], within);
        let control = self.control;
        let deadline = Instant::now() + within;
        loop {
            let mut stream = std::net::TcpStream::connect(("127.0.0.1", control)).expect("connect");
            stream
                .set_read_timeout(Some(within))
                .expect("a read timeout");
            write!(
                stream,
                "GET /branches HTTP/1.1\r\nHost: 127.0.0.1:{control}\r\nConnection: close\r\n\r\n"
            )
            .expect("write the request");
            let mut response = String::new();
            stream
                .read_to_string(&mut response)
                .expect("the control port answers rather than hanging");
            if !response.starts_with("HTTP/1.1 200") {
                return response;
            }
            assert!(
                Instant::now() < deadline,
                "the program never finished: the control port still serves"
            );
            thread::sleep(Duration::from_millis(50));
        }
    }
}

/// Spawn `program` under `--control` on a reserved port and wait for that port to
/// answer.
///
/// The wait is not optional: the program binds its control port during
/// compilation, so a request sent before then is refused rather than served.
pub(crate) fn launch_under_control(program: &str) -> Launched {
    launch_under_control_with(program, &[])
}

/// [`launch_under_control`], passing `extra` to the binary as well.
pub(crate) fn launch_under_control_with(program: &str, extra: &[String]) -> Launched {
    let control = reserve_test_port();
    let mut args = vec![format!("--control={control}")];
    args.extend_from_slice(extra);
    let spawned = launch_with(program, &args);

    let deadline = Instant::now() + Duration::from_secs(10);
    while std::net::TcpStream::connect(("127.0.0.1", control)).is_err() {
        assert!(Instant::now() < deadline, "control port never opened");
        thread::sleep(Duration::from_millis(50));
    }

    Launched { spawned, control }
}

/// Spawn `program` as the `cambra` binary with `args`, from a scratch directory
/// of its own.
pub(crate) fn launch_with(program: &str, args: &[String]) -> Spawned {
    use std::io::{BufRead, BufReader};
    use std::process::Stdio;

    // The process id keeps two test binaries apart, the counter two tests in one.
    static LAUNCHES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let launch = LAUNCHES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("cambra-live-{}-{launch}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let v1 = dir.join("v1.cambra");
    std::fs::write(&v1, program).expect("write v1");

    let mut program = RunningProgram {
        child: crate::it::cli::command()
            .args(args)
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

    Spawned {
        program,
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
    pub(crate) fn wait_for_exit(&mut self, within: Duration) {
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
        run std::http(port="{PORT}", method="POST", path="/bump") as http_resps
        http_resps_replies: Feed(String)
        reqs = http_resps::requests
        for r in reqs:
            n := n + "a"
            http_resps_replies << n + "\n"
        http_resps::respond(http_resps_replies)
    "#};

    /// `BUMP_OVER_SOURCE` with a different declared init, and nothing else
    /// changed — for the rule that a carried value wins over the init, which is
    /// only ever read on a fresh start.
    pub const BUMP_OVER_SOURCE_RESEEDED: &str = indoc! {r#"
        n := "seed"
        run std::http(port="{PORT}", method="POST", path="/bump") as http_resps
        http_resps_replies: Feed(String)
        reqs = http_resps::requests
        for r in reqs:
            n := n + "a"
            http_resps_replies << n + "\n"
        http_resps::respond(http_resps_replies)
    "#};

    /// A record-valued accumulator, and the same program with one field at
    /// another type — for the "records included" half of the retype refusal.
    /// Neither program can be written with the field at two types, so the change
    /// only exists between versions.
    pub const RECORD_ACCUMULATOR: &str = indoc! {r#"
        n := (a=0, b=1)
        run std::http(port="{PORT}", method="POST", path="/bump") as http_resps
        http_resps_replies: Feed(String)
        reqs = http_resps::requests
        for r in reqs:
            n := (a=n.a + 1, b=n.b)
            http_resps_replies << "ok\n"
        http_resps::respond(http_resps_replies)
    "#};

    pub const RECORD_ACCUMULATOR_RETYPED_FIELD: &str = indoc! {r#"
        n := (a=0, b="x")
        run std::http(port="{PORT}", method="POST", path="/bump") as http_resps
        http_resps_replies: Feed(String)
        reqs = http_resps::requests
        for r in reqs:
            n := (a=n.a + 1, b=n.b)
            http_resps_replies << "ok\n"
        http_resps::respond(http_resps_replies)
    "#};

    pub const BUMP_OVER_A_FIXED_LIST: &str = indoc! {r#"
        n := ""
        run std::http(port="{PORT}", method="POST", path="/bump") as http_resps
        http_resps_replies: Feed(String)
        reqs = http_resps::requests
        for x in ["y", "z"]:
            n := n + x
        for r in reqs:
            http_resps_replies << n + "\n"
        http_resps::respond(http_resps_replies)
    "#};

    pub const BUMP_OVER_A_MARKED_LIST: &str = indoc! {r#"
        n := ""
        run std::http(port="{PORT}", method="POST", path="/bump") as http_resps
        http_resps_replies: Feed(String)
        reqs = http_resps::requests
        for x in ["y", "z"]:
            n := n + x + "!"
        for r in reqs:
            http_resps_replies << n + "\n"
        http_resps::respond(http_resps_replies)
    "#};

    pub const BUMP_OVER_ANOTHER_FIXED_LIST: &str = indoc! {r#"
        n := ""
        run std::http(port="{PORT}", method="POST", path="/bump") as http_resps
        http_resps_replies: Feed(String)
        reqs = http_resps::requests
        for x in ["p", "q"]:
            n := n + x
        for r in reqs:
            http_resps_replies << n + "\n"
        http_resps::respond(http_resps_replies)
    "#};

    pub const GUESTBOOK_ADDS_ROUTE: &str = indoc! {r#"
        entries := ""

        run std::http(port="{PORT}", method="POST", path="/sign") as http_sign_resps
        http_sign_resps_replies: Feed(String)
        sign_reqs = http_sign_resps::requests
        run std::http(port="{PORT}", method="GET", path="/peek") as http_peek_resps
        http_peek_resps_replies: Feed(String)
        peek_reqs = http_peek_resps::requests
        run std::http(port="{PORT}", method="GET", path="/added") as http_added_resps
        http_added_resps_replies: Feed(String)
        added_reqs = http_added_resps::requests

        for entry in sign_reqs:
            entries := entries + entry + "\n"
            http_sign_resps_replies << entries

        for req in peek_reqs:
            http_peek_resps_replies << "peek\n"

        for req in added_reqs:
            http_added_resps_replies << "added\n"
        http_sign_resps::respond(http_sign_resps_replies)
        http_peek_resps::respond(http_peek_resps_replies)
        http_added_resps::respond(http_added_resps_replies)
    "#};

    pub const GUESTBOOK_DROPS_ROUTE: &str = indoc! {r#"
        entries := ""

        run std::http(port="{PORT}", method="POST", path="/sign") as http_sign_resps
        http_sign_resps_replies: Feed(String)
        sign_reqs = http_sign_resps::requests

        for entry in sign_reqs:
            entries := entries + entry + "\n"
            http_sign_resps_replies << entries
        http_sign_resps::respond(http_sign_resps_replies)
    "#};

    pub const GUESTBOOK_DROPS_STATE: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/sign") as http_sign_resps
        http_sign_resps_replies: Feed(String)
        sign_reqs = http_sign_resps::requests
        run std::http(port="{PORT}", method="GET", path="/peek") as http_peek_resps
        http_peek_resps_replies: Feed(String)
        peek_reqs = http_peek_resps::requests

        for entry in sign_reqs:
            http_sign_resps_replies << entry + "\n"

        for req in peek_reqs:
            http_peek_resps_replies << "peek\n"
        http_sign_resps::respond(http_sign_resps_replies)
        http_peek_resps::respond(http_peek_resps_replies)
    "#};

    pub const GUESTBOOK_RETYPES_STATE: &str = indoc! {r#"
        entries := 0

        run std::http(port="{PORT}", method="POST", path="/sign") as http_sign_resps
        http_sign_resps_replies: Feed(String)
        sign_reqs = http_sign_resps::requests
        run std::http(port="{PORT}", method="GET", path="/peek") as http_peek_resps
        http_peek_resps_replies: Feed(String)
        peek_reqs = http_peek_resps::requests

        for entry in sign_reqs:
            entries := entries + 1
            http_sign_resps_replies << "signed\n"

        for req in peek_reqs:
            http_peek_resps_replies << "peek\n"
        http_sign_resps::respond(http_sign_resps_replies)
        http_peek_resps::respond(http_peek_resps_replies)
    "#};

    pub const GUESTBOOK_RETYPES_STATE_ADDS_ROUTE: &str = indoc! {r#"
        entries := 0

        run std::http(port="{PORT}", method="POST", path="/sign") as http_sign_resps
        http_sign_resps_replies: Feed(String)
        sign_reqs = http_sign_resps::requests
        run std::http(port="{PORT}", method="GET", path="/peek") as http_peek_resps
        http_peek_resps_replies: Feed(String)
        peek_reqs = http_peek_resps::requests
        run std::http(port="{PORT}", method="GET", path="/added") as http_added_resps
        http_added_resps_replies: Feed(String)
        added_reqs = http_added_resps::requests

        for entry in sign_reqs:
            entries := entries + 1
            http_sign_resps_replies << "signed\n"

        for req in peek_reqs:
            http_peek_resps_replies << "peek\n"

        for req in added_reqs:
            http_added_resps_replies << "added\n"
        http_sign_resps::respond(http_sign_resps_replies)
        http_peek_resps::respond(http_peek_resps_replies)
        http_added_resps::respond(http_added_resps_replies)
    "#};

    pub const GUESTBOOK_STATELESS_EDIT: &str = indoc! {r#"
        entries := ""

        run std::http(port="{PORT}", method="POST", path="/sign") as http_sign_resps
        http_sign_resps_replies: Feed(String)
        sign_reqs = http_sign_resps::requests
        run std::http(port="{PORT}", method="GET", path="/peek") as http_peek_resps
        http_peek_resps_replies: Feed(String)
        peek_reqs = http_peek_resps::requests

        for entry in sign_reqs:
            entries := entries + entry + "\n"
            http_sign_resps_replies << entries

        for req in peek_reqs:
            http_peek_resps_replies << "peek edited\n"
        http_sign_resps::respond(http_sign_resps_replies)
        http_peek_resps::respond(http_peek_resps_replies)
    "#};

    pub const LATEST_WRITE: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/set") as http_set_resps
        http_set_resps_replies: Feed(String)
        set_reqs = http_set_resps::requests
        run std::http(port="{PORT}", method="GET", path="/get") as http_get_resps
        http_get_resps_replies: Feed(String)
        get_reqs = http_get_resps::requests

        latest: Mut(String, Txn) := "(none)"

        for msg in set_reqs:
            with begin():
                latest := msg
            http_set_resps_replies << "ok\n"

        for req in get_reqs:
            with begin():
                http_get_resps_replies << latest
        http_set_resps::respond(http_set_resps_replies)
        http_get_resps::respond(http_get_resps_replies)
    "#};

    /// [`LATEST_WRITE`] with `latest` retired and a new variable seeded from the
    /// value it held. The one program shape the `@LoadFrom` cases vary.
    pub const LATEST_WRITE_MIGRATED: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/set") as http_set_resps
        http_set_resps_replies: Feed(String)
        set_reqs = http_set_resps::requests
        run std::http(port="{PORT}", method="GET", path="/get") as http_get_resps
        http_get_resps_replies: Feed(String)
        get_reqs = http_get_resps::requests

        @LoadFrom(latest)
        held: String

        marked: Mut(String, Txn) := held + "!"

        for msg in set_reqs:
            with begin():
                marked := msg + "!"
            http_set_resps_replies << "ok\n"

        for req in get_reqs:
            with begin():
                http_get_resps_replies << marked
        http_set_resps::respond(http_set_resps_replies)
        http_get_resps::respond(http_get_resps_replies)
    "#};

    /// [`LATEST_WRITE_MIGRATED`] keeping `latest` as well — the declared-and-loaded
    /// case, where a version seeds a new variable from one it goes on holding.
    pub const LATEST_WRITE_MIGRATED_BESIDE: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/set") as http_set_resps
        http_set_resps_replies: Feed(String)
        set_reqs = http_set_resps::requests
        run std::http(port="{PORT}", method="GET", path="/get") as http_get_resps
        http_get_resps_replies: Feed(String)
        get_reqs = http_get_resps::requests

        latest: Mut(String, Txn) := "(none)"
        @LoadFrom(latest)
        held: String

        marked: Mut(String, Txn) := held + "!"

        for msg in set_reqs:
            with begin():
                latest := msg
            http_set_resps_replies << "ok\n"

        for req in get_reqs:
            with begin():
                http_get_resps_replies << latest + "/" + marked
        http_set_resps::respond(http_set_resps_replies)
        http_get_resps::respond(http_get_resps_replies)
    "#};

    /// [`LATEST_WRITE_MIGRATED`] loading a name no version ever declared.
    pub const LATEST_WRITE_LOADS_A_STRANGER: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/set") as http_set_resps
        http_set_resps_replies: Feed(String)
        set_reqs = http_set_resps::requests
        run std::http(port="{PORT}", method="GET", path="/get") as http_get_resps
        http_get_resps_replies: Feed(String)
        get_reqs = http_get_resps::requests

        @LoadFrom(nonesuch)
        held: String

        marked: Mut(String, Txn) := held + "!"

        for msg in set_reqs:
            with begin():
                marked := msg + "!"
            http_set_resps_replies << "ok\n"

        for req in get_reqs:
            with begin():
                http_get_resps_replies << marked
        http_set_resps::respond(http_set_resps_replies)
        http_get_resps::respond(http_get_resps_replies)
    "#};

    /// [`LATEST_WRITE_MIGRATED`] reading the loaded value as an `Int`, which is
    /// not what `latest` holds.
    pub const LATEST_WRITE_MIGRATED_RETYPED: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/set") as http_set_resps
        http_set_resps_replies: Feed(String)
        set_reqs = http_set_resps::requests
        run std::http(port="{PORT}", method="GET", path="/get") as http_get_resps
        http_get_resps_replies: Feed(String)
        get_reqs = http_get_resps::requests

        @LoadFrom(latest)
        held: Int

        marked: Mut(Int, Txn) := held + 1

        for msg in set_reqs:
            with begin():
                marked := marked + 1
            http_set_resps_replies << "ok\n"

        for req in get_reqs:
            with begin():
                http_get_resps_replies << "ok\n"
        http_set_resps::respond(http_set_resps_replies)
        http_get_resps::respond(http_get_resps_replies)
    "#};

    pub const LATEST_WRITE_WRITER_EDIT: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/set") as http_set_resps
        http_set_resps_replies: Feed(String)
        set_reqs = http_set_resps::requests
        run std::http(port="{PORT}", method="GET", path="/get") as http_get_resps
        http_get_resps_replies: Feed(String)
        get_reqs = http_get_resps::requests

        latest: Mut(String, Txn) := "(none)"

        for msg in set_reqs:
            with begin():
                latest := msg + "!"
            http_set_resps_replies << "ok\n"

        for req in get_reqs:
            with begin():
                http_get_resps_replies << latest
        http_set_resps::respond(http_set_resps_replies)
        http_get_resps::respond(http_get_resps_replies)
    "#};

    pub const ONE_STATEFUL_LOOP: &str = indoc! {r#"
        n := ""
        run std::http(port="{PORT}", method="POST", path="/p") as http_pr
        http_pr_replies: Feed(String)
        p = http_pr::requests
        run std::http(port="{PORT}", method="POST", path="/q") as http_qr
        http_qr_replies: Feed(String)
        q = http_qr::requests
        for x in p:
            n := n + "a"
            http_pr_replies << n + "\n"
        for y in q:
            http_qr_replies << "q\n"
        http_pr::respond(http_pr_replies)
        http_qr::respond(http_qr_replies)
    "#};

    pub const ONE_STATEFUL_LOOP_BOTH: &str = indoc! {r#"
        n := ""
        m := ""
        run std::http(port="{PORT}", method="POST", path="/p") as http_pr
        http_pr_replies: Feed(String)
        p = http_pr::requests
        run std::http(port="{PORT}", method="POST", path="/q") as http_qr
        http_qr_replies: Feed(String)
        q = http_qr::requests
        for x in p:
            n := n + "a"
            http_pr_replies << n + "\n"
        for y in q:
            m := m + "b"
            http_qr_replies << m + "\n"
        http_pr::respond(http_pr_replies)
        http_qr::respond(http_qr_replies)
    "#};

    pub const ONE_STATEFUL_LOOP_MOVED: &str = indoc! {r#"
        n := ""
        run std::http(port="{PORT}", method="POST", path="/p") as http_pr
        http_pr_replies: Feed(String)
        p = http_pr::requests
        run std::http(port="{PORT}", method="POST", path="/q") as http_qr
        http_qr_replies: Feed(String)
        q = http_qr::requests
        for x in p:
            http_pr_replies << "p\n"
        for y in q:
            n := n + "a"
            http_qr_replies << n + "\n"
        http_pr::respond(http_pr_replies)
        http_qr::respond(http_qr_replies)
    "#};

    pub const RUNNING_LOG: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/set") as http_set_resps
        http_set_resps_replies: Feed(String)
        set_reqs = http_set_resps::requests
        run std::http(port="{PORT}", method="GET", path="/get") as http_get_resps
        http_get_resps_replies: Feed(String)
        get_reqs = http_get_resps::requests

        log: Mut(String, Txn) := ""

        for msg in set_reqs:
            with begin():
                log := log + msg
            http_set_resps_replies << "ok\n"

        for req in get_reqs:
            with begin():
                http_get_resps_replies << log
        http_set_resps::respond(http_set_resps_replies)
        http_get_resps::respond(http_get_resps_replies)
    "#};

    pub const RUNNING_LOG_WRITER_EDIT: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/set") as http_set_resps
        http_set_resps_replies: Feed(String)
        set_reqs = http_set_resps::requests
        run std::http(port="{PORT}", method="GET", path="/get") as http_get_resps
        http_get_resps_replies: Feed(String)
        get_reqs = http_get_resps::requests

        log: Mut(String, Txn) := ""

        for msg in set_reqs:
            with begin():
                log := log + "-" + msg
            http_set_resps_replies << "ok\n"

        for req in get_reqs:
            with begin():
                http_get_resps_replies << log
        http_set_resps::respond(http_set_resps_replies)
        http_get_resps::respond(http_get_resps_replies)
    "#};

    pub const TWO_ACCUMULATORS: &str = indoc! {r#"
        left := ""
        right := ""

        run std::http(port="{PORT}", method="POST", path="/bump") as http_resps
        http_resps_replies: Feed(String)
        reqs = http_resps::requests

        for x in reqs:
            left := left + "a"
            right := right + "B"
            http_resps_replies << left + "|" + right + "\n"
        http_resps::respond(http_resps_replies)
    "#};

    pub const TWO_ACCUMULATORS_ADDED: &str = indoc! {r#"
        left := ""
        right := ""
        extra := ""

        run std::http(port="{PORT}", method="POST", path="/bump") as http_resps
        http_resps_replies: Feed(String)
        reqs = http_resps::requests

        for x in reqs:
            left := left + "a"
            right := right + "B"
            extra := extra + "c"
            http_resps_replies << left + "|" + right + "|" + extra + "\n"
        http_resps::respond(http_resps_replies)
    "#};

    pub const TWO_ACCUMULATORS_REORDERED: &str = indoc! {r#"
        right := ""
        left := ""

        run std::http(port="{PORT}", method="POST", path="/bump") as http_resps
        http_resps_replies: Feed(String)
        reqs = http_resps::requests

        for x in reqs:
            right := right + "B"
            left := left + "a"
            http_resps_replies << left + "|" + right + "\n"
        http_resps::respond(http_resps_replies)
    "#};

    pub const TWO_LOOPS: &str = indoc! {r#"
        a := ""
        b := ""

        run std::http(port="{PORT}", method="POST", path="/a") as http_a_resps
        http_a_resps_replies: Feed(String)
        a_reqs = http_a_resps::requests
        run std::http(port="{PORT}", method="POST", path="/b") as http_b_resps
        http_b_resps_replies: Feed(String)
        b_reqs = http_b_resps::requests

        for x in a_reqs:
            a := a + x + "\n"
            http_a_resps_replies << a

        for y in b_reqs:
            b := b + y + "\n"
            http_b_resps_replies << b
        http_a_resps::respond(http_a_resps_replies)
        http_b_resps::respond(http_b_resps_replies)
    "#};

    pub const TWO_LOOPS_ONE_EDITED: &str = indoc! {r#"
        a := ""
        b := ""

        run std::http(port="{PORT}", method="POST", path="/a") as http_a_resps
        http_a_resps_replies: Feed(String)
        a_reqs = http_a_resps::requests
        run std::http(port="{PORT}", method="POST", path="/b") as http_b_resps
        http_b_resps_replies: Feed(String)
        b_reqs = http_b_resps::requests

        for x in a_reqs:
            a := a + x + "\n"
            http_a_resps_replies << a

        for y in b_reqs:
            b := b + "* " + y + "\n"
            http_b_resps_replies << b
        http_a_resps::respond(http_a_resps_replies)
        http_b_resps::respond(http_b_resps_replies)
    "#};

    /// `TWO_LOOPS` with each loop reading the other's route, so both
    /// variables keep their values and continue on the source they moved to.
    pub const TWO_LOOPS_SWAPPED: &str = indoc! {r#"
        a := ""
        b := ""

        run std::http(port="{PORT}", method="POST", path="/a") as http_a_resps
        http_a_resps_replies: Feed(String)
        a_reqs = http_a_resps::requests
        run std::http(port="{PORT}", method="POST", path="/b") as http_b_resps
        http_b_resps_replies: Feed(String)
        b_reqs = http_b_resps::requests

        for y in b_reqs:
            a := a + y + "\n"
            http_b_resps_replies << a

        for x in a_reqs:
            b := b + x + "\n"
            http_a_resps_replies << b
        http_a_resps::respond(http_a_resps_replies)
        http_b_resps::respond(http_b_resps_replies)
    "#};

    pub const ONE_TRANSACTIONAL_LOOP: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/a") as http_ok_a
        http_ok_a_replies: Feed(String)
        set_a = http_ok_a::requests
        run std::http(port="{PORT}", method="POST", path="/b") as http_ok_b
        http_ok_b_replies: Feed(String)
        set_b = http_ok_b::requests
        run std::http(port="{PORT}", method="GET", path="/ga") as http_out_a
        http_out_a_replies: Feed(String)
        get_a = http_out_a::requests

        x: Mut(String, Txn) := ""

        for m in set_a:
            with begin():
                x := x + m
            http_ok_a_replies << "ok\n"

        for r in get_a:
            with begin():
                http_out_a_replies << x

        for m in set_b:
            http_ok_b_replies << "b\n"
        http_ok_a::respond(http_ok_a_replies)
        http_ok_b::respond(http_ok_b_replies)
        http_out_a::respond(http_out_a_replies)
    "#};

    pub const ONE_TRANSACTIONAL_LOOP_BOTH: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/a") as http_ok_a
        http_ok_a_replies: Feed(String)
        set_a = http_ok_a::requests
        run std::http(port="{PORT}", method="POST", path="/b") as http_ok_b
        http_ok_b_replies: Feed(String)
        set_b = http_ok_b::requests
        run std::http(port="{PORT}", method="GET", path="/ga") as http_out_a
        http_out_a_replies: Feed(String)
        get_a = http_out_a::requests
        run std::http(port="{PORT}", method="GET", path="/gb") as http_out_b
        http_out_b_replies: Feed(String)
        get_b = http_out_b::requests

        x: Mut(String, Txn) := ""
        y: Mut(String, Txn) := ""

        for m in set_a:
            with begin():
                x := x + m
            http_ok_a_replies << "ok\n"

        for r in get_a:
            with begin():
                http_out_a_replies << x

        for m in set_b:
            with begin():
                y := y + m
            http_ok_b_replies << "ok\n"

        for r in get_b:
            with begin():
                http_out_b_replies << y
        http_ok_a::respond(http_ok_a_replies)
        http_ok_b::respond(http_ok_b_replies)
        http_out_a::respond(http_out_a_replies)
        http_out_b::respond(http_out_b_replies)
    "#};

    pub const TWO_TRANSACTIONS: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/a") as http_ok_a
        http_ok_a_replies: Feed(String)
        set_a = http_ok_a::requests
        run std::http(port="{PORT}", method="POST", path="/b") as http_ok_b
        http_ok_b_replies: Feed(String)
        set_b = http_ok_b::requests
        run std::http(port="{PORT}", method="GET", path="/ga") as http_out_a
        http_out_a_replies: Feed(String)
        get_a = http_out_a::requests
        run std::http(port="{PORT}", method="GET", path="/gb") as http_out_b
        http_out_b_replies: Feed(String)
        get_b = http_out_b::requests

        x: Mut(String, Txn) := ""
        y: Mut(String, Txn) := ""

        for m in set_a:
            with begin():
                x := x + m
            http_ok_a_replies << "ok\n"

        for r in get_a:
            with begin():
                http_out_a_replies << x

        for m in set_b:
            with begin():
                y := y + m
            http_ok_b_replies << "ok\n"

        for r in get_b:
            with begin():
                http_out_b_replies << y
        http_ok_a::respond(http_ok_a_replies)
        http_ok_b::respond(http_ok_b_replies)
        http_out_a::respond(http_out_a_replies)
        http_out_b::respond(http_out_b_replies)
    "#};

    pub const TWO_TRANSACTIONS_SWAPPED: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/a") as http_ok_a
        http_ok_a_replies: Feed(String)
        set_a = http_ok_a::requests
        run std::http(port="{PORT}", method="POST", path="/b") as http_ok_b
        http_ok_b_replies: Feed(String)
        set_b = http_ok_b::requests
        run std::http(port="{PORT}", method="GET", path="/ga") as http_out_a
        http_out_a_replies: Feed(String)
        get_a = http_out_a::requests
        run std::http(port="{PORT}", method="GET", path="/gb") as http_out_b
        http_out_b_replies: Feed(String)
        get_b = http_out_b::requests

        x: Mut(String, Txn) := ""
        y: Mut(String, Txn) := ""

        for m in set_b:
            with begin():
                x := x + m
            http_ok_b_replies << "ok\n"

        for r in get_a:
            with begin():
                http_out_a_replies << x

        for m in set_a:
            with begin():
                y := y + m
            http_ok_a_replies << "ok\n"

        for r in get_b:
            with begin():
                http_out_b_replies << y
        http_ok_a::respond(http_ok_a_replies)
        http_ok_b::respond(http_ok_b_replies)
        http_out_a::respond(http_out_a_replies)
        http_out_b::respond(http_out_b_replies)
    "#};

    pub const TWO_TRANSACTIONS_ONE_WRITER_EDITED: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/a") as http_ok_a
        http_ok_a_replies: Feed(String)
        set_a = http_ok_a::requests
        run std::http(port="{PORT}", method="POST", path="/b") as http_ok_b
        http_ok_b_replies: Feed(String)
        set_b = http_ok_b::requests
        run std::http(port="{PORT}", method="GET", path="/ga") as http_out_a
        http_out_a_replies: Feed(String)
        get_a = http_out_a::requests
        run std::http(port="{PORT}", method="GET", path="/gb") as http_out_b
        http_out_b_replies: Feed(String)
        get_b = http_out_b::requests

        x: Mut(String, Txn) := ""
        y: Mut(String, Txn) := ""

        for m in set_a:
            with begin():
                x := x + "-" + m
            http_ok_a_replies << "ok\n"

        for r in get_a:
            with begin():
                http_out_a_replies << x

        for m in set_b:
            with begin():
                y := y + m
            http_ok_b_replies << "ok\n"

        for r in get_b:
            with begin():
                http_out_b_replies << y
        http_ok_a::respond(http_ok_a_replies)
        http_ok_b::respond(http_ok_b_replies)
        http_out_a::respond(http_out_a_replies)
        http_out_b::respond(http_out_b_replies)
    "#};

    /// A loop folding a view over its own request source: `seen` is a
    /// comprehension over `bump_reqs`, so its elements are gone once answered.
    /// The base for the two cases about a loop that cannot read its collection
    /// from the start.
    pub(crate) const VIEW_FOLD: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/bump") as http_bump_resps
        http_bump_resps_replies: Feed(String)
        bump_reqs = http_bump_resps::requests
        seen = [r + "!" for r in bump_reqs]
        n := ""
        for x in seen:
            n := n + x
            http_bump_resps_replies << n
        http_bump_resps::respond(http_bump_resps_replies)
    "#};

    /// [`VIEW_FOLD`] with `n` moved to a loop of its own and the `seen` loop
    /// carrying a new variable instead. The `seen` loop then carries nothing, so
    /// it would read `seen` from the beginning — which is the refusal.
    pub(crate) const VIEW_FOLD_REVARIABLED: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/bump") as http_bump_resps
        http_bump_resps_replies: Feed(String)
        bump_reqs = http_bump_resps::requests
        run std::http(port="{PORT}", method="POST", path="/tick") as http_tick_resps
        http_tick_resps_replies: Feed(String)
        tick_reqs = http_tick_resps::requests
        seen = [r + "!" for r in bump_reqs]
        m := ""
        for x in seen:
            m := m + x
            http_bump_resps_replies << m
        n := ""
        for z in tick_reqs:
            n := n + z
            http_tick_resps_replies << n
        http_bump_resps::respond(http_bump_resps_replies)
        http_tick_resps::respond(http_tick_resps_replies)
    "#};

    /// [`VIEW_FOLD`] plus a loop over a second route. The added loop reads a
    /// source rather than a collection, so it starts where that source is.
    pub(crate) const VIEW_FOLD_SECOND_ROUTE: &str = indoc! {r#"
        run std::http(port="{PORT}", method="POST", path="/bump") as http_bump_resps
        http_bump_resps_replies: Feed(String)
        bump_reqs = http_bump_resps::requests
        run std::http(port="{PORT}", method="POST", path="/tick") as http_tick_resps
        http_tick_resps_replies: Feed(String)
        tick_reqs = http_tick_resps::requests
        seen = [r + "!" for r in bump_reqs]
        n := ""
        for x in seen:
            n := n + x
            http_bump_resps_replies << n
        t := ""
        for z in tick_reqs:
            t := t + z
            http_tick_resps_replies << t
        http_bump_resps::respond(http_bump_resps_replies)
        http_tick_resps::respond(http_tick_resps_replies)
    "#};
}

/// [`LiveProgram`]'s calls that take a version, for a version that is one
/// file.
///
/// Every case writes a version as one program text. These build its one-file
/// [`LoadedProgram`], so a case passes the text as it reads.
pub(crate) trait OneFile: Sized {
    fn start_text(
        ctx: &mut GlobalContext,
        text: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<Self, Vec<CompileError>>;

    fn reload_text(
        &mut self,
        ctx: &mut GlobalContext,
        branch: &str,
        text: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<ReloadReport, BranchError>;

    fn diff_text(
        &self,
        ctx: &GlobalContext,
        branch: &str,
        text: &str,
        phase: Phase,
    ) -> Result<DiffReport, BranchError>;

    fn create_branch_text(
        &mut self,
        ctx: &mut GlobalContext,
        name: &str,
        parent: &str,
        text: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<Created, BranchError>;
}

impl OneFile for LiveProgram {
    fn start_text(
        ctx: &mut GlobalContext,
        text: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<Self, Vec<CompileError>> {
        LiveProgram::start(ctx, &LoadedProgram::test(text), main_consumer)
    }

    fn reload_text(
        &mut self,
        ctx: &mut GlobalContext,
        branch: &str,
        text: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<ReloadReport, BranchError> {
        self.reload(ctx, branch, &LoadedProgram::test(text), main_consumer)
    }

    fn diff_text(
        &self,
        ctx: &GlobalContext,
        branch: &str,
        text: &str,
        phase: Phase,
    ) -> Result<DiffReport, BranchError> {
        self.diff_against(ctx, branch, &LoadedProgram::test(text), phase)
    }

    fn create_branch_text(
        &mut self,
        ctx: &mut GlobalContext,
        name: &str,
        parent: &str,
        text: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<Created, BranchError> {
        self.create_branch(ctx, name, parent, &LoadedProgram::test(text), main_consumer)
    }
}

pub(crate) fn source(name: &str, port: u16) -> String {
    let text = match name {
        "guestbook" => include_str!("../../programs/hot_reload/program.cambra"),
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
        "guestbook-retypes-state-adds-route" => fixtures::GUESTBOOK_RETYPES_STATE_ADDS_ROUTE,
        "guestbook-stateful-edit" => include_str!("../../programs/hot_reload/reloaded.cambra"),
        "guestbook-stateless-edit" => fixtures::GUESTBOOK_STATELESS_EDIT,
        "latest-write" => fixtures::LATEST_WRITE,
        "latest-write-writer-edit" => fixtures::LATEST_WRITE_WRITER_EDIT,
        "latest-write-migrated" => fixtures::LATEST_WRITE_MIGRATED,
        "latest-write-migrated-beside" => fixtures::LATEST_WRITE_MIGRATED_BESIDE,
        "latest-write-migrated-retyped" => fixtures::LATEST_WRITE_MIGRATED_RETYPED,
        "latest-write-loads-a-stranger" => fixtures::LATEST_WRITE_LOADS_A_STRANGER,
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

/// Run `v1` over a live `source1()` of integers holding `before`, reload it to `v2`, then
/// deliver `after`, complete the source, and answer the program's integer value.
///
/// `before` sits at positions `0..`, and `after` at the positions following it. The source
/// calls `before` complete and stays live across the reload, so what the replacement is
/// offered is what the retired version's readers left unreleased.
pub(crate) fn int_value_across_a_reload_over_a_live_source(
    v1: &str,
    v2: &str,
    before: &[i64],
    after: &[i64],
) -> i64 {
    use std::{cell::RefCell, rc::Rc};

    use cambra::{
        ccl::load::LoadedProgram,
        ccl::{Type, context::GlobalContext},
        interpreter::{BaseType, ColumnValue, Extent, Predicate, TestDataSource, Tile, Value},
        live_program::{LiveProgram, MAIN_BRANCH},
    };

    use super::serving::no_main;

    let mut ctx = GlobalContext::default();
    let source = Rc::new(RefCell::new(TestDataSource::new(
        "source1",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    ctx.register_source(source.clone());
    let rows = |from: usize, values: &[i64]| -> Vec<(Value, Value)> {
        values
            .iter()
            .enumerate()
            .map(|(i, v)| (Value::uint_from_row(from + i), Value::Int(*v)))
            .collect()
    };
    let pull = |ctx: &mut GlobalContext, live: &mut LiveProgram| -> Tile {
        ctx.scheduler().check_for_notifications();
        let producer = live
            .main_producer_mut(MAIN_BRANCH)
            .expect("the program's value is pulled");
        producer.get(producer.tiling().universal_guard())
    };

    let mut live =
        LiveProgram::start(&mut ctx, &LoadedProgram::test(v1), &no_main).expect("v1 compiles");
    source.borrow_mut().add_data(&rows(0, before));
    source
        .borrow_mut()
        .set_yield_predicate(Predicate::at_or_below(Value::uint_from_row(
            before.len() - 1,
        )));
    for _ in 0..20 {
        pull(&mut ctx, &mut live);
    }
    live.reload(&mut ctx, MAIN_BRANCH, &LoadedProgram::test(v2), &no_main)
        .expect("v2 replaces v1");
    source.borrow_mut().add_data(&rows(before.len(), after));
    source.borrow_mut().set_yield_predicate(Predicate::True);
    for _ in 0..500 {
        let tile = pull(&mut ctx, &mut live);
        if tile.is_terminal() {
            let Tile::Scalar(ColumnValue::Ints(v)) = tile else {
                panic!("an integer value, got {tile:?}");
            };
            return v[0];
        }
    }
    panic!("the replacement never settled");
}
