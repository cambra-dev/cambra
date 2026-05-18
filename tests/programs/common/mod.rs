//! Shared helpers for the per-program integration tests under
//! `tests/programs/<name>/`.
//!
//! Each program directory holds a `program.cambra` source plus a `mod.rs`
//! that contains the program's `#[test]` function.  The test bodies are
//! concise because all of the pipeline plumbing, canonical-form rendering,
//! and HTTP client glue lives in here.
//!
//! ### Common patterns
//!
//! Scalar program (most demos):
//!
//! ```ignore
//! use super::common::expect_scalar;
//!
//! #[test]
//! fn sum() {
//!     expect_scalar(include_str!("program.cambra"), "10");
//! }
//! ```
//!
//! Program that hits a compile-time bug or missing feature:
//!
//! ```ignore
//! use super::common::expect_compile_error;
//!
//! #[test]
//! fn while_counter_currently_fails_at_lowering() {
//!     expect_compile_error(
//!         include_str!("program.cambra"),
//!         "Only assignment and function definition statements",
//!     );
//! }
//! ```
//!
//! Program that runs but returns the wrong answer (known-bug snapshot):
//!
//! ```ignore
//! use super::common::expect_scalar_currently_buggy;
//!
//! #[test]
//! fn filter_and_aggregate_currently_buggy() {
//!     // Should be 253; currently 345 because the if-clause is dropped
//!     // when the comprehension source is a let-bound list.
//!     expect_scalar_currently_buggy(include_str!("program.cambra"), "345");
//! }
//! ```
//!
//! Sink program (HTTP / long-lived):
//!
//! ```ignore
//! use super::common::{compile_sink, drive_until, free_port, http_get, http_post, wait_for_bind};
//!
//! #[test]
//! fn http_greeter() {
//!     let port = free_port();
//!     let source = include_str!("program.cambra").replace("{PORT}", &port.to_string());
//!     let mut ctx = compile_sink(&source);
//!     wait_for_bind();
//!     // …send requests on a background thread, drive_until the responses arrive…
//! }
//! ```

use std::{
    any::Any,
    cell::RefCell,
    io::{Read, Write},
    net::{TcpListener, TcpStream},
    panic::{self, AssertUnwindSafe},
    process::{Command, Stdio},
    rc::Rc,
    sync::mpsc,
    thread,
    time::{Duration, Instant},
};

use cambra::{
    ccl::context::{CompileResultExt, GlobalContext, compile_program},
    interpreter::{
        ColumnValue, Consumer, FuncBinding, Tile, Value, bindings_are_list,
        tile_operators::scalar_tile_to_column_value,
    },
};

// ---------------------------------------------------------------------------
// Scalar programs
// ---------------------------------------------------------------------------

/// Drive `source` through the full pipeline, render the result tile in
/// canonical form, and assert it equals `expected`.
///
/// `expected` is compared after stripping leading/trailing whitespace from
/// both sides so callers don't have to fuss with `\n`.
///
/// Canonical-form rules — see [`tile_to_canonical`] for the full spec; in
/// brief:
/// - Scalars: `10`, `"hello"`, `true`, `()`.
/// - Lists (sequential-UInt-domain functions): `Function [ a, b, c ]`.
/// - GroupBy-style maps: `Function [ k0 -> v0, k1 -> v1 ]`, sorted by key.
/// - Joins (Record-domain functions): `Function [ r0, r1, … ]`, sorted by
///   the codomain record's natural order (alphabetical fields).
pub fn expect_scalar(source: &str, expected: &str) {
    let tile = run_to_tile(source);
    let actual = tile_to_canonical(tile);
    assert_eq!(
        actual.trim(),
        expected.trim(),
        "\nscalar output mismatch\n  actual:   {actual}\n  expected: {expected}\n",
    );
}

/// Assert that the pipeline panics with a message containing `needle`.
///
/// Used for programs that exercise features we haven't shipped yet, or that
/// hit a known compiler bug at compile time.  The `needle` pins the specific
/// failure mode so an *unrelated* regression doesn't silently keep the test
/// green.  The test goes red the day the panic stops firing (because we
/// fixed the bug or finished the feature), at which point you replace
/// `expect_compile_error` with `expect_scalar`.
///
/// Fires for panics from any pipeline stage (lower, infer, lambda_elim,
/// operator_conversion, …) — not just lowering.
pub fn expect_compile_error(source: &str, needle: &str) {
    let result = panic::catch_unwind(AssertUnwindSafe(|| run_to_tile(source)));
    let payload = match result {
        Ok(_) => panic!(
            "expected compile_program to panic with substring {needle:?}; \
             program ran to completion"
        ),
        Err(payload) => payload,
    };
    let msg = panic_payload_to_string(&payload);
    assert!(
        msg.contains(needle),
        "expected panic to contain {needle:?}; got: {msg}",
    );
}

/// Assert that the program runs to completion but returns
/// `current_buggy_output` — i.e. the wrong answer, snapshot-style.
///
/// Used for programs that demonstrate a known bug where the natural form
/// compiles and runs but produces the wrong result.  Pinning the current
/// buggy output (rather than asserting it's "not the correct one") means
/// *any* change to the output — full or partial fix — turns the test red
/// and prompts an update.  The doc comment on the test function should say
/// what the *correct* output would be so the eventual fixer knows the
/// target.
pub fn expect_scalar_currently_buggy(source: &str, current_buggy_output: &str) {
    let tile = run_to_tile(source);
    let actual = tile_to_canonical(tile);
    assert_eq!(
        actual.trim(),
        current_buggy_output.trim(),
        "\nthe program's output changed.  If this is because the underlying bug was fixed, \
         update the test to use `expect_scalar` with the correct expected value.\n  actual:        {actual}\n  pinned (buggy): {current_buggy_output}\n",
    );
}

// ---------------------------------------------------------------------------
// Stdin-driven programs (subprocess)
// ---------------------------------------------------------------------------

/// Run a program file by spawning the `cambra` binary as a subprocess and
/// piping `stdin_input` into it; assert that the captured stdout contains
/// each substring in `expected_substrings`.
///
/// Used for programs that consume `stdin()` — the in-process
/// [`compile_program`] path can't easily inject stdin without replacing the
/// real `StdinDataSource`, which would dodge the very thing we're
/// demonstrating.  Subprocess execution drives the actual stdin file
/// descriptor.
///
/// `program_name` is the test-programs subdirectory name (e.g.
/// `"streaming_echo"`).  The binary path is resolved via
/// `CARGO_BIN_EXE_cambra`, which Cargo populates for integration tests.
///
/// Output verification is substring-based because the binary prints
/// `Got value: <Debug-formatted Tile>` for each scheduler tick; the final
/// tick contains the full result but parsing the multi-line Debug format
/// for exact equality would be brittle.  Substrings are precise enough to
/// detect regressions (a missing or misformatted line breaks the
/// assertion) without coupling to the Debug layout.
pub fn expect_stdin_program(program_name: &str, stdin_input: &str, expected_substrings: &[&str]) {
    let cambra = env!("CARGO_BIN_EXE_cambra");
    let manifest = env!("CARGO_MANIFEST_DIR");
    let program_path = format!("{manifest}/tests/programs/{program_name}/program.cambra");

    let mut child = Command::new(cambra)
        .arg(&program_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|e| panic!("failed to spawn cambra subprocess: {e}"));

    // Write all input and close stdin so the program sees EOF.  The drop
    // happens implicitly when `stdin` goes out of scope at end of block.
    {
        let mut stdin = child
            .stdin
            .take()
            .expect("subprocess has no stdin handle (Stdio::piped() should guarantee one)");
        stdin
            .write_all(stdin_input.as_bytes())
            .expect("failed to write to subprocess stdin");
    }

    let output = child
        .wait_with_output()
        .expect("failed to wait for cambra subprocess");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "cambra subprocess exited with status {:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        output.status,
    );

    for expected in expected_substrings {
        assert!(
            stdout.contains(expected),
            "expected stdout to contain {expected:?}\nfull stdout:\n{stdout}\nstderr:\n{stderr}",
        );
    }
}

// ---------------------------------------------------------------------------
// Sink programs (HTTP, etc.)
// ---------------------------------------------------------------------------

/// Compile `source` for a sink program and return the surrounding
/// [`GlobalContext`].  Sink programs (e.g. `http_serve`) have no `main`
/// output; their sinks bind their resources during `compile_program` and
/// then await scheduler ticks to dispatch values.
///
/// The caller must keep the returned context alive (and drive its scheduler
/// via [`drive_until`]) for the duration of the test — sinks are only
/// serviced while the scheduler is running.
pub fn compile_sink(source: &str) -> GlobalContext {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let _ = compile_program(&mut ctx, source, consumer).unwrap_or_render("<test>", source);
    ctx
}

/// Allocate a free TCP port by briefly binding to port 0 and reading the
/// OS-assigned address.  Used to populate the `{PORT}` placeholder in sink
/// programs so tests don't fight over a hard-coded port.
pub fn free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0")
        .expect("failed to bind ephemeral port")
        .local_addr()
        .expect("failed to read local addr")
        .port()
}

/// Sleep just long enough for `tiny_http` to have bound its listener after
/// `compile_program` returns.  Without this, the first request can race the
/// bind and ECONNREFUSED.
pub fn wait_for_bind() {
    thread::sleep(Duration::from_millis(50));
}

/// Send a raw HTTP/1.1 GET request and return the response body.  Uses a
/// plain `TcpStream` so we don't need an HTTP-client crate as a dev
/// dependency.
pub fn http_get(port: u16, path: &str) -> String {
    let request =
        format!("GET {path} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nConnection: close\r\n\r\n");
    raw_http(port, &request)
}

/// Send a raw HTTP/1.1 POST with `body` and return the response body.
pub fn http_post(port: u16, path: &str, body: &str) -> String {
    let request = format!(
        "POST {path} HTTP/1.1\r\n\
         Host: 127.0.0.1:{port}\r\n\
         Content-Length: {len}\r\n\
         Connection: close\r\n\
         \r\n\
         {body}",
        len = body.len(),
    );
    raw_http(port, &request)
}

fn raw_http(port: u16, request: &str) -> String {
    let mut stream =
        TcpStream::connect(format!("127.0.0.1:{port}")).expect("failed to connect to test server");
    stream
        .write_all(request.as_bytes())
        .expect("failed to write HTTP request");
    stream.flush().unwrap();
    let mut raw = String::new();
    stream
        .read_to_string(&mut raw)
        .expect("failed to read HTTP response");
    raw.split_once("\r\n\r\n")
        .map(|(_, body)| body.to_string())
        .unwrap_or_default()
}

/// Drive `ctx`'s scheduler on the current thread until `rx` delivers a
/// value or `timeout` elapses.
///
/// HTTP sink dispatch is handled automatically by `SinkConsumer` when the
/// scheduler notifies it; this function only needs to keep the scheduler
/// ticking while the request-sending thread runs.
pub fn drive_until<T>(ctx: &mut GlobalContext, rx: &mpsc::Receiver<T>, timeout: Duration) -> T {
    let deadline = Instant::now() + timeout;
    loop {
        ctx.scheduler().check_for_notifications();
        if let Ok(value) = rx.try_recv() {
            return value;
        }
        assert!(
            Instant::now() < deadline,
            "timed out after {timeout:?} waiting for sink response",
        );
        thread::sleep(Duration::from_millis(10));
    }
}

// ---------------------------------------------------------------------------
// Pipeline + canonical-form rendering
// ---------------------------------------------------------------------------

/// Drive `source` through the full pipeline and return the compacted
/// `main`-output [`Tile`].  Panics if the program has no `main` output
/// (e.g. a sink-only program — those use [`compile_sink`] instead).
fn run_to_tile(source: &str) -> Tile {
    let mut ctx = GlobalContext::default();
    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });
    let mut compiled =
        compile_program(&mut ctx, source, consumer).unwrap_or_render("<test>", source);
    ctx.scheduler().check_for_notifications();
    assert!(
        *notified.borrow(),
        "expected consumer notification after compile_program"
    );
    let producer = compiled
        .main_mut()
        .and_then(|o| o.producer.as_mut())
        .expect("program has no `main` output — use `compile_sink` for sink programs");
    let mut result = producer.tiling().empty_tile();
    for _ in 0..100 {
        result = producer.get(producer.tiling().universal_guard());
        if result.is_terminal() {
            break;
        }
        ctx.scheduler().check_for_notifications();
    }

    result.compact();
    result
}

/// Render a finished top-level [`Tile`] as the canonical string we diff
/// against in test bodies.  Mirrors the [`std::fmt::Display`] impl on
/// [`Value`] but imposes a stable ordering for outputs whose physical layout
/// is non-deterministic (GroupBy, join cross-products).
///
/// - `Tile::Scalar` → the scalar's `Display`.
/// - `Tile::SealedFunction` with a scalar or record codomain →
///   `Function [ … ]`.  The list contents depend on the domain shape:
///   - Sequential UInt domain (plain list): `[v0, v1, …]` in domain order.
///   - Scalar non-sequential domain (GroupBy key column): `[k -> v, …]`
///     sorted by key.  GroupBy emits in HashMap iteration order, which
///     varies run-to-run.
///   - Record domain (synthetic join cross-product index, opaque to the
///     user): `[v0, v1, …]` sorted by codomain value.
///
/// Other tile shapes (`CurriedFunction`, `Aggregation`, deeply-nested
/// codomains) panic; extend this function when a new program needs a new
/// shape.
pub fn tile_to_canonical(tile: Tile) -> String {
    match tile {
        Tile::Scalar(cv) => {
            let v = cv
                .as_single()
                .unwrap_or_else(|| panic!("scalar tile must hold exactly one element, got {cv:?}"));
            format!("{v}")
        }
        Tile::SealedFunction {
            domain, codomain, ..
        } => {
            // `scalar_tile_to_column_value` handles both `Tile::Scalar` and
            // `Tile::Record` codomains; deeper nesting panics, which is the
            // signal to extend the harness.
            let codomain_cv = scalar_tile_to_column_value(*codomain);
            let n = domain.len();
            assert_eq!(
                n,
                codomain_cv.len(),
                "domain/codomain length mismatch in result tile"
            );
            let mut bindings: Vec<FuncBinding> = (0..n)
                .map(|i| FuncBinding {
                    input: domain.index_at(i),
                    output: codomain_cv.index_at(i),
                })
                .collect();

            let domain_is_opaque = matches!(domain, ColumnValue::Records(_));
            if domain_is_opaque {
                // Join output: drop the synthetic Record key, sort codomain
                // values for stability, and present as a sequential list.
                bindings.sort_by(|a, b| {
                    a.output
                        .partial_cmp(&b.output)
                        .unwrap_or(std::cmp::Ordering::Equal)
                });
                let list_bindings: Vec<FuncBinding> = bindings
                    .into_iter()
                    .enumerate()
                    .map(|(i, b)| FuncBinding {
                        input: Value::UInt(i),
                        output: b.output,
                    })
                    .collect();
                return format!("{}", Value::Function(list_bindings));
            }

            // GroupBy emits keys in HashMap iteration order; sort by key for
            // determinism.  Sequential-index lists are detected by
            // `bindings_are_list` and left alone.
            if !bindings_are_list(&bindings) {
                bindings.sort_by(|a, b| {
                    a.input
                        .partial_cmp(&b.input)
                        .unwrap_or(std::cmp::Ordering::Equal)
                });
            }
            format!("{}", Value::Function(bindings))
        }
        other => panic!("result tile shape not yet supported by the programs harness: {other:?}"),
    }
}

/// Extract a readable string from a `catch_unwind` payload.  Most compiler
/// panics carry `String` or `&'static str`; anything else falls back to a
/// placeholder so the test doesn't lose its diagnostic.
fn panic_payload_to_string(payload: &Box<dyn Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else if let Some(s) = payload.downcast_ref::<&'static str>() {
        s.to_string()
    } else {
        "<non-string panic payload>".to_string()
    }
}
