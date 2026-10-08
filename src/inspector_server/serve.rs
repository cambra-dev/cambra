//! The inspector's endpoints: a read-only `tiny_http` server for the frontend,
//! the static JSON bodies it fetches, and the websocket carrying a run's probe
//! frames.
//!
//! One program is served, and its response bodies are rendered ahead of the
//! requests that read them. [`serve`] compiles `code` itself and renders once;
//! [`serve_compiled`] takes the compile a driver is about to run, and hands back
//! a [`ServedSnapshot`] the driver replaces when a reload installs another
//! version. There is no per-request recompilation and no mutation endpoint.
//!
//! # Routes
//!
//! - `GET /api/snapshot` — the [`snapshot_json`](super::snapshot_json) body on a
//!   successful compile; a **degraded** JSON body on compile failure (see below).
//!   `application/json`.
//! - `GET /api/diagnostics` — [`diagnostics_body`]
//!   (`{"diagnostics":[]}` on success, structured diagnostics on failure).
//!   `application/json`.
//! - `GET /api/live` — a websocket upgrade handled by
//!   [`LiveServer::accept`]; it carries the probe frames a driver publishes
//!   through the [`LiveChannel`], and nothing under [`serve`], which runs no
//!   program.
//! - `GET /` and `GET /index.html` — the CodeMirror frontend: the built,
//!   self-contained `web/dist/index.html` bundle, which
//!   fetches `/api/snapshot` and renders the source + IR tree. `text/html`.
//! - anything else — `404 Not Found`.
//!
//! Both `/api` bodies come from [`build_bodies`]' single compile, so the
//! diagnostics the two routes report can never disagree.
//!
//! # Transport decision: snapshot degrades on failure
//!
//! `/api/snapshot` does **not** error when the program fails to compile. There is
//! no `CompiledProgram` to build a real snapshot from, but the frontend still
//! needs the source text (to render the editor) and the diagnostics (to draw the
//! squiggles). So a failed compile yields a *degraded* snapshot: the real
//! `source` + the same `diagnostics` as `/api/diagnostics`, with empty
//! `panes`/indices and `meta.payloadKind: "failed"`. This way a single `GET
//! /api/snapshot` always yields source + diagnostics whether or not the program
//! type-checks — the frontend never has to branch its initial fetch on compile
//! success.

use std::sync::{Arc, RwLock};
use std::{io, thread};

use crate::ccl::context::{CompiledProgram, GlobalContext, compile_program};
use crate::inspector_model::{Diagnostic, InspectorPayload, diagnostics_from_compile_errors};
use crate::inspector_server::live::{LIVE_PATH, LiveChannel, LiveServer};
use crate::interpreter::Consumer;

use super::{snapshot_json, snapshot_json_at_version, snapshot_json_pretty};

/// The CodeMirror frontend, embedded at compile time. This is the built,
/// self-contained single-file bundle (`web/dist/index.html`,
/// produced by `npm run build`), committed to the repo so `cargo build` needs
/// no Node toolchain (R7).
///
/// The path reaches out of `src/` because the frontend is a sibling directory:
/// `web/` holds the TypeScript project, the way `formal/` holds the Lean model,
/// and this is the one place the Rust build reads from it.
const INDEX_HTML: &str = include_str!("../../web/dist/index.html");

/// The pre-rendered response bodies for the one program served.
///
/// Rendered ahead of the requests and served verbatim per request. Only the
/// snapshot is ever replaced, by a [`ServedSnapshot`]: a version a reload
/// installs has compiled, so its diagnostics body is the same empty one.
struct Bodies {
    snapshot: ServedSnapshot,
    diagnostics: String,
}

/// The `/api/snapshot` body being served, which the driver replaces when a
/// reload installs a new version of `main`.
///
/// A request holds the read side for its whole response, so it finishes against
/// the body it started on rather than seeing parts of two. The snapshot is
/// megabytes on a large program, and holding the guard is what spares every
/// request a copy of it.
#[derive(Clone)]
pub struct ServedSnapshot(Arc<RwLock<String>>);

impl ServedSnapshot {
    fn new(snapshot: String) -> Self {
        Self(Arc::new(RwLock::new(snapshot)))
    }

    /// The body being served, held for as long as the guard lives.
    fn read(&self) -> std::sync::RwLockReadGuard<'_, String> {
        self.0.read().expect("served snapshot lock")
    }

    /// Serve `compiled`, running as `main`'s version `version`, from now on.
    pub fn replace(&self, compiled: &CompiledProgram, name: &str, version: u64) {
        let snapshot = snapshot_json_at_version(compiled, name, version);
        *self.0.write().expect("served snapshot lock") = snapshot;
    }
}

/// Compile `code` **once** and render both the `/api/snapshot` and
/// `/api/diagnostics` bodies from that single result, so the two can never
/// disagree. On compile failure the snapshot body is the degraded form (see the
/// module docs) and the diagnostics body carries the same structured array.
/// The compile cost is paid once at startup, not per request.
fn build_bodies(code: &str, name: &str) -> Bodies {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    match compile_program(&mut ctx, code, consumer) {
        Ok(compiled) => Bodies {
            snapshot: ServedSnapshot::new(snapshot_json(&compiled, name)),
            diagnostics: diagnostics_body(&[]),
        },
        Err(errors) => {
            let diagnostics = diagnostics_from_compile_errors(&errors);
            Bodies {
                snapshot: ServedSnapshot::new(degraded_snapshot_json(
                    name,
                    code,
                    diagnostics.clone(),
                )),
                diagnostics: diagnostics_body(&diagnostics),
            }
        }
    }
}

/// The `{"diagnostics":[...]}` body — the same envelope the standalone
/// [`diagnose_json`](crate::diagnose_json) entry produces, built here directly
/// from the diagnostics we already hold (no recompile).
fn diagnostics_body(diagnostics: &[Diagnostic]) -> String {
    serde_json::to_string(&serde_json::json!({ "diagnostics": diagnostics }))
        .expect("diagnostics payload serializes")
}

/// The degraded `/api/snapshot` body for a program that failed to compile:
/// source text + diagnostics, no IR. Built from the same
/// [`InspectorPayload`](crate::inspector_model::InspectorPayload) type as the
/// success path (via [`InspectorPayload::degraded`]), so the two shapes cannot
/// drift; the frontend still renders the editor + squiggles from it.
fn degraded_snapshot_json(name: &str, code: &str, diagnostics: Vec<Diagnostic>) -> String {
    serde_json::to_string(&InspectorPayload::degraded(name, code, diagnostics))
        .expect("degraded snapshot payload serializes")
}

/// Compile `code` once and return the pretty-printed `/api/snapshot` body —
/// what `--dump-snapshot` prints, and therefore the exact bytes of the
/// committed golden fixtures (see [`super::snapshot_json_pretty`] for why the
/// binary owns this format). The degraded form (source + diagnostics, no panes)
/// on a compile failure, as the route serves.
///
/// One-shot and exits: this regenerates the frontend's golden test fixtures
/// **without** standing up the never-exiting HTTP server (see
/// `web/src/__fixtures__/`). The HTTP route keeps the compact form.
pub fn snapshot_body_pretty(code: &str, name: &str) -> String {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    match compile_program(&mut ctx, code, consumer) {
        Ok(compiled) => snapshot_json_pretty(&compiled, name),
        Err(errors) => serde_json::to_string_pretty(&InspectorPayload::degraded(
            name,
            code,
            diagnostics_from_compile_errors(&errors),
        ))
        .expect("degraded snapshot payload serializes"),
    }
}

/// The 404 body, as bytes so it types the same as a served body.
const NOT_FOUND: &[u8] = b"Not Found";

fn json_header() -> tiny_http::Header {
    "Content-Type: application/json"
        .parse()
        .expect("static header parses")
}

fn html_header() -> tiny_http::Header {
    "Content-Type: text/html; charset=utf-8"
        .parse()
        .expect("static header parses")
}

fn text_header() -> tiny_http::Header {
    "Content-Type: text/plain; charset=utf-8"
        .parse()
        .expect("static header parses")
}

/// Compile `code` once and serve it over HTTP on `127.0.0.1:port` until the
/// process is killed. Blocks the calling thread (this is the binary's main
/// loop).
///
/// Loopback, not `0.0.0.0`: the payload is the user's source text and the whole
/// compiler IR for it, and this is a local development tool. Reaching it from
/// another host is a port-forward.
pub fn serve(code: &str, name: &str, port: u16) -> io::Result<()> {
    // Started even without a program running: the route completes its handshake
    // and sends nothing, because nothing publishes until a run does.
    let live = LiveServer::start();
    let server = bind(name, port)?;
    serve_bodies(&server, build_bodies(code, name), &live);
    Ok(())
}

/// Serve an already-compiled program on a background thread, and return the
/// channel a driver publishes through and the snapshot it replaces.
///
/// One compile feeds both the payload and the run: `NodeId`s come from a
/// process-global counter, so compiling a second time for the payload would
/// name different nodes than the graph being driven, and a click in a pane
/// would resolve to a producer that does not exist.
///
/// `compiled` runs as `main`'s version `version`, which the payload and every
/// frame are stamped with. A reload that installs another version is followed
/// by the driver, through [`ServedSnapshot::replace`] and [`LiveChannel::follow`];
/// see `src/inspector_model/design.md`, "A reload of main is followed".
///
/// The port is bound before the server thread starts, so a port already in use
/// is this call's `Err` rather than a run with no server behind it. The server
/// thread is detached, and outlives this call by design — a run finishes long
/// before a reader is done looking at it, which is why the binary parks
/// afterwards.
pub fn serve_compiled(
    compiled: &CompiledProgram,
    name: &str,
    port: u16,
    version: u64,
) -> io::Result<(LiveChannel, ServedSnapshot)> {
    let live = LiveServer::start();
    let channel = live.channel();
    channel.follow(version);
    let snapshot = ServedSnapshot::new(snapshot_json_at_version(compiled, name, version));
    let bodies = Bodies {
        snapshot: snapshot.clone(),
        diagnostics: diagnostics_body(&[]),
    };
    let server = bind(name, port)?;
    thread::Builder::new()
        .name("cambra-inspector".to_string())
        .spawn(move || serve_bodies(&server, bodies, &live))
        .map_err(io::Error::other)?;
    Ok((channel, snapshot))
}

/// The path a request URL routes on: the URL without its query string, so a
/// cache-busting `?t=…` reaches the same route.
fn route(url: &str) -> &str {
    url.split_once('?').map_or(url, |(path, _)| path)
}

/// Bind the inspector's port on loopback, and say where to look.
fn bind(name: &str, port: u16) -> io::Result<tiny_http::Server> {
    let server = tiny_http::Server::http(format!("127.0.0.1:{port}"))
        .map_err(|e| io::Error::other(e.to_string()))?;
    // Names the scheme and says where to look: `https://` to a plain-HTTP port
    // fails the handshake and renders as a blank page with nothing logged here.
    eprintln!("cambra: inspecting {name} at http://localhost:{port} — Ctrl+C to stop");
    Ok(server)
}

/// Answer requests on `server` against pre-rendered bodies until the process
/// is killed.
fn serve_bodies(server: &tiny_http::Server, bodies: Bodies, live: &LiveServer) {
    for request in server.incoming_requests() {
        // The live route takes the socket rather than answering on it, so it is
        // matched before the bodies below, which respond and drop.
        if route(request.url()) == LIVE_PATH {
            if let Err(e) = live.accept(request) {
                eprintln!("cambra: live upgrade failed: {e}");
            }
            continue;
        }
        // `bodies` and `INDEX_HTML` both outlive the loop, so a response
        // borrows: the snapshot is megabytes on a large program and the bundle
        // is a quarter of one, and every request would otherwise copy it. The
        // snapshot's read guard is held until the response is written.
        let snapshot = bodies.snapshot.read();
        let (body, status, header) = match route(request.url()) {
            "/api/snapshot" => (snapshot.as_bytes(), 200, json_header()),
            "/api/diagnostics" => (bodies.diagnostics.as_bytes(), 200, json_header()),
            "/" | "/index.html" => (INDEX_HTML.as_bytes(), 200, html_header()),
            _ => (NOT_FOUND, 404, text_header()),
        };
        let response = tiny_http::Response::new(
            tiny_http::StatusCode(status),
            vec![header],
            body,
            Some(body.len()),
            None,
        );
        if let Err(e) = request.respond(response) {
            // A client that hung up mid-response is routine; the next request is
            // unaffected, so this reports rather than stops.
            eprintln!("cambra: responding failed: {e}");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inspector_server::wire_check::{
        assert_degraded_snapshot_shape, assert_snapshot_shape,
    };
    use serde_json::Value;

    /// A valid program's snapshot body is the full payload: a node table per
    /// pane whose nodes carry their source spans, empty `diagnostics`, and
    /// `meta.payloadKind: "program"`. The per-pane contract is pinned by
    /// [`assert_snapshot_shape`].
    #[test]
    fn snapshot_body_success_carries_a_node_table_per_pane() {
        let bodies = build_bodies("1 + 2\n", "prog.chl");
        let v: Value = serde_json::from_str(&bodies.snapshot.read()).expect("valid JSON");

        assert_snapshot_shape(&v);
        let anchor = v["panes"]
            .as_array()
            .expect("panes is an array")
            .iter()
            .find(|s| s["id"] == "post-inference")
            .expect("the post-inference pane is present");
        assert!(
            !anchor["nodes"].as_array().expect("array").is_empty(),
            "the post-inference pane carries a node table"
        );
        assert!(
            anchor["nodes"]
                .as_array()
                .expect("array")
                .iter()
                .any(|n| !n["spans"].as_array().expect("spans is an array").is_empty()),
            "the post-inference pane's nodes carry source spans"
        );
        assert_eq!(v["meta"]["payloadKind"], "program");
        assert!(
            v["diagnostics"].as_array().expect("array").is_empty(),
            "a clean compile has no diagnostics"
        );
        assert_eq!(v["source"]["name"], "prog.chl");
    }

    /// A type-error program's snapshot body degrades: empty `panes`, non-empty
    /// `diagnostics`, `meta.payloadKind: "failed"` — but source text is
    /// preserved so the frontend can still render the editor + squiggles. The
    /// top-level `ir`/`spanIndex` are retired (their absence is pinned by
    /// [`assert_degraded_snapshot_shape`]).
    #[test]
    fn snapshot_body_failure_degrades() {
        let code = "1 and 2\n";
        let bodies = build_bodies(code, "bad.chl");
        let v: Value = serde_json::from_str(&bodies.snapshot.read()).expect("valid JSON");

        assert_degraded_snapshot_shape(&v);
        assert!(v["panes"].as_array().expect("array").is_empty());
        assert!(v["definitions"].as_array().expect("array").is_empty());
        assert_eq!(v["meta"]["payloadKind"], "failed");
        assert_eq!(v["meta"]["schema"], 1);

        // source preserved.
        assert_eq!(v["source"]["name"], "bad.chl");
        assert_eq!(v["source"]["text"], code);

        // diagnostics present and structured.
        let diags = v["diagnostics"].as_array().expect("array");
        assert!(!diags.is_empty(), "a type error degrades with diagnostics");
        assert!(diags.iter().any(|d| d["stage"] == "infer"));
    }

    /// The diagnostics body matches the standalone endpoint in both branches:
    /// empty on success, the same structured array on failure as the degraded
    /// snapshot carries.
    #[test]
    fn diagnostics_body_matches_snapshot_diagnostics() {
        let ok = build_bodies("1 + 2\n", "ok.chl");
        let ok_diag: Value = serde_json::from_str(&ok.diagnostics).expect("valid JSON");
        assert!(
            ok_diag["diagnostics"].as_array().expect("array").is_empty(),
            "clean compile -> empty diagnostics endpoint"
        );

        let bad = build_bodies("1 and 2\n", "bad.chl");
        let bad_diag: Value = serde_json::from_str(&bad.diagnostics).expect("valid JSON");
        let bad_snap: Value = serde_json::from_str(&bad.snapshot.read()).expect("valid JSON");
        assert_eq!(
            bad_diag["diagnostics"], bad_snap["diagnostics"],
            "the degraded snapshot's diagnostics equal the diagnostics endpoint's"
        );
    }

    #[test]
    fn a_query_string_does_not_change_the_route() {
        assert_eq!(route("/api/live?t=1"), LIVE_PATH);
        assert_eq!(route("/api/snapshot"), "/api/snapshot");
        assert_eq!(route("/?"), "/");
    }

    /// A port already in use is `serve_compiled`'s own `Err`: the bind happens
    /// before the server thread starts, so the caller can refuse to run.
    #[test]
    fn a_taken_port_is_the_callers_error() {
        let taken = std::net::TcpListener::bind("127.0.0.1:0").expect("a free port");
        let port = taken.local_addr().expect("bound").port();
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let Ok(compiled) = compile_program(&mut ctx, "1 + 2\n", consumer) else {
            panic!("the program compiles");
        };
        assert!(serve_compiled(&compiled, "prog.chl", port, 1).is_err());
    }
}
