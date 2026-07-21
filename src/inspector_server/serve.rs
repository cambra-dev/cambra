//! The inspector's data endpoints: a read-only `tiny_http` server that answers
//! with JSON and never with a page. What a user looks at is the frontend, which
//! fetches these two routes.
//!
//! One **statically compiled** program is served. `code` is compiled once at
//! startup and the response bodies are rendered then and reused for every
//! request, so there is no per-request recompilation, no mutation endpoint, and
//! no live ticks.
//!
//! This is a sibling of [`crate::web_inspector`]'s internal dev dashboard, not
//! an extension of it: that one serves live runtime state on a background
//! thread; this one serves the read-only payload, one pane per pipeline stage.
//! They share only the `tiny_http` idiom.
//!
//! # Routes
//!
//! - `GET /api/snapshot` — the [`snapshot_json`](super::snapshot_json) body on a
//!   successful compile; a **degraded** JSON body on compile failure (see below).
//!   `application/json`.
//! - `GET /api/diagnostics` — [`diagnostics_body`]
//!   (`{"diagnostics":[]}` on success, structured diagnostics on failure).
//!   `application/json`.
//! - `GET /` and `GET /index.html` — the CodeMirror frontend: the built,
//!   self-contained `cambra-inspector/web/dist/index.html` bundle, which
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

use std::io;

use crate::ccl::context::{GlobalContext, compile_program};
use crate::inspector_model::{Diagnostic, InspectorPayload, diagnostics_from_compile_errors};
use crate::interpreter::Consumer;

use super::{snapshot_json, snapshot_json_pretty};

/// The CodeMirror frontend, embedded at compile time. This is the built,
/// self-contained single-file bundle (`cambra-inspector/web/dist/index.html`,
/// produced by `npm run build`), committed to the repo so `cargo build` needs
/// no Node toolchain (R7).
///
/// The path reaches out of `src/` because the frontend is a sibling directory
/// rather than a workspace member: `cambra-inspector/` holds the TypeScript
/// project, and this is the one place the Rust build reads from it.
const INDEX_HTML: &str = include_str!("../../cambra-inspector/web/dist/index.html");

/// The pre-rendered response bodies for the one static program.
///
/// Built once by [`build_bodies`] and served verbatim per request.
struct Bodies {
    snapshot: String,
    diagnostics: String,
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
            snapshot: snapshot_json(&compiled, name),
            diagnostics: diagnostics_body(&[]),
        },
        Err(errors) => {
            let diagnostics = diagnostics_from_compile_errors(&errors);
            Bodies {
                snapshot: degraded_snapshot_json(name, code, diagnostics.clone()),
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
    let bodies = build_bodies(code, name);
    let server = tiny_http::Server::http(format!("127.0.0.1:{port}"))
        .map_err(|e| io::Error::other(e.to_string()))?;
    // Names the scheme and says the server holds the terminal: this call never
    // returns, and `https://` to a plain-HTTP port fails the handshake and
    // renders as a blank page with nothing logged here.
    eprintln!("cambra: inspecting {name} at http://localhost:{port} — Ctrl+C to stop");

    for request in server.incoming_requests() {
        // `bodies` and `INDEX_HTML` both outlive the loop, so a response
        // borrows: the snapshot is megabytes on a large program and the bundle
        // is a quarter of one, and every request would otherwise copy it.
        let (body, status, header) = match request.url() {
            "/api/snapshot" => (bodies.snapshot.as_bytes(), 200, json_header()),
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
            eprintln!("cambra-inspector: responding failed: {e}");
        }
    }
    Ok(())
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
        let v: Value = serde_json::from_str(&bodies.snapshot).expect("valid JSON");

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
        let v: Value = serde_json::from_str(&bodies.snapshot).expect("valid JSON");

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
        let bad_snap: Value = serde_json::from_str(&bad.snapshot).expect("valid JSON");
        assert_eq!(
            bad_diag["diagnostics"], bad_snap["diagnostics"],
            "the degraded snapshot's diagnostics equal the diagnostics endpoint's"
        );
    }
}
