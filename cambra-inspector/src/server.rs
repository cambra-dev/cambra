//! The user-facing inspector HTTP server.
//!
//! A small, read-only `tiny_http` server that serves a single, **statically
//! compiled** program: `code` is compiled exactly *once* at startup and the
//! response bodies are rendered then and reused for every request. There is no
//! per-request recompilation, no mutation endpoint, no live ticks — M1 is "the
//! program, no execution".
//!
//! This is a *sibling* of [`crate::web_inspector`](cambra)'s internal dev
//! dashboard, not an extension of it: that one serves live runtime state on a
//! background thread; this one serves the read-only post-inference snapshot to
//! the embedded CodeMirror frontend. They share only the `tiny_http` idiom.
//!
//! # Routes
//!
//! - `GET /api/snapshot` — the [`snapshot_json`](crate::snapshot_json) body on a
//!   successful compile; a **degraded** JSON body on compile failure (see below).
//!   `application/json`.
//! - `GET /api/diagnostics` — the [`diagnose_json`](crate::diagnose_json) body
//!   (`{"diagnostics":[]}` on success, structured diagnostics on failure).
//!   `application/json`.
//! - `GET /` and `GET /index.html` — the CodeMirror frontend: the built,
//!   self-contained `web/dist/index.html` bundle, which fetches `/api/snapshot`
//!   and renders the source + IR tree. `text/html`.
//! - anything else — `404 Not Found`.
//!
//! # Transport decision: snapshot degrades on failure
//!
//! `/api/snapshot` does **not** error when the program fails to compile. There is
//! no `CompiledProgram` to build a real snapshot from, but the frontend still
//! needs the source text (to render the editor) and the diagnostics (to draw the
//! squiggles). So a failed compile yields a *degraded* snapshot: the real
//! `source` + the same `diagnostics` as `/api/diagnostics`, with empty
//! `stages`/indices and `meta.snapshotKind: "failed"`. This way a single `GET
//! /api/snapshot` always yields source + diagnostics whether or not the program
//! type-checks — the frontend never has to branch its initial fetch on compile
//! success.

use std::io;

use cambra::ccl::context::{GlobalContext, compile_program};
use cambra::inspector_model::{Diagnostic, SnapshotPayload, diagnostics_from_compile_errors};
use cambra::interpreter::Consumer;

use crate::snapshot_json;

/// The CodeMirror frontend, embedded at compile time. This is the built,
/// self-contained single-file bundle (`web/dist/index.html`, produced by
/// `npm run build`), committed to the repo so `cargo build` needs no Node
/// toolchain (R7).
const INDEX_HTML: &str = include_str!("../web/dist/index.html");

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
/// [`SnapshotPayload`](cambra::inspector_model::SnapshotPayload) type as the
/// success path (via [`SnapshotPayload::degraded`]), so the two shapes cannot
/// drift; the frontend still renders the editor + squiggles from it.
fn degraded_snapshot_json(name: &str, code: &str, diagnostics: Vec<Diagnostic>) -> String {
    serde_json::to_string(&SnapshotPayload::degraded(name, code, diagnostics))
        .expect("degraded snapshot payload serializes")
}

/// Compile `code` once and return the `/api/snapshot` body — the full payload
/// on success, the degraded form (source + diagnostics, no stages) on failure.
///
/// One-shot and exits: this is what the `--dump-snapshot` CLI flag calls to
/// regenerate the frontend's golden test fixtures **without** standing up the
/// never-exiting HTTP server (see `web/src/__fixtures__/`).
pub fn snapshot_body(code: &str, name: &str) -> String {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    match compile_program(&mut ctx, code, consumer) {
        Ok(compiled) => snapshot_json(&compiled, name),
        Err(errors) => degraded_snapshot_json(name, code, diagnostics_from_compile_errors(&errors)),
    }
}

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

/// Compile `code` once and serve it over HTTP on `0.0.0.0:port` until the process
/// is killed. Blocks the calling thread (this is the binary's main loop).
pub fn serve(code: &str, name: &str, port: u16) -> io::Result<()> {
    let bodies = build_bodies(code, name);
    let server = tiny_http::Server::http(format!("0.0.0.0:{port}"))
        .map_err(|e| io::Error::other(e.to_string()))?;
    eprintln!("cambra-inspector serving {name} at http://localhost:{port}");

    for request in server.incoming_requests() {
        let response = match request.url() {
            "/api/snapshot" => {
                tiny_http::Response::from_string(bodies.snapshot.clone()).with_header(json_header())
            }
            "/api/diagnostics" => tiny_http::Response::from_string(bodies.diagnostics.clone())
                .with_header(json_header()),
            "/" | "/index.html" => {
                tiny_http::Response::from_string(INDEX_HTML).with_header(html_header())
            }
            _ => tiny_http::Response::from_string("Not Found")
                .with_status_code(404)
                .with_header(text_header()),
        };
        let _ = request.respond(response);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{assert_degraded_snapshot_shape, assert_snapshot_shape};
    use serde_json::Value;

    /// A valid program's snapshot body is the full payload: per-stage IR trees +
    /// populated `spanIndex`, empty `diagnostics`, and
    /// `meta.snapshotKind: "post-inference"`. Schema 2 retired the top-level
    /// `ir`/`spanIndex`; the per-stage contract is pinned by
    /// [`assert_snapshot_shape`].
    #[test]
    fn snapshot_body_success_has_ir_and_indices() {
        let bodies = build_bodies("1 + 2\n", "prog.chl");
        let v: Value = serde_json::from_str(&bodies.snapshot).expect("valid JSON");

        assert_snapshot_shape(&v);
        let anchor = v["stages"]
            .as_array()
            .expect("stages is an array")
            .iter()
            .find(|s| s["id"] == "post-inference")
            .expect("the post-inference stage is present");
        assert!(
            !anchor["ir"].is_null(),
            "the post-inference stage carries an ir tree"
        );
        assert!(
            !anchor["spanIndex"].as_array().expect("array").is_empty(),
            "the post-inference stage spanIndex is populated"
        );
        assert_eq!(v["meta"]["snapshotKind"], "post-inference");
        assert!(
            v["diagnostics"].as_array().expect("array").is_empty(),
            "a clean compile has no diagnostics"
        );
        assert_eq!(v["source"]["name"], "prog.chl");
    }

    /// A type-error program's snapshot body degrades: empty `stages`, non-empty
    /// `diagnostics`, `meta.snapshotKind: "failed"` — but source text is
    /// preserved so the frontend can still render the editor + squiggles. Schema
    /// 2 retired the top-level `ir`/`spanIndex` (their absence is pinned by
    /// [`assert_degraded_snapshot_shape`]).
    #[test]
    fn snapshot_body_failure_degrades() {
        let code = "1 and 2\n";
        let bodies = build_bodies(code, "bad.chl");
        let v: Value = serde_json::from_str(&bodies.snapshot).expect("valid JSON");

        assert_degraded_snapshot_shape(&v);
        assert!(v["stages"].as_array().expect("array").is_empty());
        assert!(v["definitions"].as_array().expect("array").is_empty());
        assert!(v["scopes"].as_array().expect("array").is_empty());
        assert_eq!(v["meta"]["snapshotKind"], "failed");
        assert!(v["meta"]["tick"].is_null());
        assert_eq!(v["meta"]["schema"], 2);

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
