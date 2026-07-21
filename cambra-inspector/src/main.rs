//! `cambra-inspector` binary: compile a program once and serve its read-only
//! post-inference snapshot over HTTP for the inspector frontend.
//!
//! Usage:
//! ```text
//! cambra-inspector <program.chl> [--port N]
//! cambra-inspector <program.chl> --dump-snapshot   # print /api/snapshot and exit
//! cambra-inspector <program.chl> --dump-snapshot [--panes a,b] [--elide-pane-links]
//! ```
//! With no file argument, serves a tiny built-in demo program so the server is
//! immediately curl-able. `--dump-snapshot` is a one-shot that prints the
//! snapshot JSON and exits (used to regenerate the frontend's golden fixtures
//! without the never-exiting server).
//!
//! The two fixture-slimming flags apply **only** with `--dump-snapshot` and only
//! shape the committed golden corpus (driven by
//! `cambra-inspector/scripts/fixtures.manifest`); the live server always emits
//! the full wire:
//! * `--panes <comma-list>` — retain only these pipeline stages (default: all).
//! * `--elide-pane-links` — omit `paneLinks` from the payload (default: keep).

use std::process::ExitCode;

use cambra_inspector::FixtureRetention;

/// The fallback program served when no file argument is given — just enough to
/// exercise the snapshot endpoint.
const DEMO_PROGRAM: &str = "g = 10\ndef f(p, q):\n  p + q + g\nf(1, 2)\n";
const DEFAULT_PORT: u16 = 8080;

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(msg) => {
            eprintln!("error: {msg}");
            eprintln!("usage: cambra-inspector <program.chl> [--port N]");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    let mut path: Option<String> = None;
    let mut port = DEFAULT_PORT;
    let mut dump_snapshot = false;
    // Fixture-slimming flags (dump-only): retained panes and paneLinks elision.
    let mut panes: Option<Vec<String>> = None;
    let mut elide_pane_links = false;

    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--port" => {
                let val = args.next().ok_or("--port requires a value")?;
                port = val.parse().map_err(|_| format!("invalid port: {val}"))?;
            }
            "--dump-snapshot" => dump_snapshot = true,
            "--panes" => {
                let val = args.next().ok_or("--panes requires a comma-list")?;
                panes = Some(val.split(',').map(str::to_string).collect());
            }
            "--elide-pane-links" => elide_pane_links = true,
            "-h" | "--help" => {
                println!(
                    "usage: cambra-inspector <program.chl> [--port N | --dump-snapshot [--panes a,b] [--elide-pane-links]]"
                );
                return Ok(());
            }
            other if other.starts_with("--") => {
                return Err(format!("unknown flag: {other}"));
            }
            other => {
                if path.is_some() {
                    return Err(format!("unexpected extra argument: {other}"));
                }
                path = Some(other.to_string());
            }
        }
    }

    let (code, name) = match path {
        Some(p) => {
            let text = std::fs::read_to_string(&p).map_err(|e| format!("reading {p}: {e}"))?;
            (text, p)
        }
        None => (DEMO_PROGRAM.to_string(), "demo.chl".to_string()),
    };

    if dump_snapshot {
        let retention = FixtureRetention {
            panes,
            links: !elide_pane_links,
        };
        println!(
            "{}",
            cambra_inspector::server::snapshot_body_pretty(&code, &name, &retention)
        );
        return Ok(());
    }

    if panes.is_some() || elide_pane_links {
        return Err("--panes/--elide-pane-links are only valid with --dump-snapshot".to_string());
    }

    cambra_inspector::server::serve(&code, &name, port).map_err(|e| format!("serving: {e}"))
}
