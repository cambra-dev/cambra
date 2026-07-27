//! `cambra-inspector` binary: compile a program once and serve its read-only
//! post-inference snapshot over HTTP for the inspector frontend.
//!
//! Usage:
//! ```text
//! cambra-inspector <program.chl> [--port N]
//! cambra-inspector <program.chl> --dump-snapshot   # print /api/snapshot and exit
//! ```
//! With no file argument, serves a tiny built-in demo program so the server is
//! immediately curl-able. `--dump-snapshot` is a one-shot that prints the
//! snapshot JSON and exits (used to regenerate the frontend's golden fixtures
//! without the never-exiting server).

use std::process::ExitCode;

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

    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--port" => {
                let val = args.next().ok_or("--port requires a value")?;
                port = val.parse().map_err(|_| format!("invalid port: {val}"))?;
            }
            "--dump-snapshot" => dump_snapshot = true,
            "-h" | "--help" => {
                println!("usage: cambra-inspector <program.chl> [--port N | --dump-snapshot]");
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
        println!(
            "{}",
            cambra_inspector::server::snapshot_body_pretty(&code, &name)
        );
        return Ok(());
    }

    cambra_inspector::server::serve(&code, &name, port).map_err(|e| format!("serving: {e}"))
}
