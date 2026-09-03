//! wasm-bindgen entry point for running Cambra programs in a browser.
//!
//! This is an exploratory driver, not a general embedding API: it only
//! handles programs whose `main` output converges on its own (no
//! `http_serve`-style sink, no external data source). Those rely on an OS
//! thread or timer to redeliver notifications over time; there is none here
//! — the whole compile-and-run happens synchronously on the calling JS
//! thread, so anything that would block forever natively would freeze the
//! browser tab instead. `MAX_TICKS` is a hang guard for exactly that case,
//! not a load-bearing part of the language.
use wasm_bindgen::prelude::*;

use crate::ccl::context::{GlobalContext, compile_program, render_errors};
use crate::ccl::symbolic::symbolic;
use crate::interpreter::Consumer;
use crate::interpreter::tile_operators::{FunctionGuard, Tile, TileGuard};
use crate::pretty_graph::{VizOptions, pretty_tile_operator};

/// Registers a panic hook that forwards Rust panics to the browser console
/// (`console.error`) instead of the opaque "unreachable executed" trap
/// message. Call this once before `compile_and_run`.
#[wasm_bindgen]
pub fn init_panic_hook() {
    console_error_panic_hook::set_once();
}

const MAX_TICKS: u64 = 100_000;

/// Result of [`compile_and_run`]. Every field defaults to empty; `error`
/// non-empty means the others carry whatever partial information was
/// available before the failure (e.g. `ast`/`operators` are still populated
/// on a driver-level error, since those are captured before the run loop
/// starts, but not on a compile error, since there is no compiled tree yet).
#[wasm_bindgen(getter_with_clone)]
#[derive(Default)]
pub struct RunResult {
    /// Symbolic-form join-planned AST (see [`symbolic`]).
    pub ast: String,
    /// Pretty-printed operator tree, one per program output.
    pub operators: String,
    /// The last tick's producer snapshot, as the JSON object
    /// `{"tick":N,"producers":[...]}` that `www/index.html`'s inspector
    /// panel expects (the same shape the native `--inspect` dashboard
    /// polls from `/api/snapshot`).
    pub snapshot: String,
    /// Newline-joined trace of each tick's emitted tile.
    pub output: String,
    /// Non-empty on failure: a compile error, an unsupported program shape
    /// (sink-driven), or the `MAX_TICKS` hang guard firing.
    pub error: String,
}

/// Compiles and runs a Cambra program to completion.
#[wasm_bindgen]
pub fn compile_and_run(code: &str) -> RunResult {
    use std::{cell::RefCell, rc::Rc};

    let new_data = Rc::new(RefCell::new(false));
    let new_data_clone = new_data.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *new_data_clone.borrow_mut() = true;
    });

    let mut ctx = GlobalContext::default();
    let mut compiled = match compile_program(&mut ctx, code, consumer) {
        Ok(c) => c,
        Err(errs) => {
            return RunResult {
                error: render_errors(&errs, "<wasm>", code),
                ..Default::default()
            };
        }
    };

    let ast = symbolic(&compiled.ast);
    let operators = compiled
        .outputs
        .iter()
        .map(|o| pretty_tile_operator(o.op.as_ref()))
        .collect::<Vec<_>>()
        .join("\n\n");

    let mut main_producer = compiled.main_mut().and_then(|o| o.producer.take());
    let mut output = String::new();
    let mut snapshot = String::new();
    let viz_opts = VizOptions::default();

    if let Some(producer) = main_producer.as_mut() {
        for tick in 0..MAX_TICKS {
            while !*new_data.borrow() {
                ctx.scheduler().check_for_notifications();
            }
            *new_data.borrow_mut() = false;

            let tile = producer.get(producer.tiling().universal_guard());
            snapshot = format!(
                r#"{{"tick":{tick},"producers":[{}]}}"#,
                producer.inspect(&viz_opts).to_json()
            );

            let release_guard = match &tile {
                Tile::Scalar(cv) => TileGuard::Scalar(!cv.is_empty()),
                Tile::SealedFunction {
                    domain_predicate, ..
                } => TileGuard::Function(FunctionGuard::Domain(domain_predicate.clone())),
                other => {
                    return RunResult {
                        ast,
                        operators,
                        snapshot,
                        output,
                        error: format!("unexpected top-level tile shape: {other:?}"),
                    };
                }
            };
            let done = release_guard.is_universal();
            producer.release(release_guard);
            let is_empty = match &tile {
                Tile::Scalar(cv) => cv.is_empty(),
                Tile::SealedFunction { domain, .. } => domain.is_empty(),
                _ => false,
            };
            if !is_empty || done {
                output.push_str(&format!("tick {tick}: {tile:#?}\n"));
            }
            if done {
                return RunResult {
                    ast,
                    operators,
                    snapshot,
                    output,
                    error: String::new(),
                };
            }
        }
        return RunResult {
            ast,
            operators,
            snapshot,
            output,
            error:
                "exceeded MAX_TICKS without converging (unsupported sink/source-driven program?)"
                    .to_string(),
        };
    }

    if compiled.sinks().next().is_some() {
        return RunResult {
            ast,
            operators,
            error:
                "program has sink outputs (e.g. http_serve) — unsupported in this wasm demo driver"
                    .to_string(),
            ..Default::default()
        };
    }

    RunResult {
        ast,
        operators,
        snapshot,
        output,
        error: String::new(),
    }
}
