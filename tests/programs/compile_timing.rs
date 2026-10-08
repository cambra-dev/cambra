//! Compile time per gallery program, as a table.
//!
//! Every `.cambra` file under `tests/programs/` is compiled on its own, and the
//! fastest of `CAMBRA_PERF_REPS` repetitions is reported — best-of-N because a
//! single repetition on a shared machine measures the machine. The driver
//! asserts nothing: it is a measurement, like the library's
//! `provenance_pane_perf` and `lowering_session_cost_canary`, and is `#[ignore]`d
//! so `cargo test` never pays for it.
//!
//! Three drivers share the table and differ in what they time.
//! [`gallery_compile_timing`] runs `compile_program`: the whole frontend through
//! `Phase::Planning`, then operator conversion. [`gallery_infer_timing`] runs
//! `compile_to` stopped at `Phase::Infer`, so a row covers lowering, uniquify,
//! A-normalization, mutable-read naming and inference, and nothing after them.
//! [`gallery_post_infer_timing`] runs `compile_to` to both stops and attributes
//! the difference, so a row covers inline, transact, letrec, channelize, the
//! as-of-read rewrite, lambda elimination and planning.
//!
//! The compile row minus the infer row is not the post-infer row.
//! `compile_program` captures panes, records provenance, and runs operator
//! conversion; `compile_to` does none of the three. The post-infer row takes both
//! its halves from `compile_to`, so panes and provenance cancel out of it and
//! operator conversion sits outside what it measures.
//!
//! Run them in release, which is the configuration whose numbers mean anything:
//!
//! ```text
//! cargo test --release --test programs -- --ignored --nocapture gallery_compile_timing
//! cargo test --release --test programs -- --ignored --nocapture gallery_infer_timing
//! cargo test --release --test programs -- --ignored --nocapture gallery_post_infer_timing
//! ```
//!
//! A bare `--ignored` runs all three. They hold [`SERIAL`] for the length of a
//! run, so the tables never interleave.
//!
//! One program, timed without the rest of the gallery's noise:
//!
//! ```text
//! CAMBRA_TIMING_ONLY=storefront CAMBRA_PERF_REPS=9 \
//!   cargo test --release --test programs -- --ignored --nocapture gallery_compile_timing
//! ```
//!
//! What the `compile` numbers cover: `compile_program` alone — not evaluation,
//! which is where the rest of a gallery test's wall clock goes
//! (`common::run_to_tile` pumps the scheduler up to 100 rounds after the
//! compile). A sink program's sinks bind their resources inside the compile, so
//! a `{PORT}` program's row includes that bind; each compile takes a freshly
//! reserved port. `compile_to` binds the same resources from its own fresh
//! context, so the `infer` rows carry the bind too, and the `post-infer` row
//! cancels it between its two halves.
//!
//! Pane capture is part of what `gallery_compile_timing` measures. To separate
//! it, run the two arms interleaved so both see the same machine state, and
//! compare the totals:
//!
//! ```text
//! for i in 1 2 3; do
//!   CAMBRA_PROVENANCE=1 cargo test --release --test programs -- --ignored --nocapture gallery_compile_timing
//!   CAMBRA_PROVENANCE=0 cargo test --release --test programs -- --ignored --nocapture gallery_compile_timing
//! done
//! ```

use std::{
    env::VarError,
    fs,
    num::NonZeroUsize,
    panic::{self, AssertUnwindSafe},
    path::{Path, PathBuf},
    sync::Mutex,
    time::{Duration, Instant},
};

use cambra::{
    ccl::context::{
        CompileError, GlobalContext, Phase, compile_program, compile_to, render_errors,
    },
    chl_parser::SourceMap,
    interpreter::Consumer,
};

use super::{panic_message::panic_message, serving::reserve_test_port};

/// Repetition count, the same switch the library's `provenance_pane_perf`
/// reads: one knob for every ignored perf driver. Spelled here rather than
/// imported because the library's constant is `#[cfg(test)]`, so it does not
/// exist in the build an integration test links against.
const REPS_ENV: &str = "CAMBRA_PERF_REPS";

/// Substring narrowing the run to the labels containing it.
const ONLY_ENV: &str = "CAMBRA_TIMING_ONLY";

/// Held for the length of a driver's run, so two drivers selected by one
/// `--ignored` never overlap.
///
/// Two things here are process-wide and neither is re-entrant: the panic hook
/// [`time_gallery`] mutes around the repetitions, and the stderr the table is
/// written to. Concurrent drivers would restore each other's hook mid-run and
/// interleave their rows.
static SERIAL: Mutex<()> = Mutex::new(());

/// What one program's repetitions produced.
enum Outcome {
    /// The fastest of the repetitions.
    Compiled(Duration),
    /// The program never compiled, with the first line of the rejection. The
    /// gallery pins several of these deliberately (`docs/demo-programs.md`
    /// marks them blocked), so a rejection is a row rather than a failure.
    Rejected(String),
}

/// One repetition's measurement: the span the row attributes, and the product,
/// kept alive so the compile that produced it is not optimized away.
struct Measured<T> {
    span: Duration,
    product: T,
}

/// Attribute the whole of `run`, for a driver whose row is one compile.
fn whole<T>(
    run: impl FnOnce() -> Result<T, Vec<CompileError>>,
) -> Result<Measured<T>, Vec<CompileError>> {
    let start = Instant::now();
    let product = run()?;
    Ok(Measured {
        span: start.elapsed(),
        product,
    })
}

#[test]
#[ignore = "measurement, not a gate; see the module doc for the driver"]
fn gallery_compile_timing() {
    time_gallery("compile", |source| {
        let sources = SourceMap::single("<gallery>", source());
        whole(|| {
            let mut ctx = GlobalContext::default();
            let consumer: Box<dyn Consumer> = Box::new(|| {});
            compile_program(&mut ctx, &sources, consumer)
        })
    });
}

#[test]
#[ignore = "measurement, not a gate; see the module doc for the driver"]
fn gallery_infer_timing() {
    time_gallery("infer", |source| {
        let sources = SourceMap::single("<gallery>", source());
        whole(|| compile_to(&sources, Phase::Infer))
    });
}

/// The phases after inference, as one `compile_to` minus another.
///
/// The two stops share every phase up to and including inference, so the
/// difference is what `Phase::Planning` adds over `Phase::Infer`. Both halves run
/// inside one repetition, which is what puts them on one machine state; taking
/// the difference between whole runs of the other two drivers does not, and
/// carries their entry points' pane and provenance costs besides.
#[test]
#[ignore = "measurement, not a gate; see the module doc for the driver"]
fn gallery_post_infer_timing() {
    time_gallery("post-infer", |source| {
        let (to_infer, to_planning) = (
            SourceMap::single("<gallery>", source()),
            SourceMap::single("<gallery>", source()),
        );
        let inferred = whole(|| compile_to(&to_infer, Phase::Infer))?;
        let planned = whole(|| compile_to(&to_planning, Phase::Planning))?;
        Ok(Measured {
            // Saturating because the halves are separate measurements: on a
            // program whose post-inference phases cost less than the scheduling
            // noise in either half, the difference can come out negative, and a
            // 0.000ms row says that without a sign convention to read.
            span: planned.span.saturating_sub(inferred.span),
            product: (inferred.product, planned.product),
        })
    });
}

fn repetitions(value: Result<String, VarError>) -> NonZeroUsize {
    match value {
        Err(VarError::NotPresent) => NonZeroUsize::new(3).unwrap(),
        Ok(value) => value
            .parse()
            .unwrap_or_else(|_| panic!("{REPS_ENV} must be a positive integer, got {value:?}")),
        Err(VarError::NotUnicode(value)) => {
            panic!("{REPS_ENV} must be a positive integer, got {value:?}")
        }
    }
}

/// Time `compile` over every selected gallery program and print the table.
///
/// `what` labels the run and heads the timing column. `compile` receives a
/// provider of freshly port-filled program text and reports the span its row
/// attributes, which is the whole call for every driver but
/// [`gallery_post_infer_timing`].
fn time_gallery<T>(
    what: &str,
    mut compile: impl FnMut(&dyn Fn() -> String) -> Result<Measured<T>, Vec<CompileError>>,
) {
    let _serial = SERIAL
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let reps = repetitions(std::env::var(REPS_ENV));
    let only = std::env::var(ONLY_ENV).unwrap_or_default();
    let programs: Vec<(String, PathBuf)> = gallery()
        .into_iter()
        .filter(|(label, _)| label.contains(&only))
        .collect();
    assert!(
        !programs.is_empty(),
        "no gallery program's label contains {ONLY_ENV}={only:?}"
    );

    // A rejected program panics inside a phase or returns errors; either way
    // the row carries the reason, so the hook only adds a backtrace between two
    // table rows. Muting it is process-wide, which `SERIAL` is what makes safe.
    let hook = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));
    let mut rows: Vec<(String, usize, Outcome)> = programs
        .iter()
        .map(|(label, path)| {
            let source = fs::read_to_string(path).expect("read program source");
            let outcome = best_compile(label, &source, reps, &mut compile);
            (label.clone(), source.lines().count(), outcome)
        })
        .collect();
    panic::set_hook(hook);

    // Slowest first: the table is read top-down for what compilation costs, and
    // the rejected programs have no cost to rank, so they sit at the bottom.
    rows.sort_by(|a, b| match (&a.2, &b.2) {
        (Outcome::Compiled(x), Outcome::Compiled(y)) => y.cmp(x),
        (Outcome::Compiled(_), Outcome::Rejected(_)) => std::cmp::Ordering::Less,
        (Outcome::Rejected(_), Outcome::Compiled(_)) => std::cmp::Ordering::Greater,
        (Outcome::Rejected(_), Outcome::Rejected(_)) => a.0.cmp(&b.0),
    });

    let width = rows
        .iter()
        .map(|(label, ..)| label.len())
        .max()
        .unwrap_or(0);
    let mut total = Duration::ZERO;
    let mut rejected = 0usize;
    eprintln!(
        "[{what}-timing] best of {reps} repetitions, {} programs",
        rows.len()
    );
    eprintln!("  {:<width$}  {:>5}  {:>10}", "program", "lines", what);
    for (label, lines, outcome) in &rows {
        match outcome {
            Outcome::Compiled(best) => {
                total += *best;
                eprintln!("  {label:<width$}  {lines:>5}  {:>9.3}ms", millis(*best));
            }
            Outcome::Rejected(why) => {
                rejected += 1;
                eprintln!("  {label:<width$}  {lines:>5}  {:>10}  {why}", "rejected");
            }
        }
    }
    eprintln!(
        "  {:<width$}  {:>5}  {:>9.3}ms  ({rejected} rejected)",
        "TOTAL",
        "",
        millis(total),
    );
}

/// Run `compile` on `source` `reps` times and keep the fastest, stopping at the
/// first repetition that does not compile. `label` names the source in a
/// rejection's rendered position.
fn best_compile<T>(
    label: &str,
    source: &str,
    reps: NonZeroUsize,
    compile: &mut impl FnMut(&dyn Fn() -> String) -> Result<Measured<T>, Vec<CompileError>>,
) -> Outcome {
    let mut best = Duration::MAX;
    // One port per compile rather than per repetition: the port a sink program
    // binds inside a compile is still bound when the next one starts, and a
    // driver that compiles twice would rebind it. The text a rejection renders
    // against has to be the one that produced it, down to the column, so the
    // provider keeps its last answer.
    let rendered = std::cell::RefCell::new(source.to_string());
    let fresh = || {
        let text = with_port(source);
        rendered.replace(text.clone());
        text
    };
    for _ in 0..reps.get() {
        match panic::catch_unwind(AssertUnwindSafe(|| compile(&fresh))) {
            Ok(Ok(Measured { span, product })) => {
                best = best.min(span);
                std::hint::black_box(&product);
            }
            Ok(Err(errs)) => {
                let sources = SourceMap::single(label, &*rendered.borrow());
                return Outcome::Rejected(summary(&render_errors(&errs, &sources)));
            }
            Err(payload) => return Outcome::Rejected(summary(&panic_message(&*payload))),
        }
    }
    Outcome::Compiled(best)
}

/// Fill a sink program's `{PORT}` placeholder with a reserved port, leaving
/// every other program's source untouched.
fn with_port(source: &str) -> String {
    match source.contains("{PORT}") {
        true => source.replace("{PORT}", &reserve_test_port().to_string()),
        false => source.to_string(),
    }
}

/// Every `.cambra` file in the gallery, labelled `<program>` or, where a
/// directory holds more than the one source, `<program>/<stem>`. Discovered
/// rather than listed, so a new program directory is timed the day it lands.
fn gallery() -> Vec<(String, PathBuf)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs");
    let mut found = Vec::new();
    for entry in fs::read_dir(&root).expect("read the gallery root") {
        let dir = entry.expect("read a gallery entry").path();
        if !dir.is_dir() {
            continue;
        }
        let program = dir
            .file_name()
            .expect("program directory name")
            .to_string_lossy()
            .into_owned();
        for entry in fs::read_dir(&dir).expect("read a program directory") {
            let path = entry.expect("read a program entry").path();
            if path.extension().and_then(|e| e.to_str()) != Some("cambra") {
                continue;
            }
            let stem = path
                .file_stem()
                .expect("source file stem")
                .to_string_lossy()
                .into_owned();
            let label = match stem.as_str() {
                "program" => program.clone(),
                _ => format!("{program}/{stem}"),
            };
            found.push((label, path));
        }
    }
    found.sort();
    found
}

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1_000.0
}

/// A rejection's first line, carrying the source position ariadne prints on
/// the line below it, so a row says where the program stops and not only that
/// it does. A panic payload has no such position and keeps its first line.
fn summary(message: &str) -> String {
    let head = message
        .lines()
        .find(|l| !l.trim().is_empty())
        .unwrap_or("")
        .trim()
        .to_string();
    match message
        .split_once("─[")
        .and_then(|(_, rest)| rest.split_once(']'))
    {
        Some((locus, _)) => format!("{head} at {locus}"),
        None => head,
    }
}

#[test]
fn timing_repetitions_default_only_when_absent() {
    assert_eq!(repetitions(Err(VarError::NotPresent)).get(), 3);
    for reps in [1, 9, usize::MAX] {
        assert_eq!(repetitions(Ok(reps.to_string())).get(), reps);
    }
}

#[test]
fn timing_repetitions_reject_invalid_values() {
    for value in ["0", "", "abc", "-1", "1.5", "184467440737095516160"] {
        let err = panic::catch_unwind(|| repetitions(Ok(value.to_string())))
            .expect_err("invalid repetition count must fail");
        assert!(panic_message(&*err).contains("CAMBRA_PERF_REPS must be a positive integer"));
    }
    let err = panic::catch_unwind(|| {
        repetitions(Err(VarError::NotUnicode(std::ffi::OsString::from(
            "invalid",
        ))))
    })
    .expect_err("non-Unicode repetition count must fail");
    assert!(panic_message(&*err).contains("CAMBRA_PERF_REPS must be a positive integer"));
}

#[test]
fn timing_best_compile_runs_every_repetition() {
    let mut spans = [5, 2, 8].into_iter();
    let outcome = best_compile("test", "1", NonZeroUsize::new(3).unwrap(), &mut |_| {
        Ok(Measured {
            span: Duration::from_millis(spans.next().expect("exactly three repetitions")),
            product: (),
        })
    });
    assert!(spans.next().is_none());
    assert!(matches!(outcome, Outcome::Compiled(span) if span == Duration::from_millis(2)));
}
