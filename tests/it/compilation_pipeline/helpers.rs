//! Shared fixtures for the compilation-pipeline integration tests.
//!
//! All tests run through the full CCL pipeline via
//! [`compile_program`]:
//!
//! ```text
//! CHL source
//!   → ccl::lower          (CHL AST → CCL Expr)
//!   → ccl::infer          (type inference; annotates Lambda param_ty)
//!   → operator_conversion (CCL Expr → dataflow operators)
//!   → subscribe()         (operator evaluation)
//! ```
//!
//! Unlike the unit tests in each module, these tests validate the composition
//! of all passes together.
//!
//! Each themed module reaches these via `use super::helpers::*;`.
//!
//! ## Timeout budget
//!
//! Each timed test guards against runaway / exponential / non-terminating
//! compilation via rstest's wall-clock `#[timeout]`. The budget is deliberately
//! generous: CI runs on shared VMs whose core speed varies widely — a slow instance
//! runs the heaviest compile ~13x slower (~9.5s wall) than a fast one, and the
//! original uniform 1s flaked there. (We confirmed the slowdown shows up 1:1 in
//! thread-CPU time too — ratio ≈ 1.00 — so a CPU-time bound buys nothing over wall.)
//! Most tests get 10s; the three heaviest compiles get 30s.

use cambra::interpreter::LockNow;
use smol_str::SmolStr;
use std::collections::HashMap;
use std::panic::{self, AssertUnwindSafe};
use std::sync::Arc;
use std::sync::Mutex;

use bit_set::BitSet;
use cambra::ccl::Expr;
use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program};
use cambra::ccl::load::LoadedProgram;
use cambra::interpreter::tile_operators::scalar_tile_to_column_value;
use cambra::interpreter::{
    ColumnValue, Consumer, Predicate, Tile, Value, pull_laps, sort_function_by_domain, tuple_field,
};
use cambra::pretty_graph::VizOptions;
use cambra::pretty_tree::InspectNode;

use super::panic_message::panic_message;

// ---------------------------------------------------------------------------
// Helpers — CCL pipeline path
// ---------------------------------------------------------------------------

/// The kinds of the operators `code` compiles to, in graph order, with `source1` registered as a
/// source of `Int`s: what a test of a program's shape reads, such as whether an element-wise chain
/// became one map.
pub(crate) fn operator_kinds_over_source1(code: &str) -> Vec<&'static str> {
    use cambra::ccl::Type;
    use cambra::interpreter::operator_graph::GraphNode;
    use cambra::interpreter::{BaseType, Extent, TestDataSource};

    let mut ctx = GlobalContext::default();
    ctx.register_source(Arc::new(Mutex::new(TestDataSource::new(
        "source1",
        Type::Base(cambra::ccl::BaseType::Int),
        Extent::Base(BaseType::Int),
    ))));
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let program = LoadedProgram::test(code);
    let compiled = compile_program(&mut ctx, &program, consumer).unwrap_or_render(&program);
    compiled
        .operator_graph
        .nodes()
        .iter()
        .filter_map(|node| match node {
            GraphNode::Operator { kind, .. } => Some(*kind),
            GraphNode::Sink { .. } => None,
        })
        .collect()
}

/// The most values each kind of operator held at any lap of running `code` to its end, by
/// the operator's name less its instance (`InductionStore`, `Memo`, …), summed over the
/// instances of that kind at each lap ([`TileProducer::state_info`]).
///
/// What a test of how much state a program keeps reads: a count that grows with how far
/// the program has run, where its data does not, is state it never gives back.
pub(crate) fn peak_held_values(code: &str) -> HashMap<String, usize> {
    fn held(node: &InspectNode, by_kind: &mut HashMap<String, usize>) {
        if let Some(values) = node.held_values {
            let kind = node.label.split('#').next().unwrap_or(&node.label);
            *by_kind.entry(kind.to_string()).or_default() += values;
        }
        for (_, child) in &node.children {
            held(child, by_kind);
        }
    }
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(code);
    let mut compiled =
        compile_program(&mut ctx, &loaded, Box::new(|| {})).unwrap_or_render(&loaded);
    let producer = compiled
        .main_mut()
        .and_then(|o| o.producer.as_mut())
        .expect("a `main` output");
    let universal = producer.tiling().universal_guard();
    let mut peak: HashMap<String, usize> = HashMap::new();
    for _ in 0..4096 {
        ctx.scheduler().check_for_notifications();
        let tile = producer.get(universal.clone());
        let mut now = HashMap::new();
        held(&producer.inspect(&VizOptions::default()), &mut now);
        for (kind, values) in now {
            let at = peak.entry(kind).or_default();
            *at = (*at).max(values);
        }
        if tile.is_terminal() {
            return peak;
        }
    }
    panic!("{code}: stopped short of a terminal tile");
}

/// Lower `code` through the CCL pipeline (parse → `ccl::lower` → `ccl::infer`
/// → `operator_conversion` → subscribe → get) and return the resulting [`Tile`].
pub(crate) fn run_pipeline(code: &str) -> Tile {
    let mut ctx = GlobalContext::default();
    run_pipeline_with_ctx(&mut ctx, code).1
}

pub(crate) fn run_pipeline_with_ctx(ctx: &mut GlobalContext, code: &str) -> (Expr, Tile) {
    run_program_with_ctx(ctx, &LoadedProgram::test(code))
}

/// [`run_pipeline`] for a program of any number of files.
pub(crate) fn run_program(program: &LoadedProgram) -> Tile {
    let mut ctx = GlobalContext::default();
    run_program_with_ctx(&mut ctx, program).1
}

/// [`run_pipeline_with_ctx`] for a program of any number of files.
pub(crate) fn run_program_with_ctx(
    ctx: &mut GlobalContext,
    loaded: &LoadedProgram,
) -> (Expr, Tile) {
    let notified = Arc::new(Mutex::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.lock_now() = true;
    });
    let mut compiled = compile_program(ctx, loaded, consumer).unwrap_or_render(loaded);
    ctx.scheduler().check_for_notifications();
    assert!(
        *notified.lock_now(),
        "expected notification (pipeline path)"
    );
    let producer = compiled
        .main_mut()
        .and_then(|o| o.producer.as_mut())
        .expect("pipeline test expects a `main` output");
    // A single `get` is not always enough to drain a producer: a mutation loop's
    // store/drive cycle decides one more position of the recurrence per pass, and
    // re-arms by asking the scheduler to wake its consumer. The cap catches a cycle
    // that stops converging without reaching a terminal tile.
    let universal = producer.tiling().universal_guard();
    let mut result = pull_laps(ctx.scheduler(), &mut **producer, 1024, Tile::is_terminal);
    assert!(
        result.is_terminal(),
        "pipeline path: producer stopped short of a terminal tile, quiescent or after 1024 \
         laps: {result:?}"
    );
    result.compact();
    // Release everything, then pull once more: a released region must never come
    // back out, so this answers empty or trips the contract assertion.
    producer.release(universal.clone());
    let after = producer.get(universal.clone());
    assert!(
        after.is_empty(),
        "pull after a universal release returned {after:?}"
    );
    dispatch::check(loaded, &result);
    (*compiled.ast, result)
}

/// The differential suite of the pool's inline driver: with `CAMBRA_DISPATCH_CHECK=1` every
/// program a pipeline test runs is run again through `PooledRun`, and the answers must agree.
///
/// A program the plan refuses is counted with its reason, and one that does not compile on a
/// bare context (it reads a source or sink the test registered) is counted as skipped; the
/// dispatched run does not rebuild a test's sources, so such a program is not checked. The
/// programs the plan admits are pinned in `dispatch_admitted.txt`, one line each, a hash of the
/// program's files and the name of the test that ran it, separated by a tab. An admitted program
/// that is not listed, or a listed one that is refused, fails, so a plan change that admits less
/// or more is a diff in that file. `CAMBRA_DISPATCH_BLESS=1` rewrites the file from the programs a
/// run admits, sorted, so a bless run covers the whole corpus. `CAMBRA_DISPATCH_REPORT=<file>`
/// appends one line per program: outcome, reason and hash. `./ci.sh dispatch` runs the suite and
/// compares the report with the pin, so a listed program no test runs any more fails there.
mod dispatch {
    use super::*;
    use cambra::interpreter::parallel::{Config, Lap, PooledRun};
    use std::collections::BTreeMap;
    use std::io::Write;

    const PIN: &str = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/it/compilation_pipeline/dispatch_admitted.txt"
    );

    /// A 64-bit FNV-1a hash of every file of the program, with its path.
    fn key(loaded: &LoadedProgram) -> String {
        let mut hash = 0xcbf2_9ce4_8422_2325u64;
        let sources = loaded.sources();
        for file in sources.files() {
            for byte in sources.path(file).bytes().chain(sources.text(file).bytes()) {
                hash = (hash ^ u64::from(byte)).wrapping_mul(0x0100_0000_01b3);
            }
        }
        format!("{hash:016x}")
    }

    fn pinned() -> Vec<String> {
        std::fs::read_to_string(PIN)
            .unwrap_or_default()
            .lines()
            .filter_map(|line| line.split_whitespace().next().map(str::to_string))
            .collect()
    }

    /// Append `line` to the file `path` in one write, so that lines from tests on several threads
    /// do not interleave.
    fn append(path: &str, line: String) {
        let mut file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .expect("the file opens");
        file.write_all(line.as_bytes())
            .expect("the line is written");
    }

    fn report(outcome: &str, reason: &str, key: &str) {
        if let Ok(path) = std::env::var("CAMBRA_DISPATCH_REPORT") {
            append(&path, format!("{outcome}\t{reason}\t{key}\n"));
        }
    }

    /// The programs this run admitted, by hash, with the test that ran each, which a bless run
    /// writes out whole.
    static ADMITTED: Mutex<BTreeMap<String, String>> = Mutex::new(BTreeMap::new());

    /// List `key` among the admitted programs and rewrite the pin from the list.
    fn bless(key: &str) {
        let test = std::thread::current().name().unwrap_or("").to_string();
        let mut admitted = ADMITTED
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        admitted
            .entry(key.to_string())
            .and_modify(|first| {
                if test < *first {
                    *first = test.clone();
                }
            })
            .or_insert(test);
        let text: String = admitted
            .iter()
            .map(|(key, test)| format!("{key}\t{test}\n"))
            .collect();
        std::fs::write(PIN, text).expect("the pin file is written");
    }

    /// The morsel sizes the inline driver runs each program at: `CAMBRA_MORSEL_ROWS` when set, and
    /// otherwise 1 and 3, so a program over a few rows runs as one morsel per row and as several.
    fn morsel_sizes() -> Vec<u64> {
        match std::env::var("CAMBRA_MORSEL_ROWS")
            .ok()
            .and_then(|rows| rows.parse().ok())
        {
            Some(rows) => vec![rows],
            None => vec![1, 3],
        }
    }

    /// Run `loaded` through the inline driver and compare with `serial`, the answer of the plain
    /// loop, at each morsel size.
    pub(super) fn check(loaded: &LoadedProgram, serial: &Tile) {
        if std::env::var("CAMBRA_DISPATCH_CHECK").as_deref() != Ok("1") {
            return;
        }
        let key = key(loaded);
        let blessing = std::env::var("CAMBRA_DISPATCH_BLESS").as_deref() == Ok("1");
        let mut ctx = GlobalContext::default();
        if compile_program(&mut ctx, loaded, Box::new(|| {})).is_err() {
            report("skipped", "does not compile on a bare context", &key);
            return;
        }
        for (pass, morsel_rows) in morsel_sizes().into_iter().enumerate() {
            let admitted = inline_pass(loaded, serial, &key, morsel_rows);
            if pass > 0 {
                // A program the plan admits runs at every morsel size.
                assert!(
                    admitted.is_ok(),
                    "{key} is admitted and {morsel_rows} rows refuses it: {:?}",
                    admitted.err()
                );
                continue;
            }
            match admitted {
                Err(refused) => {
                    report("refused", &refused, &key);
                    assert!(
                        blessing || !pinned().contains(&key),
                        "{key} is pinned as admitted and the plan refused it: {refused}"
                    );
                    return;
                }
                Ok(()) => {
                    report("admitted", "", &key);
                    if blessing {
                        bless(&key);
                    } else {
                        assert!(
                            pinned().contains(&key),
                            "{key} was admitted and is not pinned: run with CAMBRA_DISPATCH_BLESS=1"
                        );
                    }
                }
            }
        }
    }

    /// One inline run of `loaded` with morsels of `morsel_rows` rows against `serial`, or the
    /// plan's reason for refusing the program.
    fn inline_pass(
        loaded: &LoadedProgram,
        serial: &Tile,
        key: &str,
        morsel_rows: u64,
    ) -> Result<(), String> {
        let mut ctx = GlobalContext::default();
        let mut program = compile_program(&mut ctx, loaded, Box::new(|| {}))
            .expect("the program compiled on a bare context");
        let config = Config { morsel_rows };
        let started = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}));
        let mut run = started.map_err(|refused| refused.to_string())?;
        let mut main = run.take_main().expect("a program with a `main` output");
        let universal = main.tiling().universal_guard();
        let laps = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            for _ in 0..1024 {
                ctx.scheduler().check_for_notifications();
                run.lap();
                ctx.scheduler().pull_sinks();
                let tile = main.get(universal.clone());
                if tile.is_terminal() {
                    return Some(tile);
                }
            }
            None
        }));
        let dispatched = match laps {
            Ok(dispatched) => dispatched,
            Err(panic) => {
                let why = panic
                    .downcast_ref::<String>()
                    .map(String::as_str)
                    .or_else(|| panic.downcast_ref::<&str>().copied())
                    .unwrap_or("a panic with no message");
                panic!("the dispatched run of {key} at {morsel_rows} rows panicked: {why}");
            }
        };
        let mut dispatched = dispatched.unwrap_or_else(|| {
            panic!(
                "the dispatched run of {key} at {morsel_rows} rows did not reach a terminal tile \
                 in 1024 laps"
            )
        });
        assert!(
            run.lap() == Lap::Done,
            "the dispatched run of {key} at {morsel_rows} rows has a terminal `main` and every \
             pipeline finished"
        );
        dispatched.compact();
        assert_eq!(
            sort_tile_collections(dispatched),
            sort_tile_collections(serial.clone()),
            "the dispatched run of {key} at {morsel_rows} rows differs from the serial run"
        );
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Parity assertion helpers
// ---------------------------------------------------------------------------

/// Assert `code` produces `expected` via the pipeline path.
pub(crate) fn check_tile(code: &str, expected: Tile) {
    assert_eq!(
        sort_function_by_domain(run_pipeline(code)),
        sort_function_by_domain(expected),
        "pipeline path"
    );
}

/// [`check_tile`] for a result holding materialized collections: normalizes each
/// table's binding order before comparing, since [`Value::Function`] compares
/// positionally and a collection's order is unspecified.
pub(crate) fn check_collection_tile(code: &str, expected: Tile) {
    assert_eq!(
        sort_tile_collections(run_pipeline(code)),
        sort_tile_collections(expected),
        "pipeline path"
    );
}

/// Scalar variant of [`check_tile`]: unwraps the result via
/// [`cambra::interpreter::ColumnValue::as_single`] before comparing.
pub(crate) fn check_scalar(code: &str, expected: Value) {
    check_program_scalar(&LoadedProgram::test(code), expected);
}

/// [`check_scalar`] for a program of any number of files.
pub(crate) fn check_program_scalar(program: &LoadedProgram, expected: Value) {
    let result = run_program(program);
    let scalar = scalar_tile_to_column_value(result);
    assert_eq!(scalar.as_single().unwrap(), expected);
}

/// Run `code`, which writes to the test sink `out`, and check what the sink received, rendered
/// as the differential interpreter's value: keyed, with entries in key order, so the order rows
/// arrive in is not part of it.
pub(crate) fn check_sink(code: &str, expected: &str) {
    match crate::differential::run_compiled(code) {
        crate::differential::Compiled::Value(v) => {
            assert_eq!(v.to_string(), expected, "program:\n{code}")
        }
        other => panic!("the program produced no value: {other}\n  program:\n{code}"),
    }
}

/// Check that the compiler produces an expected error on a program.
/// Use this for negative tests and for program features that have
/// only been partially implemented.
pub fn check_compile_error(code: &str, needle: &str) {
    let result = panic::catch_unwind(AssertUnwindSafe(|| run_pipeline(code)));
    let payload = match result {
        Ok(_) => panic!(
            "expected compile_program to panic with substring {needle:?}; \
             program ran to completion"
        ),
        Err(payload) => payload,
    };
    let msg = panic_message(&*payload);
    assert!(
        msg.contains(needle),
        "expected panic to contain {needle:?}; got: {msg}",
    );
}

// ---------------------------------------------------------------------------
// Value constructors
// ---------------------------------------------------------------------------

pub(crate) fn make_int_list(v: &[i64]) -> Tile {
    Tile::data_function(
        ColumnValue::uints_from_rows(0..v.len()),
        Box::new(Tile::Scalar(ColumnValue::Ints(v.into()))),
        Predicate::True,
        BitSet::new(),
    )
}

/// Order a materialized collection's bindings by key, so two tables holding the
/// same collection compare equal.
///
/// [`Value::Function`] compares its binding list positionally while a
/// collection's iteration order is unspecified ([`docs/chl-spec.md`](../../docs/chl-spec.md),
/// "3. Expression semantics"), so a comparison of two tables normalizes first. Keys that
/// no total order covers keep their delivery order.
pub(crate) fn sort_collection_bindings(value: Value) -> Value {
    match value {
        Value::Function(mut bindings) => {
            bindings.sort_by(|a, b| match (&a.input, &b.input) {
                (Value::UInt(x), Value::UInt(y)) => x.cmp(y),
                (Value::Int(x), Value::Int(y)) => x.cmp(y),
                (Value::String(x), Value::String(y)) => x.cmp(y),
                _ => std::cmp::Ordering::Equal,
            });
            Value::Function(bindings)
        }
        Value::Record(fields) => Value::Record(
            fields
                .into_iter()
                .map(|(k, v)| (k, sort_collection_bindings(v)))
                .collect(),
        ),
        other => other,
    }
}

/// [`sort_collection_bindings`] over every scalar cell of a tile.
///
/// Descends through the tilings that hold a cell rather than being one: a record's
/// fields, and a sealed function's codomain — an iterated collection of records each
/// holding a collection puts the tables one level below the rows.
pub(crate) fn sort_tile_collections(tile: Tile) -> Tile {
    match tile {
        Tile::Scalar(ColumnValue::Variants(vs)) => Tile::Scalar(ColumnValue::Variants(
            vs.into_iter().map(sort_collection_bindings).collect(),
        )),
        Tile::Record { fields, .. } => Tile::record(
            fields
                .into_iter()
                .map(|(k, t)| (k, sort_tile_collections(t)))
                .collect(),
        ),
        Tile::DataFunction {
            row_starts,
            domain,
            codomain,
            domain_predicate,
            deleted,
        } => Tile::DataFunction {
            row_starts,
            domain,
            codomain: Box::new(sort_tile_collections(*codomain)),
            domain_predicate,
            deleted,
        },
        other => other,
    }
}

pub(crate) fn make_tuple(v: &[Value]) -> Value {
    let mut map = HashMap::new();
    for (i, elem) in v.iter().enumerate() {
        map.insert(tuple_field(i), elem.clone());
    }
    Value::Record(map)
}

pub(crate) fn make_record(fields: &[(&str, Value)]) -> Value {
    Value::Record(
        fields
            .iter()
            .map(|(k, v)| (SmolStr::from(*k), v.clone()))
            .collect(),
    )
}

/// Extract a single named field from the record values of a collection tile, whether the
/// records are a tile per field or one column of records.
pub(crate) fn extract_record_field(tile: Tile, field: &str) -> ColumnValue {
    let Tile::DataFunction { codomain, .. } = tile else {
        panic!("expected a collection, got {tile:?}");
    };
    let missing =
        |names: Vec<&SmolStr>| -> ! { panic!("field {field:?} not found; available: {names:?}") };
    match *codomain {
        Tile::Record { mut fields, .. } => match fields.remove(field) {
            Some(tile) => scalar_tile_to_column_value(tile),
            None => missing(fields.keys().collect()),
        },
        Tile::Scalar(ColumnValue::Records(mut fields)) => match fields.remove(field) {
            Some(column) => column,
            None => missing(fields.keys().collect()),
        },
        other => panic!("expected records, got {other:?}"),
    }
}
