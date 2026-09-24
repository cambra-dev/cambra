//! Shared fixtures for the compilation-pipeline integration tests.
//!
//! All tests run through the full CCL pipeline via
//! [`compile_program`]:
//!
//! ```text
//! Python source
//!   → ccl::lower    (Python AST → CCL Expr)
//!   → ccl::infer    (type inference; annotates Lambda param_ty)
//!   → compile_ccl   (CCL Expr → dataflow operators)
//!   → subscribe()   (operator evaluation)
//! ```
//!
//! Unlike the unit tests in each module, these tests validate the composition
//! of all passes together.
//!
//! Each themed module reaches these via `use crate::helpers::*;`.
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

use std::any::Any;
use std::cell::RefCell;
use std::collections::HashMap;
use std::panic::{self, AssertUnwindSafe};
use std::rc::Rc;

use bit_set::BitSet;
use cambra::ccl::Expr;
use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program};
use cambra::interpreter::tile_operators::scalar_tile_to_column_value;
use cambra::interpreter::{
    ColumnValue, Consumer, FuncBinding, Predicate, Tile, Value, pull_laps, sort_function_by_domain,
    tuple_field,
};

// ---------------------------------------------------------------------------
// Helpers — CCL pipeline path
// ---------------------------------------------------------------------------

/// Lower `code` through the CCL pipeline (parse → `ccl::lower` → `ccl::infer`
/// → `compile_ccl` → subscribe → get) and return the resulting [`Tile`].
pub(crate) fn run_pipeline(code: &str) -> Tile {
    let mut ctx = GlobalContext::default();
    run_pipeline_with_ctx(&mut ctx, code).1
}

pub(crate) fn run_pipeline_with_ctx(ctx: &mut GlobalContext, code: &str) -> (Expr, Tile) {
    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });
    let mut compiled = compile_program(ctx, code, consumer).unwrap_or_render("<test>", code);
    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow(), "expected notification (pipeline path)");
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
        "pipeline path: producer did not converge within 1024 iterations"
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
    (*compiled.ast, result)
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
    let result = run_pipeline(code);
    let scalar = scalar_tile_to_column_value(result);
    assert_eq!(scalar.as_single().unwrap(), expected);
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
    let msg = panic_payload_to_string(&payload);
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
        ColumnValue::UInts((0..v.len()).collect()),
        Box::new(Tile::Scalar(ColumnValue::Ints(v.into()))),
        Predicate::True,
        BitSet::new(),
    )
}

/// A **materialized** collection value: the whole `key ↦ value` table in one
/// cell, which is how a product value holds a collection-valued component.
pub(crate) fn make_collection(bindings: &[(Value, Value)]) -> Value {
    Value::Function(
        bindings
            .iter()
            .map(|(input, output)| FuncBinding {
                input: input.clone(),
                output: output.clone(),
            })
            .collect(),
    )
}

/// A materialized collection over the positions `0..v.len()`, the shape a list
/// literal in a product component compiles to.
pub(crate) fn make_int_collection(v: &[i64]) -> Value {
    make_collection(
        &v.iter()
            .enumerate()
            .map(|(i, n)| (Value::UInt(i), Value::Int(*n)))
            .collect::<Vec<_>>(),
    )
}

/// Order a materialized collection's bindings by key, so two tables holding the
/// same collection compare equal.
///
/// [`Value::Function`] compares its binding list positionally while a
/// collection's iteration order is unspecified ([`docs/chl-spec.md`](../../docs/chl-spec.md),
/// "3. Expressions"), so a comparison of two tables normalizes first. Keys that
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
        Tile::Record(fields) => Tile::Record(
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
            .map(|(k, v)| (k.to_string(), v.clone()))
            .collect(),
    )
}

/// Extract a single named field from the record values of a collection tile.
pub(crate) fn extract_record_field(tile: Tile, field: &str) -> ColumnValue {
    let Tile::DataFunction { codomain, .. } = tile else {
        panic!("expected a collection, got {tile:?}");
    };
    let Tile::Record(mut fields) = *codomain else {
        panic!("expected Record codomain");
    };
    scalar_tile_to_column_value(fields.remove(field).unwrap_or_else(|| {
        panic!(
            "field {field:?} not found; available: {:?}",
            fields.keys().collect::<Vec<_>>()
        )
    }))
}
