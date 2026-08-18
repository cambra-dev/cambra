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

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use bit_set::BitSet;
use cambra::ccl::Expr;
use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program};
use cambra::interpreter::tile_operators::scalar_tile_to_column_value;
use cambra::interpreter::{
    ColumnValue, Consumer, Predicate, Tile, Value, sort_sealed_function_by_domain, tuple_field,
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
    // A single `get` is not always enough to fully drain a producer.  Some
    // tile operators advance their internal state by one step per pull
    // (notably a mutation loop's store/drive cycle, where each pull decides one
    // more position of the recurrence).
    // Loop until the producer reports a terminal tile, with a generous
    // iteration cap to catch the regression where the cycle stops making
    // progress without converging.
    let universal = producer.tiling().universal_guard();
    let mut result = producer.get(universal.clone());
    let mut iterations = 0usize;
    while !result.is_terminal() {
        iterations += 1;
        assert!(
            iterations < 1024,
            "pipeline path: producer did not converge within 1024 iterations"
        );
        result = producer.get(universal.clone());
    }
    result.compact();
    // Release everything, then pull once more: a released region must never come
    // back out, so this answers empty or trips the contract assertion.
    producer.release(universal.clone());
    let after = producer.get(universal.clone());
    assert!(
        after.is_empty(),
        "pull after a universal release returned {after:?}"
    );
    (compiled.ast, result)
}

// ---------------------------------------------------------------------------
// Parity assertion helpers
// ---------------------------------------------------------------------------

/// Assert `code` produces `expected` via the pipeline path.
pub(crate) fn check_tile(code: &str, expected: Tile) {
    assert_eq!(
        sort_sealed_function_by_domain(run_pipeline(code)),
        sort_sealed_function_by_domain(expected),
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

// ---------------------------------------------------------------------------
// Value constructors
// ---------------------------------------------------------------------------

pub(crate) fn make_int_list(v: &[i64]) -> Tile {
    Tile::SealedFunction {
        domain: ColumnValue::UInts((0..v.len()).collect()),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(v.into()))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
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

/// Extract a single named field from the record codomain of a SealedFunction tile.
pub(crate) fn extract_record_field(tile: Tile, field: &str) -> ColumnValue {
    let Tile::SealedFunction { codomain, .. } = tile else {
        panic!("expected SealedFunction, got {tile:?}");
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
