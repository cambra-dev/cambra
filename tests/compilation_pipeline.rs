//! End-to-end pipeline tests: Python source → CCL lower → infer → compile → eval.
//!
//! These tests exercise the full compilation stack:
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
//! of all three passes together.

use cambra::interpreter::compile_ccl::compile_chl_expr;
use cambra::interpreter::{ColumnValue, Consumer, Guard, Scheduler};
use std::cell::RefCell;
use std::rc::Rc;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Compile a Python expression string and evaluate it as a column.
fn compile_and_eval(code: &str) -> ColumnValue {
    let mut scheduler = Scheduler::new();
    let mut op = compile_chl_expr(code, &mut scheduler).expect("compile failed");

    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });
    let mut producer = op.subscribe(Guard::universal(), consumer, None, &mut scheduler);
    scheduler.check_for_notifications();
    assert!(*notified.borrow(), "expected to be notified");
    producer.get().column_value
}

fn make_int_list(v: &[i64]) -> ColumnValue {
    ColumnValue::FunctionBindings {
        inputs: Box::new(ColumnValue::UInts((0..v.len()).collect())),
        outputs: Box::new(ColumnValue::Ints(v.into())),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_identity_comp() {
    // [x for x in [10, 20]] → [10, 20]
    assert_eq!(
        compile_and_eval("[x for x in [10, 20]]"),
        make_int_list(&[10, 20])
    );
}

#[test]
fn test_pipeline_const_body_comp() {
    // [42 for x in [10, 20]] → [42, 42]
    assert_eq!(
        compile_and_eval("[42 for x in [10, 20]]"),
        make_int_list(&[42, 42])
    );
}

#[test]
fn test_pipeline_binop_comp() {
    // [x + 2 for x in [10, 20]] → [12, 22]
    assert_eq!(
        compile_and_eval("[x + 2 for x in [10, 20]]"),
        make_int_list(&[12, 22])
    );
}

#[test]
fn test_pipeline_nested_comp() {
    // [y for y in [x for x in [10, 20]]] → [10, 20]
    assert_eq!(
        compile_and_eval("[y for y in [x for x in [10, 20]]]"),
        make_int_list(&[10, 20])
    );
}
