//! Integration tests: Python source → `ccl::lower` → `ccl::infer` → [`Type`].
//!
//! These tests validate the lower + infer pipeline without invoking the
//! compiler or interpreter. They are more stable than the end-to-end
//! compilation tests because they stop before the compilation step.
//!
//! ```text
//! Python source
//!   → ccl::lower    (Python AST → CCL Expr)
//!   → ccl::infer    (type inference; annotates every node)
//!   → Type          (test assertion here)
//! ```

use std::{cell::RefCell, rc::Rc};

use cambra::ccl::{
    Type,
    infer::{InferError, TypeInferenceContext, infer},
    lower::{LoweringContext, lower_stmts},
};
use cambra::interpreter::{BaseType, Extent, TestDataSource};
use rustpython_parser::{ast as pyast, parser};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Parse Python module code, lower to CCL, run type inference, and return the
/// inferred type of the whole program. Panics on lowering or inference failure.
fn infer_program(code: &str) -> Type {
    infer_program_with_sources(code, &[])
}

/// Like [`infer_program`] but with data sources pre-registered before lowering
/// and inference. Each entry is `(source_name, element_type)`.
fn infer_program_with_sources(code: &str, sources: &[(&str, Type)]) -> Type {
    let mut lctx = LoweringContext::default();
    let mut ictx = TypeInferenceContext::new();
    for (name, elem_ty) in sources {
        let output_extent = match elem_ty {
            Type::Base(bt) => Extent::Base(bt.clone()),
            _ => panic!("infer_program_with_sources: unsupported elem_ty {elem_ty:?}"),
        };
        let stub = Rc::new(RefCell::new(TestDataSource::new(
            name,
            elem_ty.clone(),
            output_extent,
        )));
        lctx.register_source(*name, stub);
        // Sources are registered with type Fun(DataSource(name), elem_ty).
        ictx.register_source_type(
            name,
            Type::Fun(
                Box::new(Type::DataSource(name.to_string())),
                Box::new(elem_ty.clone()),
            ),
        );
    }
    let stmts = parse_module(code);
    let mut expr = lower_stmts(&stmts, &mut lctx).expect("lowering failed");
    infer(&mut expr, &mut ictx).expect("inference failed")
}

/// Like [`infer_program`] but expects inference to fail and returns all errors.
fn infer_program_err(code: &str) -> Vec<InferError> {
    let mut lctx = LoweringContext::default();
    let mut ictx = TypeInferenceContext::new();
    let stmts = parse_module(code);
    let mut expr = lower_stmts(&stmts, &mut lctx).expect("lowering failed");
    infer(&mut expr, &mut ictx).expect_err("expected inference error")
}

/// Parse a Python module string into its statement list.
fn parse_module(code: &str) -> Vec<pyast::Stmt> {
    let result =
        parser::parse(code, parser::Mode::Module, "<test>").expect("Failed to parse module");
    match result {
        pyast::Mod::Module { body, .. } => body,
        other => panic!("expected Module, got {other:?}"),
    }
}

/// Convenience alias for `Type::Base(BaseType::Int)`.
fn int() -> Type {
    Type::Base(BaseType::Int)
}

/// Convenience alias for `Type::Base(BaseType::String)`.
fn string() -> Type {
    Type::Base(BaseType::String)
}

/// Convenience alias for `Type::Base(BaseType::Bool)`.
fn bool_ty() -> Type {
    Type::Base(BaseType::Bool)
}

/// Convenience alias for `Type::Base(BaseType::Unit)`.
fn unit() -> Type {
    Type::Base(BaseType::Unit)
}

// ---------------------------------------------------------------------------
// Literal tests
// ---------------------------------------------------------------------------

#[test]
fn test_literal_int() {
    assert_eq!(infer_program("2"), int());
}

#[test]
fn test_literal_string() {
    assert_eq!(infer_program(r#""hi""#), string());
}

#[test]
fn test_literal_bool() {
    assert_eq!(infer_program("True"), bool_ty());
}

#[test]
fn test_literal_none() {
    assert_eq!(infer_program("None"), unit());
}

// ---------------------------------------------------------------------------
// Arithmetic / comparison / boolean operator tests
// ---------------------------------------------------------------------------

#[test]
fn test_add_int_int() {
    assert_eq!(infer_program("2 + 3"), int());
}

#[test]
fn test_compare_int() {
    assert_eq!(infer_program("2 > 1"), bool_ty());
}

#[test]
fn test_bool_and() {
    assert_eq!(infer_program("True and False"), bool_ty());
}

#[test]
fn test_concat_strings() {
    assert_eq!(infer_program(r#""a" + "b""#), string());
}

// ---------------------------------------------------------------------------
// Let binding / scoping tests
// ---------------------------------------------------------------------------

#[test]
fn test_let_simple() {
    assert_eq!(
        infer_program(
            r#"
x = 2
x
"#
            .trim()
        ),
        int()
    );
}

#[test]
fn test_let_chain() {
    assert_eq!(
        infer_program(
            r#"
x = 2
y = x
y + x
"#
            .trim()
        ),
        int()
    );
}

// ---------------------------------------------------------------------------
// Unary operator tests
// ---------------------------------------------------------------------------

#[test]
fn test_unary_neg() {
    assert_eq!(infer_program("-2"), int());
}

#[test]
fn test_unary_not() {
    assert_eq!(infer_program("not True"), bool_ty());
}

// ---------------------------------------------------------------------------
// List literal and comprehension tests
// ---------------------------------------------------------------------------

#[test]
fn test_list_literal() {
    assert_eq!(
        infer_program("[1, 2, 3]"),
        Type::Fun(Box::new(Type::UIntRange(3)), Box::new(int()))
    );
}

#[test]
fn test_list_comp_identity() {
    // [x for x in [1, 2]] — element type inferred from inner list
    assert_eq!(
        infer_program("[x for x in [1, 2]]"),
        Type::Fun(Box::new(Type::UIntRange(2)), Box::new(int()))
    );
}

#[test]
fn test_list_comp_arithmetic_body() {
    // [x + 1 for x in [1, 2]]
    assert_eq!(
        infer_program("[x + 1 for x in [1, 2]]"),
        Type::Fun(Box::new(Type::UIntRange(2)), Box::new(int()))
    );
}

#[test]
fn test_list_comp_two_gens() {
    // [x + y for x in [1, 2] for y in [10, 20]] — codomain is Int
    let ty = infer_program("[x + y for x in [1, 2] for y in [10, 20]]");
    assert_eq!(
        ty.codomain(),
        Some(int()),
        "expected codomain Int, got {ty}"
    );
}

#[test]
fn test_list_comp_with_filter() {
    // [x for x in [1, 2, 3] if x > 1] — codomain is Int
    let ty = infer_program("[x for x in [1, 2, 3] if x > 1]");
    assert_eq!(
        ty.codomain(),
        Some(int()),
        "expected codomain Int, got {ty}"
    );
}

// ---------------------------------------------------------------------------
// Aggregate tests
// ---------------------------------------------------------------------------

#[test]
fn test_sum() {
    assert_eq!(infer_program("sum([1, 2, 3])"), int());
}

#[test]
fn test_max() {
    assert_eq!(infer_program("max([1, 2, 3])"), int());
}

// ---------------------------------------------------------------------------
// Tuple tests
// ---------------------------------------------------------------------------

#[test]
fn test_tuple() {
    assert_eq!(
        infer_program(r#"(1, "a")"#),
        Type::Tuple(vec![int(), string()])
    );
}

#[test]
fn test_tuple_index() {
    assert_eq!(infer_program(r#"(1, "a")[0]"#), int());
}

// ---------------------------------------------------------------------------
// Type annotation tests
// ---------------------------------------------------------------------------

#[test]
fn test_ann_assign_int_ok() {
    // x: int = 2; x — annotation matches inferred Int
    assert_eq!(
        infer_program(
            r#"
x: int = 2
x
"#
            .trim()
        ),
        int()
    );
}

#[test]
fn test_ann_assign_compatible_expr() {
    // x: int = 1 + 2; x — annotation-compatible with inferred Int
    assert_eq!(
        infer_program(
            r#"
x: int = 1 + 2
x
"#
            .trim()
        ),
        int()
    );
}

#[test]
fn test_ann_assign_mismatch() {
    // x: str = 2; x — mismatch: annotation says String but value is Int
    let err = infer_program_err(
        r#"
x: str = 2
x
"#
        .trim(),
    );
    assert!(
        err.iter()
            .any(|e| matches!(e, InferError::AnnotationMismatch { .. })),
        "expected AnnotationMismatch, got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Data source tests
// ---------------------------------------------------------------------------

#[test]
fn test_source_list_comp_element_type() {
    // [x for x in mysource()] with mysource registered as String
    let ty = infer_program_with_sources(
        "[x for x in mysource()]",
        &[("mysource", Type::Base(BaseType::String))],
    );
    assert_eq!(
        ty.codomain(),
        Some(string()),
        "expected codomain String, got {ty}"
    );
}

// ---------------------------------------------------------------------------
// GroupBy + aggregate tests
// ---------------------------------------------------------------------------

#[test]
fn test_groupby_aggregate() {
    // groups = groupby([1, 2, 3], lambda x: x)
    // g = groups(1)
    // sum(g)
    // Expected: Int (sum of a group of integers)
    let ty = infer_program(
        r#"
groups = groupby([1, 2, 3], lambda x: x)
g = groups(1)
sum(g)
"#
        .trim(),
    );
    assert_eq!(ty, int(), "expected Int, got {ty}");
}

// ---------------------------------------------------------------------------
// Case / if expression tests
// ---------------------------------------------------------------------------

#[test]
fn test_if_else_int() {
    assert_eq!(
        infer_program(
            r#"
if True:
    1
else:
    0
"#
            .trim()
        ),
        int()
    );
}

#[test]
fn test_if_else_string() {
    assert_eq!(
        infer_program(
            r#"
if True:
    "yes"
else:
    "no"
"#
            .trim()
        ),
        string()
    );
}

#[test]
fn test_if_else_with_let() {
    // let binding in scope for the condition
    assert_eq!(
        infer_program(
            r#"
x = 5
if x > 3:
    10
else:
    0
"#
            .trim()
        ),
        int()
    );
}

#[test]
fn test_elif_chain() {
    assert_eq!(
        infer_program(
            r#"
if True:
    1
elif False:
    2
else:
    3
"#
            .trim()
        ),
        int()
    );
}

#[test]
fn test_ternary_int() {
    assert_eq!(infer_program("1 if True else 0"), int());
}

#[test]
fn test_ternary_string() {
    assert_eq!(infer_program(r#""yes" if True else "no""#), string());
}

#[test]
fn test_if_else_arm_type_mismatch() {
    // Arms return different types — inference must report a type mismatch.
    let err = infer_program_err(
        r#"
if True:
    1
else:
    "oops"
"#
        .trim(),
    );
    assert!(
        err.iter()
            .any(|e| matches!(e, InferError::TypeMismatch { .. })),
        "expected TypeMismatch, got {err:?}"
    );
}
