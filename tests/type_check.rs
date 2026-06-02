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
use cambra::chl_parser::{self, ast as chl_ast};
use cambra::interpreter::{BaseType, Extent, TestDataSource};
use rstest::rstest;

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
    let mut expr = lower_stmts(&stmts, &mut lctx)
        .into_result()
        .expect("lowering failed");
    infer(&mut expr, &mut ictx).expect("inference failed")
}

/// Like [`infer_program`] but expects inference to fail and returns all errors.
fn infer_program_err(code: &str) -> Vec<InferError> {
    let mut lctx = LoweringContext::default();
    let mut ictx = TypeInferenceContext::new();
    let stmts = parse_module(code);
    let mut expr = lower_stmts(&stmts, &mut lctx)
        .into_result()
        .expect("lowering failed");
    infer(&mut expr, &mut ictx).expect_err("expected inference error")
}

/// Parse a CHL module string into its statement list.
fn parse_module(code: &str) -> Vec<chl_ast::Spanned<chl_ast::Stmt>> {
    chl_parser::parse_module(code)
        .into_result()
        .expect("Failed to parse module")
        .body
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

// ---------------------------------------------------------------------------
// Literal tests
// ---------------------------------------------------------------------------

#[rstest]
#[case::int("2", BaseType::Int)]
#[case::string(r#""hi""#, BaseType::String)]
#[case::bool_lit("True", BaseType::Bool)]
#[case::none("None", BaseType::Unit)]
fn test_literal(#[case] code: &str, #[case] expected: BaseType) {
    assert_eq!(infer_program(code), Type::Base(expected));
}

// ---------------------------------------------------------------------------
// Arithmetic / comparison / boolean operator tests
// ---------------------------------------------------------------------------

#[rstest]
#[case::add_int("2 + 3", BaseType::Int)]
#[case::compare("2 > 1", BaseType::Bool)]
#[case::bool_and("True and False", BaseType::Bool)]
#[case::concat_strings(r#""a" + "b""#, BaseType::String)]
fn test_binary_op(#[case] code: &str, #[case] expected: BaseType) {
    assert_eq!(infer_program(code), Type::Base(expected));
}

// ---------------------------------------------------------------------------
// Let binding / scoping tests
// ---------------------------------------------------------------------------

#[rstest]
#[case::simple("x = 2\nx", BaseType::Int)]
#[case::chain("x = 2\ny = x\ny + x", BaseType::Int)]
fn test_let(#[case] code: &str, #[case] expected: BaseType) {
    assert_eq!(infer_program(code), Type::Base(expected));
}

// ---------------------------------------------------------------------------
// Unary operator tests
// ---------------------------------------------------------------------------

#[rstest]
#[case::neg("-2", BaseType::Int)]
#[case::not("not True", BaseType::Bool)]
fn test_unary_op(#[case] code: &str, #[case] expected: BaseType) {
    assert_eq!(infer_program(code), Type::Base(expected));
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
    // [x + y for x in [1, 2] for y in [10, 20]] — assert the full type.
    let ty = infer_program("[x + y for x in [1, 2] for y in [10, 20]]");
    assert_eq!(
        ty,
        Type::Fun(
            Box::new(Type::Tuple(vec![Type::UIntRange(2), Type::UIntRange(2)])),
            Box::new(int())
        ),
        "got {ty}"
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

#[rstest]
#[case::sum("sum([1, 2, 3])", BaseType::Int)]
#[case::max("max([1, 2, 3])", BaseType::Int)]
fn test_aggregate(#[case] code: &str, #[case] expected: BaseType) {
    assert_eq!(infer_program(code), Type::Base(expected));
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

#[rstest]
#[case::literal(
    r"
x: int = 2
x
",
    BaseType::Int
)]
#[case::expr(
    r"
x: int = 1 + 2
x
",
    BaseType::Int
)]
fn test_ann_assign_ok(#[case] code: &str, #[case] expected: BaseType) {
    assert_eq!(infer_program(code), Type::Base(expected));
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

#[rstest]
#[case::int(
    r"
if True:
    1
else:
    0
",
    BaseType::Int
)]
#[case::string(
    r#"
if True:
    "yes"
else:
    "no"
"#,
    BaseType::String
)]
#[case::with_let(
    r"
x = 5
if x > 3:
    10
else:
    0
",
    BaseType::Int
)]
#[case::elif_chain(
    r"
if True:
    1
elif False:
    2
else:
    3
",
    BaseType::Int
)]
fn test_if_else(#[case] code: &str, #[case] expected: BaseType) {
    assert_eq!(infer_program(code), Type::Base(expected));
}

#[rstest]
#[case::int("1 if True else 0", BaseType::Int)]
#[case::string(r#""yes" if True else "no""#, BaseType::String)]
fn test_ternary(#[case] code: &str, #[case] expected: BaseType) {
    assert_eq!(infer_program(code), Type::Base(expected));
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

// ---------------------------------------------------------------------------
// Edge cases: Recursive types, unapplied lambdas, etc.
// ---------------------------------------------------------------------------

#[test]
fn test_recursive_type_rejection() {
    // lambda x: x(x) -> Recursive type error
    let err = infer_program_err("lambda x: x(x)");
    assert!(
        err.iter().any(|e| {
            if let InferError::Unsupported(msg) = e {
                msg.contains("recursive type")
            } else {
                false
            }
        }),
        "expected Unsupported recursive type error, got {err:?}"
    );
}

#[rstest]
#[case::comparison(
    r"
f = lambda x: x > 1
f
",
    Type::Fun(Box::new(int()), Box::new(bool_ty()))
)]
#[case::arithmetic(
    r"
f = lambda x: x + 1
f
",
    Type::Fun(Box::new(int()), Box::new(int()))
)]
fn test_lambda_unapplied(#[case] code: &str, #[case] expected: Type) {
    assert_eq!(infer_program(code), expected);
}

#[test]
fn test_generic_identity() {
    // f = lambda x: x; f -> Fun(?a, ?b)
    // simple-sub allows unconstrained parameters to remain unresolved.
    let ty = infer_program("f = lambda x: x\nf");
    if let Type::Fun(dom, cod) = ty {
        assert!(matches!(*dom, Type::Infer(_)));
        assert!(matches!(*cod, Type::Infer(_)));
    } else {
        panic!("expected Fun type, got {ty}");
    }
}

// ---------------------------------------------------------------------------
// Subtyping / variance coverage
// ---------------------------------------------------------------------------

/// Tuple index propagation: `t[0]` flows the element's type out of a
/// heterogeneous tuple, exercising the partial-tuple / projection rule.
#[test]
fn test_tuple_index_heterogeneous() {
    assert_eq!(infer_program(r#"(1, "a")[0]"#), int());
    assert_eq!(infer_program(r#"(1, "a")[1]"#), string());
}

/// An unconstrained identity applied to a concrete value must resolve all
/// inference variables — no `Type::Infer` should survive in the result.
#[test]
fn test_unconstrained_identity_applied_resolves() {
    // bind via Let so `f(5)` is a named call (lowering doesn't yet
    // support a lambda-literal in call position).
    let ty = infer_program("f = lambda x: x\nf(5)");
    assert_eq!(ty, int());
}

/// A refined comprehension carries its filter predicate as a refinement on
/// the inferred function's domain (the predicate is `__iter_record_restr`-
/// bound). This pins down the post-§1.3 shape: the refinement is sourced
/// from the AST node and reapplied by `type_saturate`, so the inferred type
/// still surfaces it — what changed is the *source of truth*, not the type
/// shape.
#[test]
fn test_filtered_comprehension_has_refinement_on_domain() {
    let ty = infer_program("[x for x in [1, 2, 3] if x > 1]");
    if let Type::Fun(dom, cod) = &ty {
        assert!(
            matches!(&**dom, Type::Refinement(_, _)),
            "expected Refinement-wrapped domain, got {ty}"
        );
        assert_eq!(**cod, int(), "expected codomain Int, got {ty}");
    } else {
        panic!("expected Fun type, got {ty}");
    }
}
