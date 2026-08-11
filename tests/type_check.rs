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
    FieldKey, HistoryKind, Lit, Type, TypeKind,
    infer::{
        InferError, LocatedInferError, TypeInferenceContext, check_pre_desugar, infer,
        lit_singleton,
    },
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
        // Registered by element type; the data-function type (`DataSource(name)
        // ⤇ elem_ty`, `Data`) is constructed inside `register_source_type`.
        ictx.register_source_type(name, elem_ty.clone());
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
    infer(&mut expr, &mut ictx)
        .map_err(LocatedInferError::bare)
        .expect_err("expected inference error")
}

/// Like [`infer_program_with_sources`] but expects inference to fail.
fn infer_program_with_sources_err(code: &str, sources: &[(&str, Type)]) -> Vec<InferError> {
    let mut lctx = LoweringContext::default();
    let mut ictx = TypeInferenceContext::new();
    for (name, elem_ty) in sources {
        let output_extent = match elem_ty {
            Type::Base(bt) => Extent::Base(bt.clone()),
            _ => panic!("infer_program_with_sources_err: unsupported elem_ty {elem_ty:?}"),
        };
        let stub = Rc::new(RefCell::new(TestDataSource::new(
            name,
            elem_ty.clone(),
            output_extent,
        )));
        lctx.register_source(*name, stub);
        ictx.register_source_type(name, elem_ty.clone());
    }
    let stmts = parse_module(code);
    let mut expr = lower_stmts(&stmts, &mut lctx)
        .into_result()
        .expect("lowering failed");
    infer(&mut expr, &mut ictx)
        .map_err(LocatedInferError::bare)
        .expect_err("expected inference error")
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

/// The type of the integer literal `n` — its **singleton**,
/// `{Int | __elem == n}` (rendered `n`). A literal is typed by what it is, not
/// merely by its base ([`lit_singleton`]), so a test that expects a program to
/// evaluate to a known constant should say which one.
fn int_lit(n: i64) -> Type {
    lit_singleton(&Lit::Int(n))
}

/// The type of the string literal `s` — see [`int_lit`].
fn str_lit(s: &str) -> Type {
    lit_singleton(&Lit::String(s.to_string()))
}

/// The type of the boolean literal `b` — see [`int_lit`].
fn bool_lit(b: bool) -> Type {
    lit_singleton(&Lit::Bool(b))
}

/// Convenience alias for `Type::Base(BaseType::String)`.
fn string() -> Type {
    Type::Base(BaseType::String)
}

/// Convenience alias for `Type::Base(BaseType::Bool)`.
fn bool_ty() -> Type {
    Type::Base(BaseType::Bool)
}

/// The sum a control-flow join of **`box`ed** collection arms builds:
/// `Σ σ ∈ {𝐷ᵢ ⤇ elem}. σ`, whose candidates are whole collection types.
///
/// This is the *unfactored* form. `box` boxes a whole type, so each arm is already a
/// one-candidate sum in this shape, and joining them by width keeps it. Contrast
/// [`cambra::ccl::SigmaType::over`], the *factored* `Σ 𝐷 ∈ {𝐷ᵢ}. 𝐷 ⤇ elem`, whose
/// candidates are domains. The two are equivalent — each subtypes the other by Σ-width —
/// and structurally distinct, which is why `assert_eq!` can tell them apart even though
/// `Display` renders both in the factored spelling.
fn boxed_collection_sum(domains: Vec<Type>, elem: Type) -> Type {
    Type::Sigma(Box::new(cambra::ccl::SigmaType::of(TypeKind::Enumerated(
        domains
            .into_iter()
            .map(|d| Type::data_fun(d, elem.clone()))
            .collect(),
    ))))
}

// ---------------------------------------------------------------------------
// Literal tests
// ---------------------------------------------------------------------------

/// A literal is typed by **which** literal it is: its base refined by the singleton
/// `__elem == lit`. `unit` is the exception — one inhabitant, so the singleton would
/// say nothing its base does not.
#[rstest]
#[case::int("2", int_lit(2))]
#[case::string(r#""hi""#, str_lit("hi"))]
#[case::bool_lit("True", bool_lit(true))]
#[case::unit("()", Type::Base(BaseType::Unit))]
fn test_literal(#[case] code: &str, #[case] expected: Type) {
    assert_eq!(infer_program(code), expected);
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

/// A binding propagates its value's type unchanged, singleton and all — `x = 2`
/// makes `x` *the* `2`. The chain case shows the other half: `y + x` joins two
/// singletons, and a join intersects refinements, so the sum is plain `Int`.
#[rstest]
#[case::simple("x = 2\nx", int_lit(2))]
#[case::chain("x = 2\ny = x\ny + x", int())]
fn test_let(#[case] code: &str, #[case] expected: Type) {
    assert_eq!(infer_program(code), expected);
}

// ---------------------------------------------------------------------------
// Unary operator tests
// ---------------------------------------------------------------------------

/// `-2` folds to the literal `-2` at lowering, so it is a literal like any other and
/// carries its own singleton. `not True` does not fold — a unary operator computes a
/// *new* value, and its result takes no refinement from its operand.
#[rstest]
#[case::neg("-2", int_lit(-2))]
#[case::not("not True", bool_ty())]
fn test_unary_op(#[case] code: &str, #[case] expected: Type) {
    assert_eq!(infer_program(code), expected);
}

// ---------------------------------------------------------------------------
// List literal and comprehension tests
// ---------------------------------------------------------------------------

#[test]
fn test_list_literal() {
    // A list literal is a **data** function (collection domain).
    assert_eq!(
        infer_program("[1, 2, 3]"),
        Type::data_fun(Type::UIntRange(3), int())
    );
}

#[test]
fn test_conditional_collection_forms_sigma() {
    // `box` introduces the sum; the control-flow join then relates two sums by
    // width and is lossless, keeping both domains (never a lossy meet-domain
    // function). `box([1, 2])` is `Σ σ ∈ {[0, 1]}. (σ ⤇ Int)`, `box([1, 2, 3])`
    // is `Σ σ ∈ {[0, 2]}. (σ ⤇ Int)`, so the join is `Σ σ ∈ {[0, 1], [0, 2]}.
    // (σ ⤇ Int)` — the witness is the runtime branch discriminant (see
    // type-inference.md §4.6). Without the `box`es the arms are plain data
    // functions and their join is the domain conflict, which is the point of
    // making introduction a term.
    // Compared modulo binder identity: the inferred sum and this hand-built one are two
    // derivations, so their binders differ by construction while the types are the same.
    assert_eq!(
        infer_program("box([1, 2]) if True else box([1, 2, 3])").without_witness_binders(),
        boxed_collection_sum(vec![Type::UIntRange(2), Type::UIntRange(3)], int())
            .without_witness_binders()
    );
}

#[test]
fn test_conditional_collection_heterogeneous_domains() {
    // A conditional over a list literal and a **registered source** joins their
    // (different-kind) domains losslessly into the Σ — `[0, 2]` and
    // `source(mysrc)`. This only holds because a registered source is a `Data`
    // collection: were it miscategorized as a `Compute` capability, the join
    // would take the contravariant meet and collide at coalesce. Regression for
    // that source-categorization invariant (`register_source_type` constructs the
    // `Data` arrow; the kind is intrinsic, not caller-supplied).
    // Modulo binder identity: two derivations, so the binders differ by construction.
    assert_eq!(
        infer_program_with_sources(
            "box([1, 2, 3]) if True else box(mysrc())",
            &[("mysrc", int())],
        )
        .without_witness_binders(),
        boxed_collection_sum(
            vec![Type::UIntRange(3), Type::DataSource("mysrc".into())],
            int()
        )
        .without_witness_binders()
    );
}

#[test]
fn test_conditional_collection_same_domain_collapses() {
    // Idempotence: when both arms share a domain, the Sigma collapses back
    // to a plain data function — no spurious 2-choice Sigma (`join_domains`
    // dedups the shared domain).
    assert_eq!(
        infer_program("[1, 2] if True else [3, 4]"),
        Type::data_fun(Type::UIntRange(2), int())
    );
}

#[test]
fn test_conditional_record_arms_join_by_field_intersection() {
    // `emit_case` types arms by the lattice join, so two record arms with
    // differing fields no longer fail; they join to the common-field
    // intersection at positive polarity. `{a, b} if c else {a, c}` → `{a: …}`.
    // The surviving field joins like any other merge point: both arms deposit
    // the same `1`, so its singleton survives — width-narrowing to the common
    // fields is orthogonal to which witnesses each shared field keeps. Pins the
    // widening so a future change to record-arm polarity can't silently alter
    // which conditionals type-check. (design/type-inference.md, Case-arm
    // lattice joins)
    assert_eq!(
        infer_program("(a=1, b=2) if True else (a=1, c=3)").to_string(),
        "{a: 1}"
    );
    // Arms disagreeing on the shared field keep the field but not the witness.
    assert_eq!(
        infer_program("(a=1, b=2) if True else (a=7, c=3)").to_string(),
        "{a: Int}"
    );
}

#[test]
fn test_aggregate_over_scalar_lambda_is_rejected() {
    // Summing a plain lambda: a bare `λ` is a capability, built concrete
    // `Compute` (kind is a provenance property, not a domain guess). `sum`
    // demands a `Data` collection to iterate, so the argument constraint is
    // `(Int ⇒ Int) <: (?  ⤇ Int)` — the `Compute <: Data` violation, rejected up
    // front in `constrain_kind` (emission), never routed through a kind var.
    // Regression that a capability supplied as a domain is a clean error, not a
    // silent miskind or a debug panic.
    let errs = infer_program_err(
        r"
f = \i -> i + 1
sum(f)",
    );
    assert!(
        errs.iter().any(|e| matches!(
            e,
            InferError::TypeMismatch { ctx, .. }
                if ctx.contains("compute function") && ctx.contains("data collection")
        )),
        "expected a compute-where-data-required rejection, got {errs:?}"
    );
}

// A `def`/lambda parameter's type annotation is a **checking-mode declaration**
// that lowering must carry to the lambda so inference enforces it at the call
// site — mirroring variable ascription (`x: T = e`). Regression for a
// long-standing lowering gap: `uncurry_params` attached only `Mut(…)`
// annotations and dropped every other one, so a `def` param was inferred purely
// from its body and any argument was accepted.
#[test]
fn test_def_param_annotation_enforced() {
    // A scalar annotation is enforced at the call site: an identity body infers
    // nothing on its own, so without the annotation any argument was accepted.
    // The caller's singleton `1` survives, because an annotation is one *bound* on
    // the param rather than a replacement for it — the same as a value ascription
    // (`x: Int = 1` keeps the singleton) and as the unannotated case at the end of
    // this test.
    assert_eq!(infer_program("def g(a: Int):\n    a\ng(1)"), int_lit(1));
    assert!(!infer_program_err("def g(a: Int):\n    a\ng(\"x\")").is_empty());
    // A `List(Int)` annotation enforces the element type through the annotation.
    assert_eq!(
        infer_program("def g(a: List(Int)):\n    sum(a)\ng(box([1, 2, 3]))"),
        int()
    );
    assert!(
        !infer_program_err("def g(a: List(Int)):\n    sum(a)\ng(box([\"a\", \"b\"]))").is_empty()
    );
    // An unannotated param still infers purely from use.
    assert_eq!(infer_program("def g(a):\n    a\ng(\"x\")"), str_lit("x"));
}

/// A Σ-typed parameter in a **multi-parameter** function, consumed. This needs all
/// three of the uncurried **tuple** param, a **Σ**, and a **consumption** — the
/// controls below isolate that — and it is what the single domain carrier buys: the
/// opened sum and the concrete tuple-field type reach one variable through the same
/// slot, where the merge reconciles them, instead of arriving as two independent
/// contributions that coalesce rejects as incompatible lower bounds.
#[test]
fn sigma_param_in_a_multi_param_function_is_consumable() {
    assert_eq!(
        infer_program(
            r"
def f(a: List(Int), b: Int):
    sum(a) + b
f(box([1,2]),3)"
        ),
        int()
    );
    // The single-Σ diagnosis, pinned so a future fix cannot pass for the wrong
    // reason: two Σ params must work too, and the controls must keep working.
    assert_eq!(
        infer_program(
            r"
def f(a: List(Int), b: List(Int)):
    sum(a) + sum(b)
f(box([1,2]),box([3,4,5]))"
        ),
        int()
    );
}

/// A `List` parameter under a **domain-preserving** consumer, where the demand's
/// domain variable rides into the result rather than collapsing under a scalar. This
/// is the other half of the domain meet: the comprehension's fresh domain variable
/// meets the annotation's described kind, and the sum is what survives — so the
/// result is a `List`, not an arrow over an unresolved domain.
#[test]
fn list_param_under_a_domain_preserving_consumer() {
    assert_eq!(
        infer_program(
            r"
def f(a: List(Int)):
    [x + 1 for x in a]
sum(f(box([1,2])))"
        ),
        int()
    );
    // Two consumers of one `List` param — a uniform one and a domain-preserving
    // one — so the annotation's kind meets two separate demands.
    assert_eq!(
        infer_program(
            r"
def f(a: List(Int)):
    sum([x + 1 for x in a]) + sum(a)
f(box([1,2]))"
        ),
        int()
    );
}

/// A `List` parameter narrowed by a **concrete** demand: `a`'s two upper bounds are
/// its own `List(Int)` annotation and `g`'s `Array(2,Int)` demand, and the meet is
/// the `Array` — kind containment (`{[0,2)} ⊆ UIntRanges`) says the listed domain is
/// the narrower of the two. The opposite verdict is what keeps a `List` from being
/// silently narrowed when the demand is *not* in the kind.
///
#[test]
fn list_param_meets_a_concrete_demand_at_the_narrower_domain() {
    assert_eq!(
        infer_program(
            r"
def g(b: Array(2,Int)):
    sum(b)
def f(a: List(Int)):
    g(a)
f(box([1,2]))"
        ),
        int()
    );
}

/// The controls for the pin above — these pass today and must keep passing, since
/// they are what localize the failure to "tuple param + Σ + consumption".
#[test]
fn sigma_param_controls_single_and_unconsumed() {
    // Single Σ param, consumed.
    assert_eq!(
        infer_program(
            r"
def f(a: List(Int)):
    sum(a)
f(box([1,2]))"
        ),
        int()
    );
    // Plain data function (not a Σ) alongside a scalar, consumed.
    assert_eq!(
        infer_program(
            r"
def f(a: Array(2,Int), b: Int):
    sum(a) + b
f([1,2],3)"
        ),
        int()
    );
    // Σ present in a multi-param function but never consumed. `b`'s annotation
    // bounds the param without replacing it, so the caller's singleton survives.
    assert_eq!(
        infer_program(
            r"
def f(a: List(Int), b: Int):
    b
f(box([1,2]),3)"
        ),
        int_lit(3)
    );
}

#[test]
fn test_multiarg_def_param_annotation_enforced() {
    // Each tupled parameter's annotation is enforced independently, and each
    // bounds its param rather than replacing it, so the caller's singleton
    // survives (see `test_def_param_annotation_enforced`).
    assert_eq!(
        infer_program("def g(a: Int, b: String):\n    a\ng(1, \"x\")"),
        int_lit(1)
    );
    // Wrong type on `a` is rejected.
    assert!(!infer_program_err("def g(a: Int, b: String):\n    a\ng(\"x\", \"y\")").is_empty());
    // Wrong type on `b` is rejected.
    assert!(!infer_program_err("def g(a: Int, b: String):\n    a\ng(1, 2)").is_empty());
    // Fully unannotated params still infer from use.
    assert_eq!(infer_program("def g(a, b):\n    a + b\ng(1, 2)"), int());
}

#[test]
fn test_list_comp_identity() {
    // [x for x in [1, 2]] — element type inferred from inner list
    assert_eq!(
        infer_program("[x for x in [1, 2]]"),
        Type::Fun {
            name: None,
            kind: cambra::ccl::FunKind::Data,
            domain: Box::new(Type::UIntRange(2)),
            codomain: Box::new(int())
        }
    );
}

#[test]
fn test_list_comp_arithmetic_body() {
    // [x + 1 for x in [1, 2]]
    assert_eq!(
        infer_program("[x + 1 for x in [1, 2]]"),
        Type::Fun {
            name: None,
            kind: cambra::ccl::FunKind::Data,
            domain: Box::new(Type::UIntRange(2)),
            codomain: Box::new(int())
        }
    );
}

#[test]
fn test_list_comp_two_gens() {
    // [x + y for x in [1, 2] for y in [10, 20]] — assert the full type.
    let ty = infer_program("[x + y for x in [1, 2] for y in [10, 20]]");
    assert_eq!(
        ty,
        Type::Fun {
            name: None,
            kind: cambra::ccl::FunKind::Data,
            domain: Box::new(Type::Tuple(vec![Type::UIntRange(2), Type::UIntRange(2)])),
            codomain: Box::new(int())
        },
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

#[test]
fn test_list_comp_non_bool_filter_rejected() {
    // [x for x in [1, 2, 3] if x] — the filter `x` is an Int, not a Bool.
    // The `if` guard lowers to a refinement predicate (a closed function
    // `D ⇒ Bool`); inference must reject the non-Bool predicate body rather
    // than silently accepting it.
    let errs = infer_program_err("[x for x in [1, 2, 3] if x]");
    assert!(
        errs.iter()
            .any(|e| matches!(e, InferError::TypeMismatch { .. })),
        "expected a TypeMismatch from the non-Bool filter, got {errs:?}"
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
        Type::Tuple(vec![int_lit(1), str_lit("a")])
    );
}

#[test]
fn test_tuple_index() {
    assert_eq!(infer_program(r#"(1, "a").0"#), int_lit(1));
}

// ---------------------------------------------------------------------------
// Type annotation tests
// ---------------------------------------------------------------------------

/// An ascription is one-way: it must *admit* the value, and the value keeps whatever
/// more precise type it already had. So annotating a literal at its base does not
/// widen it, while an expression that computes a new value has nothing to keep.
#[rstest]
#[case::literal(
    r"
x: Int = 2
x
",
    int_lit(2)
)]
#[case::expr(
    r"
x: Int = 1 + 2
x
",
    int()
)]
#[case::wildcard(
    r"
x: _ = 2
x
",
    int_lit(2)
)]
#[case::wildcard_str(
    r#"
x: _ = "hi"
x
"#,
    str_lit("hi")
)]
fn test_ann_assign_ok(#[case] code: &str, #[case] expected: Type) {
    assert_eq!(infer_program(code), expected);
}

#[test]
fn test_ann_assign_mismatch() {
    // x: String = 2; x — mismatch: annotation says String but value is Int
    let err = infer_program_err(
        r#"
x: String = 2
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

/// A `List(_)` annotation is a value-witness Σ (`Σ n:UInt. {i | i < n} ⤇ V`).
/// Injecting a concrete collection into it tests **membership in the witness kind** —
/// does the injecting domain realize the length witness (is it a range)? — which is a
/// predicate on a shape, not a subtype constraint. When the injecting collection is
/// *computed* (a comprehension), its domain is an inference variable at emit time and
/// has no shape to read, so the requirement is recorded as a **kinding constraint** on
/// that variable and discharged when its position resolves. See
/// `src/ccl/design/collections.md`, "Injecting a domain that has no shape yet".
#[test]
fn test_comprehension_enters_a_list_annotation() {
    // The comprehension's domain resolves to `[0, 3)` — a range — which realizes
    // the length witness, so the deferred entry is discharged.
    let ty = infer_program(
        r"
x: List(Int) = box([y + 1 for y in [1, 2, 3]])
x",
    );
    // Modulo binder identity: two derivations, so the binders differ by construction.
    assert_eq!(
        ty.without_witness_binders(),
        Type::Sigma(Box::new(cambra::ccl::SigmaType::over(
            TypeKind::Enumerated(vec![Type::UIntRange(3)]),
            None,
            int(),
        )))
        .without_witness_binders(),
        "comprehension injected into List(Int) keeps its inferred range domain"
    );
    // The annotation is a *bound*, so the sum names the one domain the value has
    // rather than the whole `UIntRanges` description — and it stays a sum, because
    // the `box` is what put it there. Its factored shape is the annotation's: the
    // described `List(Int)` has no unfactored spelling, so the meet happens in the
    // one form both can be written in.
}

/// The dual of the above: a comprehension over a **source** resolves its domain
/// to `source(_)`, which does *not* realize the length witness, so the kinding
/// constraint fails at coalesce. A regression guard that recording a constraint is a
/// genuine check and not a blanket accept.
#[test]
fn test_source_comprehension_rejected_by_list_annotation() {
    let errs = infer_program_with_sources_err(
        r"
x: List(Int) = box([y + 1 for y in mysrc()])
x",
        &[("mysrc", int())],
    );
    assert!(
        errs.iter().any(|e| matches!(
            e,
            InferError::TypeMismatch { ctx, .. } if ctx == "collection annotation"
        )),
        "expected a collection-annotation mismatch, got {errs:?}"
    );
}

/// `a ++ b` (CollectionUnion) infers its domain as
/// `Type::Variant({_0: …, _1: …})` (the runtime genuinely
/// discriminates by operand) and its codomain as the *join* of branch
/// element types. For homogeneous unions the join collapses to the
/// common element type so consumers like `Sum` can constrain it
/// directly; heterogeneous unions surface `IncompatibleBounds` at
/// coalesce time (see `test_collection_union_heterogeneous_rejected`).
/// Pretty-printing flattens the synthetic `_N` domain tags so the
/// surface still reads as a bare union.
#[test]
fn test_collection_union_produces_variant_typed_domain() {
    let ty = infer_program_with_sources(
        "src1() ++ src2()",
        &[
            ("src1", Type::Base(BaseType::Int)),
            ("src2", Type::Base(BaseType::Int)),
        ],
    );
    let Type::Fun {
        domain: dom,
        codomain: cod,
        ..
    } = &ty
    else {
        panic!("expected Fun, got {ty}");
    };
    // Domain is a Variant with two anonymous positional (Index) tags.
    if let Type::Variant(tags) = &**dom {
        assert_eq!(tags.len(), 2, "expected 2-tag variant domain, got {ty}");
        assert!(
            tags.iter().all(|(k, _)| matches!(k, FieldKey::Index(_))),
            "expected anonymous positional Index tags, got {tags:?}"
        );
    } else {
        panic!("expected Variant domain, got {ty}");
    }
    // Codomain is the joined element type — Int, not a Variant.
    assert_eq!(
        **cod,
        Type::Base(BaseType::Int),
        "expected Int codomain (join of two Int branches), got {ty}"
    );
}

/// Heterogeneous CollectionUnion (`Int ++ String`) leaves the codomain
/// join with two incompatible lower-bound atoms, which
/// `coalesce_compact` rejects with `IncompatibleBounds`. Pinning this
/// behavior makes the rule explicit: there is no trait machinery yet
/// for "summable / joinable across distinct base types", so
/// heterogeneous unions are not value-typeable.
#[test]
fn test_collection_union_heterogeneous_rejected() {
    let errs = infer_program_with_sources_err(
        "src1() ++ src2()",
        &[
            ("src1", Type::Base(BaseType::Int)),
            ("src2", Type::Base(BaseType::String)),
        ],
    );
    assert!(
        errs.iter()
            .any(|e| matches!(e, InferError::IncompatibleBounds { .. })),
        "expected IncompatibleBounds error, got {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// GroupBy + aggregate tests
// ---------------------------------------------------------------------------

#[test]
fn test_groupby_aggregate() {
    // groups = groupby([1, 2, 3], \x -> x)
    // g = groups(1)
    // sum(g)
    // Expected: Int (sum of a group of integers)
    let ty = infer_program(
        r#"
groups = groupby([1, 2, 3], \x -> x)
g = groups(1)
sum(g)
"#
        .trim(),
    );
    assert_eq!(ty, int(), "expected Int, got {ty}");
}

/// Dependent application: looking up one partition of a group-by applies the
/// key function `(k) ⇒ {i | key(i) == k} ⇒ V` at a concrete key, and the
/// surviving partition predicate must reflect that key — the binder is
/// *discharged* to the argument (design §5 / Appendix A). This is the headline
/// case the Pi-type + substitution machinery unlocks: before it, the predicate
/// kept the unbound group-by key.
#[test]
fn test_groupby_dependent_application_discharges_key() {
    // groups : (k) ⇒ ({i | i ▷ xs ▷ key_fn == k} ⇒ Int); groups(0) discharges
    // k ↦ 0, so the partition predicate must mention the literal 0 and no
    // longer reference the group-by key binder `__gb_k`.
    let ty = infer_program(
        r#"
groups = groupby([1, 2, 3], \x -> x)
groups(0)
"#
        .trim(),
    );
    let Type::Fun { domain: dom, .. } = &ty else {
        panic!("expected a partition function type, got {ty}");
    };
    let Type::Refinement(_, r) = &**dom else {
        panic!("expected a refined partition domain, got {ty}");
    };
    let pred = cambra::ccl::symbolic::symbolic(&r.predicate);
    assert!(
        !pred.contains("__gb_k"),
        "group-by key binder should be discharged, but predicate still has it: {pred}"
    );
    assert!(
        pred.contains('0'),
        "discharged predicate should mention the argument 0: {pred}"
    );
}

// O3 (higher-order dependent application): apply a dependent function through a
// function-typed *parameter* whose type is still an inference variable at emit
// time. `apply0`'s parameter `g` is a var when `g(0)` is emitted, so `apply`
// cannot peek its Pi binder to build the identity correspondence — the discharge
// `[k ↦ 0]` must instead be resolved at coalesce, once `g` resolves to the
// group-by partition function. The result of `apply0(groups)` must be the same
// `{i | key(i) == 0} ⇒ Int` partition the *direct* `groups(0)` yields: predicate
// mentions `0`, not the group-by key binder `__gb_k`.
//
// Was blocked on O3 until the apply discharge moved to coalesce: `coalesce_node`
// re-derives each application's type from its already-resolved function child,
// discharging on the function's *real* binder rather than the fresh `__arg`
// binder `emit_apply` peeks when the function is still an inference variable.
#[test]
fn test_higher_order_dependent_application_discharges_key() {
    let ty = infer_program(
        r#"
groups = groupby([1, 2, 3], \x -> x)
apply0 = \g -> g(0)
apply0(groups)
"#
        .trim(),
    );
    let Type::Fun { domain: dom, .. } = &ty else {
        panic!("expected a partition function type, got {ty}");
    };
    let Type::Refinement(_, r) = &**dom else {
        panic!("expected a refined partition domain, got {ty}");
    };
    let pred = cambra::ccl::symbolic::symbolic(&r.predicate);
    assert!(
        !pred.contains("__gb_k"),
        "group-by key binder should be discharged through the higher-order apply, but: {pred}"
    );
    assert!(
        pred.contains('0'),
        "discharged predicate should mention the argument 0: {pred}"
    );
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

/// Arms of different types are rejected — as two incompatible lower-bound atoms
/// on the arms' join variable, which `coalesce_compact` reports as
/// `IncompatibleBounds`. A `Case`'s type is the join of its arms (they flow
/// one-way into one variable), so a collision surfaces at coalesce rather than
/// eagerly at the arm relation — the same place a heterogeneous list literal or
/// `CollectionUnion` reports it (see `test_collection_union_heterogeneous_rejected`).
#[test]
fn test_if_else_arm_type_mismatch() {
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
            .any(|e| matches!(e, InferError::IncompatibleBounds { .. })),
        "expected IncompatibleBounds, got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Edge cases: Self-application, unapplied lambdas, etc.
// ---------------------------------------------------------------------------

#[test]
fn test_self_application_types() {
    // `\x -> x(x)` is the MLsub poster child `(α ∧ (α ⇒ β)) ⇒ β`. With
    // both Apply edges one-way there is no var⇄var cycle, so it types
    // cleanly: the unconstrained `α` leg drops and the lambda infers as
    // `(?a ⇒ ?b) ⇒ ?c`, carrying unresolved `Infer` vars like any other
    // unapplied lambda. *Misusing* a self-applicator still errors — see
    // `self_application_rejected_without_panic` in `infer/solve.rs`.
    let ty = infer_program("\\x -> x(x)");
    assert!(
        matches!(&ty, Type::Fun { domain: d, .. } if matches!(&**d, Type::Fun { .. })),
        "expected a function-domained function type, got {ty:?}"
    );
}

#[rstest]
#[case::comparison(
    r"
f = \x -> x > 1
f
",
    Type::Fun { name: None, kind: cambra::ccl::FunKind::Compute, domain: Box::new(int()), codomain: Box::new(bool_ty()) }
)]
#[case::arithmetic(
    r"
f = \x -> x + 1
f
",
    Type::Fun { name: None, kind: cambra::ccl::FunKind::Compute, domain: Box::new(int()), codomain: Box::new(int()) }
)]
fn test_lambda_unapplied(#[case] code: &str, #[case] expected: Type) {
    assert_eq!(infer_program(code), expected);
}

#[test]
fn test_generic_identity() {
    // f = \x -> x; f -> Fun(?a, ?b)
    // inference allows unconstrained parameters to remain unresolved.
    let ty = infer_program("f = \\x -> x\nf");
    if let Type::Fun {
        domain: dom,
        codomain: cod,
        ..
    } = ty
    {
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
    assert_eq!(infer_program(r#"(1, "a").0"#), int_lit(1));
    assert_eq!(infer_program(r#"(1, "a").1"#), str_lit("a"));
}

/// An unconstrained identity applied to a concrete value must resolve all
/// inference variables — no `Type::Infer` should survive in the result.
#[test]
fn test_unconstrained_identity_applied_resolves() {
    // bind via Let so `f(5)` is a named call (lowering doesn't yet
    // support a lambda-literal in call position).
    let ty = infer_program("f = \\x -> x\nf(5)");
    assert_eq!(ty, int_lit(5));
}

/// A refined comprehension carries its filter predicate as a refinement on
/// the inferred function's domain. The refinement now rides the constraint
/// lattice natively — `emit_lambda` lifts it onto the domain and
/// `constrain_subtype`/`coalesce` propagate it — rather than being
/// re-stitched by a post-pass. This pins that the inferred domain still
/// surfaces the refinement end-to-end through inference.
#[test]
fn test_filtered_comprehension_has_refinement_on_domain() {
    let ty = infer_program("[x for x in [1, 2, 3] if x > 1]");
    if let Type::Fun {
        domain: dom,
        codomain: cod,
        ..
    } = &ty
    {
        assert!(
            matches!(&**dom, Type::Refinement(_, _)),
            "expected Refinement-wrapped domain, got {ty}"
        );
        assert_eq!(**cod, int(), "expected codomain Int, got {ty}");
    } else {
        panic!("expected Fun type, got {ty}");
    }
}

/// Infer `code` and run the post-inference consistency wall over the result,
/// returning the program's type. The wall's failures are compiler bugs, not user
/// errors — `compile_program` panics on them — so a rule that types a program
/// must also survive its own re-run in Check mode.
fn infer_and_check(code: &str) -> Type {
    let mut lctx = LoweringContext::default();
    let mut ictx = TypeInferenceContext::new();
    let stmts = parse_module(code.trim());
    let mut expr = lower_stmts(&stmts, &mut lctx)
        .into_result()
        .expect("lowering failed");
    let ty = infer(&mut expr, &mut ictx).expect("inference failed");
    check_pre_desugar(&expr)
        .expect("post-inference consistency wall must accept the inferred tree");
    ty
}

/// A `Case` whose arms are *collections* survives the consistency wall, and the
/// restriction **both** arms establish survives with it: two identical filtered
/// comprehensions join to that same filtered domain, not to the bare `[0, 2]`.
///
/// A collection carries its domain as a refinement on its `Fun` *domain*, where
/// subtyping is contravariant — which is why the arms must reach the node's type
/// by a join rather than by relating each arm to a *stripped* sibling: stripping
/// one side of a domain edge demands `[0, N] <: {[0, N] | p}` and rejects two arms
/// that are the same expression, and stripping both discards a domain that no
/// branch widens.
#[test]
fn test_case_with_filtered_comprehension_arms_passes_consistency_wall() {
    let ty = infer_and_check(
        r"
xs = [1, 2, 3]
c = 1 > 0
if c:
    [x for x in xs if x > 1]
else:
    [x for x in xs if x > 1]
",
    );
    let Type::Fun {
        domain, codomain, ..
    } = &ty
    else {
        panic!("expected a collection type, got {ty}");
    };
    assert!(
        matches!(&**domain, Type::Refinement(..)),
        "the filter both arms establish must survive the join, got {ty}"
    );
    assert_eq!(**codomain, int(), "expected an Int codomain, got {ty}");
}

/// The same relation, one construct over: a `List`'s elements join into a shared
/// variable exactly as a `Case`'s arms do, so a list *of* filtered comprehensions
/// has to clear the wall too. The reconcile compares the rule-derived type to the
/// recorded one modulo refinements, and a join variable holds its operands' real
/// (refined) types in its bounds — where erasing the two compared types cannot
/// reach them.
#[test]
fn test_list_of_filtered_comprehensions_passes_consistency_wall() {
    let ty = infer_and_check(
        r"
xs = [1, 2, 3]
[[x for x in xs if x > 1]]
",
    );
    let Type::Fun {
        domain, codomain, ..
    } = &ty
    else {
        panic!("expected a collection type, got {ty}");
    };
    assert_eq!(
        **domain,
        Type::UIntRange(1),
        "expected a 1-element list, got {ty}"
    );
    assert!(
        matches!(&**codomain, Type::Fun { domain: d, .. } if matches!(&**d, Type::Refinement(..))),
        "the element's filtered domain must survive, got {ty}"
    );
}

/// A `Case`'s type is the **join** of its arms, so a refinement survives exactly
/// when every arm establishes it. Two arms that are the same literal *are* that
/// literal; two different ones are only their base.
#[rstest]
#[case::same_literal("c = 1 > 0\n5 if c else 5", int_lit(5))]
#[case::different_literals("c = 1 > 0\n1 if c else 2", int())]
#[case::inside_a_tuple("c = 1 > 0\n(1, 2) if c else (3, 4)", Type::Tuple(vec![int(), int()]))]
#[case::at_depth(
    "c = 1 > 0\n((1, 2), 3) if c else ((4, 5), 6)",
    Type::Tuple(vec![Type::Tuple(vec![int(), int()]), int()])
)]
fn test_case_arms_join(#[case] code: &str, #[case] expected: Type) {
    assert_eq!(infer_and_check(code), expected);
}

/// Arms whose domains differ, both refinements of the *same* source domain. Two
/// data-collection arms join to a Σ over their candidate domains, so each arm's
/// filter is retained on its own candidate — neither picked (which would claim
/// positions the other branch does not produce) nor met into a single domain
/// (which would claim one domain satisfying both filters). Refinement is not a
/// special case here: the candidates are ordinary distinct domains, so this is
/// the same Σ formation as two structurally unrelated domains.
#[test]
fn test_case_arms_with_different_filters_become_sigma_candidates() {
    let ty = infer_and_check(
        r"
xs = [1, 2, 3]
c = 1 > 0
if c:
    box([x for x in xs if x > 1])
else:
    box([x for x in xs if x < 3])
",
    );
    let Type::Sigma(sigma) = &ty else {
        panic!("expected a conditional collection (Sigma), got {ty}");
    };
    let TypeKind::Enumerated(candidates) = sigma.witness.kind() else {
        panic!("expected an enumerated type-witness, got {ty}");
    };
    assert_eq!(candidates.len(), 2, "expected both arms' domains, got {ty}");
    // Each candidate is a whole collection type — `box` boxes the arm, not its
    // domain — over the source domain under exactly one witness: its own arm's
    // filter, and only that one.
    for c in candidates {
        let Type::Fun { domain, .. } = c else {
            panic!("expected a boxed collection candidate, got {ty}");
        };
        let Type::Refinement(base, _) = &**domain else {
            panic!("expected a filtered candidate domain, got {ty}");
        };
        assert_eq!(
            **base,
            Type::UIntRange(3),
            "expected the source domain under the filter, got {ty}"
        );
    }
    assert_ne!(
        candidates[0], candidates[1],
        "the two arms' filters must stay distinct, got {ty}"
    );
}

// ---------------------------------------------------------------------------
// Defer / Feed / Define typing rules (pre-channelize trees)
// ---------------------------------------------------------------------------
//
// These tests run inference on lowered-but-NOT-channelized trees, exercising
// the `Defer`/`Feed`/`Define` typing rules directly: a defer binding types
// as a feed history `feed(δ ⇒ value)`, feeds contribute `Fun(δ, elem)` channel
// shapes into it, defines set the whole stream outright, and reads discharge
// transparently through the handle as that stream. A channel's *domain* is a
// rigid nominal `Type::ChanDom(d)` minted at the `let d = defer()` site, so
// reads type concretely against that name at inference (no `Infer` residue);
// `channelize` later substitutes the assembled channel domain for `ChanDom`.

/// Destructure `ty` as a feed history `feed(domain ⇒ value)` and return the
/// channel's element type `value`; panics otherwise. A feed reads as its whole
/// stream, so its element type is the history's `value` slot directly (there is
/// no separate scalar payload to peel — scalar `<<=` is rejected by typing).
fn feed_value(ty: &Type) -> &Type {
    match ty {
        Type::History {
            value,
            kind: HistoryKind::Append,
            ..
        } => value,
        _ => panic!("expected a feed handle, got {ty}"),
    }
}

#[test]
fn test_defined_defer_is_feed_of_collection() {
    // `<<=` sets the whole channel; its RHS must be a collection (a `Fun`),
    // so the feed's element type is the collection's element.
    let ty = infer_program("x = defer()\nx <<= [1,2,3]\nx");
    assert_eq!(*feed_value(&ty), int());
}

#[test]
fn test_scalar_define_is_rejected() {
    // A scalar `<<=` RHS is disallowed — `<<=` only accepts collections
    // (`Fun`s), so an `Int` fails to align with the channel stream.
    let errs = infer_program_err("x = defer()\nx <<= 1\nx");
    assert!(
        !errs.is_empty(),
        "a scalar defined into a feed channel must be a type error"
    );
}

#[test]
fn test_fed_defer_is_feed_of_channel() {
    let ty = infer_program("x = defer()\n[x << i for i in [1,2,3]]\nx");
    assert_eq!(*feed_value(&ty), int());
}

#[test]
fn test_scalar_feeds_join_in_channel() {
    let ty = infer_program("x = defer()\nx << 1\nx << 2\nx");
    assert_eq!(*feed_value(&ty), int());
}

#[test]
fn test_defined_defer_reads_through_aggregate() {
    // A collection define sets the whole stream; `sum` reads the handle as
    // that stream and aggregates it to a scalar.
    assert_eq!(infer_program("x = defer()\nx <<= [1,2,3]\nsum(x)"), int());
}

#[test]
fn test_fed_defer_reads_through_aggregate() {
    // `sum` consumes the feed handle as its channel stream `(α → γ)`.
    assert_eq!(infer_program("x = defer()\nx << 1\nx << 2\nsum(x)"), int());
}

#[test]
fn test_defer_chain_flattens_feeds() {
    // `x <<= y` sets x's channel to y's whole stream. A feed reads through as
    // its stream, so x gets y's stream directly (a single feed layer, not
    // nested); desugar later binds x to y's channel.
    let ty = infer_program("x = defer()\ny = defer()\nx <<= y\ny <<= [0, 1]\nx");
    assert_eq!(*feed_value(&ty), int());
}

#[test]
fn test_heterogeneous_feeds_error() {
    let errs = infer_program_err("x = defer()\nx << 1\nx << \"s\"\nx");
    assert!(
        !errs.is_empty(),
        "Int and String feeds into one defer must collide"
    );
}

#[test]
fn test_feed_through_param_flows_back_to_caller() {
    // ParamAsTarget: g feeds its parameter. The call edge
    // `Feed(ρ_x) <: c` meets the feed's `c <: Feed(ρ_f)` upper bound,
    // and invariance carries g's contribution back into ρ_x — so the
    // String contribution collides with the direct Int feed.
    let errs = infer_program_err(
        r#"
def g(c):
  c << "s"
  c
x = defer()
g(x)
x << 1
x"#,
    );
    assert!(
        !errs.is_empty(),
        "a String fed through g's parameter must collide with the Int fed directly"
    );
}

#[test]
fn test_feed_through_param_compatible_types_ok() {
    // Same shape with compatible contributions: both land in ρ_x as Int.
    let ty = infer_program(
        r#"
def g(c):
  c << 100
  c
x = defer()
g(x)
x << 1
x"#,
    );
    assert_eq!(*feed_value(&ty), int());
}

#[test]
fn test_plain_value_to_feeding_param_errors() {
    // `g(5)` where g feeds its parameter: the write capability cannot be
    // conjured from a plain value (`NotAFeed` at the call edge).
    let errs = infer_program_err(
        r#"
def g(c):
  c << 1
  c
g(5)"#,
    );
    assert!(
        !errs.is_empty(),
        "feeding through a non-feed argument must error"
    );
}

#[test]
fn test_unbound_feed_target_errors() {
    let errs = infer_program_err("x << 1");
    assert!(
        errs.iter()
            .any(|e| matches!(e, InferError::UnboundVariable(n) if n == "x")),
        "feeding an unbound name must report UnboundVariable, got {errs:?}"
    );
}

#[test]
fn test_generalized_defer_function_specializes_per_element_type() {
    // A defer minted inside a generalized function instantiates a fresh
    // feed handle (and element type) per call site — monomorphize then
    // specializes per resolved Feed type.
    let ty = infer_program(
        r#"
def make(v):
  x = defer()
  x << v
  x
a = make(1)
b = make("s")
(a, b)"#,
    );
    let Type::Tuple(elems) = &ty else {
        panic!("expected a pair of feed handles, got {ty}");
    };
    // The contributed value's type flows into the channel whole, so each handle's
    // element type is the literal that was fed to it.
    assert_eq!(*feed_value(&elems[0]), int_lit(1));
    assert_eq!(*feed_value(&elems[1]), str_lit("s"));
}

// ---------------------------------------------------------------------------
// Projection (`.`) vs. lookup (`[…]`)
// ---------------------------------------------------------------------------

/// `.` projects a product and `[…]` looks up a collection. The spellings are disjoint,
/// so lowering never has to guess which operation a bracket was — a guess it has no
/// types to make, and the wrong one for `xs[0]`, the commonest subscript anyone writes
/// (`docs/chl-spec.md`, "3.9 Subscript and attribute access").
#[test]
fn dot_projects_and_brackets_look_up() {
    // Both keyings project, on the shapes that have them. Projection *selects* an
    // element rather than computing one, so the element's own singleton survives.
    assert_eq!(infer_program("t = (1, \"a\")\nt.0"), int_lit(1));
    assert_eq!(infer_program("t = (1, \"a\")\nt.1"), str_lit("a"));
    assert_eq!(infer_program("r = (a=1, b=2)\nr.b"), int_lit(2));

    // A tuple is a heterogeneous product, not a finite function, so it has no domain to
    // look up in — however the index is spelled, literal or not.
    for program in ["t = (1, \"a\")\nt[0]", "t = (1, 2)\ni = 0\nt[i]"] {
        let errs = infer_program_err(program);
        assert!(
            errs.iter()
                .any(|e| matches!(e, InferError::ExpectedFunction { .. })),
            "a tuple has no domain to look up in: `{program}` gave {errs:?}"
        );
        assert!(
            errs.iter().any(|e| format!("{e:?}").contains("`.0`")),
            "the rejection must name the projection spelling: {errs:?}"
        );
    }
}

/// The two keyings are one operation differing only in the key, so they compose freely
/// in either order and to any depth.
#[test]
fn positional_and_named_projection_compose() {
    assert_eq!(infer_program("r = (p=(1, \"a\"))\nr.p.1"), str_lit("a"));
    assert_eq!(infer_program("t = ((a=1), 2)\nt.0.a"), int_lit(1));
    assert_eq!(infer_program("t = ((1, 2), 3)\nt.0.1"), int_lit(2));
}

/// The brace *type* forms and `.` agree on keying: `{T, U}` is a tuple type, projected
/// positionally; `{name: T}` is a record type, projected by name.
#[test]
fn brace_type_annotations_project_by_their_keying() {
    assert_eq!(infer_program("t: {Int, Bool} = (1, True)\nt.0"), int_lit(1));
    assert_eq!(infer_program("r: {a: Int} = (a=1)\nr.a"), int_lit(1));
    // A *one*-element tuple type carries the trailing comma, like the `(e,)` term.
    assert_eq!(infer_program("t: {Int,} = (1,)\nt.0"), int_lit(1));
    // A one-*field* record type needs no comma — `a: Int` already marks the form.
    assert_eq!(infer_program("r: {a: Int,} = (a=1)\nr.a"), int_lit(1));
}

/// The empty product is `Unit`, and it is the *only* empty product: `{}` in an
/// annotation, an empty tuple term, and an empty record term all land on the same
/// type, so no two passes can disagree about which empty spelling a node has
/// (`docs/chl-spec.md`, "6.6 The empty product is unit").
#[test]
fn the_empty_product_is_unit() {
    let unit = Type::Base(BaseType::Unit);
    assert_eq!(infer_program("x: {} = ()\nx"), unit);
    assert_eq!(infer_program("x = ()\nx"), unit);
    // `{}` really constrains: a non-unit value against it is an annotation error.
    assert!(
        !infer_program_err("x: {} = 1\nx").is_empty(),
        "`{{}}` is the unit type, so an `Int` must not satisfy it"
    );
}

/// A projection whose target's type is still a *variable* where the projection is
/// emitted: the node states a requirement — "a product with this key" — rather than
/// deciding a shape, so an inferred parameter recovers its shape from the call site, and
/// an argument with no such key is rejected there.
#[test]
fn projection_through_an_inferred_parameter() {
    assert_eq!(infer_program("def f(x):\n    x.1\nf((1, 2))"), int_lit(2));
    assert_eq!(infer_program("def f(r):\n    r.a\nf((a=7))"), int_lit(7));
    assert!(
        !infer_program_err("def f(x):\n    x.0\nf(1)").is_empty(),
        "an `Int` has no positions to project"
    );
}

/// The diagnostics for a projection that cannot land say what the shape actually has.
///
/// Both failures otherwise report a shape the program never had, because a positional
/// requirement is a *dense* tuple (`.99` demands 100 positions) and a named one is a
/// one-field record — partial shapes that read as internal machinery next to the value's
/// own type.
#[test]
fn projection_diagnostics_name_the_shape() {
    // Past the end of a tuple: the position asked for, and the width there is.
    let errs = infer_program_err("t = (1, 2, 3)\nt.99");
    let msg = format!("{:?}", errs[0]);
    assert!(
        msg.contains("No position .99") && msg.contains("3 positions"),
        "expected the requested position and the tuple's width, got: {msg}"
    );

    // Wrong keying: a record has names and a tuple has positions, which is the whole
    // content of the failure and what the bare shapes do not say.
    for program in ["r = (a=1)\nr.0", "t = (1, 2, 3)\nt.b"] {
        let errs = infer_program_err(program);
        assert!(
            errs.iter()
                .any(|e| format!("{e:?}").contains("keyed by field *name*")),
            "expected the record/tuple keying hint for `{program}`, got {errs:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// LetRec typing (direct construction — no surface syntax emits LetRec yet)
// ---------------------------------------------------------------------------

/// Direct-construction tests for the [`TypedExprNode::LetRec`] typing rule:
/// every binding's declared type is bound over the whole group (mutual
/// recursion), each binding body checks against its declaration, and the
/// node synthesizes the letrec body's type. Constructed as raw `Expr`s
/// because nothing in the pipeline emits `LetRec` yet (the unified phase of
/// `src/ccl/design/mutability.md` lands it later).
mod letrec_typing {
    use cambra::ccl::infer::{TypeInferenceContext, infer, typecheck};
    use cambra::ccl::{
        ArithmeticKind, BinOpKind, Builtin, Expr, Lit, Type, TypedBinding, TypedExprNode,
    };
    use cambra::interpreter::BaseType;

    fn int() -> Type {
        Type::Base(BaseType::Int)
    }

    /// `get_prev_seq((history, position, default))` — the tupled-argument
    /// application convention (same as `FinalOrDefault`).
    fn get_prev_seq(history: Expr, position: Expr, default: Expr) -> Expr {
        Expr::apply(
            Expr::tuple(vec![history, position, default]),
            Expr::builtin(Builtin::GetPrevSeq),
        )
    }

    fn typed_binding(name: &str, ty: Type) -> TypedBinding {
        TypedBinding {
            name: name.into(),
            ty,
            user_annotation: None,
        }
    }

    /// The design's induction-recurrence shape typechecks end-to-end through
    /// `infer` + the strict `typecheck` wall:
    /// `letrec cnt : [0,3] ⇒ Int = λ r → get_prev_seq((cnt, r, 0)) + 1 in cnt`.
    /// The body's self-reference resolves against the group scope at the
    /// declared type, and the guard builtin's polymorphic scheme pins
    /// `ι = [0,3]`, `ν = Int`.
    #[test]
    fn guarded_single_binding_letrec_typechecks() {
        // The recurrence carrier is a *data collection* (`⤇`): `cnt` is indexed
        // by the iteration domain `[0, 2]` and read back through `get_prev_seq`,
        // whose history argument demands `Data`. Declaring it `Compute`
        // (`Type::fun`) is the miskind the `Compute <: Data` rejection now
        // catches at the recurrence's introduction.
        let cnt_ty = Type::data_fun(Type::UIntRange(3), int());
        let def = Expr::lambda(
            "r",
            Type::UIntRange(3),
            Expr::binop(
                get_prev_seq(Expr::var("cnt"), Expr::var("r"), Expr::lit(Lit::Int(0))),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                Expr::lit(Lit::Int(1)),
            ),
        );
        let mut expr = Expr::letrec(
            vec![(typed_binding("cnt", cnt_ty.clone()), def)],
            Expr::var("cnt"),
        );

        let ty = infer(&mut expr, &mut TypeInferenceContext::new()).expect("inference succeeds");
        assert_eq!(
            ty, cnt_ty,
            "the letrec's type is its body's (a read of cnt)"
        );
        typecheck(&expr).expect("strict typecheck passes");

        // The shape is also well-formed by the guardedness check.
        let TypedExprNode::LetRec { bindings, .. } = &expr.node else {
            panic!("letrec node preserved");
        };
        assert_eq!(bindings[0].0.ty, cnt_ty, "binder slot resolved in place");
        cambra::ccl::letrec::check_letrec_causal(bindings).expect("causal group");
    }

    /// A binding body whose type conflicts with its declared binding type is
    /// rejected: `letrec x : Int = "s" in x`.
    #[test]
    fn conflicting_declared_binding_type_is_rejected() {
        let mut expr = Expr::letrec(
            vec![(
                typed_binding("x", int()),
                Expr::lit(Lit::String("s".into())),
            )],
            Expr::var("x"),
        );
        infer(&mut expr, &mut TypeInferenceContext::new())
            .expect_err("String body against an Int declaration must fail");
    }

    /// Mutual scope: binding A's body references B and vice versa — both
    /// resolve against the group scope (the whole group is bound before any
    /// body is emitted), and the letrec body sees both.
    #[test]
    fn mutual_two_binding_scope_resolves() {
        let mut expr = Expr::letrec(
            vec![
                (typed_binding("a", int()), Expr::var("b")),
                (typed_binding("b", int()), Expr::var("a")),
            ],
            Expr::binop(
                Expr::var("a"),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                Expr::var("b"),
            ),
        );
        let ty = infer(&mut expr, &mut TypeInferenceContext::new())
            .expect("mutually referencing bindings resolve");
        assert_eq!(ty, int());
        typecheck(&expr).expect("strict typecheck passes");
    }
}

/// A conditional collection reaching a **collapsing** consumer through a variable — a
/// `let` binding or a UDF parameter — rather than directly. The arms' domains then
/// arrive as bounds on one domain position instead of as two arrow shapes meeting, and
/// reading that position as a *join* rather than a collision is what makes it work
/// (`denoted_domains`, in `src/ccl/infer/solver/compact.rs`).
#[test]
fn conditional_collection_consumed_through_a_variable() {
    let c = "box([1, 2]) if True else box([1, 2, 3])";
    // Through a `let`.
    assert_eq!(
        infer_program(&format!(
            r"
x = {c}
sum(x)"
        )),
        int()
    );
    // Through a UDF parameter.
    assert_eq!(
        infer_program(&format!(
            r"
def f(c):
    sum(c)
f({c})"
        )),
        int()
    );
    // Directly, which reaches the consumer as two arrow shapes and was already fine —
    // kept so a regression cannot hide behind the cases above.
    assert_eq!(infer_program(&format!("sum({c})")), int());
}

/// **Domain-preserving** consumption of a conditional collection — a comprehension,
/// which carries the domain into its own result rather than collapsing it.
///
/// Directly over the `Case` this works: `lower::comprehension` floats the source `Case`
/// out of the map, so each arm is built as its own data-kinded `Compose` — the
/// distribution over the witness happens *syntactically*, before any type-level
/// elimination is needed.
///
/// Through a **variable** there is no `Case` to float, so the distribution has to happen
/// at the type level, and the sum has to survive it: the comprehension's result ranges
/// over whichever domain the source took, which is the same sum again.
///
/// No `Type::Sigma` exists at constraint time here — a Σ is built only by an annotation
/// and by coalesce — so the arms arrive as two `Fun` *lower bounds* on one variable, and
/// the consumer's `apply` records `?v <: (__arg: ?d) ⇒ ?r`. What makes this work is that
/// the closure step unions those lower bounds' domains into the sum and relates the domain
/// edge once, instead of relating each candidate pointwise and demanding `?d` lie below both.
///
/// Every route agrees, including a **UDF parameter** — where the consumer's demand is
/// recorded while typing the body, before any candidate exists. Constraint order does not
/// matter because the join is not a snapshot taken when the demand arrives: a variable's
/// denotation is read from its lower bounds at the moment its own outgoing edge is drawn,
/// which is after the arguments have landed.
#[test]
fn domain_preserving_consumption_of_a_conditional_collection() {
    let c = "box([1, 2]) if True else box([1, 2, 3])";
    let sum = "Σ σ ∈ {[0, 1], [0, 2]}. (σ ⤇ Int)";
    for program in [
        // Directly over the `Case`.
        format!("[y + 1 for y in {c}]"),
        // Through a `let` — candidates recorded before the demand.
        format!(
            r"
x = {c}
[y + 1 for y in x]"
        ),
        // Through a UDF parameter — demand recorded before the candidates.
        format!(
            r"
def f(c):
    [y + 1 for y in c]
f({c})"
        ),
        // And with the argument itself `let`-bound, so the sum crosses two variables.
        format!(
            r"
def f(c):
    [y + 1 for y in c]
x = {c}
f(x)"
        ),
    ] {
        assert_eq!(
            infer_program(&program).to_string(),
            sum,
            "domain-preserving consumption must preserve the sum: {program}"
        );
    }
}

/// An arm whose domain is **inferred rather than written** joins like any other, because a
/// sum's candidates cross a level boundary as an *invariant* position.
///
/// A comprehension arm is the case: its domain is a variable, and a domain's content arrives
/// as an **upper** bound (the iteration key must lie in the source's domain). `extrude`'s
/// polar one-way proxy inherits only one side, so extruding a candidate at `!pol` handed it a
/// proxy carrying lower bounds — of which a domain variable has none — and the candidate
/// materialized unresolved as `Σ σ ∈ {?93, [0, 2]}. (σ ⤇ Int)`. Candidates are matched by value, so
/// they extrude through two-way proxies (`extrude_invariant`), exactly as a `History` payload
/// does.
///
/// A refinement is *not* what matters here, which is why the unfiltered comprehension arms
/// come first: their candidates are bare variables with no refinement at all.
#[test]
fn an_arm_whose_domain_is_inferred_joins_like_a_written_one() {
    let sum = "Σ σ ∈ {[0, 1], [0, 2]}. (σ ⤇ Int)";
    for arms in [
        // Written domains.
        "box([1, 2]) if True else box([1, 2, 3])",
        // One inferred domain: a comprehension arm, no refinement.
        "box([q + 1 for q in [1, 2]]) if True else box([1, 2, 3])",
        // Both inferred.
        "box([q + 1 for q in [1, 2]]) if True else box([q + 1 for q in [1, 2, 3]])",
    ] {
        for shape in [
            format!(
                r"
x = {arms}
[y + 1 for y in x]"
            ),
            format!(
                r"
def f(c):
    [y + 1 for y in c]
f({arms})"
            ),
        ] {
            assert_eq!(
                infer_program(&shape).to_string(),
                sum,
                "an inferred arm domain must resolve, not survive as a variable: {shape}"
            );
        }
    }
    // A *filtered* arm is the same rule with a refinement riding the variable, and the
    // restriction stays on its own candidate.
    let filtered = r"
x = box([q for q in [1, 2, 3] if q > 1]) if True else box([1, 2])
[y + 1 for y in x]";
    let ty = infer_program(filtered);
    let Type::Sigma(s) = &ty else {
        panic!("expected a sum, got {ty}");
    };
    let candidates = s
        .kind()
        .listed()
        .expect("an enumerated kind lists its domains");
    assert_eq!(candidates.len(), 2, "expected both arms, got {ty}");
    assert!(
        candidates
            .iter()
            .any(|d| matches!(d, Type::Refinement(b, _) if **b == Type::UIntRange(3))),
        "the filtered arm keeps its restriction over its own domain, got {ty}"
    );
    assert!(
        candidates.contains(&Type::UIntRange(2)),
        "the unfiltered arm stays bare, got {ty}"
    );
    // Nested conditionals over inferred domains flatten the same way.
    assert_eq!(
        infer_program(
            "d = 4 > 3\nx = box([q + 1 for q in [1, 2]]) if True else (box([1, 2, 3]) if d else box([1, 2, 3, 4]))\n\
             [y + 1 for y in x]"
        )
        .to_string(),
        "Σ σ ∈ {[0, 1], [0, 2], [0, 3]}. (σ ⤇ Int)"
    );
}

/// A **UDF-call** arm — the shape where the arm's own type arrives as the `applied` variable
/// dependent application mints, rather than as a data function.
///
/// This one is not closed by the join at all: the join declines a bare variable, because
/// reading a variable's denotation would mean joining *its* lower bounds transitively and
/// skipping it would risk dropping a candidate it later resolves to. It works because the
/// **solver** propagates it — the arm's collection reaches the join variable transitively as
/// an ordinary lower bound, which is what bound closure is for. The only thing that had to be
/// fixed was a *reading*: a use of a lambda parameter was being coalesced standalone, in a
/// position that has lost the contravariant-domain context its candidates are alternatives in.
#[test]
fn a_udf_call_arm_joins_through_the_bound_graph() {
    let program = "def g(n):\n    [1,2]\ndef h(n):\n    [1,2,3]\n\
                   x = box(g(0)) if True else box(h(0))\n[y + 1 for y in x]";
    assert_eq!(
        infer_program(program).to_string(),
        "Σ σ ∈ {[0, 1], [0, 2]}. (σ ⤇ Int)",
        "a call-shaped arm reaches the join transitively, like any other lower bound"
    );
}

/// A use of a **lambda parameter** takes its type from the parameter slot when resolving the
/// shared variable standalone has no answer.
///
/// A binder's type is fixed by the contravariant domain of the arrow it binds — the reason
/// `refresh_lambda_param_slot` derives `param.ty` from the coalesced domain instead of
/// resolving the slot. A *use* of that binder carries the same variable, and reading it bare
/// loses the same context; for a data-function domain the loss is not mere imprecision, since
/// the candidate domains of a conditional collection are alternatives only when read *as a
/// domain* and collide as an untagged sum when read bare.
///
/// The read still happens, because a parent's structural recovery of a contravariant domain
/// reads it — a record-typed parameter's uses are how a projection's domain is recovered at
/// all. Which is why this is pinned together with a projection over a parameter.
#[test]
fn a_lambda_param_use_falls_back_to_the_param_slot() {
    // The collection case: without the fallback this is `Conflicting Types: [0, 1] | [0, 2]`
    // at the `__iter_record` use inside the comprehension.
    assert_eq!(
        infer_program(
            r"
def f(c):
    [y + 1 for y in c]
f(box([1,2]) if True else box([1,2,3]))"
        )
        .to_string(),
        "Σ σ ∈ {[0, 1], [0, 2]}. (σ ⤇ Int)"
    );
    // And the standalone read stays load-bearing: a projection's domain is recovered from a
    // record-typed parameter's uses, so those reads must still resolve.
    assert_eq!(
        infer_program(
            r"
def f(r):
    r.age + 1
f((age=3, name=7))"
        ),
        int()
    );
}

/// How a conditional collection reaches each shape of consumer, mapped so a regression
/// cannot quietly narrow one of them back to a single candidate.
///
/// The condition is deliberately **non-constant**, and not because `if True` is broken —
/// it type-checks and evaluates correctly. It is that a literal condition tests less: the
/// gate `lambda_elim` synthesizes for the first arm is then the bare literal `true`, so
/// that arm's driver domain is left unrefined and the partition has one refined leg
/// instead of two. A non-constant condition exercises the shape every real conditional
/// has.
#[test]
fn a_conditional_collection_survives_every_shape_of_consumer() {
    let c = r"
c = 3 > 2
x = box([1, 2]) if c else box([1, 2, 3])
";
    // The two spellings of the same sum. `box` boxes a whole arm type, so the join of
    // two boxed arms is *unfactored* — its candidates are collections. Consumption
    // reads the sum through its domains and rebuilds it *factored*, the only form a
    // described kind can be written in. Each subtypes the other by Σ-width; which one a
    // program lands in says which way it was built, and is worth pinning as such.
    let boxed = "Σ σ ∈ {([0, 1] ⤇ Int), ([0, 2] ⤇ Int)}. σ";
    let sum = "Σ σ ∈ {[0, 1], [0, 2]}. (σ ⤇ Int)";
    // Collapsing consumers discard the domain, so they never present one to be joined.
    assert_eq!(infer_program(&format!("{c}sum(x)")), int());
    assert_eq!(infer_program(&format!("{c}max(x)")), int());
    // The binding alone is what the `box`es built.
    assert_eq!(infer_program(&format!("{c}x")).to_string(), boxed);
    // A domain-preserving consumer agrees on the sum, in the factored spelling.
    assert_eq!(
        infer_program(&format!("{c}[y + 1 for y in x]")).to_string(),
        sum
    );
    // Equal-length arms need no `box` at all: their join is an ordinary data function,
    // so nothing is lost and there is no sum to introduce. This is the control for every
    // case above — `box` is required exactly where the domains differ.
    assert_eq!(
        infer_program(
            r"
c = 3 > 2
x = [1, 2] if c else [3, 4]
[y + 1 for y in x]"
        )
        .to_string(),
        "([0, 1] ⤇ Int)"
    );
    // Nothing about the join is arity-two.
    assert_eq!(
        infer_program(
            "c = 3 > 2\nd = 4 > 3\nx = box([1, 2]) if c else (box([1, 2, 3]) if d else box([1, 2, 3, 4]))\n\
             [y + 1 for y in x]"
        )
        .to_string(),
        "Σ σ ∈ {[0, 1], [0, 2], [0, 3]}. (σ ⤇ Int)"
    );
    // A filtered comprehension is domain-preserving too, and its restriction rides the
    // **witness**: the filter is a fact about the domain the witness names, whichever
    // candidate that turns out to be. The candidates stay bare.
    //
    // Not on the candidates, which is where it used to land. An arm's *own* filter
    // (`box([x for x in xs if q]) if c else …`) refines a candidate as well, and that one
    // was already compiled inside the arm — so in that position the two are the same
    // shape, and no consumer can tell a filter it still owes an operator from one already
    // discharged. A single candidate can carry both at once, so comparing candidates
    // cannot recover the distinction either. On the witness it is structural.
    let filtered = infer_program(&format!("{c}[y for y in x if y > 1]"));
    let Type::Sigma(s) = &filtered else {
        panic!("a filtered conditional collection is still a sum, got {filtered}");
    };
    assert_eq!(
        s.kind()
            .listed()
            .expect("an enumerated kind lists its domains"),
        [Type::UIntRange(2), Type::UIntRange(3)],
        "the candidates carry no restriction, got {filtered}"
    );
    let Type::Fun { domain, .. } = &*s.body else {
        panic!("a consumed collection sum has a data-function body, got {filtered}");
    };
    assert!(
        matches!(&**domain, Type::Refinement(b, _) if matches!(**b, Type::WitnessRef(_))),
        "the restriction rides the witness, got {filtered}"
    );
    // And a collapsing consumer wrapping a domain-preserving one collapses the sum.
    assert_eq!(infer_program(&format!("{c}sum([y + 1 for y in x])")), int());
}

/// Nothing is enumerable where the conditional is *written*: `f`'s arms are bare
/// parameters, so no candidate set exists at the definition. The Σ still forms, at the
/// call, which is why the sum cannot be built at `emit_case` — the candidates are a
/// property of the argument, not of the conditional.
#[test]
fn a_conditional_over_parameters_forms_its_sum_at_the_call_not_the_definition() {
    let f = r"
def f(a, b, d):
    b if a else d
";
    // Scalar arms: an ordinary join, no collection involved.
    assert_eq!(infer_program(&format!("{f}f(True, 1, 2)")), int());
    // Collection arms: the candidates come from the *arguments*.
    assert_eq!(
        infer_program(&format!("{f}f(True, box([1,2]), box([1,2,3]))")).to_string(),
        // Unfactored: the arms arrive already boxed, and the join keeps that shape.
        "Σ σ ∈ {([0, 1] ⤇ Int), ([0, 2] ⤇ Int)}. σ"
    );
    // And a domain-preserving consumer carries it, exactly as it carries a directly-bound
    // one. This used to fail — the defect was in *consumption*, not in where the sum was
    // formed — and it is closed by the consumer naming the witness rather than handing over a
    // named domain (`src/ccl/design/type-inference.md`, "Consuming a sum: naming the witness").
    assert_eq!(
        infer_program(&format!(
            r"
{f}x = f(True, box([1,2]), box([1,2,3]))
[y + 1 for y in x]"
        ))
        .to_string(),
        "Σ σ ∈ {[0, 1], [0, 2]}. (σ ⤇ Int)"
    );
}

/// **Each specialization gets its own witness.** A generic definition that returns a
/// conditional collection is monomorphized per use, and each specialization is an
/// independent copy — so a Σ written in the definition must not have its binder shared by
/// every copy.
///
/// The freshening monomorphization already ran renames *inference variables by level*, and
/// a witness binder is neither a variable the solver solves for nor levelled, so it was not
/// reached: every specialization named the definition's witness, and whichever one resolved
/// narrowest decided what that shared binder ranged over. Both resulting types were
/// individually well-formed and `Display` writes every witness `𝜎`, so — exactly as with
/// the sibling identity properties below — only an assertion on binder identity can see it.
#[test]
fn each_specialization_of_a_generic_conditional_gets_its_own_witness() {
    // One inference, so the two binders are comparable. Distinct domains per call site,
    // deliberately: equal ones would type correctly even under sharing.
    // The sum must be written *in the definition* — that is the only shape with a
    // definition-side binder for the copies to share. (`f(a, b, d) = b if a else d` forms
    // its sum at the call instead, so it has none.) Element types differ per call so the
    // two uses really are two specializations rather than one memoized copy.
    let ty = infer_program(
        r"
def f(a, b):
    box([b, b]) if a else box([b, b, b])
c = 3 > 2
x = f(c, 1)
y = f(c, True)
(x, y)",
    );
    let Type::Tuple(parts) = &ty else {
        panic!("expected a pair of the two specializations' results, got {ty}")
    };
    let [Type::Sigma(first), Type::Sigma(second)] = &parts[..] else {
        panic!("expected each component to be a sum over its own call's arms, got {ty}")
    };
    assert_ne!(
        first.binder(),
        second.binder(),
        "each specialization binds its own witness: {ty}"
    );
}

/// **Two witnesses live at once.** A comprehension over two conditional collections opens
/// both sums while typing one body, so both witnesses are in scope together and the
/// result's index domain mentions each. This is the case identity exists for: with one
/// anonymous witness the two would merge into a single position and be silently conflated
/// (`src/ccl/design/type-inference.md`, "Consuming a sum: naming the witness").
///
/// Distinct domains on the two sources, deliberately — equal ones would type correctly
/// even under conflation, so they would not test it.
#[test]
fn two_conditional_sources_keep_their_witnesses_apart() {
    let ty = infer_program(
        r"
c = 3 > 2
d = 4 > 3
a = box([1, 2]) if c else box([1, 2, 3])
b = box([10, 20, 30, 40]) if d else box([10, 20, 30, 40, 50])
[x + y for x in a for y in b]",
    );
    // Asserted structurally, not on the rendering. What has to hold is that the index
    // tuple's two components name the two *binders* — and a rendered type cannot express
    // binder identity at all (`Display` writes every witness `σ`), so a string assertion
    // passes just as happily on the distributed `((Σ 𝜎 ∈ 𝐾₁. 𝜎, Σ 𝜎 ∈ 𝐾₂. 𝜎) ⤇ Int)`,
    // where each index is quantified independently of the collection it indexes.
    let Type::Sigma(outer) = &ty else {
        panic!("expected a sum over the first source's domains, got {ty}")
    };
    let Type::Sigma(inner) = &*outer.body else {
        panic!("expected the second source's sum nested inside the first, got {ty}")
    };
    assert_eq!(
        outer.kind().listed(),
        Some(&[Type::UIntRange(2), Type::UIntRange(3)][..]),
        "the first source's candidate domains: {ty}"
    );
    assert_eq!(
        inner.kind().listed(),
        Some(&[Type::UIntRange(4), Type::UIntRange(5)][..]),
        "the second source's candidate domains: {ty}"
    );
    let Type::Fun {
        kind: cambra::ccl::FunKind::Data,
        domain,
        codomain,
        ..
    } = &*inner.body
    else {
        panic!("expected a data collection under both binders, got {ty}")
    };
    assert_eq!(
        **domain,
        Type::Tuple(vec![
            Type::WitnessRef(outer.binder()),
            Type::WitnessRef(inner.binder()),
        ]),
        "the index is the pair of the two witnesses, each naming its own binder: {ty}"
    );
    assert_eq!(**codomain, int(), "element type: {ty}");
}

/// **A consumer's result is quantified over the witness it named.** The consuming rule
/// says `𝑓(𝑒) : Σ 𝑤 ∈ 𝐾. 𝑊` for the *same* `𝑤` the sum was opened at, so a comprehension
/// over a conditional collection and the collection itself name **one binder**.
///
/// The property five separate sites got wrong, each by minting a binder where it held one
/// (the naming, the constraint-time binding, the carrier's re-pairing, `distribute_sigma`, the
/// join). Every resulting type was individually well-formed — the source read
/// `Σ 𝜎₁ ∈ 𝐾. (𝜎₁ ⤇ Int)` and the result `Σ 𝜎₂ ∈ 𝐾. (𝜎₂ ⤇ Int)`, both perfectly good types
/// — so nothing downstream could report it, and rendering cannot show it either: `Display`
/// writes every witness `𝜎`. Asserted on binder identity for that reason.
#[test]
fn a_comprehension_names_the_same_witness_as_its_source() {
    // Both types from one inference, so the binders are comparable — the source is the
    // *unfactored* sum `box` builds and the comprehension the *factored* one, so their
    // candidate sets differ by form and only identity is the shared fact.
    let ty = infer_program(
        r"
c = 3 > 2
x = box([1, 2]) if c else box([1, 2, 3])
(x, [y + 1 for y in x])",
    );
    let Type::Tuple(parts) = &ty else {
        panic!("expected (source, comprehension), got {ty}")
    };
    let [Type::Sigma(src), Type::Sigma(comp)] = &parts[..] else {
        panic!("both components are sums, got {ty}")
    };
    assert_eq!(
        src.binder(),
        comp.binder(),
        "the comprehension is quantified over the witness it opened: {ty}"
    );
    assert_eq!(
        *comp.body,
        Type::data_fun(Type::WitnessRef(comp.binder()), int()),
        "and its body names that binder: {ty}"
    );
}

/// **One collection consumed twice is one witness.** Both comprehensions range over
/// whichever domain the same conditional took, so they are not independent choices — the
/// sharing half of witness identity, where
/// `two_conditional_sources_keep_their_witnesses_apart` covers the separating half.
#[test]
fn one_collection_consumed_twice_shares_its_witness() {
    let ty = infer_program(
        r"
c = 3 > 2
x = box([1, 2]) if c else box([1, 2, 3])
([y for y in x], [z for z in x])",
    );
    let Type::Tuple(parts) = &ty else {
        panic!("expected a pair of collections, got {ty}")
    };
    let [Type::Sigma(a), Type::Sigma(b)] = &parts[..] else {
        panic!("both components are conditional collections, got {ty}")
    };
    assert_eq!(
        a.binder(),
        b.binder(),
        "two consumers of one collection name one witness: {ty}"
    );
    assert_eq!(a.kind(), b.kind(), "and range over the same domains: {ty}");
}

/// **Two independent conditionals are two witnesses**, even at identical domains — the
/// case that would pass under conflation, so it is the one worth asserting. `box`'s scheme
/// is a single `Σ 𝜎 ∈ {α}. 𝜎`, and instantiating it has to α-convert or every `box` in a
/// program names the binder the scheme was written with.
#[test]
fn independent_conditionals_at_equal_domains_stay_apart() {
    let ty = infer_program(
        r"
c = 3 > 2
d = 4 > 3
a = box([1, 2]) if c else box([1, 2, 3])
b = box([4, 5]) if d else box([4, 5, 6])
(a, b)",
    );
    let Type::Tuple(parts) = &ty else {
        panic!("expected a pair, got {ty}")
    };
    let [Type::Sigma(a), Type::Sigma(b)] = &parts[..] else {
        panic!("both components are conditional collections, got {ty}")
    };
    assert_eq!(
        a.kind(),
        b.kind(),
        "equal candidate domains, deliberately: {ty}"
    );
    assert_ne!(
        a.binder(),
        b.binder(),
        "independent conditionals are independent choices: {ty}"
    );
}

/// Heterogeneous *element* types stay a hard rejection, at both the binding and a
/// consumer. A conditional collection joins its arms' **domains**; the shared codomain is
/// an ordinary join, and two distinct atoms there are the untagged-sum collision that the
/// solver refuses (see `coalesce`).
#[test]
fn conditional_collection_arms_must_share_an_element_type() {
    let c = r#"
c = 3 > 2
x = [1, 2] if c else ["a", "b", "c"]
"#;
    for tail in ["x", "sum(x)", "[y for y in x]"] {
        assert!(
            !infer_program_err(&format!("{c}{tail}")).is_empty(),
            "expected a rejection for heterogeneous elements: {tail}"
        );
    }
}

/// A conditional collection flowing into a `List`-annotated **parameter**. Two shapes
/// meet in the domain lattice: the annotation contributes the described kind
/// `UIntRanges`, and the argument contributes the arms' domains.
///
/// A parameter is the route where those domains land as *atoms on one position* rather
/// than as separate candidates — an un-generalized inference variable that both arms
/// deposit bounds on. Both domains here are dense prefix ranges, so kind containment holds
/// and the meet keeps the narrower listed side.
#[test]
fn conditional_collection_into_a_list_annotated_param() {
    let c = "box([1, 2]) if True else box([1, 2, 3])";
    assert_eq!(
        infer_program(&format!(
            r"
def f(c: List(Int)):
    sum(c)
f({c})"
        )),
        int()
    );
    // A **filtered** arm is rejected, and now for the *intended* reason: its candidate
    // keeps its refinement through the join, and a refined range is not a `UIntRange`, so
    // it fails `List` membership (the rule itself is pinned by
    // `containment_in_a_description_is_membership_of_every_candidate`, in `src/ccl/ty.rs`).
    // Before a data-function join kept
    // its candidates, this was rejected earlier and for the wrong reason — the refinement
    // floated free of the position and the kinds came out unrelated before membership was
    // ever asked.
    let filtered = "box([x for x in [1, 2, 3] if x > 1]) if True else box([1, 2])";
    assert!(
        !infer_program_err(&format!(
            r"
def f(c: List(Int)):
    sum(c)
f({filtered})"
        ))
        .is_empty(),
        "a filtered collection is not a `List` — it cannot supply a length witness for a \
         domain with holes"
    );
}

/// A refinement belongs to **one candidate**, not to the sum: put the same refinement
/// shape on different arms and the two programs get genuinely different types.
///
/// This is the property a data-function join has to preserve, and the reason it is not
/// free. A `CompactType`'s `atoms` and `refinements` are independent slots, so merging two
/// candidates' *contents* collapses both programs to one bag — atoms `{[0, 1], [0, 2]}`
/// with the predicate floating loose — and neither `Σ 𝐷 ∈ {{[0, 2] | 𝑝}, {[0, 1] | 𝑝}}. 𝐷` nor
/// `Σ 𝐷 ∈ {[0, 2], [0, 1]}. 𝐷` is the answer. So the join must union candidates rather than merge
/// them; see `src/ccl/design/type-inference.md`, "Where the conditional-collection Σ comes
/// from".
#[test]
fn a_refinement_belongs_to_one_candidate_not_the_sum() {
    let refined_wider =
        infer_program("box([x for x in [1,2,3] if x > 1]) if True else box([1, 2])");
    let refined_narrower =
        infer_program("box([1, 2, 3]) if True else box([x for x in [1,2] if x > 1])");
    // Same two domains, same predicate shape — different types, because the refinement
    // rides one candidate rather than the sum.
    assert_ne!(refined_wider, refined_narrower);
    for (ty, refined, bare) in [
        (&refined_wider, Type::UIntRange(3), Type::UIntRange(2)),
        (&refined_narrower, Type::UIntRange(2), Type::UIntRange(3)),
    ] {
        let Type::Sigma(s) = ty else {
            panic!("expected a conditional collection, got {ty}");
        };
        let candidates = s
            .kind()
            .listed()
            .expect("an enumerated kind lists its domains");
        assert_eq!(candidates.len(), 2, "expected both arms, got {ty}");
        // `box` boxes whole arms, so each candidate is a collection type; the domains
        // the refinement has to stay attached to are one level in.
        let domains: Vec<&Type> = candidates
            .iter()
            .map(|c| match c {
                Type::Fun { domain, .. } => &**domain,
                other => panic!("expected a boxed collection candidate, got {other}"),
            })
            .collect();
        assert!(
            domains
                .iter()
                .any(|d| matches!(d, Type::Refinement(base, _) if **base == refined)),
            "the filtered arm's domain must carry the refinement, got {ty}"
        );
        assert!(
            domains.contains(&&bare),
            "the unfiltered arm's domain must stay bare, got {ty}"
        );
    }
}
/// A kinding constraint (`α :: 𝐾`) recorded on a **generalized** definition's
/// variable has to be reproduced in every instantiation. Here the annotation
/// `List(Int)` constrains a domain that is still a variable when `make` is
/// generalized, so each use site is what decides whether the constraint holds: a
/// range source realizes the length witness, a data source does not.
///
/// The regression this guards is silent *acceptance*. If instantiation dropped the
/// constraint, it would survive only on the scheme's own variable — which nothing
/// resolves — and every call site would type-check regardless of its source. See
/// `src/ccl/design/type-inference.md`, "What the kind level needs from the solver".
#[test]
fn test_kinding_constraint_survives_instantiation() {
    let def = r"
def make(s):
    r: List(Int) = box([y + 1 for y in s])
    r
";
    assert_eq!(
        infer_program(&format!("{def}make([1,2,3])")).to_string(),
        // The annotation narrows to the one domain the source has, and the sum stays —
        // the `box` on `r`'s initializer is what put it there, and an annotation bounds
        // rather than replaces.
        "Σ σ ∈ {([0, 2] ⤇ Int)}. σ",
        "a range source realizes the length witness at this use site"
    );
    let errs = infer_program_with_sources_err(&format!("{def}make(mysrc())"), &[("mysrc", int())]);
    assert!(
        errs.iter().any(|e| matches!(
            e,
            InferError::TypeMismatch { ctx, .. } if ctx == "collection annotation"
        )),
        "a data source does not, and the constraint must reach this use site to say so; \
         got {errs:?}"
    );
}

// ---------------------------------------------------------------------------
// `box` — the way into a sum
// ---------------------------------------------------------------------------

/// `box(x)` is the singleton sum over `x`'s own type. The candidate position is
/// invariant, so the argument's type is pinned exactly rather than widened on the way in.
#[test]
fn box_builds_the_singleton_sum_over_its_argument() {
    assert_eq!(
        infer_program("box([1, 2, 3])").to_string(),
        "Σ σ ∈ {([0, 2] ⤇ Int)}. σ"
    );
}

/// The point of `box`: two of them at a join union their candidate lists, so both
/// domains survive where the unboxed conditional has no upper bound at all.
#[test]
fn two_boxes_at_a_join_keep_both_candidates() {
    assert_eq!(
        infer_program(
            r"
c: Bool = True
box([1, 2]) if c else box([1, 2, 3])"
        )
        .to_string(),
        "Σ σ ∈ {([0, 1] ⤇ Int), ([0, 2] ⤇ Int)}. σ"
    );
}

/// A sum over whole types needs no shared element type — the generalization the
/// unfactored form buys, and what a factored `Σ 𝐷 ∈ 𝐾. 𝐷 ⤇ 𝑉` cannot express.
#[test]
fn a_box_join_needs_no_common_element_type() {
    assert_eq!(
        infer_program(
            r#"
c: Bool = True
box(1) if c else box("x")"#
        )
        .to_string(),
        "Σ σ ∈ {1, \"x\"}. σ"
    );
}

/// **`Σ ⊔ 𝑇` — the sum dissolves.** With no subtyping edge into a sum, none lies above a
/// bare `𝑇`, so every upper bound of both is a non-sum, and consuming the sum requires it
/// above every candidate. Mixing a boxed and an unboxed arm therefore discards the box rather
/// than spreading it — derived from the rules, not a special case.
#[test]
fn a_box_meeting_an_unboxed_arm_dissolves() {
    assert_eq!(
        infer_program(
            r"
c: Bool = True
xs = [1, 2]
box(xs) if c else xs"
        )
        .to_string(),
        infer_program(
            r"
xs = [1, 2]
xs"
        )
        .to_string()
    );
}

// ---------------------------------------------------------------------------
// Carrier characterization — the behaviour the `sigma`-slot migration must preserve
// ---------------------------------------------------------------------------
//
// These pin *observable* results for the paths that migration moves: today a sum and a
// plain data function share the `fun` slot, and the annotation-meets-consumer cases
// below are the `Σ ⊓ 𝑇` law working through that sharing. Written against behaviour
// rather than representation, so they survive the carrier changing underneath them —
// which is the point.

/// A domain-preserving consumer over an abstract collection gives back an abstract
/// collection, not a concrete one: the consumer carries the sum into its own result
/// domain rather than resolving it, and the close re-binds it there.
///
/// The two routes land in the two **spellings** of that sum, and which one is not
/// arbitrary. Passing `a` straight through keeps the unfactored form the `box` built;
/// consuming it reads the sum through its domains and rebuilds it factored, the only form
/// a described kind like `List(𝑉)` has. Each subtypes the other by Σ-width, so this is one
/// type written two ways — pinned separately rather than compared, because a change that
/// silently resolved either to a concrete `[0, 2] ⤇ Int` is exactly the regression.
#[test]
fn a_comprehension_over_a_list_param_stays_abstract() {
    assert_eq!(
        infer_program(
            r"
def f(a: List(Int)):
    [x + 1 for x in a]
f(box([1, 2, 3]))"
        )
        .to_string(),
        "Σ σ ∈ {[0, 2]}. (σ ⤇ Int)"
    );
    assert_eq!(
        infer_program(
            r"
def f(a: List(Int)):
    a
f(box([1, 2, 3]))"
        )
        .to_string(),
        "Σ σ ∈ {([0, 2] ⤇ Int)}. σ"
    );
}

/// A conditional collection reaching a `List(Int)` parameter: the sum's candidates each
/// have to be members of the annotation's kind. This is the cross-kind case — a listing
/// meeting a description — and it is the one the migration is most likely to disturb.
#[test]
fn a_conditional_collection_flows_into_a_list_param() {
    assert_eq!(
        infer_program(
            r"
c: Bool = True
def f(a: List(Int)):
    sum(a)
f(box([1, 2]) if c else box([1, 2, 3]))"
        ),
        int()
    );
}

/// `Collection(Int)` is the widest annotation, so everything narrower reaches it — a
/// literal, and a conditional over two domains alike.
#[test]
fn a_conditional_collection_flows_into_a_collection_param() {
    assert_eq!(
        infer_program(
            r"
c: Bool = True
def f(a: Collection(Int)):
    sum(a)
f(box([1, 2]) if c else box([1, 2, 3]))"
        ),
        int()
    );
}

/// **Factoring keeps the candidate's Pi binder.** A `box`ed collection reaching a
/// described-kind annotation has to be put in the annotation's form first, and
/// `factored_view` does that by splitting each candidate `𝐷 ⤇ 𝑉` into the witness kind
/// `{𝐷}` and the shared body `σ ⤇ 𝑉`.
///
/// When the candidate is **dependent** — `groupby`'s result is `(__gb_k: 𝐾) ⤇ 𝑉[__gb_k]`,
/// whose codomain names its own binder — that split has a binder to carry. Dropping it
/// leaves `__gb_k` free in the body, which the scope check reports as an out-of-scope
/// binder rather than as anything about sums. The binder rides the *witness* domain in the
/// factored form (`(__gb_k: σ) ⤇ 𝑉[__gb_k]`), which is what it meant all along: it ranges
/// over elements of whichever domain the witness picked.
#[test]
fn factoring_a_boxed_dependent_collection_keeps_its_binder() {
    let gb = "box(groupby([1,2,3], \\x -> x))";
    // Bare, the sum's one candidate is the whole Pi type and nothing is factored.
    let bare = infer_program(&format!("g = {gb}\ng")).to_string();
    assert!(
        bare.starts_with("Σ σ ∈ {((__gb_k: "),
        "an unfactored sum keeps the Pi type whole, got {bare}"
    );
    // Against a described kind it must factor, and the binder has to survive that —
    // rebound over the witness. Asserted on the binder rather than on the key domain,
    // which is what the keyed-collection work refines and this test does not pin.
    let ty = infer_program(&format!("g: Collection(_) = {gb}\ng")).to_string();
    assert!(
        ty.starts_with("Σ σ ∈ {") && ty.contains("((__gb_k: σ) ⤇"),
        "factoring must rebind __gb_k over the witness, got {ty}"
    );
}

/// The rejection that keeps a collection from silently narrowing: a *filtered* range is
/// a `Refinement`, not a `UIntRange`, so it is not a member of the `List` kind and the
/// length witness it would be handed does not exist.
#[test]
fn a_filtered_collection_is_not_a_list() {
    assert!(
        !infer_program_err(
            r"
def f(a: List(Int)):
    sum(a)
f(box([x for x in [1, 2, 3] if x > 1]))"
        )
        .is_empty()
    );
}

// ---------------------------------------------------------------------------
// Consuming a `box`ed collection — the unfactored/factored relation in practice
// ---------------------------------------------------------------------------

/// A single `box`ed collection consumes: `Σ σ ∈ {𝐷 ⤇ 𝑉}. σ` is consumed by naming its
/// witness as the consumer's domain and flowing the element type through.
#[test]
fn a_boxed_collection_is_consumable() {
    assert_eq!(infer_program("c: Bool = True\nsum(box([1, 2, 3]))"), int());
}

/// The case the whole `box` design exists for: two `box`ed arms join to the unfactored
/// sum, and consuming *that* works — which needs Σ-width read on instantiated bodies, so
/// `Σ σ ∈ {𝐷ᵢ ⤇ 𝑉ᵢ}. σ` relates to the factored form rather than being compared candidate
/// against candidate (`𝐷₀ ⤇ 𝑉 <: 𝐷₀`, an arrow below a range, which never holds).
#[test]
fn a_boxed_conditional_collection_is_consumable() {
    assert_eq!(
        infer_program("c: Bool = True\nsum(box([1]) if c else box([2, 3]))"),
        int()
    );
}

/// The join keeps both arms rather than collapsing to one, and keeps them *unfactored* —
/// the element types stay per-candidate (`1` and `Int`), which the factored form would
/// join away.
#[test]
fn a_boxed_conditional_keeps_its_candidates_unfactored() {
    assert_eq!(
        infer_program("c: Bool = True\nbox([1]) if c else box([2, 3])").to_string(),
        "Σ σ ∈ {([0, 0] ⤇ 1), ([0, 1] ⤇ Int)}. σ"
    );
}

/// A `box`ed conditional collection reaching a collection **annotation**. This is the
/// cross-form meet — an unfactored listing sum against a factored described one — and the
/// case that proves the two forms cannot simply be segregated by kind: `List(𝑉)` has no
/// unfactored spelling at all.
#[rstest]
#[case("List(Int)")]
#[case("Collection(Int)")]
fn a_boxed_conditional_collection_reaches_a_collection_annotation(#[case] annotation: &str) {
    let program = format!(
        "c: Bool = True\ndef g(a: {annotation}):\n    sum(a)\ng(box([1]) if c else box([2, 3]))"
    );
    assert_eq!(infer_program(&program), int(), "{program}");
}

/// A `box` behind a user function: the candidate reaching the join is an inference
/// variable, resolved through its bounds, and the arms' sums ride a scheme instantiation's
/// morphism that the join has to *force* rather than decline.
#[test]
fn a_boxed_collection_joins_through_a_user_function() {
    assert_eq!(
        infer_program(
            r"
c: Bool = True
def f(xs):
    box(xs)
sum(f([1]) if c else f([2, 3]))"
        ),
        int()
    );
}

/// **One source feeding two joins keeps their witnesses apart.** `a` reaches two different
/// conditionals; each is its own choice, so each gets its own witness, and neither borrows
/// `a`'s.
///
/// This is the separating half of the rule
/// `one_collection_consumed_twice_shares_its_witness` states from the other side: a variable
/// merely *carrying* one sum onward keeps its binder, and a variable at which
/// several *meet* mints. Adopting a shared input's binder instead collapses the two into one
/// witness and the second source's domains disappear from the type — silently, since the
/// tree then fails the post-inference wall for an unrelated-looking reason.
///
/// A sharper repro than it looks: with *independent* sources the same program types
/// correctly either way (`two_conditional_sources_keep_their_witnesses_apart`), so the
/// sharing is the only variable.
#[test]
fn a_source_shared_between_two_joins_keeps_the_joins_apart() {
    let ty = infer_program(
        r"
c = 3 > 2
d = 4 > 3
a = box([1, 2])
x = a if c else box([1, 2, 3])
y = a if d else box([1, 2, 3, 4, 5])
[p + q for p in x for q in y]",
    );
    // Two sources, two witnesses: a sum per generator, each over its own candidates.
    let Type::Sigma(outer) = &ty else {
        panic!("expected a sum over the first source's domains, got {ty}")
    };
    let Type::Sigma(inner) = &*outer.body else {
        panic!("expected the second source's sum nested inside the first, got {ty}")
    };
    assert_eq!(
        outer.kind().listed(),
        Some(&[Type::UIntRange(2), Type::UIntRange(3)][..]),
        "the first source's candidate domains: {ty}"
    );
    assert_eq!(
        inner.kind().listed(),
        Some(&[Type::UIntRange(2), Type::UIntRange(5)][..]),
        "the second source's candidate domains: {ty}"
    );
    assert_ne!(
        outer.binder(),
        inner.binder(),
        "the two joins keep their witnesses apart: {ty}"
    );
}

/// **A nested sum is consumed like any other collection.** Aggregating a comprehension over
/// *two* conditional sources has to reach through both binders: the consumer's demand lands
/// on the innermost body, whose domain is the index `Tuple` naming one witness per position.
///
/// This is the consumption half of `two_conditional_sources_keep_their_witnesses_apart`,
/// which pins the formation. Every rule between them assumed a sum was one binder deep — a
/// body `𝑤 ⤇ 𝑉` — and answered the demand against the bare witness, which a tuple is not.
#[test]
fn a_nested_sum_is_consumed_by_an_aggregate() {
    // Through `infer_and_check`: the rules that assumed one binder live at the
    // post-inference wall, where Check re-derives what Emit inferred, so inference alone
    // does not exercise them.
    let ty = infer_and_check(
        r"
c = 3 > 2
d = 4 > 3
a = box([1, 2]) if c else box([1, 2, 3])
b = box([10, 20]) if d else box([10, 20, 30])
sum([x + y for x in a for y in b])",
    );
    assert_eq!(
        ty,
        Type::Base(cambra::ccl::BaseType::Int),
        "aggregating over two conditional sources is an `Int`, the witnesses consumed: {ty}"
    );
}
