//! Integration tests for tagged variants.
//!
//! Builds [`TypedExpr`] trees directly (mirroring `tests/simple_sub_differential.rs`)
//! and runs them through the public `cambra::ccl::infer::infer` entry point.
//! These tests exercise the variant lattice (`Type::Variant`), the new
//! AST nodes (`VariantCtor`, `Match`), and their constraint/coalesce
//! integration — without depending on CHL surface syntax for variants
//! (which is a separate workstream).

use cambra::ccl::{
    Branch, Lit, Pattern, Type, TypedBinding, TypedExpr, TypedExprNode,
    infer::{InferError, TypeInferenceContext, infer},
    simple_sub::FieldKey,
};
use cambra::interpreter::BaseType;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn int() -> Type {
    Type::Base(BaseType::Int)
}
fn string() -> Type {
    Type::Base(BaseType::String)
}
fn unit_ty() -> Type {
    Type::Base(BaseType::Unit)
}

fn variant(tags: &[(&str, Type)]) -> Type {
    Type::Variant(
        tags.iter()
            .map(|(t, ty)| (FieldKey::Name((*t).into()), ty.clone()))
            .collect(),
    )
}

/// Build a pattern-matching [`Branch`]: `.tag(binding) [if guard] → body`.
/// A `None` guard becomes the literal-`true` "no secondary filter" guard.
fn arm(tag: &str, binding: &str, guard: Option<TypedExpr>, body: TypedExpr) -> Branch {
    Branch {
        pattern: Some(Pattern {
            tag: tag.into(),
            binding: TypedBinding {
                name: binding.into(),
                ty: Type::Hole,
                user_annotation: None,
            },
        }),
        guard: guard.unwrap_or_else(|| TypedExpr::lit(Lit::Bool(true))),
        body,
    }
}

fn lit_int(n: i64) -> TypedExpr {
    TypedExpr::lit(Lit::Int(n))
}
fn lit_string(s: &str) -> TypedExpr {
    TypedExpr::lit(Lit::String(s.into()))
}
fn lit_bool(b: bool) -> TypedExpr {
    TypedExpr::lit(Lit::Bool(b))
}
fn lit_unit() -> TypedExpr {
    TypedExpr::lit(Lit::Unit)
}

fn var(name: &str) -> TypedExpr {
    TypedExpr::var(name)
}

/// Run inference on an expression, returning the inferred root type.
fn run(mut expr: TypedExpr) -> Result<Type, Vec<InferError>> {
    let mut ctx = TypeInferenceContext::new();
    infer(&mut expr, &mut ctx)
}

/// Run inference and return the fully-inferred expression (so tests can
/// inspect inner `expr.ty` / `binding.ty` slots, not just the root type).
fn run_full(mut expr: TypedExpr) -> Result<TypedExpr, Vec<InferError>> {
    let mut ctx = TypeInferenceContext::new();
    infer(&mut expr, &mut ctx)?;
    Ok(expr)
}

// ---------------------------------------------------------------------------
// Group A — Variant construction
// ---------------------------------------------------------------------------

/// `.Some(5)` infers to `[Some(Int)]`.
#[test]
fn variant_ctor_int() {
    let ty = run(TypedExpr::variant_ctor("Some", lit_int(5))).expect("inference ok");
    assert_eq!(ty, variant(&[("Some", int())]));
}

/// `.None(())` infers to `[None(Unit)]`.
#[test]
fn variant_ctor_unit() {
    let ty = run(TypedExpr::variant_ctor("None", lit_unit())).expect("inference ok");
    assert_eq!(ty, variant(&[("None", unit_ty())]));
}

/// `.Pair((1, "x"))` infers to `[Pair((Int, String))]`.
#[test]
fn variant_ctor_nested_payload() {
    let payload = TypedExpr::tuple(vec![lit_int(1), lit_string("x")]);
    let ty = run(TypedExpr::variant_ctor("Pair", payload)).expect("inference ok");
    assert_eq!(ty, variant(&[("Pair", Type::Tuple(vec![int(), string()]))]));
}

// ---------------------------------------------------------------------------
// Group B — Width subtyping (polarity-trap closer)
// ---------------------------------------------------------------------------

/// A lambda annotated with parameter type `[Some(Int), None(Unit)]` accepts
/// a call argument of `.Some(5)` (singleton variant `[Some(Int)]`). The
/// width-sub rule `[Some] <: [Some, None]` is the polarity-trap closer.
///
/// **Ignored**: hits today's bidirectional `Apply` constraint (the "TODO:
/// SOUNDNESS" hack in `infer_simple_sub.rs::emit_apply`), which forces
/// argument type to equal parameter type and so disallows width-sub at
/// apply sites. Will pass once the let-polymorphism work replaces the
/// bidirectional Apply + opposite-polarity fallback with `Type::ForAll` +
/// monomorphization (see brainstorm doc §3.1).
#[test]
#[ignore = "blocked by bidirectional Apply equality-collapse; needs let-polymorphism"]
fn variant_param_accepts_subtype() {
    let param_ty = variant(&[("Some", int()), ("None", unit_ty())]);
    let lambda = TypedExpr::new(TypedExprNode::Lambda {
        param: TypedBinding {
            name: "v".into(),
            ty: param_ty.clone(),
            user_annotation: Some(param_ty.clone()),
        },
        body: Box::new(var("v")),
        refinement: None,
    });
    let arg = TypedExpr::variant_ctor("Some", lit_int(5));
    let app = TypedExpr::apply(arg, lambda);
    let ty = run(app).expect("inference ok");
    assert_eq!(ty, param_ty);
}

/// A lambda annotated with parameter type `[Some(Int)]` rejects `.Other(5)` —
/// the tag is not in the parameter's accepted set.
#[test]
fn variant_extra_tag_rejected() {
    let param_ty = variant(&[("Some", int())]);
    let lambda = TypedExpr::new(TypedExprNode::Lambda {
        param: TypedBinding {
            name: "v".into(),
            ty: param_ty.clone(),
            user_annotation: Some(param_ty),
        },
        body: Box::new(var("v")),
        refinement: None,
    });
    let arg = TypedExpr::variant_ctor("Other", lit_int(5));
    let app = TypedExpr::apply(arg, lambda);
    assert!(
        run(app).is_err(),
        "Other tag should be rejected by [Some]-typed param"
    );
}

// ---------------------------------------------------------------------------
// Group C — Match elimination
// ---------------------------------------------------------------------------

/// `match .Some(7) { .Some(n) → n + 1; .None(_) → 0 }` typed at `Int`
/// when arm bodies are both `Int`.
///
/// The scrutinee here is a singleton `[Some(Int)]`. `emit_match` builds
/// the expected shape `[Some(α), None(β)]` and constrains `scrutinee <:
/// expected` (one-way), so the singleton flows through via variant
/// width-sub without hitting the bidirectional-Apply collapse.
#[test]
fn match_unifies_arm_bodies() {
    use cambra::ccl::{ArithmeticKind, BinOpKind};
    let arms = vec![
        arm(
            "Some",
            "n",
            None,
            TypedExpr::binop(
                var("n"),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                lit_int(1),
            ),
        ),
        arm("None", "_", None, lit_int(0)),
    ];
    let scrutinee = TypedExpr::variant_ctor("Some", lit_int(7));
    let ty = run(TypedExpr::match_expr(scrutinee, arms)).expect("match unification ok");
    assert_eq!(ty, int());
}

/// Per-arm payload narrowing: in `case .Some(n)`, `n` types at `Int` (the
/// narrowed payload), not as a union. We assert by using `n` in an Int
/// context that would fail if the binding had a non-Int type.
#[test]
fn match_per_arm_payload_narrowing() {
    use cambra::ccl::{ArithmeticKind, BinOpKind};
    let arms = vec![
        // `n + 1` only typechecks if `n: Int`.
        arm(
            "Some",
            "n",
            None,
            TypedExpr::binop(
                var("n"),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                lit_int(1),
            ),
        ),
        arm("None", "_", None, lit_int(42)),
    ];
    let scrutinee = TypedExpr::variant_ctor("Some", lit_int(3));
    let ty = run(TypedExpr::match_expr(scrutinee, arms)).expect("payload narrowing ok");
    assert_eq!(ty, int());
}

/// After inference, `arm.binding.ty` must be the resolved per-tag payload
/// type (`Int` here for `.Some(n)`), and a `Var(arm.binding.name)`
/// reference inside the arm body must also carry that type. Downstream
/// passes (lambda elimination, dictionary passing) read these slots and
/// will fail to typecheck if either is `Type::Hole`.
#[test]
fn match_fills_arm_binding_and_body_var_types() {
    use cambra::ccl::{ArithmeticKind, BinOpKind, TypedExprNode};
    let arms = vec![
        // body = `n + 1` so the `Var(n)` reference is visible.
        arm(
            "Some",
            "n",
            None,
            TypedExpr::binop(
                var("n"),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                lit_int(1),
            ),
        ),
        arm("None", "_", None, lit_int(42)),
    ];
    let scrutinee = TypedExpr::variant_ctor("Some", lit_int(3));
    let expr = run_full(TypedExpr::match_expr(scrutinee, arms)).expect("inference ok");

    let TypedExprNode::Case { branches, .. } = &expr.node else {
        panic!("expected Case, got {:?}", expr.node);
    };
    let some_arm = branches
        .iter()
        .find(|b| b.pattern.as_ref().is_some_and(|p| p.tag == "Some"))
        .expect("Some arm");
    let some_pat = some_arm.pattern.as_ref().expect("Some arm has a pattern");
    assert_eq!(
        some_pat.binding.ty,
        int(),
        "pattern binding.ty must be the narrowed payload (Int), got {}",
        some_pat.binding.ty
    );

    // Walk to the `Var(n)` inside `n + 1` and check its ty.
    let TypedExprNode::BinOp { left, .. } = &some_arm.body.node else {
        panic!("expected BinOp body");
    };
    let TypedExprNode::Var(name) = &left.node else {
        panic!("expected Var(n)");
    };
    assert_eq!(name, "n");
    assert_eq!(
        left.ty,
        int(),
        "Var(n).ty inside arm body must be Int, got {}",
        left.ty
    );
}

/// `match 5 { .Foo(_) → ... }` — scrutinee is not a variant. Inference fails.
#[test]
fn match_scrutinee_must_be_variant() {
    let arms = vec![arm("Foo", "x", None, lit_int(0))];
    // No annotation forcing a variant; lit Int is the scrutinee directly.
    let expr = TypedExpr::match_expr(lit_int(5), arms);
    assert!(run(expr).is_err(), "Int scrutinee should be rejected");
}

/// `case .Some(n) if n > 0 → n` — a Bool guard on a Match arm.
/// Verifies the guard is required to type at Bool.
#[test]
fn match_with_guard() {
    use cambra::ccl::{BinOpKind, CompareKind};
    let arms = vec![arm(
        "Some",
        "n",
        Some(TypedExpr::binop(
            var("n"),
            BinOpKind::Compare(CompareKind::Greater),
            lit_int(0),
        )),
        var("n"),
    )];
    let scrutinee = TypedExpr::variant_ctor("Some", lit_int(3));
    let ty = run(TypedExpr::match_expr(scrutinee, arms)).expect("guarded match ok");
    assert_eq!(ty, int());
}

/// Match with non-Bool guard should fail.
#[test]
fn match_with_non_bool_guard_rejected() {
    // Int-typed guard — should be rejected.
    let arms = vec![arm("Some", "n", Some(lit_int(1)), var("n"))];
    let scrutinee = TypedExpr::variant_ctor("Some", lit_int(3));
    assert!(
        run(TypedExpr::match_expr(scrutinee, arms)).is_err(),
        "non-Bool guard should be rejected"
    );
}

/// Empty `Match` arms should fail.
#[test]
fn match_empty_arms_rejected() {
    let scrutinee = TypedExpr::variant_ctor("Some", lit_int(1));
    let expr = TypedExpr::match_expr(scrutinee, vec![]);
    assert!(run(expr).is_err(), "empty arm list should be rejected");
}

// ---------------------------------------------------------------------------
// Group D — Flow through lambdas / Case
// ---------------------------------------------------------------------------

/// `(λ x: Int → .Some(x)) 5` → `[Some(Int)]`.
#[test]
fn lambda_returns_variant() {
    let lambda = TypedExpr::new(TypedExprNode::Lambda {
        param: TypedBinding {
            name: "x".into(),
            ty: int(),
            user_annotation: Some(int()),
        },
        body: Box::new(TypedExpr::variant_ctor("Some", var("x"))),
        refinement: None,
    });
    let app = TypedExpr::apply(lit_int(5), lambda);
    let ty = run(app).expect("inference ok");
    assert_eq!(ty, variant(&[("Some", int())]));
}

/// `if True then .Some(1) else .None(())` — Case unifies the two variant
/// branches at the positive polarity, yielding the union of tags.
///
/// **Ignored**: `emit_case` uses two-way constrain to unify arm bodies,
/// which forces equality and rejects width-distinct variants. Same root
/// cause as the bidirectional-Apply hack — see §3.1. The conceptually
/// correct behaviour is to drop a single-direction lower-bound constraint
/// for arm bodies, which depends on the same let-polymorphism cleanup.
#[test]
#[ignore = "blocked by two-way Case arm constraining; needs let-polymorphism"]
fn if_returns_variant() {
    let arms = vec![
        Branch {
            pattern: None,
            guard: lit_bool(true),
            body: TypedExpr::variant_ctor("Some", lit_int(1)),
        },
        Branch {
            pattern: None,
            guard: lit_bool(true),
            body: TypedExpr::variant_ctor("None", lit_unit()),
        },
    ];
    let expr = TypedExpr::new(TypedExprNode::Case {
        scrutinee: None,
        branches: arms,
    });
    let ty = run(expr).expect("inference ok");
    // Both arms get mutually constrained; the resulting type is the
    // first arm's type after the second arm flowed into it as a
    // lower bound. Coalesce at positive polarity unions the tags.
    let expected = variant(&[("None", unit_ty()), ("Some", int())]);
    assert_eq!(ty, expected, "expected union of tags, got {ty}");
}

// ---------------------------------------------------------------------------
// Group E — Payload variance / depth
// ---------------------------------------------------------------------------

/// `.A(5)` flowing into a `[A(Int), B(Str)]`-annotated lambda parameter.
/// Payload covariance accepts the Int payload against the Int slot.
///
/// **Ignored**: same bidirectional-Apply collapse as
/// `variant_param_accepts_subtype`. Will pass once the let-polymorphism
/// work replaces the hack (brainstorm doc §3.1).
#[test]
#[ignore = "blocked by bidirectional Apply equality-collapse; needs let-polymorphism"]
fn payload_covariance_accept() {
    let param_ty = variant(&[("A", int()), ("B", string())]);
    let lambda = TypedExpr::new(TypedExprNode::Lambda {
        param: TypedBinding {
            name: "v".into(),
            ty: param_ty.clone(),
            user_annotation: Some(param_ty.clone()),
        },
        body: Box::new(var("v")),
        refinement: None,
    });
    let arg = TypedExpr::variant_ctor("A", lit_int(5));
    let ty = run(TypedExpr::apply(arg, lambda)).expect("payload variance ok");
    assert_eq!(ty, param_ty);
}

/// `.A(5)` against a `[A(Str)]`-typed parameter — payload-type mismatch.
#[test]
fn payload_mismatch_reject() {
    let param_ty = variant(&[("A", string())]);
    let lambda = TypedExpr::new(TypedExprNode::Lambda {
        param: TypedBinding {
            name: "v".into(),
            ty: param_ty.clone(),
            user_annotation: Some(param_ty),
        },
        body: Box::new(var("v")),
        refinement: None,
    });
    let arg = TypedExpr::variant_ctor("A", lit_int(5));
    assert!(
        run(TypedExpr::apply(arg, lambda)).is_err(),
        "Int payload should not satisfy String payload slot"
    );
}
