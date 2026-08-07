//! Integration tests for tagged variants.
//!
//! Builds [`TypedExpr`] trees directly
//! and runs them through the public `cambra::ccl::infer::infer` entry point.
//! These tests exercise the variant lattice (`Type::Variant`), the new
//! AST nodes (`VariantCtor`, `Match`), and their constraint/coalesce
//! integration — without depending on CHL surface syntax for variants
//! (which is a separate workstream).

use cambra::ccl::{
    Branch, FieldKey, Lit, Pattern, Type, TypedBinding, TypedExpr, TypedExprNode,
    infer::{InferError, LocatedInferError, TypeInferenceContext, infer},
};
use cambra::interpreter::BaseType;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn int() -> Type {
    Type::Base(BaseType::Int)
}
/// The type of the integer literal `n` — its **singleton**, `{Int | __elem == n}`
/// (rendered `n`). A literal is typed by which literal it is.
fn int_lit(n: i64) -> Type {
    cambra::ccl::infer::lit_singleton(&Lit::Int(n))
}
/// The type of the string literal `s` — see [`int_lit`].
fn str_lit_ty_local(s: &str) -> Type {
    cambra::ccl::infer::lit_singleton(&Lit::String(s.to_string()))
}
fn string() -> Type {
    Type::Base(BaseType::String)
}
fn unit_ty() -> Type {
    Type::Base(BaseType::Unit)
}

fn variant(tags: &[(&str, Type)]) -> Type {
    Type::variant(
        tags.iter()
            .map(|(t, ty)| (FieldKey::Name((*t).into()), ty.clone()))
            .collect(),
    )
}

/// Build a pattern-matching [`Branch`]: `` `tag(binding) [if guard] → body ``.
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
    infer(&mut expr, &mut ctx).map_err(LocatedInferError::bare)
}

/// Run inference and return the fully-inferred expression (so tests can
/// inspect inner `expr.ty` / `binding.ty` slots, not just the root type).
fn run_full(mut expr: TypedExpr) -> Result<TypedExpr, Vec<InferError>> {
    let mut ctx = TypeInferenceContext::new();
    infer(&mut expr, &mut ctx).map_err(LocatedInferError::bare)?;
    Ok(expr)
}

// ---------------------------------------------------------------------------
// Group A — Variant construction
// ---------------------------------------------------------------------------

/// `` `some(5) `` infers to `` {`some{Int}} ``.
#[test]
fn variant_ctor_int() {
    let ty = run(TypedExpr::variant_ctor("some", lit_int(5))).expect("inference ok");
    assert_eq!(ty, variant(&[("some", int_lit(5))]));
}

/// `` `none(()) `` infers to `` {`none} ``.
#[test]
fn variant_ctor_unit() {
    let ty = run(TypedExpr::variant_ctor("none", lit_unit())).expect("inference ok");
    assert_eq!(ty, variant(&[("none", unit_ty())]));
}

/// `` `pair((1, "x")) `` infers to `` {`pair{Int, String}} ``.
#[test]
fn variant_ctor_nested_payload() {
    let payload = TypedExpr::tuple(vec![lit_int(1), lit_string("x")]);
    let ty = run(TypedExpr::variant_ctor("pair", payload)).expect("inference ok");
    assert_eq!(
        ty,
        variant(&[("pair", Type::Tuple(vec![int_lit(1), str_lit_ty_local("x")]))])
    );
}

// ---------------------------------------------------------------------------
// Group B — Width subtyping (polarity-trap closer)
// ---------------------------------------------------------------------------

/// A lambda annotated with parameter type `` {`some{Int} | `none} `` accepts
/// a call argument of `` `some(5) `` (singleton variant `` {`some{Int}} ``). The
/// width-sub rule `` {`some} <: {`some | `none} `` is the polarity-trap closer.
///
/// **Ignored**: the widening itself now infers correctly (the one-way Apply
/// edges admit `` {`some} <: {`some | `none} `` at the call site), but the
/// coalesced variant comes back with canonicalized tag order (`` {`none | `some} ``) rather
/// than the annotation's declaration order, so the structural equality
/// fails. Un-ignore once variant tag order is preserved (or the comparison
/// is made order-insensitive).
#[test]
#[ignore = "coalesce canonicalizes variant tag order, losing declaration order"]
fn variant_param_accepts_subtype() {
    let param_ty = variant(&[("some", int()), ("none", unit_ty())]);
    let lambda = TypedExpr::new(TypedExprNode::Lambda {
        param: TypedBinding {
            name: "v".into(),
            ty: param_ty.clone(),
            user_annotation: Some(param_ty.clone()),
        },
        body: Box::new(var("v")),
    });
    let arg = TypedExpr::variant_ctor("some", lit_int(5));
    let app = TypedExpr::apply(arg, lambda);
    let ty = run(app).expect("inference ok");
    assert_eq!(ty, param_ty);
}

/// A lambda annotated with parameter type `` {`some{Int}} `` rejects `` `other(5) `` —
/// the tag is not in the parameter's accepted set.
#[test]
fn variant_extra_tag_rejected() {
    let param_ty = variant(&[("some", int())]);
    let lambda = TypedExpr::new(TypedExprNode::Lambda {
        param: TypedBinding {
            name: "v".into(),
            ty: param_ty.clone(),
            user_annotation: Some(param_ty),
        },
        body: Box::new(var("v")),
    });
    let arg = TypedExpr::variant_ctor("other", lit_int(5));
    let app = TypedExpr::apply(arg, lambda);
    assert!(
        run(app).is_err(),
        "the `other` tag should be rejected by a one-arm `some` param"
    );
}

/// An **open** arm set admits a subtype carrying tags it does not list, and still
/// constrains the payloads of the tags it does.
///
/// The two halves of the variant width rule, which are separable only by openness: a
/// closed arm set rejects the extra tag (`variant_extra_tag_rejected` above), an open
/// one skips it — while both recurse into every shared tag. Skipping rather than
/// bailing is what keeps the shared payloads constrained regardless of where the
/// unlisted tag falls in canonical tag order.
#[test]
fn open_variant_admits_extra_tags_and_still_constrains_shared_payloads() {
    use cambra::ccl::infer::solver::ConstrainCache;
    use cambra::ccl::infer::solver::constrain_subtype;

    let open_demand = Type::open_variant(vec![
        (FieldKey::Name("b".into()), int()),
        (FieldKey::Name("d".into()), int()),
    ]);
    // The subtype carries `a` and `c` — neither listed, and ordered *around* the
    // listed ones so a bail-on-first-miss would skip `b`'s or `d`'s payload edge.
    let subtype = Type::variant(vec![
        (FieldKey::Name("a".into()), int()),
        (FieldKey::Name("b".into()), int()),
        (FieldKey::Name("c".into()), int()),
        (FieldKey::Name("d".into()), int()),
    ]);
    let mut cache = ConstrainCache::new();
    assert!(
        constrain_subtype(&subtype, &open_demand, &mut cache).is_ok(),
        "an open arm set admits tags it does not list"
    );

    // Closed: the same pair is a mismatch, because `a` is not accepted.
    let closed_demand = Type::variant(vec![
        (FieldKey::Name("b".into()), int()),
        (FieldKey::Name("d".into()), int()),
    ]);
    let mut cache = ConstrainCache::new();
    assert!(
        constrain_subtype(&subtype, &closed_demand, &mut cache).is_err(),
        "a closed arm set rejects a tag it does not list"
    );

    // And a *shared* tag's payload is still checked under openness: `b: String`
    // cannot flow into `b: Int` just because the arm set is open.
    let bad = Type::variant(vec![
        (FieldKey::Name("a".into()), int()),
        (FieldKey::Name("b".into()), string()),
    ]);
    let mut cache = ConstrainCache::new();
    assert!(
        constrain_subtype(&bad, &open_demand, &mut cache).is_err(),
        "openness relaxes the tag set, not the shared payloads"
    );
}

// ---------------------------------------------------------------------------
// Group C — Match elimination
// ---------------------------------------------------------------------------

/// ``match `some(7) { `some(n) → n + 1; `none(_) → 0 }`` typed at `Int`
/// when arm bodies are both `Int`.
///
/// The scrutinee here is a singleton `` {`some{Int}} ``. `emit_match` builds
/// the expected shape `` {`some{α} | `none{β}} `` and constrains `scrutinee <:
/// expected` (one-way), so the singleton flows through via variant
/// width-sub without hitting the bidirectional-Apply collapse.
#[test]
fn match_unifies_arm_bodies() {
    use cambra::ccl::{ArithmeticKind, BinOpKind};
    let arms = vec![
        arm(
            "some",
            "n",
            None,
            TypedExpr::binop(
                var("n"),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                lit_int(1),
            ),
        ),
        arm("none", "_", None, lit_int(0)),
    ];
    let scrutinee = TypedExpr::variant_ctor("some", lit_int(7));
    let ty = run(TypedExpr::match_expr(scrutinee, arms)).expect("match unification ok");
    assert_eq!(ty, int());
}

/// Per-arm payload narrowing: in `` case `some(n) ``, `n` types at `Int` (the
/// narrowed payload), not as a union. We assert by using `n` in an Int
/// context that would fail if the binding had a non-Int type.
#[test]
fn match_per_arm_payload_narrowing() {
    use cambra::ccl::{ArithmeticKind, BinOpKind};
    let arms = vec![
        // `n + 1` only typechecks if `n: Int`.
        arm(
            "some",
            "n",
            None,
            TypedExpr::binop(
                var("n"),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                lit_int(1),
            ),
        ),
        arm("none", "_", None, lit_int(42)),
    ];
    let scrutinee = TypedExpr::variant_ctor("some", lit_int(3));
    let ty = run(TypedExpr::match_expr(scrutinee, arms)).expect("payload narrowing ok");
    assert_eq!(ty, int());
}

/// After inference, `arm.binding.ty` must be the resolved per-tag payload
/// type (`Int` here for `` `some(n) ``), and a `Var(arm.binding.name)`
/// reference inside the arm body must also carry that type. Downstream
/// passes (lambda elimination, dictionary passing) read these slots and
/// will fail to typecheck if either is `Type::Hole`.
#[test]
fn match_fills_arm_binding_and_body_var_types() {
    use cambra::ccl::{ArithmeticKind, BinOpKind, TypedExprNode};
    let arms = vec![
        // body = `n + 1` so the `Var(n)` reference is visible.
        arm(
            "some",
            "n",
            None,
            TypedExpr::binop(
                var("n"),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                lit_int(1),
            ),
        ),
        arm("none", "_", None, lit_int(42)),
    ];
    let scrutinee = TypedExpr::variant_ctor("some", lit_int(3));
    let expr = run_full(TypedExpr::match_expr(scrutinee, arms)).expect("inference ok");

    let TypedExprNode::Case { branches, .. } = &expr.node else {
        panic!("expected Case, got {:?}", expr.node);
    };
    let some_arm = branches
        .iter()
        .find(|b| b.pattern.as_ref().is_some_and(|p| p.tag == "some"))
        .expect("Some arm");
    let some_pat = some_arm.pattern.as_ref().expect("Some arm has a pattern");
    assert_eq!(
        some_pat.binding.ty,
        int_lit(3),
        "pattern binding.ty must be the narrowed payload (the scrutinee's `3`), got {}",
        some_pat.binding.ty
    );

    // Walk to the `Var(n)` inside `n + 1` and check its ty.
    let TypedExprNode::BinOp { left, .. } = &some_arm.body.node else {
        panic!("expected BinOp body");
    };
    let TypedExprNode::Var(name) = &left.node else {
        panic!("expected Var(n)");
    };
    assert_eq!(name.base(), "n");
    assert_eq!(
        left.ty,
        int_lit(3),
        "Var(n).ty inside arm body must be the scrutinee's payload, got {}",
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

/// `` case `some(n) if n > 0 → n `` — a Bool guard on a Match arm.
/// Verifies the guard is required to type at Bool.
#[test]
fn match_with_guard() {
    use cambra::ccl::{BinOpKind, CompareKind};
    let arms = vec![arm(
        "some",
        "n",
        Some(TypedExpr::binop(
            var("n"),
            BinOpKind::Compare(CompareKind::Greater),
            lit_int(0),
        )),
        var("n"),
    )];
    let scrutinee = TypedExpr::variant_ctor("some", lit_int(3));
    // The arm returns its binding, and the binding is the scrutinee's payload — so
    // the match's type is the payload's own, singleton included.
    let ty = run(TypedExpr::match_expr(scrutinee, arms)).expect("guarded match ok");
    assert_eq!(ty, int_lit(3));
}

/// Match with non-Bool guard should fail.
#[test]
fn match_with_non_bool_guard_rejected() {
    // Int-typed guard — should be rejected.
    let arms = vec![arm("some", "n", Some(lit_int(1)), var("n"))];
    let scrutinee = TypedExpr::variant_ctor("some", lit_int(3));
    assert!(
        run(TypedExpr::match_expr(scrutinee, arms)).is_err(),
        "non-Bool guard should be rejected"
    );
}

/// Empty `Match` arms should fail.
#[test]
fn match_empty_arms_rejected() {
    let scrutinee = TypedExpr::variant_ctor("some", lit_int(1));
    let expr = TypedExpr::match_expr(scrutinee, vec![]);
    assert!(run(expr).is_err(), "empty arm list should be rejected");
}

// ---------------------------------------------------------------------------
// Group D — Flow through lambdas / Case
// ---------------------------------------------------------------------------

/// `` (λ x: Int → `some(x)) 5 `` → `` {`some{Int}} ``.
#[test]
fn lambda_returns_variant() {
    let lambda = TypedExpr::new(TypedExprNode::Lambda {
        param: TypedBinding {
            name: "x".into(),
            ty: int(),
            user_annotation: Some(int()),
        },
        body: Box::new(TypedExpr::variant_ctor("some", var("x"))),
    });
    let app = TypedExpr::apply(lit_int(5), lambda);
    let ty = run(app).expect("inference ok");
    assert_eq!(ty, variant(&[("some", int())]));
}

/// `` if True then `some(1) else `none(()) `` — Case unifies the two variant
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
            body: TypedExpr::variant_ctor("some", lit_int(1)),
        },
        Branch {
            pattern: None,
            guard: lit_bool(true),
            body: TypedExpr::variant_ctor("none", lit_unit()),
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
    let expected = variant(&[("none", unit_ty()), ("some", int())]);
    assert_eq!(ty, expected, "expected union of tags, got {ty}");
}

// ---------------------------------------------------------------------------
// Group E — Payload variance / depth
// ---------------------------------------------------------------------------

/// `` `a(5) `` flowing into a `` {`a{Int} | `b{Str}} ``-annotated lambda parameter.
/// Payload covariance accepts the Int payload against the Int slot.
///
/// **Ignored**: same bidirectional-Apply collapse as
/// `variant_param_accepts_subtype`. Will pass once the let-polymorphism
/// work replaces the hack.
#[test]
#[ignore = "blocked by bidirectional Apply equality-collapse; needs let-polymorphism"]
fn payload_covariance_accept() {
    let param_ty = variant(&[("a", int()), ("b", string())]);
    let lambda = TypedExpr::new(TypedExprNode::Lambda {
        param: TypedBinding {
            name: "v".into(),
            ty: param_ty.clone(),
            user_annotation: Some(param_ty.clone()),
        },
        body: Box::new(var("v")),
    });
    let arg = TypedExpr::variant_ctor("a", lit_int(5));
    let ty = run(TypedExpr::apply(arg, lambda)).expect("payload variance ok");
    assert_eq!(ty, param_ty);
}

/// `` `a(5) `` against a `` {`a{Str}} ``-typed parameter — payload-type mismatch.
#[test]
fn payload_mismatch_reject() {
    let param_ty = variant(&[("a", string())]);
    let lambda = TypedExpr::new(TypedExprNode::Lambda {
        param: TypedBinding {
            name: "v".into(),
            ty: param_ty.clone(),
            user_annotation: Some(param_ty),
        },
        body: Box::new(var("v")),
    });
    let arg = TypedExpr::variant_ctor("a", lit_int(5));
    assert!(
        run(TypedExpr::apply(arg, lambda)).is_err(),
        "Int payload should not satisfy String payload slot"
    );
}
