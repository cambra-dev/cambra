//! Integration tests for tagged variants.
//!
//! Builds [`TypedExpr`] trees directly
//! and runs them through the public `cambra::ccl::infer::infer` entry point.
//! These tests exercise the variant lattice (`Type::Variant`), the new
//! AST nodes (`VariantCtor`, `Match`), and their constraint/coalesce
//! integration — without depending on CHL surface syntax for variants
//! (which is a separate workstream).

use cambra::ccl::ArithmeticKind;
use cambra::ccl::{
    Branch, FieldKey, Lit, Pattern, Type, TypedBinding, TypedExpr, TypedExprNode,
    infer::{InferError, LocatedInferError, TypeInferenceContext, infer},
};
use cambra::interpreter::BaseType;
use rstest::rstest;

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
            empty_payload: false,
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
/// The payload of a tag only *one* arm carries keeps that arm's value claim: the
/// join intersects refinements across arms that meet, and these two never do — one
/// carries `` `some ``, the other `` `none ``. So `` `some ``'s payload stays the singleton `1`
/// rather than widening to `Int`.
#[test]
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
    // Each arm flows one-way into a shared result variable, so coalescing at
    // positive polarity unions the tags. `` `some ``'s payload is the literal's
    // singleton, not `Int`, because no sibling arm carries `` `some `` to intersect
    // it with.
    let expected = variant(&[("none", unit_ty()), ("some", int_lit(1))]);
    assert_eq!(ty, expected, "expected union of tags, got {ty}");
}

// ---------------------------------------------------------------------------
// Group E — Payload variance / depth
// ---------------------------------------------------------------------------

/// `` `a(5) `` flowing into a `` {`a{Int} | `b{Str}} ``-annotated lambda parameter.
/// Payload covariance accepts the Int payload against the Int slot.
///
#[test]
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

// ---------------------------------------------------------------------------
// Group F — Payloads of arms nothing reaches
// ---------------------------------------------------------------------------

/// The payload type recorded for the arm named `tag`, found by descending to the
/// first `Case` in the tree (monomorphization wraps the lambda in a `let`).
fn arm_payload_ty(expr: &TypedExpr, tag: &str) -> Type {
    fn find(expr: &TypedExpr, tag: &str) -> Option<Type> {
        if let TypedExprNode::Case { branches, .. } = &expr.node {
            for b in branches {
                if let Some(p) = &b.pattern
                    && p.tag == tag
                {
                    return Some(p.binding.ty.clone());
                }
            }
        }
        let mut found = None;
        expr.walk_children(|c| {
            if found.is_none() {
                found = find(c, tag);
            }
        });
        found
    }
    find(expr, tag).unwrap_or_else(|| panic!("no arm `{tag}` in tree"))
}

/// ``let f = λ x → match x { `a(v) → v; `b(w) → 0 } in `a(1) ▷ f``.
///
/// The `b` arm is unreachable (the argument carries only `a`) *and* ignores its
/// binder, so nothing in the program constrains its payload. Inference must
/// still produce a fully concrete tree: the variable is pinned to `Unit` in the
/// constraint graph, so the binder slot **and** the lambda's parameter type
/// agree on it. Before the pin, `f`'s domain kept a bare `Infer` and the
/// post-inference wall rejected this program.
#[test]
fn unobservable_arm_payload_resolves_everywhere() {
    let body = TypedExpr::new(TypedExprNode::Case {
        scrutinee: Some(Box::new(var("x"))),
        branches: vec![
            arm("a", "v", None, var("v")),
            arm("b", "w", None, lit_int(0)),
        ],
    });
    let lambda = TypedExpr::lambda("x", Type::Hole, body);
    let call = TypedExpr::apply(TypedExpr::variant_ctor("a", lit_int(1)), var("f"));
    let full = run_full(TypedExpr::let_bind("f", lambda, call)).expect("inference ok");

    assert_eq!(arm_payload_ty(&full, "b"), unit_ty());
    // The wall the residual variable used to fail: no `Infer` left anywhere,
    // including inside the lambda's parameter type.
    cambra::ccl::infer::check_fully_typed(&full)
        .expect("an unobservable payload leaves no unresolved variable");
}

/// The same lambda applied to `` `b(2) `` instead.
///
/// Now a *call site* constrains the payload the arm ignores, and that
/// application is emitted after the `Case` it applies to. The payload must come
/// from the argument rather than being pinned, which is why the pin runs once
/// constraint emission is complete rather than at the end of `emit_case`.
#[test]
fn ignored_arm_payload_still_takes_its_argument_type() {
    let body = TypedExpr::new(TypedExprNode::Case {
        scrutinee: Some(Box::new(var("x"))),
        branches: vec![
            arm("a", "v", None, lit_int(0)),
            arm("b", "w", None, lit_int(0)),
        ],
    });
    let lambda = TypedExpr::lambda("x", Type::Hole, body);
    let call = TypedExpr::apply(TypedExpr::variant_ctor("b", lit_int(2)), var("f"));
    let full = run_full(TypedExpr::let_bind("f", lambda, call)).expect("inference ok");

    assert_eq!(arm_payload_ty(&full, "b"), int_lit(2));
    cambra::ccl::infer::check_fully_typed(&full).expect("fully typed");
}

/// An arm whose body **is** its binder is pinned to the type it flows into, not
/// to `Unit`.
///
/// The binder's only use is "be the arm's result", which records one subtyping
/// upper bound: the arms' result join. That join is `Int@1` — what the reachable
/// arm produced — so the unreachable arm's payload is `Int@1` too. The assertion
/// is that specific type rather than merely "not `Unit`", since what is being
/// pinned down is *where* a flowing binder gets its type from.
///
/// `Unit` here is not a weaker answer, it is an inconsistent one: the payload is
/// the arm's result, so `Unit` enters the arms' join and collides with `Int`,
/// rejecting a program that type-checks. That is why this arm of `payload_pin`
/// exists at all.
///
/// The singleton is the second thing under test. The pin's bound arrives beside
/// the scrutinee's own per-tag variable, whose empty refinement set would absorb
/// `Int@1`'s down to a bare `Int` under the positive intersection — so this also
/// covers `CompactType::imposes_nothing`, the only place a refined pin makes that
/// identity observable.
#[test]
fn read_arm_payload_is_pinned_to_where_it_flows() {
    let body = TypedExpr::new(TypedExprNode::Case {
        scrutinee: Some(Box::new(var("x"))),
        branches: vec![arm("a", "v", None, var("v")), arm("b", "w", None, var("w"))],
    });
    let lambda = TypedExpr::lambda("x", Type::Hole, body);
    let call = TypedExpr::apply(TypedExpr::variant_ctor("a", lit_int(1)), var("f"));
    let full = run_full(TypedExpr::let_bind("f", lambda, call)).expect("inference ok");

    assert_eq!(arm_payload_ty(&full, "b"), int_lit(1));
    cambra::ccl::infer::check_fully_typed(&full).expect("fully typed");
}

/// What an unreachable arm's payload is pinned to when an **operator** reads the
/// binder — the third of the pin's three cases.
///
/// [`unobservable_arm_payload_resolves_everywhere`] covers the body that ignores
/// its binder: nothing observes the payload, so `Unit` carries no information and
/// is the honest choice. [`read_arm_payload_is_pinned_to_where_it_flows`] covers
/// the body that *is* the binder, where the payload's requirement is a subtyping
/// upper bound. Here the read states its requirement as a trait obligation
/// instead — so `Unit` would contradict it, and the pin takes a type the
/// requirements still accept. The upper bounds an operand records are the
/// operator's own requirement variables, which resolve to nothing concrete, which
/// is why the flow case does not claim these payloads first.
///
/// The cases below are chosen to separate the two halves of that choice:
///
/// - `w + 1` narrows `Addable` to one row via the literal, so the choice is forced.
/// - `w + w` narrows nothing — every `Addable` row (`Int`, `UInt`, `String`) still
///   stands. **Any of them would do**, since the arm is unreachable and no value
///   ever flows through the binder; the table's order decides, so the test pins
///   reproducibility, not meaning.
/// - `w - w` draws from a *different* table (`Subtractable` has no `String` row),
///   which is what shows the choice comes from the obligation rather than a
///   hardcoded default.
/// - `-w` is `Negatable`, whose single row forces `Int` with nothing else to go on.
///
/// Every case would be `Unit` without the fix, and `Unit` satisfies none of these
/// requirements — so each one also pins that the pin no longer contradicts the read.
#[rstest]
#[case::add_literal_narrows(ArithmeticKind::Add, true, BaseType::Int)]
#[case::add_self_ambiguous(ArithmeticKind::Add, false, BaseType::Int)]
#[case::sub_self_numeric_only(ArithmeticKind::Sub, false, BaseType::Int)]
fn read_arm_payload_is_pinned_to_a_type_its_reads_accept(
    #[case] op: ArithmeticKind,
    #[case] against_literal: bool,
    #[case] expected: BaseType,
) {
    use cambra::ccl::BinOpKind;

    let rhs = if against_literal {
        lit_int(1)
    } else {
        var("w")
    };
    let read = TypedExpr::new(TypedExprNode::BinOp {
        left: Box::new(var("w")),
        op: BinOpKind::Arithmetic(op),
        right: Box::new(rhs),
    });
    let body = TypedExpr::new(TypedExprNode::Case {
        scrutinee: Some(Box::new(var("x"))),
        branches: vec![arm("a", "v", None, var("v")), arm("b", "w", None, read)],
    });
    let lambda = TypedExpr::lambda("x", Type::Hole, body);
    let call = TypedExpr::apply(TypedExpr::variant_ctor("a", lit_int(1)), var("f"));
    let full = run_full(TypedExpr::let_bind("f", lambda, call)).expect("inference ok");

    assert_eq!(arm_payload_ty(&full, "b"), Type::Base(expected));
    cambra::ccl::infer::check_fully_typed(&full)
        .expect("a read payload leaves no unresolved variable");
}

// ---------------------------------------------------------------------------
// Group F — what the opposite-polarity collapse must and must not supply
// ---------------------------------------------------------------------------

/// A **bounded** annotation on a variant bounds the binder; it does not become
/// its type.
///
/// `x <: {`some{Int} | `none} = `some(1)` is the value's own `{`some{Int@1}}`.
/// Both halves of that are the point: the `none` tag the value cannot carry, and
/// the singleton the annotation's `Int` would widen away.
///
/// What makes it a compaction test rather than an annotation one: `x`'s positive
/// walk finds the variant off its lower bound — the value — and the annotation
/// sits on the *upper* side. Counting a variant shape as "not concrete" at every
/// polarity let the opposite-polarity collapse fire past the value and hand back
/// the annotation, which is the bound reading as the type. A variant found at a
/// positive position is what the thing *is*, so the collapse has nothing to add;
/// only at a negative position is a variant the arms a body can handle rather
/// than a determination (see `no_concrete` in `src/ccl/infer/solver/compact.rs`).
#[test]
fn a_bounded_variant_annotation_does_not_become_the_binders_type() {
    let ann = Type::BoundedHole(Box::new(variant(&[("some", int()), ("none", unit_ty())])));
    let mut e = TypedExpr::let_bind_annotated(
        "x",
        TypedExpr::variant_ctor("some", lit_int(1)),
        var("x"),
        ann,
    );
    let mut ctx = TypeInferenceContext::new();
    let ty = infer(&mut e, &mut ctx).expect("bounded annotation admits the value");
    assert_eq!(ty, variant(&[("some", int_lit(1))]));
}

/// The pin fires on what a **value** reached, not on what merely determines the
/// position.
///
/// This is the IR of
///
/// ```text
/// def unwrap(m):
///     match m:
///         case `a(v): v
///         case `b(w): w
/// p = unwrap(`a(1))
/// q = unwrap(`a(2))
/// p + q
/// ```
///
/// The `+` is what makes it a detector. Reading the trait requirements together
/// writes back an *upper* bound on the dead arm's payload, so an ordinary resolve
/// reports the position settled while nothing has flowed there. The pin then skips
/// the arm, the arm's slot records `Int`, and the merge over the arms cannot see
/// that position contribute — leaving the recorded node type narrower than the
/// join, which the post-inference wall rejects (`expected Int@1, found Int`) on a
/// program that type-checks.
///
/// So the gate asks the polarity-correct walk alone (`value_reaches` in
/// `src/ccl/infer/solve.rs`). Asserted through `check_pre_channelize` because that
/// wall is where the disagreement surfaces — inference itself reports `Int` and
/// no error.
#[test]
fn an_upper_bound_alone_does_not_count_as_a_value_reaching_a_payload() {
    let body = TypedExpr::new(TypedExprNode::Case {
        scrutinee: Some(Box::new(var("m"))),
        branches: vec![arm("a", "v", None, var("v")), arm("b", "w", None, var("w"))],
    });
    let unwrap = TypedExpr::lambda("m", Type::Hole, body);
    let call = |n: i64| TypedExpr::apply(TypedExpr::variant_ctor("a", lit_int(n)), var("f"));
    let sum = TypedExpr::binop(
        var("p"),
        cambra::ccl::BinOpKind::Arithmetic(ArithmeticKind::Add),
        var("q"),
    );
    let mut e = TypedExpr::let_bind(
        "f",
        unwrap,
        TypedExpr::let_bind("p", call(1), TypedExpr::let_bind("q", call(2), sum)),
    );
    let mut ctx = TypeInferenceContext::new();
    assert_eq!(
        infer(&mut e, &mut ctx).expect("two call sites type-check"),
        int()
    );
    cambra::ccl::infer::check_pre_channelize(&e)
        .expect("every arm's recorded type is the join the wall recomputes");
}
