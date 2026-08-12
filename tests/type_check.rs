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
    FieldKey, HistoryKind, Lit, Type,
    infer::{
        InferError, LocatedInferError, TypeInferenceContext, check_pre_desugar, infer,
        lit_singleton,
    },
    lower::{LoweringContext, lower_stmts},
};
use cambra::chl_parser::{self, ast as chl_ast};
use cambra::interpreter::{BaseType, Extent, TestDataSource};
use indoc::indoc;
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

/// A control-flow join of two collections with **different** domains. The domain of
/// a data function *is* its data, so there is no domain both branches' rows fit in:
/// the contravariant meet the compute lattice would take drops whichever rows the
/// narrower domain lacks. The kind distinction is what turns that into a rejection
/// (`CoalesceError::DomainJoinConflict`) instead of a silently short collection.
/// `[1, 2]` is `[0, 1] ⤇ Int` and `[1, 2, 3]` is `[0, 2] ⤇ Int`, so this join has no
/// answer the lattice can express.
#[test]
fn test_conditional_collection_join_is_rejected() {
    let errs = infer_program_err("[1, 2] if True else [1, 2, 3]");
    let rendered = format!("{errs:?}");
    assert!(
        rendered.contains("collection domain conflict"),
        "expected the domain-join rejection, got:\n{rendered}"
    );
}

#[test]
fn test_conditional_collection_heterogeneous_domains_rejected() {
    // A conditional over a list literal and a **registered source** has two
    // unrelated domains (`[0, 2]` and `source(mysrc)`), so it rejects for the same
    // reason. This is the regression for the source-categorization invariant: a
    // registered source is a `Data` collection, and were it miscategorized as a
    // `Compute` capability the join would become an honest domain meet and
    // *succeed*, silently discarding one branch's rows. The rejection is the
    // evidence the kind is right (`register_source_type` constructs the `Data`
    // arrow; the kind is intrinsic, not caller-supplied).
    let errs =
        infer_program_with_sources_err("[1, 2, 3] if True else mysrc()", &[("mysrc", int())]);
    let rendered = format!("{errs:?}");
    assert!(
        rendered.contains("collection domain conflict"),
        "expected the domain-join rejection, got:\n{rendered}"
    );
}

#[test]
fn test_conditional_collection_same_domain_joins() {
    // The join *is* defined where it changes nothing: both arms over one domain
    // stay that collection. This is the arm that keeps the `Data` rule a rule about
    // losing data rather than a blanket ban on joining collections.
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
    // Regression that a capability supplied where a collection is demanded is a
    // clean error, not a
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
    assert_eq!(infer_program("def g(a: Int):\n    a\ng(1)"), int_lit(1));
    assert!(!infer_program_err("def g(a: Int):\n    a\ng(\"x\")").is_empty());
    // A `List(Int)` annotation enforces the element type through the annotation.
    assert_eq!(
        infer_program("def g(a: List(Int)):\n    sum(a)\ng([1, 2, 3])"),
        int()
    );
    assert!(!infer_program_err("def g(a: List(Int)):\n    sum(a)\ng([\"a\", \"b\"])").is_empty());
    // An unannotated param still infers purely from use.
    assert_eq!(infer_program("def g(a):\n    a\ng(\"x\")"), str_lit("x"));
}

#[test]
fn test_multiarg_def_param_annotation_enforced() {
    // Each tupled parameter's annotation is enforced independently.
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

// A group-by's key type is its key function's codomain, and the lowering says so
// **directly** rather than leaving it to be recovered through the partition
// predicate's `==`.
//
// `__gb_k`'s only occurrence in the lowered shape is as an operand of that
// comparison, so without a stated relation its type can only arrive backwards
// along the operand requirement that relates a comparison's two sides — making a
// group-by's key inference depend on an operator's internals. One
// `Type::SharedHole` states it, carried by the key application and by the domain of
// the group-by's own `data_fun` annotation; these cases pin that the key resolves
// to the key function's result type and not to the collection's element type.
//
// The relation is **not** visible in `test_lower_groupby`'s snapshots, because
// `symbolic` does not render annotations. These are the tests that cover it.
#[rstest]
#[case("groupby([1, 2, 3], \\x -> x)", int())]
#[case("groupby([(a=1, b=\"w\"), (a=2, b=\"e\")], \\r -> r.b)", string())]
fn test_groupby_key_type_comes_from_the_key_function(#[case] code: &str, #[case] key_ty: Type) {
    let ty = infer_program(code);
    let Type::Fun { domain, .. } = &ty else {
        panic!("a group-by is a function from key to partition, got {ty}");
    };
    assert_eq!(**domain, key_ty, "wrong key type for {code}");
}

/// The key type of the group-by in `code`'s result, which is expected to be a
/// tuple of two group-bys — one per instantiation / occurrence under test.
fn groupby_key_types(code: &str) -> (Type, Type) {
    let ty = infer_program(code);
    let Type::Tuple(parts) = &ty else {
        panic!("expected a pair of group-bys, got {ty}");
    };
    let key_of = |t: &Type| match t {
        Type::Fun { domain, .. } => (**domain).clone(),
        other => panic!("a group-by is a function from key to partition, got {other}"),
    };
    (key_of(&parts[0]), key_of(&parts[1]))
}

// A `SharedHole` id states an identity, and that identity is scoped to the one
// lowered construct that minted it. Sharing is the whole point of the marker, so
// over-sharing is its characteristic failure — and it has two shapes, one per
// case here. Both collapse the two key types into a single variable, so both
// surface the same way: not as a wrong key type but as an `Int | String`
// collision that rejects the program outright.
//
//   - **Across instantiations of one construct.** A `def` is lowered once, so
//     its body carries one id however many times it is called. What keeps the
//     instantiations apart is not the marker but ordinary generalization:
//     `normalize_annotation` resolves the id to an inference variable minted at
//     the current level, and from then on freshening treats it like any other
//     quantified variable. The `def` here is the case that would notice if it
//     did not — e.g. if the variable were minted at level 0 and so never
//     generalized (the level caveat on `InferCtx::shared_holes`).
//   - **Across distinct constructs.** The id → variable memo lives on the
//     inference context, so every group-by in a program shares one table; ids
//     minted per construct must stay distinct within a lowering.
#[rstest]
#[case::polymorphic_def(indoc! {r#"
    def by_key(c, f):
        groupby(c, f)
    ints = by_key([1, 2, 3], \x -> x)
    strs = by_key([(a=1, b="w"), (a=2, b="e")], \r -> r.b)
    (ints, strs)
"#})]
#[case::two_occurrences(indoc! {r#"
    ints = groupby([1, 2, 3], \x -> x)
    strs = groupby([(a=1, b="w"), (a=2, b="e")], \r -> r.b)
    (ints, strs)
"#})]
fn test_groupby_key_relation_is_per_occurrence(#[case] code: &str) {
    assert_eq!(groupby_key_types(code), (int(), string()), "for {code}");
}

// The tests above pin what a group-by's key type *resolves to*; this one pins
// that the key type is still **enforced** at a lookup. Stating the relation on
// the `data_fun` annotation makes the edge directional (`key_ty <: ⟨domain⟩` —
// contravariance), and a directional edge is exactly the kind that can go slack
// without any test noticing: every case above would still pass if a lookup at an
// unrelated key type were silently accepted.
//
// Asserted on the rendered message rather than the error *variant*: which check
// catches this is a property of how `==` is typed, not of the key relation, so
// pinning the variant would make the test fail on any change to that — it says
// only that the two types met and were refused.
#[test]
fn test_groupby_lookup_at_wrong_key_type_rejected() {
    let errs = infer_program_err(indoc! {r#"
        groups = groupby([(a=1, b="w"), (a=2, b="e")], \r -> r.b)
        groups(1)
    "#});
    assert!(
        errs.iter()
            .map(|e| format!("{e:?}"))
            .any(|msg| msg.contains("Int") && msg.contains("String")),
        "expected the Int key to be rejected against the String key type, got {errs:?}"
    );
}

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
/// A collection carries its filter as a refinement on its `Fun` *domain*, where
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

/// Arms whose domains differ, both refinements of the *same* source domain. Refinement
/// is not a special case: `{[0, 2] | x > 1}` and `{[0, 2] | x < 3}` are two distinct
/// domains, so this rejects exactly like two structurally unrelated domains. Meeting
/// them would claim one domain satisfying both filters; picking either would claim
/// positions the other branch does not produce.
#[test]
fn test_case_arms_with_different_filters_are_rejected() {
    let errs = infer_program_err(
        r"
xs = [1, 2, 3]
c = 1 > 0
if c:
    [x for x in xs if x > 1]
else:
    [x for x in xs if x < 3]
",
    );
    let rendered = format!("{errs:?}");
    assert!(
        rendered.contains("collection domain conflict"),
        "expected the domain-join rejection, got:\n{rendered}"
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

/// The domain-join rejection must not be reachable-around: a consumer downstream of
/// the join cannot make it succeed, whichever way the domains arrive at the domain
/// position. Directly, two arrow shapes meet there; through a `let` or a UDF
/// parameter, the two domains arrive as bounds on one position instead. Both routes
/// reject, and so does a consumer that *preserves* the domain (a comprehension) as
/// well as one that collapses it (`sum`).
#[test]
fn conditional_collection_rejects_under_every_consumer() {
    let c = "[1, 2] if True else [1, 2, 3]";
    for program in [
        // Collapsing consumer: directly, through a `let`, through a UDF parameter.
        format!("sum({c})"),
        format!(
            r"
x = {c}
sum(x)"
        ),
        format!(
            r"
def f(c):
    sum(c)
f({c})"
        ),
        // Domain-preserving consumer: the same three routes.
        format!("[y + 1 for y in {c}]"),
        format!(
            r"
x = {c}
[y + 1 for y in x]"
        ),
        format!(
            r"
def f(c):
    [y + 1 for y in c]
f({c})"
        ),
    ] {
        assert!(
            !infer_program_err(&program).is_empty(),
            "expected a rejection, not a silent miscompile: {program}"
        );
    }
}
