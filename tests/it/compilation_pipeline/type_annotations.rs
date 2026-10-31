use std::collections::HashMap;
use std::rc::Rc;

use bit_set::BitSet;
use indoc::indoc;
use rstest::rstest;

use super::helpers::{check_compile_error, check_scalar, check_tile, make_int_list};

use cambra::ccl::infer::{TypeInferenceContext, infer, typecheck};
use cambra::ccl::lower::{LoweringContext, lower_stmts};
use cambra::ccl::{
    ArithmeticKind, BinOpKind, Builtin, CompareKind, Expr, FunKind, Lit, LogicKind, Name,
    Refinement, Type, anf, comprehension, mut_read, opaque_output, uniquify,
};
use cambra::chl_parser::{self, FileId};
use cambra::interpreter::{BaseType, ColumnValue, Predicate, Tile, Value};

#[test]
fn refinement() {
    check_compile_error(
        include_str!("type_annotations/refined_div_zero.cambra"),
        "expected {Int | __elem != 0}",
    );
    // The demanded predicate reads a field of the record it refines, and the
    // argument's own type pins that field to `0`, so the rejection is a
    // refutation rather than a comparison nothing decided.
    check_compile_error(
        include_str!("type_annotations/complex_refinement.cambra"),
        "expected {{x: Int, y: Int} | __elem.y != 0}, found {x: Int@1, y: Int@0}",
    );
    check_compile_error(
        include_str!("type_annotations/underscore.cambra"),
        "`_` binds nothing, so it reads no value",
    )
}

#[test]
fn output_annotation_base() {
    check_scalar(
        "
def foo(a: Int, b: Int) => Int:
    a + b

x = (4,-1)

foo(x)
",
        Value::Int(3),
    )
}

#[test]
fn output_annotation_base_neg() {
    check_compile_error(
        "
def itsa_five(a) => String:
    5

itsa_five(\"dummy_arg\")
",
        "Annotation mismatch: annotated as String, but inferred as {Int where _ == 5}",
    )
}

#[test]
fn output_annotation_singleton_matches_the_literal() {
    check_scalar(
        "
def itsa_nine(a) => {Int where _ == 9}:
    9

itsa_nine(\"dummy_arg\")
",
        Value::Int(9),
    )
}

#[test]
fn output_annotation_singleton_rejects_another_literal() {
    check_compile_error(
        "
def itsa_nine(a) => {Int where _ == 9}:
    8

itsa_nine(\"dummy_arg\")
",
        "Annotation mismatch: annotated as {Int where _ == 9}, but inferred as {Int where _ == 8}",
    )
}

#[test]
fn function_type_annotation() {
    // A binding annotated with a function type `(Int => Int)` checks against the
    // lambda it binds (a lambda is a compute function, the kind `=>` denotes).
    check_scalar(
        "
f: (Int => Int) = \\x -> x + 1
f(4)
",
        Value::Int(5),
    )
}

#[test]
fn function_type_annotation_refined_codomain() {
    // A refinement nested in the codomain is a `Bool` predicate over `_`, typed
    // through `Type::Fun` like any other annotation refinement. The body `9` is
    // `Int@9`, which discharges `{Int where _ == 9}`.
    check_scalar(
        "
f: (Int => {Int where _ == 9}) = \\x -> 9
f(4)
",
        Value::Int(9),
    )
}

#[test]
fn function_type_annotation_refined_codomain_neg() {
    // The codomain refinement is enforced: a body of `8` does not satisfy
    // `{Int where _ == 9}`.
    check_compile_error(
        "
f: (Int => {Int where _ == 9}) = \\x -> 8
f(4)
",
        "Annotation mismatch",
    )
}

/// `->` in type position builds a tuple, and the report names both spellings.
///
/// Nothing below the parser tells `Int -> Int` from `(Int, Int)` (`docs/chl-spec.md`,
/// "2.4 Atoms"), so a function type written with the pair arrow arrives at lowering as a
/// term product, and the message has to name the tuple type and the function type both.
#[test]
fn a_pair_arrow_in_type_position_names_both_spellings() {
    check_compile_error(
        indoc! {r#"
            f: (Int -> Int) = \x -> x + 1
            f(4)
        "#},
        "a function type with `=>`",
    )
}

/// A `def`'s return annotation takes `=>`, and `->` there never reaches the message above.
///
/// `def_stmt` wants the arrow, a `requires` clause, or the `:` after the parameter list, so
/// the commonest miswriting of a function type is a parse error in the statement grammar
/// rather than a lowering report about the annotation.
#[test]
fn a_pair_arrow_in_a_def_return_annotation_is_a_parse_error() {
    check_compile_error(
        indoc! {r#"
            def f(x: Int) -> Int:
                x + 1

            f(4)
        "#},
        "found '->', expected 'requires', '=>', or ':'",
    )
}

#[test]
fn function_type_in_value_position_is_rejected() {
    // `T => U` names a type; it is annotation-only, not a value.
    check_compile_error(
        "
x = Int => Int
x
",
        "is a function *type*",
    )
}

// This test fails because the output of _ + _ is currently unrefined.
// Once that is fixed, it should fail for the different reason that
// the argument b is not >= 0.
#[test]
fn output_annotation_naming_a_parameter_not_entailed() {
    check_compile_error(
        "
def sum_up(a: Int, b: {Int where _ >= 0}) => {Int where _ >= a}:
    a + b

x = (3,-1)

sum_up(x)
",
        "Annotation mismatch: annotated as {Int where _ >= ‹__arg_tuple_0›.0}, but inferred as Int",
    )
}

// The refinement body in the output type of `test` should be well
// typed, refering only to `x` which is in its scope.
//
// Currently the test still fails afterward, since `x + 1` does not
// get refined.
#[test]
fn pi_type_scope() {
    check_compile_error(
        "
def test(x: Int) => {Int where _ > x}:
    x + 1

()
",
        "Annotation mismatch: annotated as {Int where _ > x}, but inferred as Int",
    )
}

// The refinement body in the output type of `test` should fail to
// type, since it refers to `y` which is unbound.
#[test]
fn type_scope_neg() {
    check_compile_error(
        "
def test(x: Int) => {Int where _ > y}:
    x + 1

()
",
        "Unbound variable: 'y'",
    )
}

// The refinement body in the output type of `test` should be well
// typed, refering to `x` which is in its scope from the input
// argument, and to `y` which is in the outer scope. The body of `x`'s
// refinement can also refer to `y`.
//
// Currently the test still fails afterward, since `x + 3` does not
// get refined.
#[test]
fn type_scope_outer() {
    check_compile_error(
        "
y = 3

def test(x: {{Int where _ != y + y} where _ != y}) => {Int where _ > y + x}:
    x + 3

()
",
        "Annotation mismatch: annotated as {Int where _ > y + x}, but inferred as Int",
    )
}

#[test]
fn type_refined_input_only_true() {
    check_scalar(
        "
def f(x: {Int where True}) => Int:
    x
()
",
        Value::Unit,
    )
}

#[test]
fn type_refined_input_only_self_comparison() {
    check_scalar(
        "
def f(x: {Int where _ >= _}) => Int:
    x
()
",
        Value::Unit,
    )
}

#[test]
fn type_refined_input_only_self_equality_after_a_parameter() {
    check_scalar(
        "
def f(y: Int, x: {Int where _ == _}):
    x
()
",
        Value::Unit,
    )
}

#[test]
fn type_refined_input_only_self_equality() {
    check_scalar(
        "
def f(x: {Int where _ == _}):
    x
()
",
        Value::Unit,
    )
}

// This should succeed eventually, but fails for now since refinements
// are only compared by equality.
#[test]
fn type_refined_input_output() {
    check_compile_error(
        "
def f(x: {Int where _ == _}) => {Int where _ == x}:
    x
()
",
        "Annotation mismatch: annotated as {Int where _ == x}, but inferred as {Int where _ == _}",
    )
}

// This should succeed eventually, but fails for now since refinements
// are only compared by equality.
#[test]
fn type_refined_output() {
    check_compile_error(
        "
def f(x: Int) => {Int where _ == x}:
    x
()
",
        "Annotation mismatch: annotated as {Int where _ == x}, but inferred as Int",
    )
}

// The refinement body for `x` should fail to typecheck, since it
// should not be able to refer to itself by `x`, only by `_`.
#[test]
fn type_scope_self() {
    check_compile_error(
        "
def test(x: {Int where x >= 1}) => Int:
    x + 1

()
",
        "Unbound variable: 'x'",
    )
}

// The refinement body for `x` should fail to typecheck, since the `x`
// inside is refering to the outer scope `x`, which is a `String`.
#[test]
fn type_scope_outer_shadow() {
    check_compile_error(
        "
x = \"Hello\"

def test(x: {Int where _ >= x}) => Int:
    x + 1

()
",
        "No Orderable instance for BinOp: operand 2 is String",
    )
}

#[test]
fn type_binop_mismatch() {
    check_compile_error(
        "
def test(a: String, b: Int):
    a + b

()
",
        "No Addable instance for BinOp: operand 2 is Int, but the only type accepted there is String",
    )
}

/// A parameter's annotation is read in the scope enclosing the binder, so a
/// reference to a parameter resolves outward and not to the parameter. With
/// nothing outside to resolve to it is an ordinary unbound variable, at every
/// shape a parameter list takes: tupled siblings in either order, and the
/// single parameter that can only be naming itself.
///
/// Nothing rejects these earlier. Lowering carries no scope to tell a reference
/// to the parameter apart from one to an enclosing binder of the same name, and
/// a name-based rejection there reports the wrong cause for the shadowing case
/// (`type_scope_outer_shadow`).
#[rstest]
#[case::sibling("def f(a: Int, c: {Int where _ >= a}):\n    c\n\nf\n", "a")]
#[case::sibling_reversed("def f(c: {Int where _ >= a}, a: Int):\n    c\n\nf\n", "a")]
#[case::sibling_of_three("def f(a: Int, b: Int, c: {Int where _ >= b}):\n    c\n\nf\n", "b")]
#[case::own_binder("def f(a: {Int where _ >= a}):\n    a\n\nf\n", "a")]
fn type_annotation_naming_a_parameter_is_unbound(#[case] code: &str, #[case] name: &str) {
    check_compile_error(code, &format!("Unbound variable: '{name}'"));
}

#[test]
fn refined_add() {
    check_scalar("z: {Int where _ == 1 ^+ 3} = 1 ^+ 3\n()", Value::Unit)
}

// ---------------------------------------------------------------------------
// Semantic entailment of a refinement
//
// Every case below leaves a structural deficit, so the verdict comes from the
// semantic fallback (`src/ccl/design/type-inference.md`, "Semantic entailment as
// a fallback"): the annotation's predicate and the body's are unequal terms, and
// what decides the subtyping is whether the second entails the first.
// ---------------------------------------------------------------------------

/// A chain of `let`s whose definitions are substituted into the body's
/// refinement: `y` is `1 ^+ 3 ^+ 2`, which entails `_ == 1 ^+ 5` without matching
/// it.
#[test]
fn a_let_chain_entails_the_result_annotation() {
    check_scalar(
        indoc! {r#"
            def foo(t: Int) => {Int where _ == 1 ^+ 5}:
                x = 1 ^+ 3
                y = x ^+ 2
                y
            ()
        "#},
        Value::Unit,
    )
}

/// A `let` whose definition names the parameter. The substitution puts the
/// parameter into the result refinement, where the function type binds it.
#[test]
fn a_let_definition_naming_the_parameter_composes() {
    check_scalar(
        indoc! {r#"
            def foo(t: Int):
                x = t ^+ 3
                x ^+ 2
            foo(1)
        "#},
        Value::Int(6),
    )
}

/// The same sum written without the `let`: no substitution runs, and the
/// refinement is the one the `let` form has to arrive at.
#[test]
fn a_nested_sum_with_no_let_refines_the_same_way() {
    check_scalar(
        indoc! {r#"
            def foo(t: Int):
                (t ^+ 3) ^+ 2
            foo(1)
        "#},
        Value::Int(6),
    )
}

/// A parameter refinement the argument entails semantically but not structurally:
/// `1 ^+ 3 ^+ 2` and `1 ^+ 5` are unequal terms denoting one value. Inference accepts
/// the call through `smt_sub`, and `inline`'s beta-reduction discharges the same
/// precondition the same way (see `src/ccl/design/type-inference.md`, "Semantic
/// entailment as a fallback").
#[test]
fn refined_arg_entailed_only_semantically() {
    check_scalar(
        indoc! {r#"
            def foo(t: {Int where _ == 1 ^+ 5}):
                t
            foo((1 ^+ 3) ^+ 2)
        "#},
        Value::Int(6),
    )
}

/// A `let` the body returns unchanged. Its refinement names nothing, so the
/// result type is closed before the substitution runs at all.
#[test]
fn a_let_bound_constant_returned_directly() {
    check_scalar(
        indoc! {r#"
            def foo(t: Int):
                x = 1 ^+ 3
                x
            foo(1)
        "#},
        Value::Int(4),
    )
}

/// A demand at one parameter of two, entailed by the argument without matching it:
/// `Int@2` against `{Int | __elem != 0}`. Inference admits the call through
/// `smt_sub`, and `inline`'s beta-reduction substitutes the argument for the binder,
/// so the refined parameter is gone before planning's post-pass check runs. That
/// check still compares structurally; `post_planning_smt` pins a refinement that
/// survives to it. The rejecting counterpart is `tests/programs/refinement/`.
#[test]
fn a_refined_divisor_entailed_by_the_argument() {
    check_scalar(
        indoc! {r#"
            def no_zero_no_one_div(left: Int, right: {Int where _ != 0}):
                left // right

            no_zero_no_one_div(4, 2)
        "#},
        Value::Int(2),
    )
}

/// A `let` bound to a call carries no refinement to compose with: `//` records no
/// sum, so `x` is a bare `Int` and `x ^+ 2` refines over it rather than over a
/// term naming `t`.
#[test]
fn a_let_bound_call_result_carries_no_refinement() {
    check_scalar(
        indoc! {r#"
            def bar(i: Int):
                i // 2

            def foo(t: Int):
                x = bar(t)
                x ^+ 2
            foo(2)
        "#},
        Value::Int(3),
    )
}

// ---------------------------------------------------------------------------
// What a query may assume about a name in scope
//
// `src/ccl/design/type-inference.md`, "The scope a query runs in".
// ---------------------------------------------------------------------------

/// A transparent binder is assumed equal to its definition. `y`'s type is `Int`, since
/// `+` puts no refinement on its result, so `w`'s refinement `__elem == y ^+ 0` meets the
/// annotation only through `y == x + 1`. The checks after lambda elimination read the
/// definition `(x, 1) ▷ add` in its normal form and assume the same fact.
#[test]
fn a_binder_is_assumed_equal_to_its_definition() {
    check_scalar(
        indoc! {r#"
            x: Int = 4
            y = x + 1
            w = y ^+ 0
            z: {Int where _ == x + 1} = w
            z
        "#},
        Value::Int(5),
    )
}

/// `t ^+ x == t + 2` follows only from `x == 2`, which is the refinement on the
/// type the top-level binder holds. The literal puts that singleton on the node,
/// so the scope answers without resolving anything.
#[test]
fn a_top_level_binder_is_assumed_at_its_own_type() {
    check_scalar(
        indoc! {r#"
            x = 2

            def foo(t: Int) => {Int where _ == t + 2}:
                t ^+ x

            foo(2)
        "#},
        Value::Int(4),
    )
}

/// The same, with the binder's singleton on its inference variable's bounds
/// rather than on the node. Unresolved it has no SMT sort, so the scope resolves
/// the scheme body before reading it as a fact.
#[test]
fn a_top_level_binder_whose_singleton_needs_resolving() {
    check_scalar(
        indoc! {r#"
            x = 2 ^+ 1

            def foo(t: Int) => {Int where _ == t + 3}:
                t ^+ x

            foo(2)
        "#},
        Value::Int(5),
    )
}

/// Assumptions chain: `y` is declared, `x` is met inside `y`'s own predicate, and
/// `x`'s refinement joins the antecedent in turn.
#[test]
fn assumptions_chain_through_a_binders_own_refinement() {
    check_scalar(
        indoc! {r#"
            x = 2

            y = x ^+ 1

            def foo(t: Int) => {Int where _ == t + 3}:
                t ^+ y

            foo(2)
        "#},
        Value::Int(5),
    )
}

/// TODO(refinement-through-a-call): a call in the body leaves the result
/// unrefined. `bar(t)` types as an `Apply`, which carries no predicate relating
/// its result to its argument, so the body's refinement quotes the call term
/// itself — `t ▷ bar` — which is outside the encoded fragment and decides
/// nothing. Inlining `bar` first would make the annotation hold.
#[test]
fn a_call_in_the_body_leaves_the_result_unrefined() {
    check_compile_error(
        indoc! {r#"
            x = 2

            y = x ^+ 1

            def bar(x: Int):
                y ^+ x ^+ x

            def foo(t: Int) => {Int where _ == t + 3 + t + 5}:
                t ^+ y ^+ bar(t)

            foo(2)
        "#},
        "inferred as {Int where _ == t ^+ y ^+ bar(t)}",
    )
}

// ---------------------------------------------------------------------------
// Aggregates carry no refinement
//
// TODO(refined-aggregate): `max` over a filtered comprehension types as a bare
// `Int`. A refinement-propagating aggregate would carry the comprehension's own
// domain filter into the result; each case below says what it would then decide.
// ---------------------------------------------------------------------------

/// The filter is on a record field, so the bound the aggregate would carry comes
/// from the projected domain rather than from the elements.
#[test]
fn an_aggregate_over_a_record_collection_carries_no_refinement() {
    check_compile_error(
        indoc! {r#"
            def f(u: Int) => {Int where _ <= 15}:
                products = [
                    (name="foo", quant=10),
                    (name="bar", quant=20),
                ]
                max([p.quant for p in products if p.quant <= 15])

            f(0)
        "#},
        "but inferred as Int",
    )
}

/// `_ <= 15` restates the comprehension's own filter, so the weakest
/// refinement-propagating `max` accepts it. This case flips on that fix.
#[test]
fn an_aggregate_bound_following_from_the_filter_alone() {
    check_compile_error(
        indoc! {r#"
            def f(u: Int) => {Int where _ <= 15}:
                products = [ 10, 20 ]
                max([p for p in products if p <= 15])

            f(0)
        "#},
        "Annotation mismatch: annotated as {Int where _ <= 15}, but inferred as Int",
    )
}

/// `_ <= 10` is true of this collection — `max` is `10` — but it does not follow
/// from the filter, which permits `15`. Deciding it needs the elements' own
/// singletons, so this case stays rejected under the fix above and flips only
/// under a stronger one.
#[test]
fn an_aggregate_bound_needing_the_elements() {
    check_compile_error(
        indoc! {r#"
            def f(u: Int) => {Int where _ <= 10}:
                products = [ 10, 20 ]
                max([p for p in products if p <= 15])

            f(0)
        "#},
        "Annotation mismatch: annotated as {Int where _ <= 10}, but inferred as Int",
    )
}

/// `_ <= 5` is false — `max` is `10` — so this case stays rejected under every
/// aggregate rule, and is what tells the two above apart from a fix that simply
/// stopped checking.
#[test]
fn an_aggregate_bound_the_elements_refute() {
    check_compile_error(
        indoc! {r#"
            def f(u: Int) => {Int where _ <= 5}:
                products = [ 10, 20 ]
                max([p for p in products if p <= 15])

            f(0)
        "#},
        "Annotation mismatch: annotated as {Int where _ <= 5}, but inferred as Int",
    )
}

// ---------------------------------------------------------------------------
// Products are reached through their fields
//
// `src/ccl/design/type-inference.md`, "A product is reached through its fields".
// ---------------------------------------------------------------------------

/// A record has no SMT sort, so `x.b` is the leaf a constant is minted for, and
/// `x.b == 3` is what the entailment runs on.
#[test]
fn a_field_read_of_a_top_level_record_is_assumed() {
    check_scalar(
        indoc! {r#"
            x = ( a = 10, b = 2 ^+ 1 )

            def foo(t: Int) => {Int where _ == t + 3}:
                t ^+ x.b

            foo(2)
        "#},
        Value::Int(5),
    )
}

/// Two roots read through: the parameter, whose field the annotation names, and
/// the top-level record, whose field the scope supplies a refinement for.
#[test]
fn a_field_read_of_the_parameter_and_of_a_record_in_scope() {
    check_scalar(
        indoc! {r#"
            x = ( a = 10, b = 2 ^+ 1 )

            def foo(t: {a:Int, b:Int}) => {Int where _ == t.a + 3}:
                t.a ^+ x.b

            foo((a=2, b=3))
        "#},
        Value::Int(5),
    )
}

/// A record equality in the *body* is accepted, and the refinement above it is what
/// the program then fails: `Equatable` reads a product componentwise
/// (`tests/it/type_check.rs`, `products_are_equatable_componentwise`), so `t == t` is an
/// ordinary `Bool`, and a `Bool` carries no singleton for `Bool@true` to match.
///
/// A refinement is discharged by matching the predicate rather than by proving it, so
/// the body being true at every argument does not reach the question.
#[test]
fn a_record_equality_leaves_a_singleton_annotation_undischarged() {
    check_compile_error(
        indoc! {r#"
            def foo(t: {a:Int, b:Int}) => {Bool where _ == True}:
                t == t

            foo((a=2, b=3))
        "#},
        "Annotation mismatch: annotated as {Bool where _ == True}, but inferred as Bool",
    )
}

/// The same reading from inside a refinement *predicate*, where a record equality is the
/// natural way to write "this value". The predicate typechecks, and what remains is the
/// discharge: the body is the parameter itself, which carries no refinement to match
/// `__elem == t` against.
#[test]
fn a_record_equality_in_a_refinement_predicate_is_not_discharged() {
    check_compile_error(
        indoc! {r#"
            def foo(t: {a:Int, b:Int}) => {{a:Int, b:Int} where _ == t}:
                t

            foo((a=1, b=2)).a
        "#},
        "Annotation mismatch: annotated as {{a: Int, b: Int} where _ == t}, but inferred as {a: Int, b: Int}",
    )
}

/// A refinement in a `Map` key type that no key satisfies, reported by the plain annotation and
/// by the `Mut` form.
///
/// Neither program is well-typed today: a literal key carries `__elem == "a"`, and a
/// refinement is discharged by matching the predicate rather than by proving it, so
/// `__elem != ""` is not satisfied. The plain annotation is an `Annotation mismatch`
/// against the whole `Σ`, which names the annotation the program wrote. The mutable one
/// boxes the map, so the key domain is a candidate of the box's binder, and the report is
/// that candidate's membership in the annotated kind, decided where the position
/// materializes.
#[test]
fn a_refined_map_key_no_key_satisfies() {
    check_compile_error(
        r#"
m: Map({String where _ != ""}, Int) = map([("a", 1), ("z", 2)])
m
"#,
        r#"Annotation mismatch: annotated as Map({String where _ != ""}, Int), but inferred as {String where _ in ["a", "z"]} |=> Int"#,
    )
}

#[test]
fn a_refined_map_key_in_a_mut_annotation_is_reported() {
    check_compile_error(
        r#"
m: Mut(Map({String where _ != ""}, Int)) := box(map([("a", 1), ("z", 2)]))
m
"#,
        r#"Type mismatch for collection annotation: expected Σ (σ : SubtypesOf({String | __elem != ""})). (σ ⤇ _), found {String | __elem ▷ (([("a", 1), ("z", 2)] ≫ (λ __map_kv : (String, Int) → __map_kv.0)) ▷ collection_contains)}"#,
    )
}

/// This and the following two tests exclude a bug in which captured
/// input expressions that are later used to create a trait instance
/// refinement are stale at that point. Bug was fixed by freshening
/// the inputs before creating the refinement.
#[test]
fn freshen_refined_add_double_arg_and_global() {
    check_scalar(
        indoc! {r#"
g = 10
def f(p,q):
    p ^+ q ^+ g
f(1,2)
        "#},
        Value::Int(13),
    )
}

#[test]
fn freshen_refined_add_double_arg() {
    check_scalar(
        indoc! {r#"
def f(p,q):
    p ^+ q
f(1,2)
        "#},
        Value::Int(3),
    )
}

#[test]
fn freshen_refined_add_single_arg() {
    check_scalar(
        indoc! {r#"
def f(p):
    p ^+ p
f(1)
        "#},
        Value::Int(2),
    )
}

/// Test the UInt trait instance of ^+. Currently pins the fact that a
/// numeric literal can only be inferred as an Int.
#[test]
fn refined_add_uint_row() {
    check_compile_error(
        indoc! {r#"
def f(p) => {UInt where _ == p ^+ p}:
    p ^+ p
f(1)
        "#},
        "Type mismatch for Apply: expected UInt, found Int",
    )
}

/// Type error messages show the original code the user wrote, despite
/// the pre-inference ANF phase.
#[test]
fn complex_anf() {
    check_compile_error(
        indoc! {r#"
1 + 2 + "Hello" + 4 + 5
        "#},
        "1 + 2 + \"Hello\" + 4 + 5",
    )
}

/// The same error in a chain holding a mutable variable's read, which A-normalization flattens
/// onto the statement spine. The message is built from a partly typed tree, and respelling the
/// chain's temps there keeps every occurrence it replaces typed.
#[test]
fn a_type_error_in_a_chain_holding_a_read() {
    check_compile_error(
        indoc! {r#"
            x := 1
            y = x + "a" + 2 + 3
            y
        "#},
        "No Addable instance for BinOp: operand 2 is String",
    )
}

/// TODO: The typecheck for uses of polymorphic functions occurs
/// during Coalesce, in which SMT is not currently used. In this
/// example, structural equality comparison cannot reconcile the
/// semantically equivalent refinements {_ == 4 ^+ 1} and {_ == a}.
#[test]
fn monomorphization_check_is_not_smt() {
    check_compile_error(
        indoc! {r#"
def f(x: Int):
    4 ^+ 1
a = f(1)
b: {Int where _ == a} = f(2)
a == b
        "#},
        "Type mismatch for monomorphization specialization",
    )
}

/// It is unsound to consider the `r` from `f(1)` and the `r` from
/// `f(2)` to be the same value, and so `r` is not present in the
/// external output type inferred for `f`: the refinement naming it is
/// dropped at the lambda boundary and `f` reports `Int`
/// (`src/ccl/design/type-inference.md`, "A lambda's codomain drops the body's
/// opaque binders").
///
/// `b`'s annotation then demands `{Int | __elem == a}` of a value known
/// only to be an `Int`, which nothing establishes.
#[test]
fn dont_discharge_opaques_out_of_fun_bodies_with_an_unannotated_codomain() {
    check_compile_error(
        indoc! {r#"
def f(x: Int):
    r ^= x;
    r ^+ 0
a = f(1)
b: {Int where _ == a} = f(2)
a == b
        "#},
        "Annotation mismatch: annotated as {Int where _ == a}, but inferred as Int",
    )
}

/// A `_` output annotation leaves the codomain to inference, so it is not
/// concrete and `f`'s result still passes through a barrier variable that drops
/// the refinement naming `r`, as in
/// `dont_discharge_opaques_out_of_fun_bodies_with_an_unannotated_codomain`.
#[test]
fn dont_discharge_opaques_out_of_fun_bodies_with_a_hole_codomain() {
    check_compile_error(
        indoc! {r#"
def f(x: Int) => _:
    r ^= x;
    r ^+ 0
a = f(1)
b: {Int where _ == a} = f(2)
a == b
        "#},
        "Annotation mismatch: annotated as {Int where _ == a}, but inferred as Int",
    )
}

#[test]
fn dont_discharge_opaques_out_of_fun_bodies_with_an_unrefined_codomain() {
    check_compile_error(
        indoc! {r#"
def f(x: Int) => Int:
    r ^= x;
    r ^+ 0
a = f(1)
b: {Int where _ == a} = f(2)
a == b
        "#},
        "Annotation mismatch: annotated as {Int where _ == a}, but inferred as Int",
    )
}

#[test]
fn dont_discharge_opaques_out_of_fun_bodies_rejects_an_argument_outside_the_refined_domain() {
    check_compile_error(
        indoc! {r#"
def f(x: {Int where _ == 2}) => {Int where _ == 2}:
    r ^= x;
    r ^+ 0
a = f(1)
b: {Int where _ == a} = f(2)
a == b
        "#},
        "Type mismatch for Apply: expected Int@2, found Int@1",
    )
}

/// TODO: this should be typecheckable, but `a`'s refinement isn't
/// being used.
#[test]
fn dont_discharge_opaques_out_of_fun_bodies_with_a_singleton_codomain_named_by_an_annotation() {
    check_compile_error(
        indoc! {r#"
def f(x: {Int where _ == 2}) => {Int where _ == 2}:
    r ^= x;
    r ^+ 0
a = f(2)
b: {Int where _ == a} = f(2)
a == b
        "#},
        "Type mismatch for monomorphization specialization: expected {Int | __elem == a}, found Int@2",
    )
}

#[test]
fn dont_discharge_opaques_out_of_fun_bodies_without_annotations_compares_at_runtime() {
    check_scalar(
        indoc! {r#"
def f(x):
    r ^= x;
    r ^+ 0
a = f(1)
b = f(2)
a == b
        "#},
        Value::Bool(false),
    )
}

#[test]
fn dont_discharge_opaques_out_of_fun_bodies_with_a_singleton_codomain_meets_a_literal_annotation() {
    check_scalar(
        indoc! {r#"
def f(x: {Int where _ == 2}) => {Int where _ == 2}:
    r ^= x;
    r ^+ 0
a = f(2)
b: {Int where _ == 2} = f(2)
a == b
        "#},
        Value::Bool(true),
    )
}

/// An annotated `let` at the head of a body annotates only its definiens, so the
/// opaque `r` bound after it is still dropped from `f`'s codomain and `f` reports
/// `Int`.
#[test]
fn dont_discharge_opaques_out_of_fun_bodies_after_an_annotated_let() {
    check_compile_error(
        indoc! {r#"
def f(x: Int):
    y: Int = x
    r ^= y
    r ^+ 0
a = f(1)
b: {Int where _ == a} = f(1)
a == b
        "#},
        "Annotation mismatch: annotated as {Int where _ == a}, but inferred as Int",
    )
}

/// `f`'s codomain barrier variable is minted under `g`'s generalized body and reaches
/// the lower-level variable `h` inside `f`'s function type.
#[test]
fn barrier_var_returned_from_a_nested_def() {
    check_scalar(
        indoc! {r#"
def g(z):
    def f(x):
        r ^= x
        r ^+ z
    f
h = g(1)
h(2)
        "#},
        Value::Int(3),
    )
}

/// `barrier_var_returned_from_a_nested_def` with the nested `f` passed to `g`'s
/// parameter rather than returned.
#[test]
fn barrier_var_passed_to_a_parameter() {
    check_scalar(
        indoc! {r#"
def k(f):
    f(1)
def g(h):
    def f(x):
        r ^= x
        r ^+ 0
    h(f)
g(k)
        "#},
        Value::Int(1),
    )
}

/// `k`'s domain refinement names the opaque variable `r`, so `f`'s
/// barrier var is refused, as in
/// `return_opaque_annotated_function_from_unannotated_function`.
#[test]
fn complex_refined_program_post_inline_failure() {
    check_compile_error(
        indoc! {r#"
def f(x):
    r ^= x;
    def k(y: {Int where _ == r}):
        y
    k
g = f(1)
def p(w: {Int where _ > 5}):
    w
def h(z):
    g(z) + p(z)
h(7)
        "#},
        "this function's result type ({Int | __elem == r} ⇒ Int) refines a parameter by `r`",
    )
}

/// It is unsound to consider the `r` from `f(1)` and the `r` from
/// `f(2)` to be the same value, and so `r` should not be present in
/// the external output type inferred for `f`.
///
/// This version rejects the `r` in the output type annotation as
/// unbound.
#[test]
fn opaque_vars_in_fun_body_are_unbound_in_annotation() {
    check_compile_error(
        indoc! {r#"
def f(x: Int) => { Int where _ == r }:
    r ^= x;
    r ^+ 0
a = f(1)
b: {Int where _ == a} = f(2)
a == b
        "#},
        "Unbound variable: 'r'",
    )
}

/// Reading a mutable variable introduces an opaque binder inside the body, so the
/// body's type reaches the codomain through a barrier variable; the refinement it drops
/// names the parameter as well as that binder
/// (`src/ccl/design/type-inference.md`, "A lambda's codomain drops the body's
/// opaque binders").
#[test]
fn safe_to_read_captured_mut_inside_function() {
    check_scalar(
        indoc! {r#"
x: Mut({Int where _ >= 0}) := 0
def g(a: Int):
    x ^+ a
g(1)
        "#},
        Value::Int(1),
    )
}

/// A comprehension element reading a mutable variable.
#[test]
fn reading_mut_in_comprehension() {
    check_tile(
        indoc! {r#"
x := 3
ys = [x ^+ i for i in [1,2]]
ys
        "#},
        make_int_list(&[4, 5]),
    )
}

/// TODO: Post-planning typechecks are still limited to structural
/// equality, and thus fail for refinements that survive to
/// post-planning. This is currently blocked by the lack of SMT
/// encoding rules for point-free expressions.
#[test]
fn post_planning_smt() {
    check_compile_error(
        indoc! {r#"
x: Mut({Int where _ >= 0}) := 0
y = x ^+ x
z: {Int where _ >= 0} = y
z        "#},
        "post-planning produced an invalid tree",
    )
}

/// A filter and a nested comprehension around an element that reads a mutable
/// variable. The conditional-element case is
/// `a_conditional_element_reading_an_enclosing_binder` in
/// `tests/it/compilation_pipeline/conditionals.rs`.
#[rstest]
#[case::filtered(
    indoc! {r#"
x := 3
ys = [x ^+ i for i in [1,2,3] if i > 1]
ys
    "#},
    Tile::data_function(
        ColumnValue::UInts(vec![1, 2]),
        Box::new(Tile::Scalar(ColumnValue::Ints(vec![5, 6]))),
        Predicate::True,
        BitSet::new(),
    ),
)]
#[case::nested(
    indoc! {r#"
x := 3
ys = [[x ^+ j for j in [1,2]] for i in [1,2] if i > 1]
ys
    "#},
    Tile::data_function(
        ColumnValue::UInts(vec![1]),
        Box::new(Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![4, 5]))),
            Predicate::False,
            BitSet::new(),
        )),
        Predicate::True,
        BitSet::new(),
    ),
)]
fn a_comprehension_that_reads_a_mut(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected)
}

/// A filter over a mutable source. The comprehension phase copies the source
/// into the cast's predicate after `mut_read` has rewritten the read of `xs`,
/// so both copies carry the rewrite and no mutable variable reaches the
/// predicate.
#[test]
fn filtering_a_comprehension_over_a_mut_source() {
    check_tile(
        indoc! {r#"
xs := [1,2,3]
ys = [i for i in xs if i > 1]
ys
        "#},
        Tile::data_function(
            ColumnValue::UInts(vec![1, 2]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3]))),
            Predicate::True,
            BitSet::new(),
        ),
    )
}

/// A filtered two-generator comprehension whose element reads a mutable
/// variable and whose guard does not.
#[test]
fn filtering_a_two_generator_comprehension_that_reads_a_mut() {
    check_tile(
        indoc! {r#"
x := 3
ys = [x ^+ i + j for i in [1,2] for j in [5,6] if i < j]
ys
        "#},
        Tile::data_function(
            ColumnValue::Records(HashMap::from([
                ("_0".into(), ColumnValue::UInts(vec![0, 0, 1, 1])),
                ("_1".into(), ColumnValue::UInts(vec![0, 1, 0, 1])),
            ])),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![9, 10, 10, 11]))),
            Predicate::Record(HashMap::from([
                ("_0".into(), Predicate::True),
                ("_1".into(), Predicate::True),
            ])),
            BitSet::new(),
        ),
    )
}

/// A lambda checks against an annotation its own type is below without being an
/// instance of: `\x -> x` is `𝑎 ⇒ 𝑎`, and `{Int where _ > 0} => Int` widens the
/// codomain. Each use is typed at the annotation.
#[test]
fn a_lambda_below_a_refined_function_annotation() {
    check_scalar(
        indoc! {r#"
            g: {Int where _ > 0} => Int = \x -> x
            g(3)
        "#},
        Value::Int(3),
    );
}

/// Uses typed at an exact function annotation the definition's own type is below
/// without being an instance of. The body's type need not mention the annotation's
/// codomain at all, and a record codomain may be narrower than the body's.
#[rstest]
#[case::constant_body(
    indoc! {r#"
        g: Int => Int = \x -> 0
        g(3)
    "#},
    Value::Int(0),
)]
#[case::record_codomain_the_body_widens(
    indoc! {r#"
        g: Int => {a: Int} = \x -> (a=x, b=x)
        g(4).a
    "#},
    Value::Int(4),
)]
#[case::two_uses(
    indoc! {r#"
        g: Int => Int = \x -> 0
        g(3) + g(4)
    "#},
    Value::Int(0),
)]
#[case::through_an_alias(
    indoc! {r#"
        g: Int => Int = \x -> 0
        h = g
        h(3)
    "#},
    Value::Int(0),
)]
fn a_use_is_typed_at_the_function_annotation(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

#[test]
fn a_lambda_below_a_refined_function_annotation_is_checked_at_the_argument() {
    check_compile_error(
        indoc! {r#"
            g: {Int where _ > 0} => Int = \x -> x
            g(-1)
        "#},
        "expected {Int | __elem > 0}, found Int@-1",
    );
}

/// A refinement the annotation states on the codomain is met by the clone through
/// the solver: the pin decides `Int@5 <: {Int | __elem > 0}` semantically, as the
/// annotation check did.
#[rstest]
#[case::exact(
    indoc! {r#"
        g: Int => {Int where _ > 0} = \x -> 5
        g(3)
    "#},
)]
#[case::polymorphic(
    indoc! {r#"
        g: forall (T <: Int) T => {Int where _ > 0} = \x -> 5
        g(3)
    "#},
)]
fn a_use_meets_the_annotations_codomain_refinement(#[case] code: &str) {
    check_scalar(code, Value::Int(5));
}

/// TODO: false rejections. The specialization pin decides a refinement without the
/// definition's scope, so a predicate naming an enclosing binder (`n`) cannot be
/// discharged, though the annotation check proved it.
#[test]
fn a_use_meets_a_codomain_refinement_naming_an_enclosing_binder() {
    check_compile_error(
        indoc! {r#"
            n = 2
            g: Int => {Int where _ > n} = \x -> 5
            g(3)
        "#},
        "Type mismatch for monomorphization specialization: expected {Int | __elem > n}, found Int@5",
    );
}

/// TODO: false rejection. The pin now discharges `Int@1 <: {Int | __elem > 0}` at
/// `f`'s domain, but the clone's `f(1)` reaches the post-inference check with its
/// argument typed `Int`, which the refined domain does not admit structurally.
#[test]
fn a_use_meets_a_refined_domain_of_a_function_parameter() {
    check_compile_error(
        indoc! {r#"
            g: ({Int where _ > 0} => Int) => Int = \f -> f(1)
            g(\y -> y + 1)
        "#},
        "post-inference produced an invalid tree: [Type mismatch for Apply: expected {Int | __elem > 0}, found Int]",
    );
}

/// An opaque `let`'s body type names an enclosing binder: the read of `x` types
/// `y` as `{Int | __elem == __anf ^+ a}`, and meeting `z`'s annotation needs both
/// `__anf`'s refinement and the parameter `a`'s. Coalescing decides it under the
/// walk's lexical scope, which supplies `a`.
///
/// Currently passes inference but fails post-planning
/// typecheck. Expect this to be fixed if post-inference refinements
/// are erased.
#[test]
fn an_opaque_let_body_entailed_under_an_enclosing_binder() {
    check_compile_error(
        indoc! {r#"
            def f(a: {Int where _ >= 0}):
                x: Mut({Int where _ >= 0}) := 0
                y = x ^+ a
                z: {Int where _ >= 0} = y
                z

            f(1)
        "#},
        "post-planning produced an invalid tree",
    )
}

/// Two reads of a refined mutable variable meet a refined annotation: `y` is the opaque
/// `let __anf : {Int | __elem >= 0} ^= x in __anf ^+ __anf`, and its body type
/// `{Int | __elem == __anf ^+ __anf}` entails `{Int | __elem >= 0}` given `__anf`'s
/// refinement.
///
/// TODO: Currently fails at post-planning typecheck due to pointfree
/// refinements which are not structurally equal, and yet cannot be
/// compared by SMT due to lack of encoding for pointfree
/// expressions. Expect to fix this if post-inference refinements are
/// erased.
#[test]
fn two_reads_of_a_refined_mut_meet_a_refined_annotation() {
    check_compile_error(
        indoc! {r#"
            x: Mut({Int where _ >= 0}) := 0
            y = x ^+ x
            z: {Int where _ >= 0} = y
            z
        "#},
        "post-planning produced an invalid tree",
    )
}

#[test]
fn opaque_let_on_ite() {
    check_scalar(
        indoc! {r#"
acc = 10
t = if True:
        r ^= acc
        r
    else:
        0
t
        "#},
        Value::Int(10),
    )
}

/// A `^+` in a comprehension element: the element's refinement quotes the generator's own
/// source lookup, which lambda elimination rewrites with the rest of the body.
#[test]
fn refined_add_in_a_comprehension_element() {
    check_tile(
        indoc! {r#"
ys = [1 ^+ i for i in [1,2]]
ys
        "#},
        make_int_list(&[2, 3]),
    )
}

/// A comprehension body reading a captured mutable variable.
#[rstest]
#[case::singleton("x := 3", "")]
#[case::refined("x: Mut({Int where _ >= 0}) := 3", "")]
#[case::read_before_a_write("x := 3", "x := 7")]
fn read_captured_mut_inside_comprehension(#[case] decl: &str, #[case] after: &str) {
    let mut program = format!("{decl}\nys = [x ^+ i for i in [1,2]]\n");
    if !after.is_empty() {
        program.push_str(after);
        program.push('\n');
    }
    program.push_str("ys\n");
    check_tile(&program, make_int_list(&[4, 5]));
}

/// TODO: Allow a second operation between a comprehension element's mutable
/// read and the element value.
#[test]
fn two_operations_on_a_mut_read_in_a_comprehension_not_supported() {
    check_compile_error(
        indoc! {r#"
x := 3
ys = [x ^+ x ^+ i for i in [1,2]]
ys
        "#},
        // The binder's uid counts from the run, not from the program, so it is left out.
        "Barendregt violation: substitution range mentions binder `Unique { base: \"i\"",
    )
}

/// TODO: Allow a nested comprehension's element to read a mutable variable.
///
/// The same lift
/// (`two_operations_on_a_mut_read_in_a_comprehension_not_supported`). The outer
/// generator's binder is the first operation's second operand here, so the inner
/// element lambda carries the same intermediate transparent `let`, and its
/// eliminated definition holds the refinement free on the same unnamed `Fun`
/// slots. The binder reported is the nested pair the enclosing binders merge
/// into rather than any generator's own parameter.
#[test]
fn nested_comprehension_reading_a_mut_not_supported() {
    check_compile_error(
        indoc! {r#"
x := 3
ys = [[x ^+ i ^+ j for j in [10,20]] for i in [1,2]]
ys
        "#},
        "Barendregt violation: substitution range mentions binder `Synthetic { kind: Pair",
    )
}

/// TODO: Allow comprehensions nested through let-bindings
#[test]
fn consuming_a_comprehension_carries_mut_into_refinement() {
    check_compile_error(
        indoc! {r#"
x := 3
ys = [x ^+ i for i in [1,2]]
zs = [y ^+ 1 for y in ys]
zs
        "#},
        "Scope violation",
    )
}

/// `(i: {Int | __elem >= 1 and __elem <= 5}) ⤇ {Int | __elem == i ^+ 1}`: a collection
/// mapping the keys 1 through 5 to the values 2 through 6, whose codomain names its key.
fn pi_typed_collection() -> Type {
    let int = || Type::Base(BaseType::Int);
    let elem = || Expr::var(Name::elem());
    let int_lit = |n| Expr::lit(Lit::Int(n));
    let refined = |predicate| Type::refined_one(int(), Refinement::born(Rc::new(predicate)));

    let keys = refined(Expr::binop(
        Expr::binop(
            elem(),
            BinOpKind::Compare(CompareKind::GreaterOrEq),
            int_lit(1),
        ),
        BinOpKind::BoolLogic(LogicKind::And),
        Expr::binop(
            elem(),
            BinOpKind::Compare(CompareKind::LessOrEq),
            int_lit(5),
        ),
    ));
    let values = refined(Expr::binop(
        elem(),
        BinOpKind::Compare(CompareKind::Equals),
        Expr::binop(
            Expr::var("i"),
            BinOpKind::Arithmetic(ArithmeticKind::AddRefined),
            int_lit(1),
        ),
    ));
    Type::pi_kinded("i", keys, values, FunKind::Data(None))
}

/// Infer and type-check `λ c : 𝐶 → body`, where `𝐶` is [`pi_typed_collection`].
///
/// TODO: Bind a Pi's binder while typing its codomain's annotation predicates.
///
/// Construction closes `i` in the codomain to a `PiBound` reference, and
/// `emit_annotation_predicates` descends into the codomain without opening it, so
/// the reference reaches the `Var` lookup unbound. Inference reports `Unbound
/// variable: 'i'` (the `PiBound` prints its hint), and every caller pins it.
fn check_over_pi_typed_collection(body: Expr) {
    let mut expr = uniquify::run(Expr::lambda("c", pi_typed_collection(), body));
    infer(&mut expr, &mut TypeInferenceContext::new())
        .unwrap_or_else(|errs| panic!("inference must succeed: {errs:?}"));
    typecheck(&expr).unwrap_or_else(|errs| panic!("the tree must type-check: {errs:?}"));
}

/// A parameter whose annotation is a Pi-typed collection, used bare: `λ c : 𝐶 → c`.
///
/// Nothing applies `c`, so the only predicate naming the binder `i` is the annotation's
/// own codomain refinement, which is in scope under the Pi that binds it.
///
/// No CHL spelling names a Pi binder in an annotation (`FullMap(K, V)` mints its own), so
/// the tree is built directly.
#[test]
#[should_panic = "Unbound variable: 'i'"]
fn a_pi_typed_collection_parameter() {
    check_over_pi_typed_collection(Expr::var("c"));
}

/// `collection_contains` applied to a Pi-typed collection: `λ c : 𝐶 → c ▷ collection_contains`.
///
/// No CHL spelling applies the builtin to a bare collection, so the tree is built directly.
///
/// TODO: the type template for collection_contains has no way to
/// handle a Pi-binder referenced in the collection's codomain. See
/// also `collection_contains_of_an_inferred_pi_typed_collection`.
#[test]
#[should_panic = "Unbound variable: 'i'"]
fn collection_contains_of_a_pi_typed_collection() {
    check_over_pi_typed_collection(Expr::apply(
        Expr::var("c"),
        Expr::builtin(Builtin::CollectionContains),
    ));
}

/// `collection_contains` applied to a collection that infers a Pi type with no annotation.
///
/// No CHL spelling applies the builtin to a bare collection, so it is applied to the
/// lowered program.
///
/// TODO: Currently fails because the collection codomain still
/// references its Pi binder after being moved from the context of the
/// collection Pi type into the non-Pi-type template of
/// `collection_contains`.
#[test]
#[should_panic = "references out-of-scope binder(s) [\"__iter_record\"]"]
fn collection_contains_of_an_inferred_pi_typed_collection() {
    let code = indoc! {r#"
        xs = [1, 2, 3, 4, 5]
        c = [x ^+ 1 for x in xs]
        c
    "#};
    let module = chl_parser::parse_module(FileId::ROOT, code)
        .into_result()
        .expect("the program parses");
    let mut lctx = LoweringContext::default();
    let program = lower_stmts(&module, &mut lctx)
        .into_result()
        .expect("the program lowers");
    let applied = Expr::apply(program, Expr::builtin(Builtin::CollectionContains));
    // The phases `compile_program` runs before inference.
    let expr = mut_read::run(anf::run(uniquify::run(applied)));
    let mut expr = opaque_output::run(comprehension::run(expr, lctx.shared_holes()));
    infer(&mut expr, &mut TypeInferenceContext::new())
        .unwrap_or_else(|errs| panic!("inference must succeed: {errs:?}"));
    typecheck(&expr).unwrap_or_else(|errs| panic!("the tree must type-check: {errs:?}"));
}

/// A compute function composed with a refining lambda, then applied:
/// `let fc = λ f1 : (String ⇒ Int) → f1 ≫ (λ i → i ^+ 1) in "Hello" ▷ ((λ s → 1) ▷ fc)`.
///
/// CHL has no `≫` and no call of a call's result, so the tree is built directly.
///
/// TODO: Currently fails because the emit rule for >> uses the final
/// function's codomain as-is, even though it has been removed from
/// the context of its Pi-binder.
#[test]
#[should_panic = "open bound recorded"]
fn dependent_function_composition() {
    let fc = Expr::lambda(
        "f1",
        Type::fun(Type::Base(BaseType::String), Type::Base(BaseType::Int)),
        Expr::compose(vec![
            Expr::var("f1"),
            Expr::lambda(
                "i",
                Type::Hole,
                Expr::binop(
                    Expr::var("i"),
                    BinOpKind::Arithmetic(ArithmeticKind::AddRefined),
                    Expr::lit(Lit::Int(1)),
                ),
            ),
        ])
        // The chain's kind stamp: a composition of compute functions is one.
        .with_ty(Type::fun(Type::Hole, Type::Hole)),
    );
    let call = Expr::apply(
        Expr::lit(Lit::String("Hello".into())),
        Expr::apply(
            Expr::lambda("s", Type::Hole, Expr::lit(Lit::Int(1))),
            Expr::var("fc"),
        ),
    );
    let mut expr = uniquify::run(Expr::let_bind("fc", fc, call));
    infer(&mut expr, &mut TypeInferenceContext::new())
        .unwrap_or_else(|errs| panic!("inference must succeed: {errs:?}"));
    typecheck(&expr).unwrap_or_else(|errs| panic!("the tree must type-check: {errs:?}"));
}

/// TODO: Allow a comprehension over a collection whose elements read a mutable
/// variable.
///
/// The consuming element's refinement quotes the producing comprehension whole,
/// read and all, so the read's opaque binder sits inside a term a later
/// refinement names rather than standing between the mutable variable and the
/// type. Inference rejects it as `MutableInRefinedType`.
///
/// Plan to fix by making comprehension bindings opaque.
#[test]
fn binding_a_comprehension_carries_mut_into_refinement() {
    check_compile_error(
        indoc! {r#"
x := 3
ys = [x ^+ i for i in [1,2]]
[y ^+ 1 for y in ys]
        "#},
        "Scope violation",
    )
}

/// TODO: Make comprehension bindings opaque.
#[test]
fn nesting_a_comprehension_carries_mut_into_refinement() {
    check_compile_error(
        indoc! {r#"
x := 3
[y ^+ 1 for y in [x ^+ i for i in [1,2]]]
        "#},
        "Barendregt violation: substitution range mentions binder `Synthetic { kind: IterRecord,",
    )
}

/// TODO: Make function bindings opaque. This is currently blocked by
/// later inline-phase handling of opaque let-bindings.
#[test]
fn binding_a_function_carries_mut_into_refinement() {
    check_compile_error(
        indoc! {r#"
x := 3
f = \y -> y ^+ x
f(1) ^+ 1
        "#},
        "Scope violation",
    )
}

/// TODO: Make function bindings opaque
#[test]
fn declaring_a_function_carries_mut_into_refinement() {
    check_compile_error(
        indoc! {r#"
x := 3
def f(y):
    y ^+ x
f(1) ^+ 1
        "#},
        "Scope violation",
    )
}

/// A refined `^+` on a binding whose refinement names a mutable variable's read.
#[test]
fn refined_op_on_opaque() {
    check_scalar(
        indoc! {r#"
x := 4
y = x ^+ 1
y ^+ 1
        "#},
        Value::Int(6),
    )
}

/// The refined `y ^+ 1` in `zs` keeps its refinement through lambda elimination, which
/// rewrites the refinement's free variable.
#[test]
fn refined_op_in_nested_comprehension() {
    check_tile(
        indoc! {r#"
ys = [i for i in [1,2]]
zs = [y ^+ 1 for y in ys]
zs
        "#},
        make_int_list(&[2, 3]),
    )
}

/// The refinement `r ^+ 0` names `r`, which is scoped inside `f`'s body, and
/// sits in a tuple component of the body's type rather than at its top.
/// Compaction moves it to an obligation at that nested position, as Check's
/// reconstruction drops it there.
#[test]
fn opaque_refined_op_in_tuple() {
    check_scalar(
        indoc! {r#"
def f(x: Int):
    r ^= x
    (r ^+ 0, 1)
a = f(1)
a.0
        "#},
        Value::Int(1),
    )
}

/// `k`'s domain refinement names no opaque variable, so the barrier
/// var's solution keeps it: a refinement at a negative position of the
/// solution is kept, and dropping it would accept `-5`.
#[test]
fn return_refined_function_from_function() {
    check_compile_error(
        indoc! {r#"
def f(x: Int):
    r ^= x
    def k(y: {Int where _ > 0}):
        y
    k
f1 = f(1)
f1(-5)
        "#},
        "Type mismatch for Apply: expected {Int | __elem > 0}, found Int@-5",
    )
}

#[test]
fn return_opaque_annotated_function_from_annotated_function() {
    check_compile_error(
        indoc! {r#"
def f(x: Int) => ({Int where _ > 0} => Int):
    r ^= x
    def k(y: {Int where _ > 0 and r == r}):
        y
    k
f1 = f(1)
f1(-5)
        "#},
        "──── Type mismatch for Apply: expected {Int | __elem > 0}, found Int@-5",
    )
}

#[test]
fn return_opaque_unannotated_function_from_annotated_function() {
    check_compile_error(
        indoc! {r#"
def f(x: Int) => ({Int where _ > 0} => Int):
    r ^= x
    def k(y: Int):
        r
    k
f1 = f(1)
f1(-5)
        "#},
        "──── Type mismatch for Apply: expected {Int | __elem > 0}, found Int@-5",
    )
}

/// `k`'s domain refinement names the opaque variable `r`, so inference
/// refuses to solve the barrier var: keeping the refinement brings `r`
/// out of its scope, and dropping it is unsound. A codomain annotation
/// on `f` that does not name `r` resolves the refusal
/// (`return_opaque_annotated_function_from_annotated_function`), so the
/// message suggests one.
#[test]
fn return_opaque_annotated_function_from_unannotated_function() {
    check_compile_error(
        indoc! {r#"
def f(x: Int):
    r ^= x
    def k(y: {Int where _ > 0 and r == r}):
        y
    k
f1 = f(1)
f1(-5)
        "#},
        "this function's result type ({Int | __elem > 0 and r == r} ⇒ Int) refines a parameter by `r`, which the function body binds opaquely; annotate the function's result type with a type that does not name `r`",
    )
}

/// This represents a user's incorrect response to the suggestion in
/// the error given by
/// `return_opaque_annotated_function_from_unannotated_function`. Here,
/// the added codomain for `f` is not a subtype of `f`'s actual body
/// type, and type inference rejects it.
#[test]
fn return_opaque_annotated_function_from_unannotated_function_bad_fix() {
    check_compile_error(
        indoc! {r#"
def f(x: Int) => (Int => Int):
    r ^= x
    def k(y: {Int where _ > 0 and r == r}):
        y
    k
f1 = f(1)
f1(-5)
        "#},
        "────── Annotation mismatch: annotated as Int => Int, but inferred as {Int where _ > 0 and r == r} => {Int where _ > 0 and r == r}",
    )
}

/// This represents a user's correct response to the suggestion in the
/// error given by
/// `return_opaque_annotated_function_from_unannotated_function`. Here,
/// the added codomain for `f` is a subtype of `f`'s actual body type,
/// and in fact precisely describes it but without mentioning `r`.
///
/// Because `f` successfully types, type inference can continue to
/// fail on the application `f1(-5)`, where an argument is encountered
/// that does not satisfy the new annotation.
#[test]
fn return_opaque_annotated_function_from_unannotated_function_good_fix() {
    check_compile_error(
        indoc! {r#"
def f(x: Int) => ({Int where _ > 0} => {Int where _ > 0}):
    r ^= x
    def k(y: {Int where _ > 0 and r == r}):
        y
    k
f1 = f(1)
f1(-5)
        "#},
        "──── Type mismatch for Apply: expected {Int | __elem > 0}, found Int@-5",
    )
}

/// `f`'s barrier variable is checked against the use `f1(-5)` before compaction, so
/// `y` is solved before the walk reads it. If the `^=` is replaced with `=`, then no
/// barrier var is introduced.
#[test]
fn return_unrefined_function_from_function() {
    check_scalar(
        indoc! {r#"
def f(x: Int):
    r ^= x
    def k(y):
        y
    k
f1 = f(1)
f1(-5)
        "#},
        Value::Int(-5),
    )
}

/// TODO: solve relevant base types before running an SMT check, and
/// provide a better error message when an SMT check can't run.
///
/// The failure message this test pins is unhelpful: it looks like the
/// quoted types do match, and should pass an SMT check. What's really
/// happening is that the SMT check is refusing to run at all because
/// `x`'s base type (and thus SMT encoding sort) is not yet known when
/// the SMT check is called for.
#[test]
fn unsettled_base_type_auto_fails_smt_check() {
    check_compile_error(
        indoc! {r#"
def f(x) => ({Int where _ > 0} => Int):
    def k(y: {Int where _ > 0 and x == x}):
        1
    k
f1 = f(1)
f1(-5)
        "#},
        "Annotation mismatch: annotated as {Int where _ > 0} => Int, but inferred as {Int where _ > 0 and x == x} => {Int where _ == 1}",
    )
}

#[test]
fn barrier_var_with_sub_barrier_var() {
    check_scalar(
        indoc! {r#"
def f(x):
    r ^= x
    r ^+ 0
def g(y):
    s ^= y
    f(s)
g(1)
        "#},
        Value::Int(1),
    )
}

/// `f` and `g` differ only in what their codomain barrier variables resolve to, `Int` and
/// `Bool`, so the two uses of `id` key apart and take a clone each. Keyed without the
/// resolution, they share one clone, typed at whichever use came first.
#[test]
fn uses_differing_only_in_a_barrier_variable_resolution_specialize_apart() {
    check_scalar(
        indoc! {r#"
def f(x: Int):
    r ^= x;
    r ^+ 0
def g(x: Int):
    r ^= x;
    (r ^+ 0) > 5
def id(h):
    h
p = id(f)
q = id(g)
3
        "#},
        Value::Int(3),
    )
}

/// `f`'s body is an `Index` applied at the argument `[1, 2]` refines, an invariant position.
/// The barrier variable keeps that refinement, so the result's argument stays equal to the
/// body's. Dropped, it would make the two `Index` values' arguments differ, and the join of
/// two applications of an invariant parameter at different arguments has no type.
#[test]
fn a_refinement_in_an_invariant_nominal_argument_survives_the_barrier() {
    check_scalar(
        indoc! {r#"
type Index(K):
    index(FullMap(K, Int))
def f(x: Int):
    r ^= x
    Index::index(map([(1, 10), (2, 20)]))
i = f(1)
7
        "#},
        Value::Int(7),
    )
}

/// A data-function type whose domain is a bare `_` admits a plain collection and a sum alike
/// (`docs/chl-spec.md`, "6.3 Direction: collection types [Decided]").
#[rstest]
#[case::a_plain_collection("xs: _ |=> Int = [1, 2, 3]\nsum(xs)", 6)]
#[case::a_sum("xs: _ |=> Int = box([1, 2, 3])\nsum([x for x in xs])", 6)]
#[case::a_parameter(
    indoc! {"
        def total(xs: _ |=> Int) => Int:
            sum([x for x in xs])
        total([1, 2]) + total(box([3, 4]))
    "},
    10
)]
#[case::each_use_of_an_alias(
    indoc! {"
        Ints = _ |=> Int
        a: Ints = [1, 2]
        b: Ints = box([3, 4])
        sum(a) + sum(b)
    "},
    10
)]
#[case::a_codomain("f: Int => _ |=> Int = \\n -> [n, n]\nsum(f(3))", 6)]
// A group-by's codomain reads its key, and a hole in the annotation's codomain is filled under
// the annotation's binder.
#[case::a_group_by(
    indoc! {"
        xs = [1, 2, 3]
        g: _ |=> _ = groupby(xs, \\x -> x > 1)
        sum([sum(v) for v in g])
    "},
    6
)]
fn a_data_function_type_admits_both_collections(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A written domain, a type parameter included, names a plain collection, so a type parameter
/// at several positions relates plain collections over one domain.
#[rstest]
#[case::a_type_parameter_domain(
    indoc! {"
        def total(D, xs: D |=> Int) => Int:
            sum(xs)
        total([1, 2]) + total([3, 4])
    "},
    10
)]
#[case::a_polymorphic_annotation(
    "f: forall (D) (D |=> Int) => Int = \\xs -> sum(xs)\nf([1, 2]) + f([3])",
    6
)]
#[case::a_shared_domain_over_one_plain_domain(
    indoc! {"
        def both(D, a: D |=> Int, b: D |=> Int) => Int:
            sum(a) + sum(b)
        both([1, 2], [3, 4])
    "},
    10
)]
#[case::a_nominal_types_domain(
    indoc! {"
        type Keyed(D) = D |=> Int
        k = Keyed::new([1, 2])
        sum(k.extract())
    "},
    3
)]
#[case::a_domain_shared_with_a_requirement(
    indoc! {"
        def total(D, xs: D |=> Int) => Int requires Equatable(D, D):
            sum(xs)
        total([1, 2])
    "},
    3
)]
fn a_written_domain_admits_a_plain_collection(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A written domain admits no sum, whether it is a type, a type parameter at one position or at
/// several, and two plain domains a type parameter names are one.
#[rstest]
#[case::a_written_type(
    "xs: Int |=> Int = box([1, 2])\nsum(xs)",
    "annotated as Int |=> Int, but inferred as Box(Array(2, Int))"
)]
#[case::a_type_parameter(
    indoc! {"
        def total(D, xs: D |=> Int) => Int:
            sum(xs)
        total(box([3, 4]))
    "},
    SUM_REACHED_PLAIN
)]
#[case::a_polymorphic_annotation(
    "f: forall (D) (D |=> Int) => Int = \\xs -> sum(xs)\nf(box([1, 2]))",
    SUM_REACHED_PLAIN
)]
#[case::two_sums(
    indoc! {"
        def both(D, a: D |=> Int, b: D |=> Int) => Int:
            sum(a) + sum(b)
        both(box([1, 2]), box([3, 4, 5]))
    "},
    SUM_REACHED_PLAIN
)]
#[case::a_sum_and_its_result(
    indoc! {"
        def ident(D, a: D |=> Int) => D |=> Int:
            a
        sum(ident(box([1, 2])))
    "},
    SUM_REACHED_PLAIN
)]
#[case::two_plain_domains(
    indoc! {"
        def both(D, a: D |=> Int, b: D |=> Int) => Int:
            sum(a) + sum(b)
        both([1, 2], [3, 4, 5])
    "},
    "a collection over one domain does not stand in for a collection over another"
)]
#[case::a_sum_in_a_nominal_type(
    indoc! {"
        type Keyed(D) = D |=> Int
        k = Keyed::new(box([1, 2]))
        sum(k.extract())
    "},
    SUM_REACHED_PLAIN
)]
fn a_written_domain_admits_no_sum(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
}

const SUM_REACHED_PLAIN: &str = "a sum reached a plain collection";

/// A data-function type is written in annotation position, as `T => U` is.
#[test]
fn a_data_function_type_is_no_value() {
    check_compile_error("x = Int |=> Int\n1", "`T |=> U` is a data-function *type*");
}
