use std::collections::HashMap;

use bit_set::BitSet;
use indoc::indoc;
use rstest::rstest;

use crate::helpers::{check_compile_error, check_scalar, check_tile};

use cambra::interpreter::{ColumnValue, Predicate, Tile, Value};

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
    check_scalar(
        include_str!("type_annotations/underscore.cambra"),
        Value::Int(3),
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
fn output_annotation_ref1() {
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
fn output_annotation_ref2() {
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
fn output_annotation_ref3() {
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
fn type_refined_input_only1() {
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
fn type_refined_input_only2() {
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
fn type_refined_input_only3() {
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
fn type_refined_input_only4() {
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
/// (`tests/type_check.rs`, `products_are_equatable_componentwise`), so `t == t` is an
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

/// A refinement in a `Map` key type that no key satisfies. The plain annotation reports it,
/// and the `Mut` form reaches a pass boundary instead.
///
/// Neither program is well-typed today: a literal key carries `__elem == "a"`, and a
/// refinement is discharged by matching the predicate rather than by proving it, so
/// `__elem != ""` is not satisfied. What differs is the report. The plain
/// annotation is an `Annotation mismatch` against the whole `Σ`, which names the
/// annotation the program wrote; the mutable one panics at the post-inference boundary as
/// an invalid tree, which reads as a compiler bug for a program that is simply rejected.
///
/// Pinned on both, so the day the `Mut` form reports a user error the pin says so.
#[test]
fn a_refined_map_key_no_key_satisfies() {
    check_compile_error(
        r#"
m: Map({String where _ != ""}, Int) = map([("a", 1), ("z", 2)])
m
"#,
        r#"Annotation mismatch: annotated as Map({String where _ != ""}, Int), but inferred as FullMap({String where _ in ["a", "z"]}, Int)"#,
    )
}

#[test]
fn a_refined_map_key_in_a_mut_annotation_reaches_the_boundary() {
    check_compile_error(
        r#"
m: Mut(Map({String where _ != ""}, Int)) := box(map([("a", 1), ("z", 2)]))
m
"#,
        "produced an invalid tree: [Type mismatch for collection domain",
    )
}

/// This and the following two tests exclude a bug in which captured
/// input expressions that are later used to create a trait instance
/// refinement are stale at that point. Bug was fixed by freshening
/// the inputs before creating the refinement.
#[test]
fn freshen_refined_add_double_arg1() {
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
fn freshen_refined_add_double_arg2() {
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
/// (`Typing::close_body_type`).
///
/// `b`'s annotation then demands `{Int | __elem == a}` of a value known
/// only to be an `Int`, which nothing establishes.
#[test]
fn dont_discharge_opaques_out_of_fun_bodies() {
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

/// Reading a mutable variable introduces an opaque binder whose scope closes
/// inside the body, so the codomain's opaque drop runs; the same refinement names
/// the parameter, which the Pi binds. The codomain variable carrying the drop is
/// minted under the parameter binder for that reason
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

/// TODO: Allow mutable reads to be read in the body of a
/// comprehension.
///
/// The limitation surfaces as `lambda_elim`'s point-free reconstruction assert, which is
/// `debug_assertions`-gated, so the program compiles under a profile that drops it.
#[cfg(debug_assertions)]
#[test]
fn reading_mut_in_comprehension_not_supported() {
    check_compile_error(
        indoc! {r#"
x := 3
ys = [x ^+ i for i in [1,2]]
ys
        "#},
        "λ i : Int → let __read : Int@3 ^= x
in __read ^+ i
to
let __read : (Int ⇒ Int@3) = x ▷ const
in (((id, __read ▷ const) ▷ zip ≫ apply, id) ▷ zip, add_refined ▷ const) ▷ zip ≫ apply
with (Int ⇒ Int) vs ((i: Int) ⇒ {Int | __elem == x ▷ const ^+ i})",
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

/// Type inference drops the refinement from the `ys` function, making
/// its type `(Int => Int)`, because the refinement contains an opaque
/// read of `x`. During lambda_elim, a debug assertion rebuilds a
/// refined type for the codomain from the body (containing `x`, which
/// is now immutable, and has had its opaque read erased).  The two
/// types are not structurally equal, and so the assertion fails.
///
/// This is the assert `reading_mut_in_comprehension_not_supported`
/// pins for the unfiltered case. A filter, a nested comprehension and a
/// conditional element each reach it too, where before the comprehension
/// phase they failed inference with `MutableInRefinedType`.
///
/// TODO: Fix by mirroring the opaque dropping logic in lambda_elim's
/// type reconstruction, or by dropping non-data-fun-domain type
/// refinements (and debug assertion logic that reconstructs them)
/// after inference.
#[cfg(debug_assertions)]
#[rstest]
#[case::filtered(
    indoc! {r#"
x := 3
ys = [x ^+ i for i in [1,2,3] if i > 1]
ys
    "#},
    "(Int ⇒ Int) vs ((i: Int) ⇒ {Int | __elem == x ▷ const ^+ i})"
)]
#[case::nested(
    indoc! {r#"
x := 3
ys = [[x ^+ j for j in [1,2]] for i in [1,2] if i > 1]
ys
    "#},
    "(Int ⇒ Int) vs ((j: Int) ⇒ {Int | __elem == x ▷ const ^+ j})"
)]
#[case::conditional_element(
    indoc! {r#"
x := 3
ys = [x ^+ i if i > 1 else 0 for i in [1,2,3]]
ys
    "#},
    "(Int ⇒ Int) vs ((i: Int) ⇒ {Int | __elem == x ▷ const ^+ i})"
)]
fn a_comprehension_that_reads_a_mut_fails_lambda_elims_reconstruction(
    #[case] code: &str,
    #[case] needle: &str,
) {
    check_compile_error(code, needle)
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
