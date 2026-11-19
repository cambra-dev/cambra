use cambra::ccl::Occurrence;
use std::collections::HashMap;
use std::rc::Rc;

use bit_set::BitSet;
use indoc::indoc;
use rstest::rstest;

use super::helpers::{check_compile_error, check_scalar, check_sink, check_tile, make_int_list};

use cambra::ccl::infer::{TypeInferenceContext, infer, typecheck};
use cambra::ccl::lower::{LoweringContext, lower_stmts};
use cambra::ccl::{
    ArithmeticKind, BinOpKind, Builtin, CompareKind, Expr, FunKind, Lit, LogicKind, Name,
    Refinement, Type, anf, comprehension, mut_read, opaque_output, uniquify,
};
use cambra::chl_parser::{self, FileId};
use cambra::interpreter::{BaseType, ColumnValue, Predicate, Tile, Value};

/// A later parameter's annotation reads an earlier one, at the argument the call passes for it:
/// `f(𝑥, 𝑦)` takes `𝑦` at `{Int where _ >= 𝑥}`, whatever `𝑥`'s type has resolved to when the
/// argument meets its parameter.
#[rstest]
#[case::literal("f(1, 5)")]
#[case::bound_names(indoc! {r#"
    x = 1
    y = 5
    f(x, y)
"#})]
#[case::projections(indoc! {r#"
    pair = (1, 5)
    f(pair.0, pair.1)
"#})]
#[case::a_returned_tuple_s_components(indoc! {r#"
    def pair():
        (1, 5)
    p = pair()
    f(p.0, p.1)
"#})]
#[case::parameters_reading_each_other(indoc! {r#"
    def g(n: Int, m: {Int where _ >= n}) => Int:
        f(n, m)
    g(1, 5)
"#})]
#[case::a_refined_sum(indoc! {r#"
    def g(n: Int) => Int:
        f(n, n ^+ 4)
    g(1)
"#})]
#[case::annotated_higher_order(indoc! {r#"
    def apply(fn: (a: Int, b: {Int where _ >= a}) => Int, x: Int, y: {Int where _ >= x}):
        fn(x, y)
    apply(f, 1, 5)
"#})]
fn dependent_parameters_take_their_arguments(#[case] call: &str) {
    let definition = indoc! {r#"
        def f(a: Int, b: {Int where _ >= a}):
            b
    "#};
    check_scalar(&format!("{definition}{call}"), Value::Int(5));
}

/// A call whose later argument the earlier one does not bound is refused: an argument known
/// only by its type bounds nothing.
#[rstest]
#[case::literals("f(5, 1)", "expected {Int where _ >= 5}, found {Int where _ == 1}")]
#[case::an_unrefined_result(indoc! {r#"
    def one() => Int:
        1
    f(one(), 5)
"#}, "Type mismatch for this call")]
#[case::an_unrefined_sum(indoc! {r#"
    def g(n: Int) => Int:
        f(n, n + 4)
    g(1)
"#}, "expected {Int where _ >= n}, found Int")]

fn dependent_parameters_refuse_an_unbounded_argument(#[case] call: &str, #[case] needle: &str) {
    let definition = indoc! {r#"
        def f(a: Int, b: {Int where _ >= a}):
            b
    "#};
    check_compile_error(&format!("{definition}{call}"), needle);
}

#[test]
fn an_unsolved_higher_order_callee_takes_its_arguments_whole() {
    check_compile_error(
        indoc! {r#"
        def f(a: Int, b: {Int where _ >= a}):
            b
        def apply(h, x, y):
            h(x, y)
        apply(f, 1, 5)
    "#},
        "expected {Int where _ >= x}, found {Int where _ == 5}",
    );
}

/// A tuple passed to a function of a parameter list is one argument, which a list of two does not
/// take (`docs/chl-spec.md`, "Parameter lists").
#[test]
fn dependent_parameters_take_no_tuple() {
    check_compile_error(
        indoc! {r#"
            def f(a: Int, b: {Int where _ >= a}):
                b
            pair = (1, 5)
            f(pair)
        "#},
        "`f` takes 2 arguments, got 1",
    );
}

#[test]
fn a_late_callee_still_checks_parameter_count() {
    check_compile_error(
        indoc! {r#"
        def inc(x: Int) => Int:
            x + 1
        def apply2(h, x):
            h(x, 1)
        apply2(inc, 5)
    "#},
        "Type mismatch",
    );
}

#[test]
fn a_single_parameter_list_uses_no_comma() {
    check_compile_error(
        indoc! {r#"
            f: (Int,) => Int = \x -> x
            f(1)
        "#},
        "a one-parameter type is A => C",
    );
}

#[test]
fn parameters_in_one_signature_have_distinct_names() {
    check_compile_error(
        indoc! {r#"
        def f(a: Int, a: Int):
            a
        f(1, 2)
    "#},
        "parameter `a` is declared twice",
    );
}

/// An annotation reading its one input whole is completed from a function reading the input's
/// components by name, and the reverse.
#[rstest]
#[case::named_whole(indoc! {r#"
    h: {(a: Int), (b: Int)} => Int = \p -> p.0 ^+ p.1
    g: (p: {Int, Int}) => _ = h
    g((1, 2))
"#})]
#[case::unnamed_whole(indoc! {r#"
    h: {(a: Int), (b: Int)} => Int = \p -> p.0 ^+ p.1
    g: {Int, Int} => _ = h
    g((1, 2))
"#})]
fn complete_whole_input_annotation_from_component_parameters(#[case] code: &str) {
    check_scalar(code, Value::Int(3));
}

#[test]
fn complete_component_annotation_from_whole_input_parameter() {
    check_scalar(
        indoc! {r#"
            g: {(a: Int), (b: Int)} => _ = \p: {Int, Int} -> p.0 ^+ p.1
            g((1, 2))
        "#},
        Value::Int(3),
    );
}

#[test]
fn dependent_tuple_alias_keeps_its_contract() {
    check_scalar(
        indoc! {r#"
            p: {(a: Int), (b: {Int where _ >= a})} = (1, 5)
            q: {(x: Int), (y: {Int where _ >= x})} = p
            q.1
        "#},
        Value::Int(5),
    );
}

#[test]
fn project_a_component_whose_bound_depends_on_an_earlier_projection() {
    check_scalar(
        indoc! {r#"
            p: {(a: Int), (b: {Int where _ >= a}), (c: {Int where _ >= b})} = (1, 2, 3)
            p.2
        "#},
        Value::Int(3),
    );
}

#[test]
fn named_one_tuple_domain_keeps_its_width() {
    check_scalar(
        indoc! {r#"
            f: {(x: Int),} => Int = \p: {Int,} -> p.0
            f((7,))
        "#},
        Value::Int(7),
    );
}

#[test]
fn refinement() {
    check_compile_error(
        include_str!("type_annotations/refined_div_zero.cambra"),
        "expected {Int where _ != 0}",
    );
    // The demanded predicate reads a field of the record it refines, and the
    // argument's own type pins that field to `0`, so the rejection is a
    // refutation rather than a comparison nothing decided.
    check_compile_error(
        include_str!("type_annotations/complex_refinement.cambra"),
        "expected {{x: Int, y: Int} where _.y != 0}, found {x: {Int where _ == 1}, y: {Int where _ == 0}}",
    );
    check_compile_error(
        include_str!("type_annotations/underscore.cambra"),
        "`_` binds nothing, so it reads no value",
    )
}

#[test]
fn output_annotation_base() {
    check_scalar(
        indoc::indoc! {r#"

            def foo(a: Int, b: Int) => Int:
                a + b

            foo(4, -1)
            "#},
        Value::Int(3),
    )
}

#[test]
fn output_annotation_base_neg() {
    check_compile_error(
        indoc::indoc! {r#"

            def itsa_five(a) => String:
                5

            itsa_five("dummy_arg")
            "#},
        "Annotation mismatch: annotated as String, but inferred as {Int where _ == 5}",
    )
}

/// A bounded annotation is written as the bound it states.
#[test]
fn a_bounded_annotation_mismatch_writes_the_bound() {
    check_compile_error(
        indoc! {"
            x <: {at: Int} = 5
            x
        "},
        "Annotation mismatch: annotated as <: {at: Int}, but inferred as {Int where _ == 5}",
    )
}

#[test]
fn output_annotation_singleton_matches_the_literal() {
    check_scalar(
        indoc::indoc! {r#"

            def itsa_nine(a) => {Int where _ == 9}:
                9

            itsa_nine("dummy_arg")
            "#},
        Value::Int(9),
    )
}

#[test]
fn output_annotation_singleton_rejects_another_literal() {
    check_compile_error(
        indoc::indoc! {r#"

            def itsa_nine(a) => {Int where _ == 9}:
                8

            itsa_nine("dummy_arg")
            "#},
        "Annotation mismatch: annotated as {Int where _ == 9}, but inferred as {Int where _ == 8}",
    )
}

#[test]
fn function_type_annotation() {
    // A binding annotated with a function type `(Int => Int)` checks against the
    // lambda it binds (a lambda is a compute function, the kind `=>` denotes).
    check_scalar(
        indoc::indoc! {r#"

            f: (Int => Int) = \x -> x + 1
            f(4)
            "#},
        Value::Int(5),
    )
}

#[test]
fn function_type_annotation_refined_codomain() {
    // A refinement nested in the codomain is a `Bool` predicate over `_`, typed
    // through `Type::Fun` like any other annotation refinement. The body `9` is
    // `Int@9`, which discharges `{Int where _ == 9}`.
    check_scalar(
        indoc::indoc! {r#"

            f: (Int => {Int where _ == 9}) = \x -> 9
            f(4)
            "#},
        Value::Int(9),
    )
}

#[test]
fn function_type_annotation_refined_codomain_neg() {
    // The codomain refinement is enforced: a body of `8` does not satisfy
    // `{Int where _ == 9}`.
    check_compile_error(
        indoc::indoc! {r#"

            f: (Int => {Int where _ == 9}) = \x -> 8
            f(4)
            "#},
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
        "found '->', expected 'requires', 'causes', '=>', or ':'",
    )
}

#[test]
fn function_type_in_value_position_is_rejected() {
    // `T => U` names a type; it is annotation-only, not a value.
    check_compile_error(
        indoc::indoc! {r#"

            x = Int => Int
            x
            "#},
        "is a function *type*",
    )
}

// This test fails because the output of _ + _ is currently unrefined.
// Once that is fixed, it should fail for the different reason that
// the argument b is not >= 0.
#[test]
fn output_annotation_naming_a_parameter_not_entailed() {
    check_compile_error(
        indoc::indoc! {r#"

            def sum_up(a: Int, b: {Int where _ >= 0}) => {Int where _ >= a}:
                a + b

            x = (3,-1)

            sum_up(x)
            "#},
        "Annotation mismatch: annotated as {Int where _ >= a}, but inferred as Int",
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
        indoc::indoc! {r#"

            def test(x: Int) => {Int where _ > x}:
                x + 1

            ()
            "#},
        "Annotation mismatch: annotated as {Int where _ > x}, but inferred as Int",
    )
}

// The refinement body in the output type of `test` should fail to
// type, since it refers to `y` which is unbound.
#[test]
fn type_scope_neg() {
    check_compile_error(
        indoc::indoc! {r#"

            def test(x: Int) => {Int where _ > y}:
                x + 1

            ()
            "#},
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
        indoc::indoc! {r#"

            y = 3

            def test(x: {{Int where _ != y + y} where _ != y}) => {Int where _ > y + x}:
                x + 3

            ()
            "#},
        "Annotation mismatch: annotated as {Int where _ > y + x}, but inferred as Int",
    )
}

#[test]
fn type_refined_input_only_true() {
    check_scalar(
        indoc::indoc! {r#"

            def f(x: {Int where True}) => Int:
                x
            ()
            "#},
        Value::Unit,
    )
}

#[test]
fn type_refined_input_only_self_comparison() {
    check_scalar(
        indoc::indoc! {r#"

            def f(x: {Int where _ >= _}) => Int:
                x
            ()
            "#},
        Value::Unit,
    )
}

#[test]
fn type_refined_input_only_self_equality_after_a_parameter() {
    check_scalar(
        indoc::indoc! {r#"

            def f(y: Int, x: {Int where _ == _}):
                x
            ()
            "#},
        Value::Unit,
    )
}

#[test]
fn type_refined_input_only_self_equality() {
    check_scalar(
        indoc::indoc! {r#"

            def f(x: {Int where _ == _}):
                x
            ()
            "#},
        Value::Unit,
    )
}

// This should succeed eventually, but fails for now since refinements
// are only compared by equality.
#[test]
fn type_refined_input_output() {
    check_compile_error(
        indoc::indoc! {r#"

            def f(x: {Int where _ == _}) => {Int where _ == x}:
                x
            ()
            "#},
        "Annotation mismatch: annotated as {Int where _ == x}, but inferred as {Int where _ == _}",
    )
}

// This should succeed eventually, but fails for now since refinements
// are only compared by equality.
#[test]
fn type_refined_output() {
    check_compile_error(
        indoc::indoc! {r#"

            def f(x: Int) => {Int where _ == x}:
                x
            ()
            "#},
        "Annotation mismatch: annotated as {Int where _ == x}, but inferred as Int",
    )
}

// The refinement body for `x` should fail to typecheck, since it
// should not be able to refer to itself by `x`, only by `_`.
#[test]
fn type_scope_self() {
    check_compile_error(
        indoc::indoc! {r#"

            def test(x: {Int where x >= 1}) => Int:
                x + 1

            ()
            "#},
        "Unbound variable: 'x'",
    )
}

// The refinement body for `x` should fail to typecheck, since the `x`
// inside is refering to the outer scope `x`, which is a `String`.
#[test]
fn type_scope_outer_shadow() {
    check_compile_error(
        indoc::indoc! {r#"

            x = "Hello"

            def test(x: {Int where _ >= x}) => Int:
                x + 1

            ()
            "#},
        "No Orderable instance for `>=`: operand 2 is String",
    )
}

#[test]
fn type_binop_mismatch() {
    check_compile_error(
        indoc::indoc! {r#"

            def test(a: String, b: Int):
                a + b

            ()
            "#},
        "No Addable instance for `+`: operand 2 is Int, but the only type accepted there is String",
    )
}

/// A parameter's annotation reads the parameters before it and none after it, nor the
/// parameter itself (`docs/chl-spec.md`, "4.1 `def` — function definition"). A reference to a
/// later parameter or to its own resolves outward, and with nothing outside to resolve to it is
/// an ordinary unbound variable.
#[rstest]
#[case::later_sibling(indoc::indoc! {r#"
    def f(c: {Int where _ >= a}, a: Int):
        c

    f
    "#}, "a")]
#[case::own_binder(indoc::indoc! {r#"
    def f(a: {Int where _ >= a}):
        a

    f
    "#}, "a")]
fn type_annotation_naming_a_parameter_is_unbound(#[case] code: &str, #[case] name: &str) {
    check_compile_error(code, &format!("Unbound variable: '{name}'"));
}

/// A later parameter's annotation reads an earlier parameter, and a call is checked with each
/// earlier argument in its place.
#[rstest]
#[case::two(indoc::indoc! {r#"
    def f(a: Int, c: {Int where _ >= a}):
        c

    f(1, 5)
    "#}, 5)]
#[case::of_three(indoc::indoc! {r#"
    def f(a: Int, b: Int, c: {Int where _ >= b}):
        a + c

    f(1, 2, 3)
    "#}, 4)]
fn a_parameter_annotation_reads_an_earlier_parameter(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A function type names the parameters of its list, `(lo: Int, x: Int) => Int`, and is the
/// type `(Int, Int) => Int` (`docs/chl-spec.md`, "Parameter lists").
#[test]
fn a_function_type_names_its_parameters() {
    check_scalar(
        indoc::indoc! {r#"
            g: (lo: Int, x: Int) => Int = \lo, x -> lo + x
            h: (Int, Int) => Int = g
            h(1, 5)
        "#},
        Value::Int(6),
    );
}

/// A message writes a function of several parameters with the ones its types read named, as a
/// program writes the type.
#[test]
fn a_message_names_the_parameters_a_type_reads() {
    check_compile_error(
        indoc::indoc! {r#"
            def above(lo: Int, x: {Int where _ >= lo}) => {Int where _ >= lo}:
                x
            y: Int = above
            y
        "#},
        "inferred as (lo: Int, x: {Int where _ >= lo}) => {Int where _ >= lo}",
    );
}

/// A written dependent tuple holds a value whose later components have their types with the
/// earlier ones in place, and a projection reads the earlier components of what it projects
/// (`docs/chl-spec.md`, "Named components").
#[rstest]
#[case::a_literal(indoc::indoc! {r#"
    t: {(n: Int), {Int where _ > n}} = (1, 2)
    t.0 + t.1
    "#}, 3)]
#[case::a_projection_reads_the_earlier_component(indoc::indoc! {r#"
    p: {(a: Int), (b: {Int where _ >= a})} = (1, 5)
    r: {Int where _ >= p.0} = p.1
    r
    "#}, 5)]
#[case::an_open_tuple_holds_it(indoc::indoc! {r#"
    p: {(a: Int), (b: {Int where _ >= a})} = (1, 2)
    q <: {Int, ..} = p
    q.0
    "#}, 1)]
#[case::a_function_returns_it(indoc::indoc! {r#"
    def mk(a: {Int where _ >= 0}) => {(x: Int), (y: {Int where _ >= x})}:
        (0, a)
    mk(3).1
    "#}, 3)]
#[case::a_lambda_annotated_with_a_dependent_parameter_list(indoc::indoc! {r#"
    g: (lo: Int, x: {Int where _ >= lo}) => {Int where _ >= lo} = \lo, x -> x
    g(1, 5)
    "#}, 5)]
#[case::a_collection_keyed_by_dependent_positions(indoc::indoc! {r#"
    flat: {(i: _), (j: _)} |=> Int = [x for xs in [box([1, 2]), box([3])] for x in xs]
    sum(flat)
    "#}, 6)]
#[case::four_dependent_components(indoc! {r#"
    p: {(a: Int), (b: {Int where _ >= a}), (c: {Int where _ >= b}), (d: {Int where _ >= c})} = (1, 2, 3, 4)
    q: {Int where _ >= p.2} = p.3
    q
"#}, 4)]
#[case::a_whole_input_meets_a_dependent_component_contract(indoc! {r#"
    g: {(a: Int), (b: {Int where _ >= a})} => {Int where _ >= a} = \p: {(x: Int), (y: {Int where _ >= x})} -> p.1
    g((1, 5))
"#}, 5)]
#[case::components_meet_a_dependent_whole_input_contract(indoc! {r#"
    h: {(a: Int), (b: {Int where _ >= a})} => {Int where _ >= a} = \p: {(x: Int), (y: {Int where _ >= x})} -> p.1
    g: (p: {(a: Int), (b: {Int where _ >= a})}) => {Int where _ >= p.0} = h
    g((1, 5))
"#}, 5)]
fn a_written_dependent_tuple(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A value whose later component does not have its type with the earlier ones in place is
/// refused, and the message writes the annotation as the program did.
#[rstest]
#[case::a_literal(indoc::indoc! {r#"
    p: {(a: Int), (b: {Int where _ >= a})} = (5, 1)
    p.1
    "#})]
#[case::a_function_result(indoc::indoc! {r#"
    def mk(n: {Int where _ >= 0}) => {(a: Int), (b: {Int where _ >= a})}:
        (1, n)
    mk(3).1
    "#})]
fn a_value_outside_a_written_dependent_tuple_is_refused(#[case] code: &str) {
    check_compile_error(code, "annotated as {(a: Int), {Int where _ >= a}}");
}

/// An argument outside a type that reads an earlier parameter is refused at the call, the
/// earlier argument in the parameter's place.
#[rstest]
#[case::literal("f(5, 1)")]
#[case::a_named_tuple_s_components(indoc! {r#"
    pair = (5, 1)
    f(pair.0, pair.1)
"#})]
#[case::higher_order(indoc! {r#"
    def apply(fn, a, b):
        fn(a, b)
    apply(f, 5, 1)
"#})]
fn an_argument_outside_a_type_reading_an_earlier_parameter_is_refused(#[case] call: &str) {
    let definition = indoc! {r#"
        def f(a: Int, c: {Int where _ >= a}):
            c
    "#};
    check_compile_error(
        &format!("{definition}{call}"),
        "Type mismatch for this call",
    );
}

#[test]
fn refined_add() {
    check_scalar(
        indoc::indoc! {r#"
        z: {Int where _ == 1 + 3} = 1 ^+ 3
        ()"#},
        Value::Unit,
    )
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
/// refinement: `y` is `1 ^+ 3 ^+ 2`, which entails `_ == 1 + 5` without matching
/// it.
#[test]
fn a_let_chain_entails_the_result_annotation() {
    check_scalar(
        indoc! {r#"
            def foo(t: Int) => {Int where _ == 1 + 5}:
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
            def foo(t: {Int where _ == 1 + 5}):
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
/// `+` puts no refinement on its result, so `w`'s refinement `__elem == y + 0` meets the
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
/// rather than on the node. Unresolved, the variable encodes at an uninterpreted sort that
/// carries none of its bounds, so the scope resolves the scheme body before reading it as a fact.
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
/// its result to its argument, so the body's refinement holds the call term
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
        "inferred as {Int where _ == t ^+ y + bar(t)}",
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
        indoc::indoc! {r#"

            m: Map({String where _ != ""}, Int) = map([("a", 1), ("z", 2)])
            m
            "#},
        r#"Annotation mismatch: annotated as Map({String where _ != ""}, Int), but inferred as {String where _ in ["a", "z"]} |=> Int"#,
    )
}

#[test]
fn a_refined_map_key_in_a_mut_annotation_is_reported() {
    check_compile_error(
        indoc::indoc! {r#"

            m: Mut(Map({String where _ != ""}, Int)) := box(map([("a", 1), ("z", 2)]))
            m
            "#},
        r#"Type mismatch for collection annotation: expected Map({String where _ != ""}, _), found {String where _ in ["a", "z"]}"#,
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
def f(p) => {UInt where _ == p + p}:
    p ^+ p
f(1)
        "#},
        "Type mismatch for this call: expected UInt, found Int",
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
        "No Addable instance for `+`: operand 2 is String",
    )
}

/// The typecheck for uses of polymorphic functions occurs during Coalesce, under the binders
/// in scope at the use, so the solver reconciles `{_ == 4 ^+ 1}` with `{_ == a}`, which
/// structural equality cannot.
#[test]
fn monomorphization_check_is_smt() {
    check_scalar(
        indoc! {r#"
def f(x: Int):
    4 ^+ 1
a = f(1)
b: {Int where _ == a} = f(2)
a == b
        "#},
        Value::Bool(true),
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
        "Type mismatch for this call: expected {Int where _ == 2}, found {Int where _ == 1}",
    )
}

/// `a`'s refinement, `Int@2`, is what the specialization pin assumes of `a`, so `f(2)` meets
/// `{Int | __elem == a}`.
#[test]
fn dont_discharge_opaques_out_of_fun_bodies_with_a_singleton_codomain_named_by_an_annotation() {
    check_scalar(
        indoc! {r#"
def f(x: {Int where _ == 2}) => {Int where _ == 2}:
    r ^= x;
    r ^+ 0
a = f(2)
b: {Int where _ == a} = f(2)
a == b
        "#},
        Value::Bool(true),
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
        "this function's result type {Int where _ == r} => Int refines a parameter by `r`",
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

/// An annotation inside a body demanding something of a parameter or loop variable in terms of
/// a binder the body introduced panics: a read of the binder is its variable as-is, and that
/// variable stands where the binder is bound, outside the body. The demand lands on it naming
/// `y`, which nothing there binds (`src/ccl/design/type-inference.md`, "The invariant"). Both
/// programs run, `y` being one more than the value annotated, so the panic is a compiler gap.
#[rstest]
#[case::a_parameter(indoc! {r#"
    def f(x):
        y = x + 1
        z: {Int where _ < y} = x
        z
    f(3)
"#})]
#[case::a_loop_variable(indoc! {r#"
    total := 0
    for x in [1, 2, 3]:
        y = x + 1
        z: {Int where _ < y} = x
        total += z
    total
"#})]
fn a_demand_naming_a_body_binder_escapes_to_the_binder_variable(#[case] code: &str) {
    check_compile_error(code, "open bound recorded");
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

/// A refinement on a value computed from a read reaches planning stated over the value the
/// read took, which mutability elimination names: `y`'s `__elem == x + x` is `0 + 0` by then,
/// so the post-planning check compares it like any other.
#[test]
fn a_refinement_on_a_read_reaches_planning_over_the_value_read() {
    check_scalar(
        indoc! {r#"
x: Mut({Int where _ >= 0}) := 0
y = x ^+ x
z: {Int where _ >= 0} = y
z
        "#},
        Value::Int(0),
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

/// A lambda's parameter states its type as a `def`'s does: refined, bounded, a parenthesised
/// function type, and one of two parameters.
#[rstest]
#[case::refined(
    indoc! {r#"
        g = \x: {Int where _ > 0} -> x
        g(3)
    "#},
    Value::Int(3),
)]
#[case::bounded(
    indoc! {r#"
        g = \x <: Int -> x
        g(3)
    "#},
    Value::Int(3),
)]
#[case::a_function(
    indoc! {r#"
        g = \f: (Int => Int) -> f(1)
        g(\x -> x + 4)
    "#},
    Value::Int(5),
)]
#[case::one_of_two(
    indoc! {r#"
        g = \x: {Int where _ > 0}, y -> x + y
        g(2, 3)
    "#},
    Value::Int(5),
)]
fn a_lambda_parameter_states_its_type(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

#[test]
fn a_lambda_parameter_s_type_is_checked_at_the_argument() {
    check_compile_error(
        indoc! {r#"
            g = \x: {Int where _ > 0} -> x
            g(-1)
        "#},
        "expected {Int where _ > 0}, found {Int where _ == -1}",
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
        "expected {Int where _ > 0}, found {Int where _ == -1}",
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

/// The specialization pin decides a refinement under the binders in scope at the use, so a
/// predicate naming an enclosing binder (`n`) is discharged with what `n` is.
#[test]
fn a_use_meets_a_codomain_refinement_naming_an_enclosing_binder() {
    check_scalar(
        indoc! {r#"
            n = 2
            g: Int => {Int where _ > n} = \x -> 5
            g(3)
        "#},
        Value::Int(5),
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
        "post-inference produced an invalid tree: [Type mismatch for this call: expected {Int where _ > 0}, found Int]",
    );
}

/// An opaque `let`'s body type names an enclosing binder: the read of `x` types
/// `y` as `{Int | __elem == __anf + a}`, and meeting `z`'s annotation needs both
/// `__anf`'s refinement and the parameter `a`'s. Coalescing decides it under the
/// walk's lexical scope, which supplies `a`.
#[test]
fn an_opaque_let_body_entailed_under_an_enclosing_binder() {
    check_scalar(
        indoc! {r#"
            def f(a: {Int where _ >= 0}):
                x: Mut({Int where _ >= 0}) := 0
                y = x ^+ a
                z: {Int where _ >= 0} = y
                z

            f(1)
        "#},
        Value::Int(1),
    )
}

/// Two reads of a refined mutable variable meet a refined annotation: `y` is the opaque
/// `let __anf : {Int | __elem >= 0} ^= x in __anf ^+ __anf`, and its body type
/// `{Int | __elem == __anf + __anf}` entails `{Int | __elem >= 0}` given `__anf`'s
/// refinement.
#[test]
fn two_reads_of_a_refined_mut_meet_a_refined_annotation() {
    check_scalar(
        indoc! {r#"
            x: Mut({Int where _ >= 0}) := 0
            y = x ^+ x
            z: {Int where _ >= 0} = y
            z
        "#},
        Value::Int(0),
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

/// A `^+` in a comprehension element: the element's refinement holds the generator's own
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

/// Two operations between a comprehension element's mutable read and the element value.
#[test]
fn two_operations_on_a_mut_read_in_a_comprehension() {
    check_tile(
        indoc! {r#"
x := 3
ys = [x ^+ x ^+ i for i in [1,2]]
ys
        "#},
        make_int_list(&[7, 8]),
    )
}

/// A nested comprehension's element reads a mutable variable and both generators' binders.
#[test]
fn nested_comprehension_reading_a_mut() {
    check_sink(
        indoc! {r#"
x := 3
ys = [[x ^+ i ^+ j for j in [10,20]] for i in [1,2]]
out = test_sink()
out << ys
        "#},
        "[() -> [[14, 24], [15, 25]]]",
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

/// `(i: {Int | __elem >= 1 and __elem <= 5}) ⤇ {Int | __elem == i + 1}`: a collection
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
/// `emit_annotation_predicates` types the codomain's predicate opened, with `i` in scope at
/// the keys.
fn check_over_pi_typed_collection(body: Expr) {
    let mut expr = uniquify::run(Expr::lambda(
        "c",
        Occurrence::mint(),
        pi_typed_collection(),
        body,
    ));
    infer(&mut expr, &mut TypeInferenceContext::new())
        .unwrap_or_else(|errs| panic!("inference must succeed: {errs:?}"));
    typecheck(&expr).unwrap_or_else(|errs| panic!("the tree must type-check: {errs:?}"));
}

/// A parameter whose annotation is a Pi-typed collection, used bare: `λ c : 𝐶 → c`.
///
/// Nothing applies `c`, so the only predicate naming the binder `i` is the annotation's
/// own codomain refinement, which is in scope under the Pi that binds it.
///
/// The tree is built directly, its binder spelled `i` by name.
#[test]
fn a_pi_typed_collection_parameter() {
    check_over_pi_typed_collection(Expr::var("c"));
}

/// `collection_contains` applied to a Pi-typed collection: `λ c : 𝐶 → c ▷ collection_contains`.
///
/// No CHL spelling applies the builtin to a bare collection, so the tree is built directly.
///
/// The template's codomain variable is one type for every key, and the collection's codomain
/// refinement reads the Pi binder, so the variable's lower bound drops that refinement
/// (`src/ccl/design/type-inference.md`, "The invariant").
#[test]
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
#[test]
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
#[test]
fn dependent_function_composition() {
    let fc = Expr::lambda(
        "f1",
        Occurrence::mint(),
        Type::fun(Type::Base(BaseType::String), Type::Base(BaseType::Int)),
        Expr::compose(vec![
            Expr::var("f1"),
            Expr::lambda(
                "i",
                Occurrence::mint(),
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
            Expr::lambda("s", Occurrence::mint(), Type::Hole, Expr::lit(Lit::Int(1))),
            Expr::var("fc"),
        ),
    );
    let mut expr = uniquify::run(Expr::let_bind("fc", Occurrence::mint(), fc, call));
    infer(&mut expr, &mut TypeInferenceContext::new())
        .unwrap_or_else(|errs| panic!("inference must succeed: {errs:?}"));
    typecheck(&expr).unwrap_or_else(|errs| panic!("the tree must type-check: {errs:?}"));
}

/// TODO: Allow a comprehension over a collection whose elements read a mutable
/// variable.
///
/// The consuming element's refinement holds the producing comprehension whole,
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

/// A comprehension over a comprehension whose elements read a mutable variable: the inner
/// element's refinement names the read, and the outer element's names the inner's.
#[test]
fn nesting_a_comprehension_carries_mut_into_refinement() {
    check_tile(
        indoc! {r#"
x := 3
[y ^+ 1 for y in [x ^+ i for i in [1,2]]]
        "#},
        make_int_list(&[5, 6]),
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
        "Type mismatch for this call: expected {Int where _ > 0}, found {Int where _ == -5}",
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
        "──── Type mismatch for this call: expected {Int where _ > 0}, found {Int where _ == -5}",
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
        "──── Type mismatch for this call: expected {Int where _ > 0}, found {Int where _ == -5}",
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
        "this function's result type {Int where _ > 0 and r == r} => Int refines a parameter by `r`, which the function body binds opaquely; annotate the function's result type with a type that does not name `r`",
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
        "──── Type mismatch for this call: expected {Int where _ > 0}, found {Int where _ == -5}",
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

/// `x`'s base type is unsolved when the annotation on `f` is checked, so the solver reads `x`
/// at an uninterpreted sort, where `x == x` holds. The annotation is met, and the call that
/// passes `-5` is what fails.
#[test]
fn an_unsettled_base_type_is_checked_at_an_uninterpreted_sort() {
    check_compile_error(
        indoc! {r#"
def f(x) => ({Int where _ > 0} => Int):
    def k(y: {Int where _ > 0 and x == x}):
        1
    k
f1 = f(1)
f1(-5)
        "#},
        "Type mismatch for this call: expected {Int where _ > 0}, found {Int where _ == -5}",
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
#[case::a_plain_collection(indoc::indoc! {r#"
    xs: _ |=> Int = [1, 2, 3]
    sum(xs)"#}, 6)]
#[case::a_sum(indoc::indoc! {r#"
    xs: _ |=> Int = box([1, 2, 3])
    sum([x for x in xs])"#}, 6)]
#[case::a_parameter(
    indoc! {"
        def total(xs: _ |=> Int) => Int:
            sum([x for x in xs])
        total([1, 2]) + total(box([3, 4]))
    "},
    10
)]
// Two sums over different domains specialize the definition apart.
#[case::a_parameter_at_two_domains(
    indoc! {"
        def total(xs: _ |=> Int) => Int:
            sum([x for x in xs])
        total(box([1, 2])) + total(box([10, 20, 30]))
    "},
    63
)]
// A comprehension keyed by the source bound just ahead of the call: the definition's clone
// stands inside that binding, where its type is in scope.
#[case::a_comprehension_over_a_sum_passed_in(
    indoc! {"
        def total(xs: _ |=> Int) => Int:
            sum([x for x in xs])
        total([x + 1 for x in box([1, 2])])
    "},
    5
)]
#[case::a_filter_reading_a_let(
    indoc! {"
        n = 2
        def total(xs: _ |=> Int) => Int:
            sum([x for x in xs])
        total([x for x in [1, 2, 3] if x > n])
    "},
    3
)]
#[case::through_a_generic_identity(
    indoc! {"
        def ident(T, t: T) => T:
            t
        n = 2
        sum(ident([x for x in [1, 2, 3] if x > n]))
    "},
    3
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
#[case::a_codomain(indoc::indoc! {r#"
    f: Int => _ |=> Int = \n -> [n, n]
    sum(f(3))"#}, 6)]
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
    indoc::indoc! {r#"
        f: forall (D) (D |=> Int) => Int = \xs -> sum(xs)
        f([1, 2]) + f([3])"#},
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
    indoc::indoc! {r#"
        xs: Int |=> Int = box([1, 2])
        sum(xs)"#},
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
    indoc::indoc! {r#"
        f: forall (D) (D |=> Int) => Int = \xs -> sum(xs)
        f(box([1, 2]))"#},
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
    "Type mismatch for this call: expected {UInt where _ < 2}, found {UInt where _ < 3}",
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
    check_compile_error(
        indoc::indoc! {r#"
        x = Int |=> Int
        1"#},
        "`T |=> U` is a data-function *type*",
    );
}

/// `Option::some(v: T)` produces a value with type `{Option(T) where
/// (not _.is_none()) and _.value() == v}`, and `Option::none`
/// produces a value with type `{Option(T) where _.is_none()}`, with
/// no constraint on `_.value()` in that case.
///
/// The `o.unwrap_or(w)` method, for `o: Option(T1)` and `w: T2`, is a `match` over `o`, and
/// produces a value with the refinement that `match` derives from its arms, `{T3 where (not
/// o.is_none() and _ == o.value()) or (o.is_none() and _ == w)}`, where `T1 <: T3` and
/// `T2 <: T3`.
#[test]
fn unwrap_or_follows_the_option_constructor() {
    check_scalar(
        indoc! {r#"
x = Option::some(1)
y = Option::none
x1: {Int where _ == 1} = x.unwrap_or(2)
y1: {Int where _ == 2} = y.unwrap_or(2)
x1 == 1 and y1 == 2
        "#},
        Value::Bool(true),
    )
}

/// `unwrap_or`'s default need not have the option's payload type: the payload is `T1`, the
/// default `T2`, and the result `T3` lies above both.
#[rstest]
#[case::refined_payload_plain_default_none(
    indoc! {"
        def f(o: Option({Int where _ > 0}), d: Int) => Int:
            o.unwrap_or(d)
        f(Option::none, -3)
    "},
    Value::Int(-3),
)]
#[case::refined_payload_plain_default_some(
    indoc! {"
        def f(o: Option({Int where _ > 0}), d: Int) => Int:
            o.unwrap_or(d)
        f(Option::some(4), -3)
    "},
    Value::Int(4),
)]
#[case::bounded_payload(
    indoc! {"
        def f(T <: Int, o: Option(T), d: Int) => Int:
            o.unwrap_or(d)
        f(Option::some(4), 9)
    "},
    Value::Int(4),
)]
#[case::bounded_default(
    indoc! {"
        def f(T <: Int, o: Option(Int), d: T) => Int:
            o.unwrap_or(d)
        f(Option::none, 9)
    "},
    Value::Int(9),
)]
#[case::none_with_record_default(
    indoc! {"
        y = Option::none
        r = y.unwrap_or((a=5))
        r.a
    "},
    Value::Int(5),
)]
fn unwrap_or_default_differs_from_payload(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// `!` is a unary operator, acting as a function with type `(o:
/// {Option(T) where not _.is_none()}) => {T where _ == o.value()}`.
///
/// This test can only typecheck because `x` uses the `some`
/// constructor.
#[test]
fn unwrapping_some_meets_the_domain_refinement() {
    check_scalar(
        indoc! {r#"
x = Option::some(1)
x1: {Int where _ == 1} = x!
x1 == 1
        "#},
        Value::Bool(true),
    )
}

/// This test should fail to typecheck, because `!`'s domain
/// refinement is not satisfied.
#[test]
fn unwrapping_none_violates_the_domain_refinement() {
    check_compile_error(
        indoc! {r#"
x = Option::none
x1: {Int where _ == 1} = x!
x1 == 1
        "#},
        "where not _.is_none()}, found {Option(",
    )
}

/// A predicate's `.is_none()` and `.value()` state what the constructors' refinements state,
/// so the solver decides an annotation written with them.
#[rstest]
#[case::some_is_not_none(indoc! {"
    y: {Option(Int) where not _.is_none()} = Option::some(3)
    y.is_none()
"}, Value::Bool(false))]
#[case::none_is_none(indoc! {"
    y: {Option(Int) where _.is_none()} = Option::none
    y.is_none()
"}, Value::Bool(true))]
#[case::some_value(indoc! {"
    y: {Option(Int) where _.value() == 3} = Option::some(3)
    y.is_none()
"}, Value::Bool(false))]
#[case::parameter_unwrapped(indoc! {"
    def f(o: {Option(Int) where not _.is_none()}) => Int:
        o!
    f(Option::some(4))
"}, Value::Int(4))]
// A path names the same function a method call does, and a predicate reads it the same.
#[case::is_none_by_path(indoc! {"
    y: {Option(Int) where not Option::is_none(_)} = Option::some(3)
    y!
"}, Value::Int(3))]
#[case::value_by_path(indoc! {"
    y: {Option(Int) where Option::value(_) == 3} = Option::some(3)
    y.is_none()
"}, Value::Bool(false))]
fn an_option_meets_a_predicate_written_with_its_methods(
    #[case] code: &str,
    #[case] expected: Value,
) {
    check_scalar(code, expected);
}

/// The annotations of [`an_option_meets_a_predicate_written_with_its_methods`] refuse a value
/// their predicate does not hold of.
#[rstest]
#[case::none_is_not_some(
    indoc! {"
        y: {Option(Int) where not _.is_none()} = Option::none
        y.is_none()
    "},
    "Annotation mismatch",
)]
#[case::other_value(
    indoc! {"
        y: {Option(Int) where _.value() == 4} = Option::some(3)
        y.is_none()
    "},
    "Annotation mismatch",
)]
#[case::parameter_given_none(
    indoc! {"
        def f(o: {Option(Int) where not _.is_none()}) => Int:
            o!
        f(Option::none)
    "},
    "Type mismatch for this call: expected {Option(Int) where not _.is_none()}, found {Option(",
)]
// The derived refinement prints `Option`'s constructor tests as the method a predicate writes.
#[case::derived_refinement_printed(
    indoc! {"
        x: {Int where _ == 5} = Option::some(1).unwrap_or(2)
        x
    "},
    "not Option::some(1).is_none() and _ == Option::some(1).value()",
)]
fn an_option_violating_a_predicate_written_with_its_methods(
    #[case] code: &str,
    #[case] needle: &str,
) {
    check_compile_error(code, needle);
}

/// `unwrap_or` of an `Option::some` whose payload is computed. The result's refinement reads
/// `Option::some(a + 1)`, which `lambda_elim` rewrites to `Option::some((a, 1) ▷ add)`; the
/// constructor rule still reads `__elem ▷ ctor_payload(Option::some) == (a, 1) ▷ add` off it, so
/// the re-derived type matches the recorded one.
#[test]
fn unwrap_or_of_some_of_a_computed_value() {
    check_scalar(
        indoc! {"
            a = 5
            b = a + 1
            Option::some(b).unwrap_or(a)
        "},
        Value::Int(6),
    );
}

/// `Option::some(b)` with `b` computed rather than literal. Its type carries
/// `__elem ▷ ctor_payload(Option::some) == b`, which `lambda_elim` rewrites point-free.
#[rstest]
#[case::is_none(
    indoc! {"
        a = 5
        b = a + 1
        Option::some(b).is_none()
    "},
    Value::Bool(false),
)]
#[case::matched(
    indoc! {"
        a = 5
        b = a + 1
        match Option::some(b):
            case Option::some(v):
                v
            case Option::none:
                0
    "},
    Value::Int(6),
)]
fn some_of_a_computed_value(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// `b ^+ x` in a comprehension's element, with `b` computed. Its type carries
/// `__elem == b ^+ x`, which names `b` where the planned term reads `6 ▷ const`.
#[test]
fn refined_add_of_a_computed_value_in_a_comprehension() {
    check_scalar(
        indoc! {"
            a = 5
            b = a + 1
            xs = [1, 2]
            sum([b ^+ x for x in xs])
        "},
        Value::Int(15),
    );
}

/// `!` applied twice. The outer `Option::value`'s parameter is refined
/// `not (__elem ▷ ctor_is(Option::none))`, which the inner `!`'s result type entails.
#[test]
fn unwrap_of_an_unwrap() {
    check_scalar(
        indoc! {"
            x = Option::some(Option::some(1))
            x!!
        "},
        Value::Int(1),
    );
}

/// `!` of an `Option` whose annotation alone proves it `some`.
#[test]
fn unwrap_of_an_annotated_option() {
    check_scalar(
        indoc! {"
            y: {Option(Int) where not _.is_none()} = Option::some(3)
            y!
        "},
        Value::Int(3),
    );
}

/// `!` and `unwrap_or` in a comprehension's element.
#[rstest]
#[case::unwrap(
    indoc! {"
        xs = [1, 2]
        sum([Option::some(x)! for x in xs])
    "},
    3
)]
#[case::unwrap_or(
    indoc! {"
        xs = [1, 2]
        sum([Option::some(x).unwrap_or(0) for x in xs])
    "},
    3
)]
// The `match` `unwrap_or` is, written out. Its `none` arm reads only the outer binder, and its
// leg keeps the gate that restricts it to the `none` positions.
#[case::written_out(
    indoc! {"
        def f(o, d):
            match o:
                case Option::some(v):
                    v
                case Option::none:
                    d
        xs = [1, 2]
        sum([f(Option::some(x), 0) for x in xs])
    "},
    3
)]
// `o!` inside the arm that proves `o` is `some`: a one-arm `match o` nested in the outer `some`
// arm, whose leg projects the outer arm's tag before the inner one's.
#[case::in_an_arm(
    indoc! {"
        def f(o: Option(Int)) => Int:
            match o:
                case Option::some(v):
                    o! + v
                case Option::none:
                    0
        sum([f(Option::some(x)) for x in [1, 2]])
    "},
    6
)]
#[case::in_an_arm_of_mixed_options(
    indoc! {"
        def f(o: Option(Int)) => Int:
            match o:
                case Option::some(v):
                    o! + v
                case Option::none:
                    10
        def g(x: Int) => Option(Int):
            r = if x > 1:
                    Option::some(x)
                else:
                    Option::none
            r
        sum([f(g(x)) for x in [1, 2, 3]])
    "},
    20
)]
fn unwrap_in_a_comprehension(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A constructor states its payload whatever the payload's type. The refinement encoding reads
/// none of these payloads and drops what it states of them.
#[rstest]
#[case::string(indoc! {r#"
    x = Option::some("a")
    x.is_none()
"#})]
#[case::record("Option::some((a=1)).is_none()")]
#[case::tuple("Option::some((1, 2)).is_none()")]
fn a_payload_outside_the_encoding(#[case] code: &str) {
    check_scalar(code, Value::Bool(false));
}

/// `Option(T)` requires `Equatable(T, T)`, which a constructor states, so `Option::some` of a
/// payload with no `Equatable` instance is rejected where it is called.
#[rstest]
#[case::list("Option::some([1, 2]).is_none()")]
#[case::nominal(indoc! {"
    type W:
        w(Int)
    Option::some(W::w(1)).is_none()
"})]
fn a_payload_with_no_equatable_instance(#[case] code: &str) {
    check_compile_error(code, "No Equatable instance for this call");
}

/// `unit` is `Equatable`, which `Option(unit)`, a `Set`'s checked lookup, requires.
#[test]
fn unit_equals_unit() {
    check_scalar("() == ()", Value::Bool(true));
}

/// `!` of a `String` payload.
#[test]
fn unwrap_of_a_string_payload() {
    check_scalar(
        indoc! {r#"
            x = Option::some("a")
            x!
        "#},
        Value::String("a".into()),
    );
}

/// An arm knows which constructor built the value it matched, so `o!` holds in the `some` arm.
/// A default arm knows which constructors the arms before it name did not build it, so `o!`
/// holds in a `case _:` after `case Option::none:`.
#[rstest]
#[case::some_arm(indoc! {"
    def f(o: Option(Int)) => Int:
        match o:
            case Option::some(v):
                o!
            case Option::none:
                0
    f(Option::some(4))
"})]
#[case::default_arm(indoc! {"
    def f(o: Option(Int)) => Int:
        match o:
            case Option::none:
                0
            case _:
                o!
    f(Option::some(4))
"})]
fn unwrap_in_the_arm_that_matched_some(#[case] code: &str) {
    check_scalar(code, Value::Int(4));
}

/// A `match` needs no arm for a constructor the scrutinee's refinement rules out.
#[test]
fn an_arm_the_refinement_rules_out_is_omitted() {
    check_scalar(
        indoc! {"
            def f(o: {Option(Int) where not _.is_none()}) => Int:
                match o:
                    case Option::some(v):
                        v
            f(Option::some(4))
        "},
        Value::Int(4),
    );
}

/// An arm nothing rules out is required.
#[rstest]
#[case::unrefined(indoc! {"
    def f(o: Option(Int)) => Int:
        match o:
            case Option::some(v):
                v
    f(Option::some(4))
"})]
// What the payload's type states holds only of a value `some` built, so it does not rule `none`
// out: `none` is the one value of this type.
#[case::uninhabited_payload(indoc! {"
    def f(o: Option({Int where False})) => Int:
        match o:
            case Option::some(v):
                v
    f(Option::none)
"})]
fn an_arm_nothing_rules_out_is_required(#[case] code: &str) {
    check_compile_error(code, "has no arm for `Option::none`");
}

/// A predicate's `.is_none()` and `.value()` resolve by the receiver's type, so another type's
/// method of the same name does not change what they mean.
#[rstest]
#[case::is_none(indoc! {"
    type W = Int
    def W::is_none(self) => Bool:
        False
    y: {Option(Int) where not _.is_none()} = Option::some(3)
    y!
"})]
#[case::value(indoc! {"
    type W = Int
    def W::value(self) => Int:
        0
    y: {Option(Int) where _.value() == 3} = Option::some(3)
    y.unwrap_or(0)
"})]
fn another_types_method_of_the_same_name(#[case] code: &str) {
    check_scalar(code, Value::Int(3));
}

/// `f`'s parameter is inferred from both calls, so it admits `Option::none`, and `!`'s domain
/// refinement `not _.is_none()` rejects it.
#[test]
fn unwrapping_a_parameter_called_with_none_is_rejected() {
    check_compile_error(
        indoc! {r#"
def f(x):
    x1: {Int where _ == 1} = x!
    x1 == 1
f(Option::some(1)) == f(Option::none)
        "#},
        "Type mismatch for this call: expected {Option(Int) where not _.is_none()}, found {Option(",
    )
}

#[test]
fn anf_puts_lets_on_the_spine() {
    check_scalar(
        indoc! {r#"
f = \x -> x ^+ x
v: {Int where _ == 6} = f(1) ^+ f(2)
v
        "#},
        Value::Int(6),
    )
}

/// A function body's annotated `let` is peeled like the program's: the hoisted calls are in scope
/// at the annotation's check with their own refined types.
#[test]
fn anf_puts_lets_on_the_spine_in_a_function_body() {
    check_scalar(
        indoc! {r#"
f = \x -> x ^+ x
def g(y: Int):
    v: {Int where _ == 6} = f(1) ^+ f(2)
    v
g(0)
        "#},
        Value::Int(6),
    )
}

/// An output annotation is checked with the hoisted calls ahead of it on the spine.
#[test]
fn anf_puts_lets_on_the_spine_ahead_of_an_output_annotation() {
    check_scalar(
        indoc! {r#"
f = \x -> x ^+ x
def g(y: Int) => {Int where _ == 6}:
    f(1) ^+ f(2)
g(0)
        "#},
        Value::Int(6),
    )
}
