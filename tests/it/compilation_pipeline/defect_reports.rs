//! One report per defect (`src/ccl/design/diagnostics.md`, "One report per defect").
//!
//! A defect is reported once, at the first node inference meets it at, however many nodes
//! carry it on; two sites that fail alike are two reports, and so is each use of a generic
//! definition that fails.

use std::time::Duration;

use cambra::ccl::context::{CompileError, GlobalContext, compile_program};
use cambra::ccl::load::LoadedProgram;
use cambra::interpreter::Consumer;
use indoc::indoc;
use rstest_log::rstest;

/// Compile `code`, expect only inference errors, and return the source text each one
/// underlines, in report order.
fn underlined(code: &str) -> Vec<String> {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let program = LoadedProgram::test(code);
    let Err(errs) = compile_program(&mut ctx, &program, consumer) else {
        panic!("expected a compile error, but the program compiled");
    };
    errs.iter()
        .map(|e| {
            let CompileError::Infer { span, .. } = e else {
                panic!("expected only inference errors, got {errs:?}");
            };
            code[span.start..span.end].to_string()
        })
        .collect()
}

#[rstest]
#[timeout(Duration::from_secs(10))]
// The binding, each use and the tuple read the literal's failing position.
#[case::a_join_and_the_values_built_from_it(
    indoc! {r#"
        x = [1, "a"]
        y = [x, x]
        (x, y)
    "#},
    &[r#"[1, "a"]"#],
)]
#[case::two_joins_failing_alike(
    indoc! {r#"
        x = [1, "a"]
        z = [2, "b"]
        (x, z)
    "#},
    &[r#"[1, "a"]"#, r#"[2, "b"]"#],
)]
#[case::two_width_conflicts(
    indoc! {"
        x = [(1, 2), (1, 2, 3)]
        z = [(3, 4), (3, 4, 5)]
        (x, z)
    "},
    &["[(1, 2), (1, 2, 3)]", "[(3, 4), (3, 4, 5)]"],
)]
#[case::each_use_failing_a_definition(
    indoc! {r#"
        def f(c, a, b):
            [a, b]
        (f(True, 1, "x"), f(False, 2, "y"))
    "#},
    &["f", "f"],
)]
// Both reads of `r` and the function read one failing position.
#[case::a_parameter_read_two_ways(
    indoc! {"
        def g(r):
            (r.0, r.foo)
        1
    "},
    &["r"],
)]
#[case::two_definitions_failing_alike(
    indoc! {"
        def g(r):
            (r.0, r.foo)
        def h(r):
            (r.0, r.foo)
        1
    "},
    &["r", "r"],
)]
// `inner` is walked once in each of `outer`'s specializations and once in its check alone.
#[case::a_dead_definition_in_a_generic_one(
    indoc! {r#"
        def outer(a):
            def inner(b):
                b + "s" + 1
            a + 1
        outer(1) + outer(2)
    "#},
    &[r#"b + "s" + 1"#],
)]
// Every node holding the conditional's collection meets its two domains.
#[case::a_domain_join_and_the_nodes_holding_it(
    indoc! {"
        c: Bool = True
        xs = [y * 10 for y in box([1, 2])] if c else [z * 100 for z in box([1, 2, 3])]
        xs
    "},
    &["[y * 10 for y in box([1, 2])] if c else [z * 100 for z in box([1, 2, 3])]"],
)]
// Each function's escape is reported at that function, not at the program's first statement.
#[case::two_functions_whose_results_escape(
    indoc! {"
        z = 1
        def f(x: Int):
            r ^= x
            def k(y: {Int where _ > 0 and r == r}):
                y
            k
        f1 = f(1)
        def g(x: Int):
            r ^= x
            def k(y: {Int where _ > 0 and r == r}):
                y
            k
        g1 = g(1)
        (f1(-5), g1(-5))
    "},
    &[
        indoc! {"
            def f(x: Int):
                r ^= x
                def k(y: {Int where _ > 0 and r == r}):
                    y
                k
        "},
        indoc! {"
            def g(x: Int):
                r ^= x
                def k(y: {Int where _ > 0 and r == r}):
                    y
                k
        "},
    ],
)]
// The comprehension's element reaches its binder through `Iterable`'s instance, as a copy of
// the list's element bounds, born at the literal.
#[case::a_join_comprehensions_read(
    indoc! {r#"
        x = [1, "a"]
        y = [v for v in x]
        z = [v for v in x]
        (y, z)
    "#},
    &[r#"[1, "a"]"#],
)]
// Each call's result holds copies of the arguments the parameter joined.
#[case::a_function_called_at_two_types(
    indoc! {r#"
        pair = (\x -> x, 1)
        g = pair.0
        (g(1), g("s"), g(2), g("t"))
    "#},
    &[r"\x -> x"],
)]
// `a` and `b` have concrete types, so each list's element bounds are born at that list.
#[case::two_joins_of_the_same_values(
    indoc! {r#"
        a = 1
        b = "s"
        x = [a, b]
        z = [a, b]
        (x, z)
    "#},
    &["[a, b]", "[a, b]"],
)]
// The projection's domain holds the join's tuples beside its own demand.
#[case::a_width_conflict_a_projection_reads(
    indoc! {"
        c = 1 > 0
        x = (1, 2) if c else (1, 2, 3)
        x.0
    "},
    &["(1, 2) if c else (1, 2, 3)"],
)]
// `box` and its call hold the one collection the annotation does not admit.
#[case::a_collection_outside_its_annotated_kind(
    indoc! {"
        xs = box([1, 2, 3])
        ys: List(Int) = box([x for x in xs if x > 1])
        sum(ys)
    "},
    &["box"],
)]
#[case::an_undetermined_parameter_and_its_uses(
    indoc! {r"
        f = \x -> [x, x]
        f
    "},
    &["x"],
)]
#[case::a_function_returning_a_mutable_variable(
    indoc! {r"
        x := 0
        f = \z -> x
        f
    "},
    &[r"\z -> x"],
)]
// A use failing at a value the join holds is the join's defect met downstream.
#[case::a_join_and_a_use_failing_at_one_of_its_values(
    indoc! {r#"
        xs = [1, "a"]
        ys = [x + 1 for x in xs]
        ys
    "#},
    &[r#"[1, "a"]"#],
)]
#[case::a_join_and_two_uses_failing_at_its_values(
    indoc! {r#"
        xs = [1, "a"]
        ys = [x ++ "b" for x in xs]
        zs = [x + 1 for x in xs]
        (ys, zs)
    "#},
    &[r#"[1, "a"]"#],
)]
fn a_defect_is_reported_once_per_site(#[case] code: &str, #[case] expected: &[&str]) {
    assert_eq!(underlined(code), expected);
}

/// A failed statement hides no defect elsewhere: inference starts over without it, and what
/// that run finds is reported too, but for a type nothing determines
/// (`src/ccl/design/type-inference.md`, "An error stops its statement, not the pass").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_join_past_an_unbound_name(
    indoc! {r#"
        x = undefined_name + 1
        y = [1, "a"]
        y
    "#},
    &["undefined_name", r#"[1, "a"]"#],
)]
// The list's element type is what the failed statement would have fixed.
#[case::a_value_only_the_failed_statement_determines(
    indoc! {"
        xs = []
        z = xs ++ nope
        xs
    "},
    &["nope"],
)]
#[case::each_definition_no_type_satisfies(
    indoc! {r#"
        def f(a):
            (a + 1, a + "s")
        def g(b):
            (b + 1, b + "s")
        1
    "#},
    &[
        "def f(a):\n    (a + 1, a + \"s\")\n",
        "def g(b):\n    (b + 1, b + \"s\")\n",
    ],
)]
// A barrier check's failure leaves its statement out as an emission error does.
#[case::a_join_past_an_annotation_an_opaque_result_fails(
    indoc! {r#"
        def f(x: Int):
            r ^= x;
            r ^+ 0
        a = f(1)
        b: {Int where _ == a} = f(2)
        y = [1, "a"]
        (a == b, y)
    "#},
    &["b: {Int where _ == a} = f(2)", r#"[1, "a"]"#],
)]
// The binding keeps its declared type over a definition that failed.
#[case::a_use_against_a_declared_type(
    indoc! {r#"
        w: Int = "s"
        v = w + "t"
        v
    "#},
    &[r#"w: Int = "s""#, r#"w + "t""#],
)]
// The annotation fails without the definition too, so the second run leaves it out.
#[case::a_join_past_a_result_annotation_that_fails(
    indoc! {r#"
        def f(x: Int) => {Int where _ == r}:
            x
        y = [1, "a"]
        y
    "#},
    &["r", r#"[1, "a"]"#],
)]
// The function's result is the binding left out, which nothing determines.
#[case::a_failed_binding_under_an_opaque_one(
    indoc! {"
        def f(x: Int):
            r ^= x
            def k(y: {Int where _ > 0 and r == r}):
                nope
            k
        f1 = f(1)
        f1(-5)
    "},
    &["nope"],
)]
fn each_defect_is_reported_past_a_failed_statement(#[case] code: &str, #[case] expected: &[&str]) {
    assert_eq!(underlined(code), expected);
}

/// Compile `code` and return each error's phase and the source text it underlines, in
/// report order.
fn underlined_by_phase(code: &str) -> Vec<(&'static str, String)> {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let program = LoadedProgram::test(code);
    let Err(errs) = compile_program(&mut ctx, &program, consumer) else {
        panic!("expected a compile error, but the program compiled");
    };
    errs.iter()
        .map(|e| {
            let phase = match e {
                CompileError::Lower(_) => "lower",
                CompileError::Infer { .. } => "infer",
                _ => panic!("expected only lowering and inference errors, got {errs:?}"),
            };
            let span = e.span().expect("a lowering or inference error has a span");
            (phase, code[span.start..span.end].to_string())
        })
        .collect()
}

/// A statement lowering fails in hides no inference error elsewhere, and its names are bound
/// at a poison, so their uses report nothing (`src/ccl/design/type-inference.md`, "An error
/// stops its statement, not the pass").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_join_past_a_failed_binding(
    indoc! {r#"
        x: Mut(Int) = 3
        y = [1, "a"]
        z = x + 1
        y
    "#},
    &[("lower", "x: Mut(Int) = 3"), ("infer", r#"[1, "a"]"#)],
)]
#[case::a_join_past_a_failed_function(
    indoc! {r#"
        def f(a):
            pass
        y = [1, "a"]
        f(1)
    "#},
    &[("lower", "pass"), ("infer", r#"[1, "a"]"#)],
)]
#[case::a_join_past_a_failed_last_statement(
    indoc! {r#"
        y = [1, "a"]
        x: Mut(Int) = 3
    "#},
    &[("lower", "x: Mut(Int) = 3"), ("infer", r#"[1, "a"]"#)],
)]
fn inference_runs_past_a_statement_lowering_failed_in(
    #[case] code: &str,
    #[case] expected: &[(&str, &str)],
) {
    let expected: Vec<(&str, String)> = expected.iter().map(|(p, s)| (*p, s.to_string())).collect();
    assert_eq!(underlined_by_phase(code), expected);
}
