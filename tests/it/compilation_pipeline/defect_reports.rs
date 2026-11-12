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
#[case::two_undetermined_parameters(
    indoc! {r"
        f = \x -> \y -> (x, y)
        f
    "},
    &["x", "y"],
)]
#[case::a_function_returning_a_mutable_variable(
    indoc! {r"
        x := 0
        f = \z -> x
        f
    "},
    &[r"\z -> x"],
)]
fn a_defect_is_reported_once_per_site(#[case] code: &str, #[case] expected: &[&str]) {
    assert_eq!(underlined(code), expected);
}
