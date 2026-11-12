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

#[test]
fn a_join_labels_the_types_of_its_contributing_values() {
    let code = r#"[1, "a"]"#;
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let errors = compile_program(&mut ctx, &LoadedProgram::test(code), consumer)
        .err()
        .unwrap();
    let [CompileError::Infer { related, .. }] = errors.as_slice() else {
        panic!("{errors:?}")
    };
    let labels: Vec<_> = related
        .iter()
        .map(|(at, label)| (&code[at.start..at.end], label.as_str()))
        .collect();
    assert_eq!(
        labels,
        [
            ("1", "contributes {Int where _ == 1}"),
            (r#""a""#, r#"contributes {String where _ == "a"}"#)
        ]
    );
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

#[test]
fn long_copy_chains_keep_independently_narrowed_conflicts_distinct() {
    let mut code = indoc! {r#"
        def add(a, b):
            a + b
        alias0 = add
    "#}
    .to_owned();
    for n in 1..=12 {
        use std::fmt::Write;
        writeln!(code, "alias{n} = alias{}", n - 1).unwrap();
    }
    code.push_str(indoc! {r#"
        def left(x):
            (alias12(x, 1), alias12(x, "s"))
        def right(x):
            (alias12(x, 2), alias12(x, "t"))
        1
    "#});
    assert_eq!(
        underlined(&code),
        &[
            indoc! {r#"
            def left(x):
                (alias12(x, 1), alias12(x, "s"))
        "#},
            indoc! {r#"
            def right(x):
                (alias12(x, 2), alias12(x, "t"))
        "#},
        ]
    );
}

#[test]
fn a_carrier_of_two_conflicts_keeps_both_original_defects() {
    let code = indoc! {r#"
        def left(x):
            (x + 1, x + "s")
        def right(x):
            (x + 2, x + "t")
        def carrier(x):
            (left(x), right(x), x > 0)
        alias = carrier
        1
    "#};
    assert_eq!(
        underlined(code),
        &[
            indoc! {r#"
            def left(x):
                (x + 1, x + "s")
        "#},
            indoc! {r#"
            def right(x):
                (x + 2, x + "t")
        "#},
        ]
    );
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
        indoc! {r#"
            def f(a):
                (a + 1, a + "s")
        "#},
        indoc! {r#"
            def g(b):
                (b + 1, b + "s")
        "#},
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
    &["Int", r#"w + "t""#],
)]
#[case::equal_messages_at_different_sites_across_runs(
    indoc! {r#"
        x: Int = "s"
        y = x + "t"
        z = 1 + "u"
        (y, z)
    "#},
    &["Int", r#"1 + "u""#, r#"x + "t""#],
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
#[case::a_broken_definition_its_aliases_carry(
    indoc! {r#"
        def healthy(x: Int) => Int:
            x
        def broken(x):
            (x + 1, x + "s")
        def indirect(x):
            broken(x)
        alias = indirect
        1
    "#},
    &[indoc! {r#"
        def broken(x):
            (x + 1, x + "s")
    "#}],
)]
#[case::copies_narrowed_in_different_definitions_are_different_defects(
    indoc! {r#"
        def add(a, b):
            a + b
        def g(x):
            (add(x, 1), add(x, "s"))
        def h(x):
            (add(x, 2), add(x, "t"))
        1
    "#},
    &[
        indoc! {r#"
            def g(x):
                (add(x, 1), add(x, "s"))
        "#},
        indoc! {r#"
            def h(x):
                (add(x, 2), add(x, "t"))
        "#},
    ],
)]
#[case::a_carrier_adds_a_requirement_beside_an_existing_conflict(
    indoc! {r#"
        def broken(x):
            (x + 1, x + "s")
        def indirect(x):
            (broken(x), x > 0)
        1
    "#},
    &[indoc! {r#"
        def broken(x):
            (x + 1, x + "s")
    "#}],
)]
#[case::a_transitive_key_conflict_names_the_lookup(
    indoc! {r#"
        def healthy(x: Int) => Int:
            x
        m = map([(1, 10), (2, 20)])
        answer = m["nope"]
        y = [1, "a"]
        y
    "#},
    &[r#"m["nope"]"#, r#"[1, "a"]"#],
)]
fn each_defect_is_reported_past_a_failed_statement(#[case] code: &str, #[case] expected: &[&str]) {
    assert_eq!(underlined(code), expected);
}

#[test]
fn an_independent_defect_after_a_join_blamed_at_its_statement_is_reported() {
    let got = underlined(indoc! {r#"
        xs = [(1, 2), ("a", 2)]
        def id(v):
            v
        x = id((sku=1))
        y = x.at
        (xs, y)
    "#});
    assert!(got.iter().any(|u| u == "x.at"), "{got:?}");
}

#[test]
fn an_unresolved_method_call_hides_no_later_join() {
    let got = underlined(indoc! {r#"
        type Price = Int
        def Price::cents(self) => Int:
            Price::extract(self)
        p = nope
        q = p.cents()
        w = [1, "a"]
        w
    "#});
    assert!(got.iter().any(|u| u == "nope"), "{got:?}");
    assert!(got.iter().any(|u| u == r#"[1, "a"]"#), "{got:?}");
}

#[test]
fn an_unresolved_method_call_hides_no_operand_conflict() {
    let got = underlined(indoc! {r#"
        type Price = Int
        def Price::cents(self) => Int:
            Price::extract(self)
        def bad(x):
            (Price::new(1), x + 1, x + "s")
        q = bad(2).0.cents()
        q
    "#});
    assert!(got.iter().any(|u| u.starts_with("def bad(x):")), "{got:?}");
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
                CompileError::Parse(_) => "parse",
                CompileError::Lower(_) => "lower",
                CompileError::Infer { .. } => "infer",
                _ => panic!("expected only parse, lowering and inference errors, got {errs:?}"),
            };
            let span = e
                .span()
                .expect("a parse, lowering or inference error has a span");
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

#[rstest]
#[case::exact(indoc! {r#"
    x: Int = m::y
    w = x + "s"
    (w, 1)
"#}, &[r#"x + "s""#])]
#[case::bounded(indoc! {r#"
    x <: Int = m::y
    w = x + "s"
    (w, 1)
"#}, &["x", r#"x + "s""#])]
#[case::partial(indoc! {r#"
    x: {Int, _} = m::y
    w = x.0 + "s"
    (w, 1)
"#}, &[r#"x.0 + "s""#])]
#[case::mutable(indoc! {r#"
    x: Mut(Int) := m::y
    x := "s"
    x
"#}, &[r#"x := "s""#])]
fn a_lowering_failure_preserves_declared_constraints(
    #[case] code: &str,
    #[case] expected: &[&str],
) {
    let got = underlined_by_phase(code);
    assert!(got.iter().any(|(phase, _)| *phase == "lower"), "{got:?}");
    assert!(
        got.iter()
            .any(|(phase, span)| *phase == "infer" && expected.contains(&span.as_str())),
        "{got:?}"
    );
}

#[test]
fn an_annotation_lowering_cannot_read_establishes_no_constraint() {
    let got = underlined_by_phase(indoc! {r#"
        x: Nope = 3
        w = x + "s"
        z = [1, "a"]
        (w, z)
    "#});
    let inferred: Vec<_> = got
        .iter()
        .filter(|(phase, _)| *phase == "infer")
        .map(|(_, span)| span.as_str())
        .collect();
    assert_eq!(inferred, vec![r#"[1, "a"]"#], "{got:?}");
    assert!(got.iter().any(|(phase, _)| *phase == "lower"), "{got:?}");
}

#[rstest]
#[case(cambra::ccl::context::Phase::Anf)]
#[case(cambra::ccl::context::Phase::MutRead)]
#[case(cambra::ccl::context::Phase::Comprehension)]
#[case(cambra::ccl::context::Phase::OpaqueOutput)]
fn a_lowering_failure_respects_a_stop_before_inference(#[case] stop: cambra::ccl::context::Phase) {
    let program = LoadedProgram::test(indoc! {r#"
        x: Int = m::y
        w = [1, "a"]
        w
    "#});
    let got = GlobalContext::default()
        .sources_and_sinks()
        .compile_to(&program, stop)
        .unwrap_err();
    assert!(
        got.iter().any(|e| matches!(e, CompileError::Lower(_))),
        "{got:?}"
    );
    assert!(
        !got.iter().any(|e| matches!(e, CompileError::Infer { .. })),
        "{got:?}"
    );
}

/// An unreadable sub-expression fails its statement before inference reads its values.
#[rstest]
#[case::joined_comprehension(indoc! {r#"
    users = [(id=1, name="alice"), (id=, name="bob")]
    orders = [(user_id=1, amount=50)]
    [(customer=u.name, total=o.amount) for u in users for o in orders if u.id == o.user_id]
"#})]
#[case::groupby(indoc! {r#"
    users = [(id=1, name="alice"), (id=, name="bob")]
    groupby(users, \u -> u.id)
"#})]
fn an_unreadable_list_element_reports_only_its_parse_error(#[case] code: &str) {
    let phases: Vec<_> = underlined_by_phase(code)
        .into_iter()
        .map(|(phase, _)| phase)
        .collect();
    assert_eq!(phases, ["parse"]);
}

#[test]
fn an_unreadable_list_element_hides_no_independent_join() {
    let got = underlined_by_phase(indoc! {r#"
        users = [(id=1, name="alice"), (id=, name="bob")]
        bad = [1, "s"]
        bad
    "#});
    assert!(got.iter().any(|(phase, _)| *phase == "parse"), "{got:?}");
    assert!(
        got.iter()
            .any(|(phase, span)| *phase == "infer" && span == r#"[1, "s"]"#),
        "{got:?}"
    );
}

/// The mutability rules are inference's, so a type error elsewhere hides none of them
/// (`src/ccl/design/mutability.md`, "No aliasing: `Mut` values are second-class
/// (downward-only)").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_write_to_a_value(
    indoc! {r#"
        x = 0
        x += 1
        y = [1, "a"]
        (x, y)
    "#},
    &["x += 1", r#"[1, "a"]"#],
)]
#[case::a_value_passed_by_reference(
    indoc! {r#"
        def bump(c: Mut(Int)):
            c += 1
        x = 1
        bump(x)
        y = [1, "a"]
        y
    "#},
    &["x", r#"[1, "a"]"#],
)]
#[case::a_function_returning_a_mutable_variable(
    indoc! {r#"
        x := 0
        f = \z -> x
        y = [1, "a"]
        (f, y)
    "#},
    &[r#"[1, "a"]"#, r"\z -> x"],
)]
fn a_mutability_error_is_reported_with_type_errors(#[case] code: &str, #[case] expected: &[&str]) {
    assert_eq!(underlined(code), expected);
}

/// A statement the parser could not read hides no inference error elsewhere: it binds the
/// names its head does, as a poison, and nothing reports it again
/// (`chl-parser/design-chl-parser.md`, "Threading partial ASTs through to lowering").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_join_past_a_broken_binding(
    indoc! {r#"
        x = 1 +* 2
        z = x + 1
        w = [1, "a"]
        (z, w)
    "#},
    &[("parse", "*"), ("infer", r#"[1, "a"]"#)],
)]
#[case::a_join_past_a_broken_function_header(
    indoc! {r#"
        def f(a:
            a
        w = [1, "a"]
        (f(1), w)
    "#},
    &[("parse", "("), ("infer", r#"[1, "a"]"#)],
)]
#[case::a_join_past_a_broken_bracket(
    indoc! {r#"
        x = (1 + ]
        y = x + 1
        w = [1, "a"]
        (y, w)
    "#},
    &[("parse", "]"), ("infer", r#"[1, "a"]"#)],
)]
// A declaration states its types in full, so one it cannot read fails it, and only the
// lexer reports it.
#[case::a_declaration_with_a_broken_type(
    indoc! {"
        type Price = {Int where _ >
        p = Price::new(3)
        p
    "},
    &[("parse", "{")],
)]
#[case::a_loop_with_a_broken_statement(
    indoc! {r#"
        total := 0
        for x in [1, 2]:
            total +=
        w = [1, "a"]
        (total, w)
    "#},
    &[("parse", "\n"), ("infer", r#"[1, "a"]"#)],
)]
// A `run` cut off after its `as` binds a module name no one can read, which a qualifier
// may be.
#[case::a_join_past_a_run_cut_off_before_its_name(
    indoc! {r#"
        run nothere as
        z = a::x + 1
        w = [1, "a"]
        (z, w)
    "#},
    &[("parse", "\n"), ("infer", r#"[1, "a"]"#)],
)]
#[case::an_await_of_a_broken_declaration(
    indoc! {"
        pool: M$ut(Int, Txn) := 100
        await_final(pool)
    "},
    &[("parse", "$")],
)]
fn inference_runs_past_a_statement_the_parser_could_not_read(
    #[case] code: &str,
    #[case] expected: &[(&str, &str)],
) {
    let expected: Vec<(&str, String)> = expected.iter().map(|(p, s)| (*p, s.to_string())).collect();
    assert_eq!(underlined_by_phase(code), expected);
}

#[test]
fn unreadable_names_do_not_escape_their_block() {
    let code = indoc! {"
        def first(x: Int):
            await_final(x)
        def second(dummy):
            x = 1 +* 2
            1
        1
    "};
    let reports = underlined_by_phase(code);
    assert_eq!(
        reports.iter().map(|(phase, _)| *phase).collect::<Vec<_>>(),
        ["parse", "lower"],
        "{reports:?}"
    );
}

#[test]
fn an_unreadable_module_alias_does_not_escape_its_block() {
    let code = indoc! {"
        def first(dummy):
            absent::value
        def second(dummy):
            run absent as
            1
        1
    "};
    let reports = underlined_by_phase(code);
    assert_eq!(
        reports.iter().map(|(phase, _)| *phase).collect::<Vec<_>>(),
        ["parse", "lower"],
        "{reports:?}"
    );
}
