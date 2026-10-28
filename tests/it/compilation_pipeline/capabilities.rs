//! What a function requires and causes, as inference collects it and a module's interface
//! prints it (`docs/chl-spec.md`, "6.9 Capabilities";
//! `src/ccl/design/type-inference.md`, "Capability variables").

use std::time::Duration;

use cambra::ccl::context::{GlobalContext, check_program};
use indoc::indoc;
use rstest_log::rstest;

use super::modules::program;

/// The members the cases below share: a transactional mutable variable, a feed, a function
/// that commits a transaction, and a higher-order function.
const PRELUDE: &str = indoc! {"
    stock: Mut(Int, Txn) := 10
    out: Feed(_)

    pub def take(n: Int):
        with begin():
            stock := stock - n

    def apply(f, x):
        f(x)
"};

/// The interface `code`, checked as a module, prints.
fn interface_of(code: &str) -> String {
    check_program(&mut GlobalContext::default(), &program(code, &[]))
        .unwrap_or_else(|errors| panic!("{errors:?}"))
}

/// The errors checking `code` as a module reports, rendered.
fn errors_of(code: &str) -> String {
    match check_program(&mut GlobalContext::default(), &program(code, &[])) {
        Ok(interface) => panic!("expected an error, got:\n{interface}"),
        Err(errors) => format!("{errors:?}"),
    }
}

/// The clauses after the codomain of `member`'s contract, as `cambra check` prints it: from its
/// `requires` or, without one, its `causes`. A parameter's or a codomain's own clauses are in
/// parentheses, so the contract's are the first outside every bracket.
fn clauses_of(code: &str, member: &str) -> String {
    let interface = interface_of(&format!("{PRELUDE}\n{code}"));
    let prefix = format!("pub {member}: ");
    let line = interface
        .lines()
        .find(|l| l.starts_with(&prefix))
        .unwrap_or_else(|| panic!("no `{member}` in the interface:\n{interface}"));
    let mut depth = 0usize;
    for (at, c) in line.char_indices() {
        match c {
            '(' | '{' | '[' => depth += 1,
            ')' | '}' | ']' => depth -= 1,
            ' ' if depth == 0
                && (line[at..].starts_with(" requires ") || line[at..].starts_with(" causes ")) =>
            {
                return line[at + 1..].to_owned();
            }
            _ => {}
        }
    }
    String::new()
}

#[rstest]
#[timeout(Duration::from_secs(10))]
// A `with begin():` block commits, and its write names the variable it writes.
#[case(
    "",
    "take",
    "requires ReadTxn(stock) causes WriteTxn(stock), RunTransaction"
)]
// A feed names the feed it appends to.
#[case(
    indoc! {"
        pub def report(n: Int):
            out << n
    "},
    "report",
    "causes Append(out)"
)]
// A call does what its callee does.
#[case(
    indoc! {"
        pub def twice(n: Int):
            take(n)
            take(n)
    "},
    "twice",
    "requires ReadTxn(stock) causes WriteTxn(stock), RunTransaction"
)]
// A loop body runs where the loop stands, and so does a comprehension's element.
#[case(
    indoc! {"
        pub def report_all(xs):
            for x in xs:
                out << x
    "},
    "report_all",
    "requires r: Iterable(A), r::Elements <: C causes Append(out)"
)]
#[case(
    indoc! {"
        pub def take_listed(xs):
            [take(x) for x in xs]
    "},
    "take_listed",
    "requires r: Iterable(A), r::Elements <: C, ReadTxn(stock) causes WriteTxn(stock), RunTransaction"
)]
// Each use of a polymorphic function collects its own capabilities, so a call that passes it a
// committing function commits and one that passes it a pure function does not.
#[case(
    indoc! {"
        pub def committing_use(x: Int):
            apply(take, x)
    "},
    "committing_use",
    "requires ReadTxn(stock) causes WriteTxn(stock), RunTransaction"
)]
#[case(
    indoc! {"
        pub def committing_use(x: Int):
            apply(take, x)
        pub def pure_use(x: Int):
            apply(\\y -> y + 1, x)
    "},
    "pure_use",
    ""
)]
// A variable a function's body binds is the function's own, so writing it is no effect of
// the function's.
#[case(
    indoc! {"
        pub def total(xs):
            t := 0
            for x in xs:
                t += x
            t
    "},
    "total",
    "requires r: Iterable(A), r::Elements <: B, r1: Addable(Int, C), r1::Output <: Int"
)]
#[case(
    indoc! {"
        pub def local_feed(xs):
            g: Feed(_)
            for x in xs:
                g << x
            sum(g)
    "},
    "local_feed",
    "requires r: Iterable(A), r::Elements <: B"
)]
// A `Mut` parameter's history is its argument's, so the call writes the argument: the
// caller's own variable here, which is no effect of the caller's…
#[case(
    indoc! {"
        def inc(x: Mut(Int)):
            x += 1
        pub def counted(xs):
            c := 0
            for x in xs:
                inc(c)
            c
    "},
    "counted",
    "requires r: Iterable(A), r::Elements <: B"
)]
// …and a transactional variable there, which is.
#[case(
    indoc! {"
        def bump(x: Mut(Int, Txn)):
            with begin():
                x += 1
        pub def bump_stock(n: Int):
            bump(stock)
    "},
    "bump_stock",
    "requires ReadTxn(stock) causes WriteTxn(stock), RunTransaction"
)]
// A read of an induction variable the function does not bind requires it.
#[case(
    indoc! {"
        cnt := 0
        for x in [1, 2]:
            cnt += x
        pub def peek(n: Int) => Int:
            cnt + n
    "},
    "peek",
    "requires Read(cnt)"
)]
fn a_contract_states_what_the_function_causes(
    #[case] code: &str,
    #[case] member: &str,
    #[case] expected: &str,
) {
    assert_eq!(clauses_of(code, member), expected);
}

/// A function type with clauses is parenthesized where another type follows it, in a tuple, or
/// where clauses after it would read as its own: those of an arrow whose codomain it is.
#[rstest]
#[case::a_codomain(
    indoc! {"
        pub def make(n: Int):
            out << n
            take
    "},
    "pub make: Int => (Int => {} requires ReadTxn(stock) causes WriteTxn(stock), \
     RunTransaction) causes Append(out)"
)]
#[case::a_tuple_component(
    indoc! {"
        pub def pair(n: Int):
            (take, n)
    "},
    "pub pair: Int => {(Int => {} requires ReadTxn(stock) causes WriteTxn(stock), \
     RunTransaction), Int}"
)]
fn a_function_type_with_clauses_is_parenthesized(#[case] code: &str, #[case] line: &str) {
    let interface = interface_of(&format!("{PRELUDE}\n{code}"));
    assert!(interface.lines().any(|l| l == line), "{interface}");
}

/// A feed reached through a second name is not tracked: a capability is keyed by the name it is
/// recorded through, and a feed handle, unlike a `Mut` one, is a value that travels
/// (`src/ccl/design/type-inference.md`, "4.9 Capabilities"). These pin the current output, which
/// names the parameter, the alias and the projection, where each should be `Append(out)`; the
/// mutability redesign decides how a feed travels.
#[rstest]
#[case::an_unannotated_parameter(
    indoc! {"
        def emit(o, v: Int):
            o << v
        pub def emit_out(v: Int):
            emit(out, v)
    "},
    "emit_out",
    "causes Append(o)"
)]
#[case::an_alias(
    indoc! {"
        pub def via_alias(v: Int):
            log: Feed(_) = out
            log << v
    "},
    "via_alias",
    "causes Append(log)"
)]
#[case::a_projection(
    indoc! {"
        pub def via_tuple(v: Int):
            p = (out, v)
            q = p.0
            q << v
    "},
    "via_tuple",
    "causes Append(q)"
)]
// An annotated parameter is tracked: its capability is its argument's.
#[case::an_annotated_parameter(
    indoc! {"
        def emit(o: Feed(Int), v: Int):
            o << v
        pub def emit_out(v: Int):
            emit(out, v)
    "},
    "emit_out",
    "causes Append(out)"
)]
fn a_feed_reached_through_another_name(
    #[case] code: &str,
    #[case] member: &str,
    #[case] expected: &str,
) {
    assert_eq!(clauses_of(code, member), expected);
}

/// A transactional variable belongs to the run, so it is declared at a module's top level
/// (`docs/chl-spec.md`, "Discharging requirements and effects").
#[rstest]
#[case::in_a_def(
    indoc! {"
        pub def scratch(n: Int) => Int:
            c: Mut(Int, Txn) := 0
            with begin():
                c := c + n
            n
    "},
    "`c` is a transactional mutable variable, which belongs to the run, so it is declared at a \
     module's top level"
)]
#[case::in_a_branch(
    indoc! {"
        if True:
            c: Mut(Int, Txn) := 0
            with begin():
                c := 1
            await_final(c)
        else:
            0
    "},
    "`c` is a transactional mutable variable, which belongs to the run"
)]
#[case::in_a_match_arm(
    indoc! {"
        match `some(1):
            case `some(n):
                c: Mut(Int, Txn) := 0
                with begin():
                    c := n
                await_final(c)
    "},
    "`c` is a transactional mutable variable, which belongs to the run"
)]
fn a_transactional_variable_is_the_runs(#[case] code: &str, #[case] needle: &str) {
    let errors = errors_of(code);
    assert!(errors.contains(needle), "{errors}");
}

/// Each node of a specialization has the capabilities of the use that minted it, its arguments'
/// included, and uses that differ in what they cause share no specialization: the call of
/// `apply`'s parameter commits in the clone `take` reaches and does nothing in the one `keep`
/// reaches, though both uses are at one type, and each reaches `apply` through a use in its own
/// clone of `apply_inside` (`src/ccl/design/type-inference.md`, "Capabilities on every expression").
#[test]
fn a_specialization_has_its_uses_effects() {
    use cambra::ccl::context::{Phase, compile_to};
    use cambra::ccl::{Expr, TypedExprNode};
    let code = indoc! {"
        stock: Mut(Int, Txn) := 10

        def take(n: Int):
            with begin():
                stock := stock - n

        def keep(n: Int):
            ()

        def apply(f, x):
            f(x)

        def apply_inside(f, x):
            apply(f, x)

        apply_inside(take, 1)
        apply_inside(keep, 1)
    "};
    /// The capabilities of each call of a function `apply`'s parameters hold.
    fn parameter_calls(e: &Expr, out: &mut Vec<String>) {
        if let TypedExprNode::Apply { function, .. } = &e.node
            && cambra::ccl::symbolic::symbolic(function).starts_with("__arg_tuple")
        {
            out.push(e.capabilities.to_string());
        }
        e.walk_children(|c| parameter_calls(c, out));
    }
    let loaded = cambra::ccl::load::LoadedProgram::test(code);
    let expr = compile_to(&loaded, Phase::Infer).expect("the program compiles");
    let mut calls = Vec::new();
    parameter_calls(&expr, &mut calls);
    calls.sort();
    assert_eq!(
        calls,
        [
            "",
            " requires ReadTxn(stock) causes WriteTxn(stock), RunTransaction"
        ]
    );
}

/// A read of a mutable variable is its mention's own capability, so it stays with the mention
/// wherever a pass moves it (`src/ccl/design/type-inference.md`, "Capabilities on every
/// expression").
#[test]
fn a_read_is_its_mentions_effect() {
    use cambra::ccl::context::{Phase, compile_to};
    use cambra::ccl::{Expr, TypedExprNode};
    let code = indoc! {"
        n: Mut(Int, Txn) := 0
        for r in [1, 2]:
            with begin():
                n := n + r
        await_final(n)
    "};
    fn mentions_of_n(e: &Expr, out: &mut Vec<String>) {
        if let TypedExprNode::Var(name) = &e.node
            && name.base() == "n"
        {
            out.push(e.capabilities.to_string());
        }
        e.walk_children(|c| mentions_of_n(c, out));
    }
    let loaded = cambra::ccl::load::LoadedProgram::test(code);
    let expr = compile_to(&loaded, Phase::Infer).expect("the program compiles");
    let mut mentions = Vec::new();
    mentions_of_n(&expr, &mut mentions);
    assert_eq!(mentions, [" requires Transaction, ReadTxn(n)", ""]);
}
