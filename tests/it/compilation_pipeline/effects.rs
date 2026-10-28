//! What a function requires and causes, as inference collects it and a module's interface
//! prints it (`docs/chl-spec.md`, "6.9 Effects and requirements [Decided]";
//! `src/ccl/design/type-inference.md`, "Effect variables").

use std::time::Duration;

use cambra::ccl::context::{GlobalContext, check_program};
use indoc::indoc;
use rstest_log::rstest;

use super::modules::program;

/// The members the cases below share: a transactional mutable variable, a feed, a function
/// that commits a transaction, and a higher-order function.
const PRELUDE: &str = indoc! {"
    stock: Mut(Int, Txn) := 10
    out = defer()

    pub def take(n: Int):
        with begin():
            stock := stock - n

    def apply(f, x):
        f(x)
"};

/// The clauses after the codomain of `member`'s contract, as `cambra check` prints it.
fn clauses_of(code: &str, member: &str) -> String {
    let source = format!("{PRELUDE}\n{code}");
    let interface = check_program(&mut GlobalContext::default(), &program(&source, &[]))
        .unwrap_or_else(|errors| panic!("{errors:?}"));
    let prefix = format!("pub {member}: ");
    let line = interface
        .lines()
        .find(|l| l.starts_with(&prefix))
        .unwrap_or_else(|| panic!("no `{member}` in the interface:\n{interface}"));
    match line.find(" causes ") {
        Some(at) => line[at + 1..].to_owned(),
        None => String::new(),
    }
}

#[rstest]
#[timeout(Duration::from_secs(10))]
// A `with begin():` block commits, and its write names the variable it writes.
#[case("", "take", "causes Write(stock), Commit")]
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
    "causes Write(stock), Commit"
)]
// A loop body runs where the loop stands, and so does a comprehension's element.
#[case(
    indoc! {"
        pub def report_all(xs):
            for x in xs:
                out << x
    "},
    "report_all",
    "causes Append(out)"
)]
#[case(
    indoc! {"
        pub def take_listed(xs):
            [take(x) for x in xs]
    "},
    "take_listed",
    "causes Write(stock), Commit"
)]
// Each use of a polymorphic function collects its own effects, so a call that passes it a
// committing function commits and one that passes it a pure function does not.
#[case(
    indoc! {"
        pub def committing_use(x: Int):
            apply(take, x)
    "},
    "committing_use",
    "causes Write(stock), Commit"
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
    ""
)]
#[case(
    indoc! {"
        pub def local_feed(xs):
            g = defer()
            for x in xs:
                g << x
            sum(g)
    "},
    "local_feed",
    ""
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
    ""
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
    "causes Write(stock), Commit"
)]
fn a_contract_states_what_the_function_causes(
    #[case] code: &str,
    #[case] member: &str,
    #[case] expected: &str,
) {
    assert_eq!(clauses_of(code, member), expected);
}

/// An expression statement before its block's last statement is evaluated only for what it
/// causes, so one that causes nothing is refused (`docs/chl-spec.md`, "4.9 Expression
/// statement").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_pure_call("def f(x):\n    x + 1\nf(3)\n2\n")]
#[case::arithmetic("x = 1\nx + 1\n2\n")]
fn an_expression_statement_that_causes_nothing_is_refused(#[case] root: &str) {
    let errors = super::modules::compile_errors(&program(root, &[]));
    assert!(
        errors.contains("this statement causes nothing and its value is discarded"),
        "{errors}"
    );
}

/// A statement calling a function parameter does what the function each use passes does,
/// which the definition does not know, so the definition does not refuse it.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_statement_calling_a_parameter_is_kept() {
    super::helpers::check_program_scalar(
        &program(
            indoc! {"
                def each(f, x):
                    f(x)
                    x
                each(\\y -> y + 1, 2)
            "},
            &[],
        ),
        cambra::interpreter::Value::Int(2),
    );
}

/// A public function whose type names an induction variable of its module would let another
/// module read or write it (`docs/chl-spec.md`, "9.10 Induction variables stay in their
/// module").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_read("pub def current(n: Int):\n    cnt + n\n", "has `Read(cnt)`")]
#[case::a_write(
    "def bump(c: Mut(Int)):\n    c += 1\npub def tick(n: Int):\n    bump(cnt)\n    n\n",
    "has `Write(cnt)`"
)]
fn a_public_function_naming_an_induction_variable_is_refused(
    #[case] code: &str,
    #[case] needle: &str,
) {
    let source = format!("cnt := 0\nfor x in [1, 2]:\n    cnt += x\n{code}");
    let errors = check_program(&mut GlobalContext::default(), &program(&source, &[]))
        .expect_err("a public function naming an induction variable is refused");
    let rendered = format!("{errors:?}");
    assert!(rendered.contains(needle), "{rendered}");
}
