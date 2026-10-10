//! Runs of a module: each `run` statement performs its module's top level as a
//! run of its own, with its own state and sinks, reached through its run name
//! from its statement down (`docs/chl-spec.md`, "9.3 Runs", "9.9 Running").

use std::time::Duration;

use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program};
use cambra::ccl::load::LoadedProgram;
use cambra::interpreter::{Consumer, Value};
use indoc::indoc;
use rstest_log::rstest;

use crate::helpers::*;
use crate::modules::{assert_refused, compile_errors, program};

/// A module of values and functions.
const COUNTER: &str = indoc! {"
    pub limit = 10
    pub def double(x):
        x * 2
    pub def id(x):
        x
    pub def item(p):
        (price=p, cost=1)
    pub Small = {Int where _ < limit}
"};

/// A module whose run folds a loop into an induction variable and publishes the
/// result.
const SUMMER: &str = indoc! {"
    total := 0
    for x in [1, 2, 3]:
        total += x
    pub sum = total
"};

/// A module whose run commits a transaction on its own variable.
const BANK: &str = indoc! {"
    pool: Mut(Int, Txn) := 100
    with begin():
        pool := pool - 10
    pub left = await_final(pool)
"};

/// A module whose run writes one value to its sink.
const EMIT: &str = indoc! {"
    out = test_sink()
    out << 7
"};

/// Run `program` to completion with a test sink registered under each of
/// `sinks`, and answer what each received.
fn observe(program: &LoadedProgram, sinks: &[&str]) -> Vec<String> {
    const CAP: usize = 10_000;
    let mut ctx = GlobalContext::default();
    let handles: Vec<_> = sinks.iter().map(|n| ctx.register_test_sink(*n)).collect();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let compiled = compile_program(&mut ctx, program, consumer).unwrap_or_render(program);
    let completed = (0..CAP).any(|_| {
        ctx.scheduler().check_for_notifications();
        compiled.done.try_recv().is_ok()
    });
    assert!(completed, "sinks did not all complete within {CAP} pulls");
    handles
        .iter()
        .map(|s| format!("{}", s.value().expect("a value")))
        .collect()
}

/// A run's name is its module's last segment, or the name `as` gives; its
/// public members are reached through it, as a value, a callee, and a label's
/// qualifier.
#[rstest]
#[case::default_name("run counter\ncounter::double(counter::limit)\n", 20)]
#[case::named("run counter as eu\neu::double(eu::limit)\n", 20)]
#[case::labels("run counter as eu\neu::item(5).eu::price\n", 5)]
#[case::used("run counter as eu use double, limit as cap\ndouble(cap)\n", 20)]
#[case::generic_through_use("run counter as eu use id\nid(3) if id(True) else 0\n", 3)]
#[case::a_type("run counter as eu\nx: eu::Small = 3\nx\n", 3)]
#[case::a_type_through_use("run counter as eu use Small\nx: Small = 3\nx\n", 3)]
#[timeout(Duration::from_secs(10))]
fn a_run_reaches_its_modules_public_members(#[case] root: &str, #[case] expected: i64) {
    check_program_scalar(
        &program(root, &[("counter", COUNTER)]),
        Value::Int(expected),
    );
}

/// Each run performs its module's top level with state of its own: two runs of
/// one module hold two variables, induction and transactional alike
/// (`docs/chl-spec.md`, "9.9 Running").
#[rstest]
#[case::induction("summer", SUMMER, "a::sum + b::sum", 12)]
#[case::transactional("bank", BANK, "a::left + b::left", 180)]
#[timeout(Duration::from_secs(10))]
fn two_runs_of_a_module_have_their_own_state(
    #[case] module: &str,
    #[case] text: &str,
    #[case] read: &str,
    #[case] expected: i64,
) {
    let root = format!("run {module} as a\nrun {module} as b\n{read}\n");
    check_program_scalar(&program(&root, &[(module, text)]), Value::Int(expected));
}

/// Each run's sinks are its own, named by its run path.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn two_runs_of_a_module_have_their_own_sinks() {
    let program = program("run emit as a\nrun emit as b\n", &[("emit", EMIT)]);
    assert_eq!(
        observe(&program, &["a::out", "b::out"]),
        ["Function [ () -> 7 ]", "Function [ () -> 7 ]"]
    );
}

/// A run's own runs run with it, at run paths under its own.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_run_runs_its_own_runs() {
    check_program_scalar(
        &program(
            "run outer as o\no::n\n",
            &[
                ("summer", SUMMER),
                ("outer", "run summer as s\npub n = s::sum + 1\n"),
            ],
        ),
        Value::Int(7),
    );
    let program = program(
        "run twice as t\n",
        &[("emit", EMIT), ("twice", "run emit as a\nrun emit as b\n")],
    );
    assert_eq!(
        observe(&program, &["t::a::out", "t::b::out"]),
        ["Function [ () -> 7 ]", "Function [ () -> 7 ]"]
    );
}

/// A run name and the names its `use` clause binds are in scope from its
/// statement to the end of its module, as a value binding is.
#[rstest]
#[case::run_name(
    "x = eu::limit\nrun counter as eu\nx\n",
    "the run `eu` is declared below this use"
)]
#[case::used_type(
    "x: Small = 3\nrun counter use Small\nx\n",
    "`Small` is declared below this use"
)]
#[case::used_value(
    "x = double(1)\nrun counter use double\nx\n",
    "Unbound variable: 'double'"
)]
#[timeout(Duration::from_secs(10))]
fn a_run_name_is_in_scope_below_its_statement(#[case] root: &str, #[case] needle: &str) {
    assert_refused(&program(root, &[("counter", COUNTER)]), needle);
}

#[rstest]
#[case::bound_twice(
    "run counter as eu\nrun counter as eu\n1\n",
    "`eu` is already a run name"
)]
#[case::an_import_name(
    "import counter\nrun counter\n1\n",
    "`counter` is already an import name"
)]
#[case::public("pub run counter\n1\n", "`pub` is refused on a `run`")]
#[case::a_binder_named_like_a_run(
    "run counter as eu\neu = 1\neu\n",
    "`eu` is a run name, so no binder in its module takes it"
)]
#[timeout(Duration::from_secs(10))]
fn a_misused_run_is_refused(#[case] root: &str, #[case] needle: &str) {
    assert_refused(
        &program(root, &[("counter", COUNTER), ("summer", SUMMER)]),
        needle,
    );
}

/// A `run` inside an imported module would give the run no run path, so it is
/// refused.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_run_in_an_imported_module_is_refused() {
    assert_refused(
        &program(
            "import lib\n1\n",
            &[("counter", COUNTER), ("lib", "run counter\npub n = 1\n")],
        ),
        "a `run` in an imported module is not supported yet",
    );
}

/// Every route is unique across all runs, so two runs of a module serving a
/// literal route conflict, an error at the second run's statement with a note at
/// the first's (`docs/chl-spec.md`, "9.9 Running").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn two_runs_serving_one_route_are_refused() {
    let service = indoc! {r#"
        reqs, resps = http_serve("0", "GET", "/ping")
        for r in reqs:
            resps << "pong"
    "#};
    let errors = compile_errors(&program(
        "run service as eu\nrun service as us\n",
        &[("service", service)],
    ));
    assert!(
        errors.contains(
            "the run `us` serves port=0, method=GET, path=/ping, which the run `eu` already serves"
        ),
        "{errors}"
    );
    assert!(errors.contains("the run that serves it first"), "{errors}");
}

/// A module of value parameters: `base` without a default, `step` with one.
const STEPPER: &str = indoc! {"
    param base: Int
    param step: Int = 1
    pub total = base + step
"};

/// A run's parameters take its arguments, and a parameter without one takes
/// its default (`docs/chl-spec.md`, "9.4 Parameters"). An argument is any
/// expression over the names above the run: the module's own members, and
/// another run's members, so one run's result can be passed into another.
#[rstest]
#[case::default("run stepper(base=10) as a\na::total\n", 11)]
#[case::overriding_a_default("run stepper(base=10, step=5) as a\na::total\n", 15)]
#[case::two_runs_two_arguments(
    "run stepper(base=1) as a\nrun stepper(base=100) as b\na::total + b::total\n",
    103
)]
#[case::another_runs_member(
    "run stepper(base=1) as a\nrun stepper(base=a::total) as b\nb::total\n",
    3
)]
#[case::the_modules_own_member("x = 41\nrun stepper(base=x) as a\na::total\n", 42)]
#[case::through_a_run_that_passes_its_own("run relay(start=7) as r\nr::out\n", 8)]
#[timeout(Duration::from_secs(10))]
fn a_runs_parameters_take_its_arguments(#[case] root: &str, #[case] expected: i64) {
    let relay = "param start: Int\nrun stepper(base=start) as s\npub out = s::total\n";
    check_program_scalar(
        &program(root, &[("stepper", STEPPER), ("relay", relay)]),
        Value::Int(expected),
    );
}

/// The root and an imported module are run by no `run` statement, so their
/// parameters take their defaults.
#[rstest]
#[case::root("param n: Int = 5\nn + 1\n", &[], 6)]
#[case::imported(
    "import scaled\nscaled::by(3)\n",
    &[("scaled", "param scale: Int = 2\npub def by(x):\n    x * scale\n")],
    6
)]
#[case::unannotated(
    "run bump(k=3) as b\nb::v\n",
    &[("bump", "param k\npub v = k + 1\n")],
    4
)]
#[timeout(Duration::from_secs(10))]
fn a_parameter_without_an_argument_takes_its_default(
    #[case] root: &str,
    #[case] modules: &[(&str, &str)],
    #[case] expected: i64,
) {
    check_program_scalar(&program(root, modules), Value::Int(expected));
}

#[rstest]
#[case::missing(
    "run stepper as a\n1\n",
    "the run `a` passes no argument for the parameter `base`"
)]
#[case::unknown(
    "run stepper(base=1, nope=2) as a\n1\n",
    "module `stepper` has no parameter `nope`"
)]
#[case::mistyped("run stepper(base=\"x\") as a\na::total\n", "annotated as Int")]
#[case::twice(
    "run stepper(base=1, base=2) as a\n1\n",
    "the parameter `base` already has an argument"
)]
#[case::root_without_a_default(
    "param n: Int\nn\n",
    "the root module's parameter `n` has no default"
)]
#[case::bound_by_a_member(
    "run clash(base=1)\n1\n",
    "`base` is a parameter, so no member of its module takes it"
)]
#[timeout(Duration::from_secs(10))]
fn a_misused_parameter_is_refused(#[case] root: &str, #[case] needle: &str) {
    assert_refused(
        &program(
            root,
            &[
                ("stepper", STEPPER),
                ("clash", "param base: Int\nbase = 2\n"),
            ],
        ),
        needle,
    );
}

/// A module feeds a run's public feed through its run name, in a loop or once
/// (`docs/chl-spec.md`, "9.9 Running").
#[rstest]
#[case::in_a_loop("run audit as a\nfor x in [1, 2]:\n    a::events << x\na::total\n", 3)]
#[case::once("run audit as a\na::events << 5\na::total\n", 5)]
#[timeout(Duration::from_secs(10))]
fn a_module_feeds_a_runs_feed(#[case] root: &str, #[case] expected: i64) {
    let audit = "pub events = defer()\npub total = sum([e for e in events])\n";
    check_program_scalar(&program(root, &[("audit", audit)]), Value::Int(expected));
}
