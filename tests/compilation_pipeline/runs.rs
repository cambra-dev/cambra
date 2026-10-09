//! Runs of a module: each `run` statement performs its module's top level as a
//! run of its own, with its own state and sinks, reached through its run name
//! from its statement down (`docs/chl-spec.md`, "9.3 Runs", "9.9 Running").

use std::time::Duration;

use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program};
use cambra::ccl::load::LoadedProgram;
use cambra::interpreter::{Consumer, Value};
use indoc::{formatdoc, indoc};
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
#[case::default_name(indoc! {"
    run counter
    counter::double(counter::limit)
"}, 20)]
#[case::named(indoc! {"
    run counter as eu
    eu::double(eu::limit)
"}, 20)]
#[case::labels(indoc! {"
    run counter as eu
    eu::item(5).eu::price
"}, 5)]
#[case::used(indoc! {"
    run counter as eu use double, limit as cap
    double(cap)
"}, 20)]
#[case::generic_through_use(indoc! {"
    run counter as eu use id
    id(3) if id(True) else 0
"}, 3)]
#[case::a_type(indoc! {"
    run counter as eu
    x: eu::Small = 3
    x
"}, 3)]
#[case::a_type_through_use(indoc! {"
    run counter as eu use Small
    x: Small = 3
    x
"}, 3)]
#[case::a_local_above_spelled_like_a_use_name(indoc! {"
    def f(double):
        double + 1
    run counter as eu use double
    f(1) + double(1)
"}, 4)]
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
    let root = formatdoc! {"
        run {module} as a
        run {module} as b
        {read}
    "};
    check_program_scalar(&program(&root, &[(module, text)]), Value::Int(expected));
}

/// Each run's sinks are its own, named by its run path.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn two_runs_of_a_module_have_their_own_sinks() {
    let program = program(
        indoc! {"
            run emit as a
            run emit as b
        "},
        &[("emit", EMIT)],
    );
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
            indoc! {"
                run outer as o
                o::n
            "},
            &[
                ("summer", SUMMER),
                (
                    "outer",
                    indoc! {"
                        run summer as s
                        pub n = s::sum + 1
                    "},
                ),
            ],
        ),
        Value::Int(7),
    );
    let program = program(
        "run twice as t\n",
        &[
            ("emit", EMIT),
            (
                "twice",
                indoc! {"
                    run emit as a
                    run emit as b
                "},
            ),
        ],
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
    indoc! {"
        x = eu::limit
        run counter as eu
        x
    "},
    "the run `eu` is declared below this use"
)]
#[case::used_type(
    indoc! {"
        x: Small = 3
        run counter use Small
        x
    "},
    "`Small` is declared below this use"
)]
#[case::used_value(
    indoc! {"
        x = double(1)
        run counter use double
        x
    "},
    "`double` is declared below this use"
)]
#[timeout(Duration::from_secs(10))]
fn a_run_name_is_in_scope_below_its_statement(#[case] root: &str, #[case] needle: &str) {
    assert_refused(&program(root, &[("counter", COUNTER)]), needle);
}

#[rstest]
#[case::bound_twice(
    indoc! {"
        run counter as eu
        run counter as eu
        1
    "},
    "`eu` is already a run name"
)]
#[case::an_import_name(
    indoc! {"
        import counter
        run counter
        1
    "},
    "`counter` is already an import name"
)]
#[case::public(indoc! {"
    pub run counter
    1
"}, "`pub` is refused on a `run`")]
#[case::a_binder_named_like_a_run(
    indoc! {"
        run counter as eu
        eu = 1
        eu
    "},
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
/// refused, once.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_run_in_an_imported_module_is_refused() {
    let errors = compile_errors(&program(
        indoc! {"
                import lib
                1
            "},
        &[
            ("counter", COUNTER),
            (
                "lib",
                indoc! {"
                        run counter
                        pub n = 1
                    "},
            ),
        ],
    ));
    assert!(
        errors.contains("an imported module declares no run"),
        "{errors}"
    );
    assert_eq!(errors.matches("Error:").count(), 1, "{errors}");
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
        indoc! {"
            run service as eu
            run service as us
        "},
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
#[case::default(indoc! {"
    run stepper(base=10) as a
    a::total
"}, 11)]
#[case::overriding_a_default(indoc! {"
    run stepper(base=10, step=5) as a
    a::total
"}, 15)]
#[case::two_runs_two_arguments(
    indoc! {"
        run stepper(base=1) as a
        run stepper(base=100) as b
        a::total + b::total
    "},
    103
)]
#[case::another_runs_member(
    indoc! {"
        run stepper(base=1) as a
        run stepper(base=a::total) as b
        b::total
    "},
    3
)]
#[case::the_modules_own_member(indoc! {"
    x = 41
    run stepper(base=x) as a
    a::total
"}, 42)]
#[case::through_a_run_that_passes_its_own(indoc! {"
    run relay(start=7) as r
    r::out
"}, 8)]
#[timeout(Duration::from_secs(10))]
fn a_runs_parameters_take_its_arguments(#[case] root: &str, #[case] expected: i64) {
    let relay = indoc! {"
        param start: Int
        run stepper(base=start) as s
        pub out = s::total
    "};
    check_program_scalar(
        &program(root, &[("stepper", STEPPER), ("relay", relay)]),
        Value::Int(expected),
    );
}

/// The root and an imported module are run by no `run` statement, so their
/// parameters take their defaults.
#[rstest]
#[case::root(indoc! {"
    param n: Int = 5
    n + 1
"}, &[], 6)]
#[case::imported(
    indoc! {"
        import scaled
        scaled::by(3)
    "},
    &[("scaled", indoc! {"
        param scale: Int = 2
        pub def by(x):
            x * scale
    "})],
    6
)]
#[case::unannotated(
    indoc! {"
        run bump(k=3) as b
        b::v
    "},
    &[("bump", indoc! {"
        param k
        pub v = k + 1
    "})],
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
    indoc! {"
        run stepper as a
        1
    "},
    "the run `a` passes no argument for the parameter `base`"
)]
#[case::unknown(
    indoc! {"
        run stepper(base=1, nope=2) as a
        1
    "},
    "module `stepper` has no parameter `nope`"
)]
#[case::mistyped(indoc! {r#"
    run stepper(base="x") as a
    a::total
"#}, "annotated as Int")]
#[case::twice(
    indoc! {"
        run stepper(base=1, base=2) as a
        1
    "},
    "the parameter `base` already has an argument"
)]
#[case::root_without_a_default(
    indoc! {"
        param n: Int
        n
    "},
    "the root module's parameter `n` has no default"
)]
#[case::bound_by_a_member(
    indoc! {"
        run clash(base=1)
        1
    "},
    "`base` is a parameter, so no member of its module takes it"
)]
#[timeout(Duration::from_secs(10))]
fn a_misused_parameter_is_refused(#[case] root: &str, #[case] needle: &str) {
    assert_refused(
        &program(
            root,
            &[
                ("stepper", STEPPER),
                (
                    "clash",
                    indoc! {"
                        param base: Int
                        base = 2
                    "},
                ),
            ],
        ),
        needle,
    );
}

/// A module feeds a run's public feed through its run name, in a loop or once
/// (`docs/chl-spec.md`, "9.9 Running").
#[rstest]
#[case::in_a_loop(indoc! {"
    run audit as a
    for x in [1, 2]:
        a::events << x
    a::total
"}, 3)]
#[case::once(indoc! {"
    run audit as a
    a::events << 5
    a::total
"}, 5)]
#[timeout(Duration::from_secs(10))]
fn a_module_feeds_a_runs_feed(#[case] root: &str, #[case] expected: i64) {
    let audit = indoc! {"
        pub events = defer()
        pub total = sum([e for e in events])
    "};
    check_program_scalar(&program(root, &[("audit", audit)]), Value::Int(expected));
}
