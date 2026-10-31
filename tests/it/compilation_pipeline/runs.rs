//! Runs of a module: each `run` statement performs its module's top level as a
//! run of its own, with its own state and sinks, reached through its run name
//! from its statement down (`docs/chl-spec.md`, "9.3 Runs", "9.9 Running").

use std::time::Duration;

use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program};
use cambra::ccl::load::LoadedProgram;
use cambra::interpreter::{Consumer, Value};
use indoc::{formatdoc, indoc};
use rstest_log::rstest;

use super::helpers::*;
use super::modules::{assert_refused, compile_errors, program, report_count};

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
    visits: Mut(Int, Txn) := 0
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

/// Two runs of a module whose code holds refinements each hold their own copy of them: a
/// refined parameter type, and a nominal type's refined constructor. Each module holds state,
/// so it is run.
#[rstest]
#[case::function(
    indoc! {"
        pub def f(x: {Int where _ > 0}) => Int:
            x
        visits: Mut(Int, Txn) := 0
    "},
    "a::f(1) + b::f(2)"
)]
#[case::constructor(
    indoc! {"
        pub type P = {Int where _ > 0}
        visits: Mut(Int, Txn) := 0
    "},
    "a::P::new(1).extract() + b::P::new(2).extract()"
)]
#[timeout(Duration::from_secs(10))]
fn two_runs_of_a_module_hold_their_own_refinements(#[case] text: &str, #[case] read: &str) {
    let root = formatdoc! {"
        run refined as a
        run refined as b
        {read}
    "};
    check_program_scalar(&program(&root, &[("refined", text)]), Value::Int(3));
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

/// Two runs of a module reading a source each read all of it: the context holds the source
/// once, and each run's read is a reader of its own, so the elements 1, 2, 3 total 6 in both.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn two_runs_of_a_module_each_read_all_of_its_source() {
    use cambra::ccl::{BaseType, Type};
    use cambra::interpreter::tile_operators::scalar_tile_to_column_value;
    use cambra::interpreter::{Extent, Predicate, TestDataSource};
    let mut ctx = GlobalContext::default();
    let source = std::rc::Rc::new(std::cell::RefCell::new(TestDataSource::new(
        "nums",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    source.borrow_mut().add_data(&[
        (Value::UInt(0), Value::Int(1)),
        (Value::UInt(1), Value::Int(2)),
        (Value::UInt(2), Value::Int(3)),
    ]);
    source.borrow_mut().set_yield_predicate(Predicate::True);
    ctx.register_source(source);
    let program = program(
        indoc! {"
            run total as a
            run total as b
            a::sum + 10 * b::sum
        "},
        &[("total", "pub sum = sum([x for x in nums()])\n")],
    );
    let (_, result) = run_program_with_ctx(&mut ctx, &program);
    assert_eq!(
        scalar_tile_to_column_value(result).as_single().unwrap(),
        Value::Int(66)
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
    assert_eq!(report_count(&errors), 1, "{errors}");
}

/// The root serving a route a run serves is refused at the root's `http_serve`, naming
/// the run, with a note at its `run` statement.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn the_root_serving_a_runs_route_is_refused() {
    let errors = compile_errors(&program(
        indoc! {r#"
            run service as eu
            reqs, resps = http_serve("0", "GET", "/ping")
            for r in reqs:
                resps << "pong"
        "#},
        &[(
            "service",
            indoc! {r#"
                reqs, resps = http_serve("0", "GET", "/ping")
                for r in reqs:
                    resps << "pong"
            "#},
        )],
    ));
    assert!(
        errors.contains(
            "this program serves port=0, method=GET, path=/ping, which the run `eu` already serves"
        ),
        "{errors}"
    );
    assert!(errors.contains("the run that serves it"), "{errors}");
}

/// A sink's name has one binding in its module, the declaration, as in the root: a later
/// top-level binding is refused, once however many runs the module has.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_run_rebinding_a_sink_is_refused() {
    let errors = compile_errors(&program(
        indoc! {"
            run emit as a
            run emit as b
        "},
        &[(
            "emit",
            indoc! {"
                out = test_sink()
                out << 7
                out = 5
            "},
        )],
    ));
    assert_eq!(
        errors
            .matches("`out` is a sink, so it cannot be bound again")
            .count(),
        1,
        "{errors}"
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

/// A route takes its address from `const` parameters, so two runs given the same address
/// conflict as two runs of a literal route do, and an address that is not a constant, or
/// one that is no port, is refused.
#[rstest]
#[case::one_address(
    indoc! {r#"
        run service(path="/ping") as eu
        run service(path="/ping") as us
    "#},
    "the run `us` serves port=0, method=GET, path=/ping, which the run `eu` already serves"
)]
#[case::the_roots(
    indoc! {r#"
        const param path: String = "/ping"
        run service(path="/ping") as eu
        reqs, resps = http_serve("0", "GET", path)
        for r in reqs:
            resps << "pong"
    "#},
    "this program serves port=0, method=GET, path=/ping, which the run `eu` already serves"
)]
#[case::not_a_port(
    "run service(path=\"/ping\", port=\"http\") as eu\n",
    "the route declared here has no address in this run: http_serve port must be a u16, got \"http\""
)]
#[timeout(Duration::from_secs(10))]
fn a_route_takes_its_address_from_its_run(#[case] root: &str, #[case] needle: &str) {
    let service = indoc! {r#"
        const param path: String
        const param port: String = "0"
        reqs, resps = http_serve(port, "GET", path)
        for r in reqs:
            resps << "pong"
    "#};
    let errors = compile_errors(&program(root, &[("service", service)]));
    assert!(errors.contains(needle), "{errors}");
}

/// A route's address is a string constant: one read from a parameter without `const` is
/// refused, and so is an argument that is no string in any run, once, at the statement.
#[rstest]
#[case::not_a_constant(
    indoc! {r#"
        param path: String
        reqs, resps = http_serve("0", "GET", path)
        for r in reqs:
            resps << "pong"
    "#},
    "`path` is a parameter without `const`"
)]
#[case::not_a_string(
    indoc! {r#"
        const param path: String
        reqs, resps = http_serve(8080, "GET", path)
        for r in reqs:
            resps << "pong"
    "#},
    "http_serve's arguments are strings, and one is `8080`"
)]
#[timeout(Duration::from_secs(10))]
fn a_routes_address_is_a_string_constant(#[case] service: &str, #[case] needle: &str) {
    let errors = compile_errors(&program(
        indoc! {r#"
            run service(path="/eu") as eu
            run service(path="/us") as us
        "#},
        &[("service", service)],
    ));
    assert_eq!(errors.matches(needle).count(), 1, "{errors}");
}

/// A module of value parameters: `base` without a default, `step` with one.
const STEPPER: &str = indoc! {"
    param base: Int
    param step: Int = 1
    pub total = base + step
    visits: Mut(Int, Txn) := 0
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
#[case::inferred(
    indoc! {"
        run bump(k=3) as b
        b::v
    "},
    &[("bump", indoc! {"
        param k: _
        pub v = k + 1
        visits: Mut(Int, Txn) := 0
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
#[case::an_import_name(
    indoc! {"
        run named_like_an_import(lib=1) as a
        1
    "},
    "`lib` is an import name, so no binder in its module takes it"
)]
#[case::a_run_name(
    indoc! {"
        run named_like_a_run(r=1) as a
        1
    "},
    "`r` is a run name, so no binder in its module takes it"
)]
#[case::a_use_name(
    indoc! {"
        run named_like_a_use(x=1) as a
        1
    "},
    "`x` is a `use` name, so no parameter of its module takes it"
)]
#[case::unannotated(
    indoc! {"
        run unannotated(k=1) as u
        1
    "},
    "the parameter `k` has no annotation: write its type, `param k: Int`, or `param k: _`"
)]
#[case::a_monomorphic_argument_for_a_polymorphic_parameter(
    indoc! {"
        def inc(x: Int) => Int:
            x + 1
        run poly(f=inc) as p
        p::n
    "},
    "annotated as forall (T) T => T, but inferred as Int => Int"
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
                ("lib", "pub x = 1\n"),
                (
                    "named_like_an_import",
                    indoc! {"
                        import lib
                        param lib: Int
                        pub y = lib::x
                    "},
                ),
                (
                    "named_like_a_run",
                    indoc! {"
                        param r: Int
                        run lib as r
                        pub y = r::x
                    "},
                ),
                (
                    "named_like_a_use",
                    indoc! {"
                        import lib use x
                        param x: Int
                        pub y = x
                    "},
                ),
                ("poly", POLY),
                (
                    "unannotated",
                    indoc! {"
                        param k
                        pub v = k
                    "},
                ),
            ],
        ),
        needle,
    );
}

/// A module whose parameter is a polymorphic function, which it calls at two types.
const POLY: &str = indoc! {r#"
    param f: forall (T) T => T
    pub n = f(1) if f("ab") == "ab" else 0
"#};

/// A parameter's annotation is the whole annotation of its `let`, so it may be polymorphic,
/// and a run passes a polymorphic function for it (`docs/chl-spec.md`, "Polymorphic type
/// annotations").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_parameter_takes_a_polymorphic_function() {
    check_program_scalar(
        &program(
            indoc! {"
                def id(x):
                    x
                run poly(f=id) as p
                p::n
            "},
            &[("poly", POLY)],
        ),
        Value::Int(1),
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
        pub events: Feed(_)
        pub total = sum([e for e in events])
    "};
    check_program_scalar(&program(root, &[("audit", audit)]), Value::Int(expected));
}

/// A module whose top level requires and causes nothing is imported, so running it with
/// arguments an import could pass is an error (`docs/chl-spec.md`, "Shareable modules
/// [Decided]").
#[rstest]
#[case::no_arguments(
    "run pure as p\np::v\n",
    "module `pure` performs no IO and holds no state, so running it is an error: import it \
     instead"
)]
#[case::constant_arguments(
    "run scaled(k=2) as s\ns::v\n",
    "module `scaled` performs no IO and holds no state, so running it is an error: import it \
     instead"
)]
#[timeout(Duration::from_secs(10))]
fn a_run_of_a_module_an_import_could_share_is_refused(#[case] root: &str, #[case] needle: &str) {
    assert_refused(
        &program(
            root,
            &[
                ("pure", "pub v = 1\n"),
                ("scaled", "param k: Int\npub v = k * 2\n"),
            ],
        ),
        needle,
    );
}

/// A run passing another run gives its module state an import cannot share, so it is run
/// whatever its own top level does.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_run_given_a_run_is_run() {
    check_program_scalar(
        &program(
            indoc! {"
                run store as s
                run reader(source=s) as r
                r::v
            "},
            &[
                ("store", "pub v = 3\nvisits: Mut(Int, Txn) := 0\n"),
                (
                    "reader",
                    "param source: Module{v: Int}\npub v = source::v + 1\n",
                ),
            ],
        ),
        Value::Int(4),
    );
}
