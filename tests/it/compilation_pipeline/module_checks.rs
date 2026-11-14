//! Checking each module on its own (`docs/chl-spec.md`, "9.14 Checking a module
//! on its own"): a module's errors are its own and reported once, and an error a
//! module's use raises in another module's code carries a label at the use.

use std::time::Duration;

use cambra::ccl::context::{GlobalContext, check_program};
use indoc::indoc;
use rstest_log::rstest;

use super::modules::{compile_errors, program, report_count};

#[rstest]
#[case::constructor("Option::some(1) == Option::none")]
#[case::grouping_key(r"groupby([1, 2], \x -> Option::some(x))")]
fn module_check_reaches_prelude_constructors(#[case] code: &str) {
    let program = program(code, &[]);
    let mut ctx = GlobalContext::default();
    check_program(&mut ctx, &program).unwrap_or_else(|errors| panic!("{errors:?}"));
}

/// A module that adds an `Int` to a value of its type parameter's type.
const ADDER: &str = indoc! {"
    param T
    param x: T
    pub y = x + 1
    visits: Mut(Int, Txn) := 0
"};

#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_module_defect_keeps_the_inferred_type_of_its_parameter() {
    let worker = indoc! {r#"
        param x: _
        pub y = x + 1
        pub bad = [1, "a"]
    "#};
    let root = indoc! {r#"
        run worker(x="s") as w
        w::y
    "#};
    let errors = compile_errors(&program(root, &[("worker", worker)]));
    assert!(
        errors.contains("The values that meet here have no common type"),
        "{errors}"
    );
    assert!(
        errors.contains("annotated as Int, but inferred as {String"),
        "{errors}"
    );
    assert_eq!(report_count(&errors), 2, "{errors}");
}

#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_module_defect_and_a_bad_type_argument_are_both_reported() {
    let worker = indoc! {r#"
        param T <: Int
        param x: T
        pub y = x + 1
        pub bad = [1, "a"]
    "#};
    let root = indoc! {r#"
        run worker(T=String, x="s") as w
        w::y
    "#};
    let errors = compile_errors(&program(root, &[("worker", worker)]));
    assert!(
        errors.contains("The values that meet here have no common type"),
        "{errors}"
    );
    assert!(
        errors.contains("annotated as Int, but inferred as String"),
        "{errors}"
    );
    assert_eq!(report_count(&errors), 2, "{errors}");
}

#[rstest]
#[case::rejected_first(true)]
#[case::rejected_second(false)]
#[timeout(Duration::from_secs(10))]
fn rejecting_one_run_keeps_another_runs_call_checked(#[case] rejected_first: bool) {
    let worker = indoc! {r#"
        param T <: Int
        pub def f(x):
            x + 1
        pub bad = [1, "a"]
    "#};
    let good = "run worker(T=Int) as good";
    let bad = "run worker(T=String) as bad";
    let (first, second) = if rejected_first {
        (bad, good)
    } else {
        (good, bad)
    };
    let root = indoc::formatdoc! {r#"
        {first}
        {second}
        good::f("s")
    "#};
    let errors = compile_errors(&program(&root, &[("worker", worker)]));
    assert!(
        errors.contains("No Addable instance for this call"),
        "{errors}"
    );
    assert_eq!(report_count(&errors), 3, "{errors}");
}

#[rstest]
#[case::left_first(false)]
#[case::right_first(true)]
#[timeout(Duration::from_secs(10))]
fn a_rejected_nested_run_keeps_the_other_side_of_a_diamond_checked(#[case] reverse: bool) {
    let worker = indoc! {r#"
        param T <: Int
        pub def f(x):
            x + 1
        pub bad = [1, "a"]
    "#};
    let left = indoc! {r#"
        run worker(T=String) as rejected
        pub value = rejected::f(1)
    "#};
    let right = indoc! {r#"
        run worker(T=Int) as accepted
        pub def f(x):
            accepted::f(x)
    "#};
    let (first, second) = if reverse {
        ("right", "left")
    } else {
        ("left", "right")
    };
    let root = indoc::formatdoc! {r#"
        run {first} as {first}
        run {second} as {second}
        right::f("s")
    "#};
    let errors = compile_errors(&program(
        &root,
        &[("worker", worker), ("left", left), ("right", right)],
    ));
    assert_eq!(report_count(&errors), 3, "{errors}");
    assert!(
        errors.contains("annotated as Int, but inferred as String"),
        "{errors}"
    );
    assert!(
        errors.contains("No Addable instance for this call"),
        "{errors}"
    );
    assert!(errors.contains("main.cambra:3:"), "{errors}");
}

#[rstest]
#[case::left_first(false)]
#[case::right_first(true)]
#[timeout(Duration::from_secs(10))]
fn a_shared_broken_dependency_keeps_both_diamond_callers_checked(#[case] reverse: bool) {
    let worker = indoc! {r#"
        pub def f(x: Int) => Int:
            x
        pub bad = [1, "a"]
    "#};
    let wrapper = indoc! {r#"
        import worker
        pub def f(x):
            worker::f(x)
    "#};
    let (first, second) = if reverse {
        ("right", "left")
    } else {
        ("left", "right")
    };
    let root = indoc::formatdoc! {r#"
        import {first}
        import {second}
        left::f(True)
        right::f("s")
    "#};
    let errors = compile_errors(&program(
        &root,
        &[("worker", worker), ("left", wrapper), ("right", wrapper)],
    ));
    assert_eq!(report_count(&errors), 3, "{errors}");
    assert!(errors.contains("main.cambra:3:"), "{errors}");
    assert!(errors.contains("main.cambra:4:"), "{errors}");
}

#[rstest]
#[case::self_reference(indoc! {r#"
    pub def f(x: Int) => Int:
        f(x)
"#})]
#[case::mutual_reference(indoc! {r#"
    pub def f(x: Int) => Int:
        g(x)
    pub def g(x: Int) => Int:
        f(x)
"#})]
#[timeout(Duration::from_secs(10))]
fn unsupported_recursion_keeps_declared_inputs_checked(#[case] library: &str) {
    let root = indoc! {r#"
        import lib
        lib::f(True)
    "#};
    let errors = compile_errors(&program(root, &[("lib", library)]));
    assert_eq!(report_count(&errors), 2, "{errors}");
    assert!(errors.contains("Unbound variable:"), "{errors}");
    assert!(errors.contains("expected Int, found Bool"), "{errors}");
    assert!(errors.contains("main.cambra:2:"), "{errors}");
}

/// A module with an error of its own is reported once, however many runs it has.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_modules_error_is_reported_once() {
    let errors = compile_errors(&program(
        indoc! {"
            run broken as a
            run broken as b
            1
        "},
        &[("broken", "pub v = 1 + \"a\"\n")],
    ));
    assert!(errors.contains("broken.cambra:1:9"), "{errors}");
    assert_eq!(report_count(&errors), 1, "{errors}");
}

/// An error whose type reads a module's member is reported once, though each check
/// that runs the module writes the member through a different run
/// (`docs/modules.md`, "Checking a module on its own").
#[rstest]
#[case::an_annotation(indoc! {"
    lo = 0
    pub v: {Int where _ > lo} = 0
"})]
#[case::an_argument(indoc! {"
    lo = 0
    pub def f(x: {Int where _ > lo}) => Int:
        x
    pub v = f(0)
"})]
#[timeout(Duration::from_secs(10))]
fn an_error_reading_a_member_is_reported_once(#[case] broken: &str) {
    let errors = compile_errors(&program(
        indoc! {"
            run lib_a as a
            run lib_b as b
            run broken as c
            1
        "},
        &[
            ("broken", broken),
            (
                "lib_a",
                indoc::indoc! {r#"
                run broken as x
                pub v = x::v
                "#},
            ),
            (
                "lib_b",
                indoc::indoc! {r#"
                run broken as y
                pub v = y::v
                "#},
            ),
        ],
    ));
    assert!(errors.contains("broken.cambra"), "{errors}");
    assert_eq!(report_count(&errors), 1, "{errors}");
}

/// An error a module's run raises in the code it runs is reported there, with a
/// label at the module's statement that brings that code in.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_error_a_run_raises_is_labelled_at_the_run() {
    let errors = compile_errors(&program(
        indoc! {"
            run middle as m
            m::v
        "},
        &[
            ("adder", ADDER),
            (
                "middle",
                indoc! {r#"
                    run adder(T=String, x="a") as a
                    pub v = a::y
                "#},
            ),
        ],
    ));
    assert!(errors.contains("adder.cambra:3:9"), "{errors}");
    assert!(errors.contains("brought in here"), "{errors}");
    assert!(errors.contains("middle.cambra:1:1"), "{errors}");
    assert_eq!(report_count(&errors), 1, "{errors}");
}

/// A module is checked whether or not anything uses what it exports.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_module_is_checked_alone() {
    let errors = compile_errors(&program(
        indoc! {"
            import lib
            1
        "},
        &[(
            "lib",
            indoc! {"
                param n: Int = 1
                pub v: String = n
            "},
        )],
    ));
    assert!(errors.contains("lib.cambra:2"), "{errors}");
}

/// An argument for a parameter its module annotates with `_` is checked at the
/// argument, against the type the module's own check infers for the parameter.
#[rstest]
#[case::run(indoc! {r#"
    run bump(k="x") as b
    b::v
"#}, "main.cambra:1:10")]
#[case::import(indoc! {r#"
    import bump(k="x")
    bump::v
"#}, "main.cambra:1:15")]
#[timeout(Duration::from_secs(10))]
fn an_argument_for_an_inferred_parameter_is_checked_at_the_argument(
    #[case] root: &str,
    #[case] at: &str,
) {
    let bump = indoc! {"
        param k: _
        pub v = k + 1
    "};
    let errors = compile_errors(&program(root, &[("bump", bump)]));
    assert!(errors.contains(at), "{errors}");
    assert!(errors.contains("annotated as Int"), "{errors}");
    assert!(!errors.contains("bump.cambra"), "{errors}");
}

/// A parameter whose uses leave its type open takes any argument at the
/// statement, and its uses check the argument.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_argument_for_an_open_parameter_is_checked_through_its_uses() {
    let errors = compile_errors(&program(
        indoc! {r#"
            run scale(k="x") as s
            s::v
        "#},
        &[(
            "scale",
            indoc! {"
                param k: _
                pub v = [k, 1]
            "},
        )],
    ));
    assert!(errors.contains("scale.cambra"), "{errors}");
}

/// An error linking raises in a run's copy names that run at its `run`
/// statement, and copies that raise it alike are one error, labelled at each:
/// whether inference merges them, as it does a bounds conflict, or linking does,
/// across their inference variables.
#[rstest]
#[case::one_run(
    ADDER,
    indoc! {r#"
        run m(T=String, x="a") as a
        run m(T=Int, x=1) as b
        b::y
    "#},
    &["the run `a`, whose copy fails"],
    &["the run `b`"]
)]
#[case::two_runs(
    ADDER,
    indoc! {r#"
        run m(T=String, x="a") as a
        run m(T=String, x="b") as b
        1
    "#},
    &["the run `a`, whose copy fails", "the run `b`, whose copy fails"],
    &[]
)]
#[case::a_bounds_conflict(
    indoc! {"
        param T
        param x: T
        pub y = [x, 1]
        visits: Mut(Int, Txn) := 0
    "},
    indoc! {r#"
        run m(T=String, x="a") as a
        run m(T=String, x="b") as b
        1
    "#},
    &["the run `a`, whose copy fails", "the run `b`, whose copy fails"],
    &[]
)]
#[case::inference_variables(
    indoc! {"
        param T
        param x: T
        pub y = x.name
        visits: Mut(Int, Txn) := 0
    "},
    indoc! {"
        run m(T=Int, x=1) as a
        run m(T=Int, x=2) as b
        1
    "},
    &["the run `a`, whose copy fails", "the run `b`, whose copy fails"],
    &[]
)]
#[timeout(Duration::from_secs(10))]
fn a_link_time_error_names_its_run(
    #[case] module: &str,
    #[case] root: &str,
    #[case] labels: &[&str],
    #[case] absent: &[&str],
) {
    let errors = compile_errors(&program(root, &[("m", module)]));
    assert!(errors.contains("m.cambra:3:9"), "{errors}");
    for label in labels {
        assert!(errors.contains(label), "{errors}");
    }
    for label in absent {
        assert!(!errors.contains(label), "{errors}");
    }
    assert_eq!(report_count(&errors), 1, "{errors}");
}

/// `cambra check` checks a file on its own, with its parameters abstract, and
/// prints its interface: each parameter, then each public member with its
/// contract, its annotation or the type it infers.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_checked_module_prints_its_interface() {
    let program = program(
        indoc! {"
            import nums
            param scale: Int = 2
            param T <: Int
            pub Count = {Int where _ > 0}
            pub base: Count = 3
            pub def double(x):
                x * scale
            pub def first(U, a: U, b: U) => U:
                a
            pub def keep(c: T) => T:
                c
            hidden = 1
            pub total = nums::limit + base
        "},
        &[("nums", "pub limit = 10\n")],
    );
    let interface = check_program(&mut GlobalContext::default(), &program)
        .unwrap_or_else(|errors| panic!("{errors:?}"));
    assert_eq!(
        interface,
        indoc! {"
            module main
            param scale: Int = …
            param T <: Int
            pub Count = {Int where _ > 0}
            pub base: {Int where _ > 0}  # a constant
            pub double: forall (A, B) A => B ∨ Int requires r: Multipliable(A, Int), r::Output <: B
            pub first: forall (U) {U, U} => U  # callable in a constant
            pub keep: T => T  # callable in a constant
            pub total: Int  # a constant
        "}
    );
}

/// A checked module that is run says what makes it one, and a module whose only state is
/// induction variables says nothing, since it is imported (`docs/chl-spec.md`, "Shareable
/// modules").
#[rstest]
#[case::transactional(
    "stock: Mut(Int, Txn) := 0\npub n = 1\n",
    "module main\npub n: {Int where _ == 1}  # a constant\nrun, since its top level causes `WriteTxn(stock)`\n"
)]
#[case::a_sink(
    "out = test_sink()\nout << 1\n",
    "module main\nrun, since its top level causes `AffectWorld`\n"
)]
#[case::induction(
    indoc! {"
        total := 0
        for x in [1, 2]:
            total += x
        pub n = total
    "},
    "module main\npub n: Int\n"
)]
#[timeout(Duration::from_secs(10))]
fn a_checked_module_says_whether_it_is_run(#[case] module: &str, #[case] expected: &str) {
    let interface = check_program(&mut GlobalContext::default(), &program(module, &[]))
        .unwrap_or_else(|errors| panic!("{errors:?}"));
    assert_eq!(interface, expected);
}

/// A public nominal type prints as its module declares it, with each type parameter's
/// variance and the module's type parameters whose arguments tell its instances apart,
/// and each public associated function prints with its contract.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_checked_module_prints_its_nominal_types() {
    let program = program(
        indoc! {"
            param Receipt
            pub type Box(T):
                boxed(T)
                empty
            pub type Price = Int
            pub def Price::doubled(self) => Int:
                self.extract() * 2
            def Price::hidden(self) => Int:
                1
            pub type Order:
                placed(r: Receipt, total: Price)
            impl Box(T):
                pub def or_else(self, d: T) => T:
                    match self:
                        case Box::boxed(v):
                            v
                        case Box::empty:
                            d
        "},
        &[],
    );
    let interface = check_program(&mut GlobalContext::default(), &program)
        .unwrap_or_else(|errors| panic!("{errors:?}"));
    assert_eq!(
        interface,
        indoc! {"
            module main
            param Receipt
            pub type Box(T):  # covariant in T
                boxed(T)
                empty
            pub type Price = Int
            pub Price::doubled: Price => Int
            pub type Order:  # one type per argument of Receipt
                placed(r: Receipt, total: Price)
            pub Box::or_else: forall (T) {Box(T), T} => T
        "}
    );
}

/// A family parameter prints with its kind, over one value and over two.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_checked_module_prints_a_family_parameter_s_kind() {
    let program = program(
        indoc! {"
            pub type Groups(K, V: K => Type) = (k: K) |=> V(k)
            pub type Pairs(A, B, V: {A, B} => Type) = (a: A) |=> (b: B) |=> V(a, b)
        "},
        &[],
    );
    let interface = check_program(&mut GlobalContext::default(), &program)
        .unwrap_or_else(|errors| panic!("{errors:?}"));
    assert_eq!(
        interface,
        indoc! {"
            module main
            pub type Groups(K, V: K => Type) = (k: K) |=> V(k)  # invariant in K; covariant in V
            pub type Pairs(A, B, V: {A, B} => Type) = (a: A) |=> (b: B) |=> V(a, b)  # invariant in A; invariant in B; covariant in V
        "}
    );
}

/// A `const` parameter prints with `const` and a public constant binding with a note, a type
/// reaching a `const` parameter names it among the parameters whose arguments tell its runs'
/// types apart, and a refinement prints the term of each constant it reads, a ternary included.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_checked_module_prints_its_constants() {
    let program = program(
        indoc! {"
            const param max_rate: Int = 5
            pub limit = max_rate * 2
            pub type Capped = {Int where _ <= limit}
            tier = 10 if max_rate > 3 else 1
            pub type Tiered = {Int where _ <= tier}
        "},
        &[],
    );
    let interface = check_program(&mut GlobalContext::default(), &program)
        .unwrap_or_else(|errors| panic!("{errors:?}"));
    assert_eq!(
        interface,
        indoc! {"
            module main
            const param max_rate: Int = …
            pub limit: Int  # a constant
            pub type Capped = {Int where _ <= max_rate * 2}  # one type per argument of max_rate
            pub type Tiered = {Int where _ <= (10 if max_rate > 3 else 1)}  # one type per argument of max_rate
        "}
    );
}

/// A type parameter with no kind written is one variable for the whole check, and a
/// contract writes it as the parameter, in a member's type and in a generalized one's
/// scheme alike.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_contract_writes_a_parameter_with_no_kind_by_name() {
    let program = program(
        indoc! {"
            param T
            def id(x: T) => T:
                x
            pub def wrap(x):
                id(x)
            pub def pick(a: T, b):
                b
        "},
        &[],
    );
    let interface = check_program(&mut GlobalContext::default(), &program)
        .unwrap_or_else(|errors| panic!("{errors:?}"));
    assert_eq!(
        interface,
        indoc! {"
            module main
            param T
            pub wrap: T => T  # callable in a constant
            pub pick: forall (A) {T, A} => A  # callable in a constant
        "}
    );
}

/// A contract writes the module's own types by name, and another module's qualified by
/// it.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_contract_qualifies_only_another_modules_types() {
    let program = program(
        indoc! {"
            import shop
            pub type Price = Int
            pub def convert(p: shop::Price) => Price:
                Price::new(p.extract())
        "},
        &[("shop", "pub type Price = Int\n")],
    );
    let interface = check_program(&mut GlobalContext::default(), &program)
        .unwrap_or_else(|errors| panic!("{errors:?}"));
    assert!(
        interface.contains("pub convert: shop::Price => Price\n"),
        "{interface}"
    );
}

/// A member declared after a statement that binds no member, a loop, a feed or an
/// `impl` block, has its contract.
#[rstest]
#[case::a_loop(indoc! {"
    total := 0
    for x in [1, 2]:
        total := total + x
    pub n = 1
"})]
#[case::a_feed(indoc! {"
    events: Feed(_)
    events << 1
    pub n = 1
"})]
#[case::an_impl_block(indoc! {"
    type Price = Int
    impl Price:
        def doubled(self) => Int:
            self.extract() * 2
    pub n = 1
"})]
#[timeout(Duration::from_secs(10))]
fn a_member_after_a_statement_has_its_contract(#[case] file: &str) {
    let interface = check_program(&mut GlobalContext::default(), &program(file, &[]))
        .unwrap_or_else(|errors| panic!("{errors:?}"));
    assert!(
        interface.contains("pub n: {Int where _ == 1}"),
        "{interface}"
    );
}

/// A `def` with a `Mut` parameter lowers curried, and its contract is written in
/// the shape its callers apply it in: one function of its parameters.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_def_with_a_mut_parameter_is_written_uncurried() {
    let program = program(
        indoc! {"
            pub def draw(p: Mut(Int, Txn), amt: Int):
                with begin():
                    p := p - amt
            pub def reset(p: Mut(Int, Txn)):
                with begin():
                    p := 0
        "},
        &[],
    );
    let interface = check_program(&mut GlobalContext::default(), &program)
        .unwrap_or_else(|errors| panic!("{errors:?}"));
    assert_eq!(
        interface,
        indoc! {"
            module main
            pub draw: {Mut(Int, Txn), Int} => {} causes RunTransaction
            pub reset: Mut(Int, Txn) => {} causes RunTransaction
        "}
    );
}

/// A file whose check fails reports its errors alongside its established interface.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_checked_module_reports_its_errors() {
    let program = program(
        indoc! {"
            param n: Int
            pub v: String = n
        "},
        &[],
    );
    let errors = check_program(&mut GlobalContext::default(), &program)
        .unwrap_err()
        .errors;
    assert_eq!(errors.len(), 1, "{errors:?}");
}

/// `cambra check` creates a file's runs as linking does, so an error in creating
/// one is reported, once, however many modules' checks create the run: here a
/// run that passes no argument for a parameter without one.
#[rstest]
#[case::run_by_the_file(indoc! {"
    run counter
    pub m = counter::v
"})]
#[case::run_by_a_run_of_the_file(indoc! {"
    run outer
    pub m = outer::w
"})]
#[timeout(Duration::from_secs(10))]
fn a_checked_module_reports_a_runs_missing_argument(#[case] file: &str) {
    let counter = indoc! {"
        param n: Int
        pub v = n + 1
    "};
    let outer = indoc! {"
        run counter
        pub w = counter::v
    "};
    let program = program(file, &[("counter", counter), ("outer", outer)]);
    let errors = check_program(&mut GlobalContext::default(), &program)
        .unwrap_err()
        .errors;
    let messages: Vec<String> = errors.iter().map(|e| e.message()).collect();
    assert_eq!(
        messages,
        ["the run `counter` passes no argument for the parameter `n`, which has no default"]
    );
}

/// A linked compile reports an error in a module's `run` statement once, from the
/// module's own check, however many runs of the module copy the statement.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_runs_missing_argument_is_reported_once_however_often_it_is_copied() {
    let counter = indoc! {"
        param n: Int
        pub v = n + 1
    "};
    let outer = indoc! {"
        run counter
        pub w = counter::v
    "};
    let errors = compile_errors(&program(
        indoc! {"
            run outer as a
            run outer as b
            a::w + b::w
        "},
        &[("counter", counter), ("outer", outer)],
    ));
    assert!(
        errors.contains("the run `counter` passes no argument"),
        "{errors}"
    );
    assert!(errors.contains("outer.cambra:1:1"), "{errors}");
    assert_eq!(report_count(&errors), 1, "{errors}");
}

/// The `cambra check` subcommand reads the file and the modules it reaches from
/// disk, prints the file's interface and exits 0, prints a failing check's
/// errors alongside established contracts and exits 1, and refuses a missing file argument.
#[rstest]
#[timeout(Duration::from_secs(30))]
fn cambra_check_prints_an_interface_or_errors() {
    let dir = std::env::temp_dir().join(format!("cambra-check-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("creating the directory");
    std::fs::write(dir.join("nums.cambra"), "pub limit = 10\n").expect("writing nums");
    std::fs::write(
        dir.join("lib.cambra"),
        indoc! {"
            import nums
            pub total = nums::limit + 1
        "},
    )
    .expect("writing lib");
    std::fs::write(
        dir.join("bad.cambra"),
        indoc! {r#"
        pub good = 1
        pub declared: String = 1
        pub missing = absent
    "#},
    )
    .expect("writing bad");
    let check = |args: &[&std::path::Path]| {
        std::process::Command::new(env!("CARGO_BIN_EXE_cambra"))
            .arg("check")
            .args(args)
            .output()
            .expect("the cambra binary spawns")
    };

    let checked = check(&[&dir.join("lib.cambra")]);
    let stderr = String::from_utf8_lossy(&checked.stderr);
    assert!(checked.status.success(), "{stderr}");
    assert_eq!(
        String::from_utf8_lossy(&checked.stdout),
        indoc! {"
            module lib
            pub total: Int  # a constant
        "}
    );

    let failed = check(&[&dir.join("bad.cambra")]);
    let stderr = String::from_utf8_lossy(&failed.stderr);
    assert_eq!(failed.status.code(), Some(1), "{stderr}");
    let stdout = String::from_utf8_lossy(&failed.stdout);
    assert!(stdout.contains("pub good: {Int where _ == 1}"), "{stdout}");
    assert!(stdout.contains("pub declared: String"), "{stdout}");
    assert!(!stdout.contains("pub missing:"), "{stdout}");
    assert!(stderr.contains("bad.cambra:"), "{stderr}");

    let usage = check(&[]);
    assert_eq!(usage.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&usage.stderr).contains("Usage: cambra check"));
}

/// A module's check traces an error at a node that inference minted to the source.
/// Inference raises at its copy of `sales`, which comprehension put in a group's predicate.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_error_at_a_node_a_module_check_minted_has_a_span() {
    let library = "pub g = [sum([s.amount for s in g]) for g in groupby(sales, \\r -> r.region)]\n";
    let root = indoc! {"
        import lib
        lib::g
    "};
    let errors = compile_errors(&program(root, &[("lib", library)]));
    assert!(errors.contains("Unbound variable: 'sales'"), "{errors}");
    assert!(errors.contains("lib.cambra:1:46"), "{errors}");
}

/// Checking a file on its own, as `cambra check` and an editor do, reports its type errors past
/// a parse, load or lowering error a placeholder stands in for (`docs/modules.md`, "Checking a
/// module on its own").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_lowering_error("pub x: Mut(Int) = 3", "introduces a mutable")]
#[case::a_parse_error("pub a = 1 +* 2", "found '*'")]
#[case::a_loading_error("import nothere", "no module `nothere`")]
fn checking_a_file_reports_its_type_errors_past_another_error(
    #[case] first_line: &str,
    #[case] first: &str,
) {
    let root = format!("{first_line}\npub y = [1, \"a\"]\n");
    let program = program(&root, &[]);
    let Err(errors) = check_program(&mut GlobalContext::default(), &program) else {
        panic!("expected `{root}` not to check");
    };
    let messages: Vec<String> = errors.errors.iter().map(|e| e.message()).collect();
    assert_eq!(messages.len(), 2, "{messages:?}");
    assert!(messages[0].contains(first), "{messages:?}");
    assert!(
        messages[1].contains("The values that meet here have no common type"),
        "{messages:?}"
    );
}

#[rstest]
#[case::missing(None)]
#[case::partial(Some("pub broken = 1 +* 2"))]
#[timeout(Duration::from_secs(10))]
fn checking_unavailable_use_members_preserves_only_established_contracts(
    #[case] library: Option<&str>,
) {
    let root = indoc! {r#"
        import lib use Area, Shape, f, T
        instance Area(Int):
            def area(s):
                1 + "skipped"
        pub dependent = f(1)
        pub constructed = Shape::circle(1)
        pub typed: T = f(1)
        pub healthy = 7
        pub bad = [1, "a"]
    "#};
    let modules: Vec<_> = library.into_iter().map(|text| ("lib", text)).collect();
    let result =
        check_program(&mut GlobalContext::default(), &program(root, &modules)).unwrap_err();
    let messages: Vec<_> = result.errors.iter().map(|error| error.message()).collect();
    assert_eq!(messages.len(), 2, "{messages:?}");
    assert!(
        messages
            .iter()
            .any(|message| message.contains("The values that meet here have no common type")),
        "{messages:?}"
    );
    let interface = result
        .interface
        .expect("healthy export establishes a contract");
    assert!(interface.contains("pub healthy:"), "{interface}");
    for absent in [
        "pub dependent:",
        "pub constructed:",
        "pub typed:",
        "pub bad:",
    ] {
        assert!(!interface.contains(absent), "{interface}");
    }
}
