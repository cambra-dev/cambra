//! Checking each module on its own (`docs/chl-spec.md`, "9.14 Checking a module
//! on its own"): a module's errors are its own and reported once, and an error a
//! module's use raises in another module's code carries a label at the use.

use std::time::Duration;

use cambra::ccl::context::{GlobalContext, check_program};
use indoc::indoc;
use rstest_log::rstest;

use super::modules::{compile_errors, program, report_count};

/// A module that adds an `Int` to a value of its type parameter's type.
const ADDER: &str = indoc! {"
    param T
    param x: T
    pub y = x + 1
"};

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
            ("lib_a", "run broken as x\npub v = x::v\n"),
            ("lib_b", "run broken as y\npub v = y::v\n"),
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
            pub double: forall (A) A => Int requires Multipliable(A, Int, Output=Int)
            pub first: forall (U) {U, U} => U
            pub keep: T => T
            pub total: Int  # a constant
        "}
    );
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
            pub wrap: T => T
            pub pick: forall (A) {T, A} => A
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
    events = defer()
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
            pub draw: {Mut(Int, Txn), Int} => {}
            pub reset: Mut(Int, Txn) => {}
        "}
    );
}

/// A file whose check fails reports its errors, and prints no interface.
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
    let errors = check_program(&mut GlobalContext::default(), &program).unwrap_err();
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
    let errors = check_program(&mut GlobalContext::default(), &program).unwrap_err();
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
/// errors and exits 1, and refuses a missing file argument.
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
    std::fs::write(dir.join("bad.cambra"), "pub v: String = 1\n").expect("writing bad");
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
    assert!(failed.stdout.is_empty());
    assert!(stderr.contains("bad.cambra:1:"), "{stderr}");

    let usage = check(&[]);
    assert_eq!(usage.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&usage.stderr).contains("Usage: cambra check"));
}
