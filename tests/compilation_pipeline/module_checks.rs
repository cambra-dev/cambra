//! Checking each module on its own (`docs/chl-spec.md`, "9.14 Checking a module
//! on its own"): a module's errors are its own and reported once, and an error a
//! module's use raises in another module's code carries a label at the use.

use std::time::Duration;

use cambra::ccl::context::{GlobalContext, check_program};
use indoc::indoc;
use rstest_log::rstest;

use crate::modules::{compile_errors, program};

/// A module whose type parameter's kind its uses infer.
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
    assert_eq!(errors.matches("Error:").count(), 1, "{errors}");
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
    assert_eq!(errors.matches("Error:").count(), 1, "{errors}");
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

/// An argument for a parameter its module leaves unannotated is checked at the
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
fn an_argument_for_an_unannotated_parameter_is_checked_at_the_argument(
    #[case] root: &str,
    #[case] at: &str,
) {
    let errors = compile_errors(&program(root, &[("bump", "param k\npub v = k + 1\n")]));
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
        &[("scale", "param k\npub v = [k, 1]\n")],
    ));
    assert!(errors.contains("scale.cambra"), "{errors}");
}

/// An error linking raises in a run's copy names that run at its `run`
/// statement, and copies that raise it alike are one error, labelled at each.
#[rstest]
#[case::one_run(
    indoc! {r#"
        run adder(T=String, x="a") as a
        run adder(T=Int, x=1) as b
        b::y
    "#},
    &["the run `a`, whose copy fails"]
)]
#[case::two_runs(
    indoc! {r#"
        run adder(T=String, x="a") as a
        run adder(T=String, x="b") as b
        1
    "#},
    &["the run `a`, whose copy fails", "the run `b`, whose copy fails"]
)]
#[timeout(Duration::from_secs(10))]
fn a_link_time_error_names_its_run(#[case] root: &str, #[case] labels: &[&str]) {
    let errors = compile_errors(&program(root, &[("adder", ADDER)]));
    assert!(errors.contains("adder.cambra:3:9"), "{errors}");
    for label in labels {
        assert!(errors.contains(label), "{errors}");
    }
    assert!(
        !errors.contains("the run `b`") || labels.len() == 2,
        "{errors}"
    );
    assert_eq!(errors.matches("Error:").count(), 1, "{errors}");
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
            pub base: {Int where _ > 0}
            pub double: forall (A) A => Int requires Multipliable(A, Int, Output=Int)
            pub first: forall (U) {U, U} => U
            pub keep: T => T
            pub total: Int
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
        "import nums\npub total = nums::limit + 1\n",
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
        "module lib\npub total: Int\n"
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
