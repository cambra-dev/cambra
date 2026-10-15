//! Checking each module on its own (`docs/chl-spec.md`, "9.14 Checking a module
//! on its own"): a module's errors are its own and reported once, and an error a
//! module's use raises in another module's code carries a label at the use.

use std::time::Duration;

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
