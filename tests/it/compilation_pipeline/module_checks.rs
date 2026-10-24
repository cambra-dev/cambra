//! Checking each module on its own (`docs/chl-spec.md`, "9.14 Checking a module
//! on its own"): a module's errors are its own and reported once, and an error a
//! module's use raises in another module's code carries a label at the use.

use std::time::Duration;

use indoc::indoc;
use rstest_log::rstest;

use super::modules::{compile_errors, program};

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
    assert_eq!(errors.matches("Error:").count(), 1, "{errors}");
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
