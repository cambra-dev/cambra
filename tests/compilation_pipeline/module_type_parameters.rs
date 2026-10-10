//! Type parameters of a module, `param T <: B = D`, and a type as an argument to
//! a run or an import (`docs/chl-spec.md`, "9.4 Parameters").

use std::time::Duration;

use cambra::interpreter::Value;
use indoc::indoc;
use rstest_log::rstest;

use crate::helpers::*;
use crate::modules::{assert_refused, compile_errors, program, shared_runs};

/// A module generic in the type of the value it holds.
const BOX: &str = indoc! {"
    param T
    param x: T
    pub held: T = x
    pub def get(d: T) => T:
        d
"};

/// A module of a value and a type alias over its type parameter.
const HOLDER: &str = indoc! {"
    param T
    pub Pair = {first: T, second: T}
"};

/// A module of a value of its type parameter's type.
const VALUED: &str = indoc! {"
    param T
    pub z: {a: T} = (a=3)
"};

/// A module whose type parameter's kind is inferred from a use as an `Int`.
const ADDER: &str = indoc! {"
    param T
    param x: T
    pub y = x + 1
"};

/// A module whose second type parameter defaults to a type over its first.
const KEYED: &str = indoc! {"
    param K
    param V = {K, K}
    param x: V
    pub def first(p: V) => K:
        p.0
    pub held = first(x)
"};

/// A module that runs `box` at a type over its own type parameter.
const NEST: &str = indoc! {"
    param U
    param y: U
    run box(T={a: U}, x=(a=y)) as b
    pub out = b::held
"};

/// Each run of a module takes its own type arguments, in its run's types and
/// its type members, and a type argument is a type the declaring module writes:
/// its own alias, or a refinement reading its own value.
#[rstest]
#[case::a_value("run box(T=Int, x=3) as b\nb::held\n", Value::Int(3))]
#[case::a_function("run box(T=Int, x=3) as b\nb::get(5)\n", Value::Int(5))]
#[case::a_used_function("run box(T=Int, x=3) as b use get\nget(5)\n", Value::Int(5))]
#[case::two_runs_at_two_types(
    "run box(T=String, x=\"a\") as s\nrun box(T=Int, x=3) as i\ni::held\n",
    Value::Int(3)
)]
#[case::a_local_alias(
    "Pos = {Int where _ > 0}\nrun box(T=Pos, x=3) as b\nb::held\n",
    Value::Int(3)
)]
#[case::a_refinement_reading_a_local_value(
    "lo = 2\nrun box(T={Int where _ > lo}, x=3) as b\nb::held\n",
    Value::Int(3)
)]
#[case::an_inferred_kind("run adder(T=Int, x=4) as a\na::y\n", Value::Int(5))]
#[case::a_default_over_another_parameter(
    "run keyed(K=Int, x=(5, 6)) as k\nk::held\n",
    Value::Int(5)
)]
#[case::a_type_member(
    "run holder(T=Int) as h\nx: h::Pair = (h::first=1, h::second=2)\nx.h::second\n",
    Value::Int(2)
)]
#[case::a_used_type_member(
    "run holder(T=Int) as h use Pair\nx: Pair = (h::first=1, h::second=2)\nx.h::second\n",
    Value::Int(2)
)]
#[case::a_nested_run_at_a_type_over_a_parameter(
    "run nest(U=Int, y=4) as n\nn::out.n::a\n",
    Value::Int(4)
)]
#[case::a_type_member_through_a_member(
    "run shop as s\nx: s::k::Pair = (s::k::first=1, s::k::second=2)\nx.s::k::first\n",
    Value::Int(1)
)]
#[case::a_module_type_over_a_parameter(
    "run box(T=Int, x=7) as b\nrun typed(T=Int, m=b) as t\nt::v\n",
    Value::Int(7)
)]
#[case::a_root_parameter_takes_its_default("param T = Int\nx: T = 3\nx\n", Value::Int(3))]
#[timeout(Duration::from_secs(10))]
fn a_run_takes_its_type_arguments(#[case] root: &str, #[case] expected: Value) {
    check_program_scalar(
        &program(
            root,
            &[
                ("box", BOX),
                ("holder", HOLDER),
                ("adder", ADDER),
                ("keyed", KEYED),
                ("nest", NEST),
                ("shop", "run holder(T=Int) as h\npub k = h\n"),
                (
                    "typed",
                    "param T\nparam m: Module{held: T}\npub v: T = m::held\n",
                ),
            ],
        ),
        expected,
    );
}

/// An import takes its type arguments as a run does, and an argument may be a
/// type member of another import, written above it or below.
#[rstest]
#[case::a_value("import valued(T=Int)\nvalued::z.valued::a\n", Value::Int(3))]
#[case::a_refinement_of_literals(
    "import valued(T={Int where _ > 0})\nvalued::z.valued::a\n",
    Value::Int(3)
)]
#[case::a_type_member(
    "import holder(T=Int)\nx: holder::Pair = (holder::first=1, holder::second=2)\nx.holder::first\n",
    Value::Int(1)
)]
#[case::a_used_type_member(
    "import holder(T=Int) use Pair\nx: Pair = (holder::first=1, holder::second=2)\nx.holder::first\n",
    Value::Int(1)
)]
#[case::another_imports_member(
    indoc! {"
        import holder(T=Int) as h
        import holder(T=h::Pair) as g
        x: g::Pair = (g::first=(h::first=1, h::second=2), g::second=(h::first=3, h::second=4))
        x.g::second.h::first
    "},
    Value::Int(3)
)]
#[case::another_imports_member_below(
    indoc! {"
        import holder(T=g::Pair) as h
        import holder(T=Int) as g
        x: h::Pair = (h::first=(g::first=1, g::second=2), h::second=(g::first=3, g::second=4))
        x.h::second.g::first
    "},
    Value::Int(3)
)]
#[timeout(Duration::from_secs(10))]
fn an_import_takes_its_type_arguments(#[case] root: &str, #[case] expected: Value) {
    check_program_scalar(
        &program(root, &[("holder", HOLDER), ("valued", VALUED)]),
        expected,
    );
}

/// Imports of one module at equal types reach one shared run, and at different
/// types two (`docs/chl-spec.md`, "9.2 Imports").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn imports_at_equal_types_reach_one_shared_run() {
    let program = program(
        indoc! {"
            import valued(T=Int) as h
            import valued(T=String) as g
            import both
            both::t
        "},
        &[
            ("valued", VALUED),
            ("both", "import valued(T=Int)\npub t = 1\n"),
        ],
    );
    let expected = ["both", "valued(T=Int)", "valued(T=String)"];
    assert_eq!(
        shared_runs(&program),
        expected.iter().map(|s| s.to_string()).collect()
    );
}

#[rstest]
#[case::a_missing_argument(
    "run box(x=3) as b\n1\n",
    "the run `b` passes no argument for the parameter `T`, which has no default"
)]
#[case::an_import_missing_one(
    "import holder\n1\n",
    "this import passes no argument for the parameter `T`, which has no default"
)]
#[case::a_root_parameter_without_a_default(
    "param T\n1\n",
    "the root module's parameter `T` has no default"
)]
#[case::an_argument_outside_its_type(
    "run box(T={Int where _ > 0}, x=0) as b\nb::held\n",
    "annotated as {Int where _ > 0}, but inferred as {Int where _ == 0}"
)]
#[case::a_type_member_of_the_wrong_type(
    "run holder(T=Int) as h\nx: h::Pair = (h::first=1, h::second=\"a\")\n1\n",
    "annotated as {holder::first: Int, holder::second: Int}"
)]
#[case::an_inferred_kind_the_argument_does_not_fit(
    "run adder(T=String, x=\"a\") as a\na::y\n",
    "No Addable instance"
)]
#[case::a_local_alias_passed_to_an_import(
    "Local = Int\nimport holder(T=Local)\n1\n",
    "`Local` is a type this module declares, and an argument to an import is built from \
     built-in types and imported type members for now"
)]
#[case::a_refinement_reading_a_value_passed_to_an_import(
    "lo = 1\nimport holder(T={Int where _ > lo})\n1\n",
    "this type's refinement reads `lo`, and an argument to an import is a type whose \
     refinements read no value for now"
)]
#[case::a_type_member_above_its_run(
    "x: h::Pair = (h::first=1, h::second=2)\nrun holder(T=Int) as h\n1\n",
    "the run `h` is declared below this use"
)]
#[case::a_built_in_type_name("param Int = String\n1\n", "`Int` is a built-in type")]
#[timeout(Duration::from_secs(10))]
fn a_misused_type_parameter_is_refused(#[case] root: &str, #[case] needle: &str) {
    assert_refused(
        &program(root, &[("box", BOX), ("holder", HOLDER), ("adder", ADDER)]),
        needle,
    );
}

/// A type argument that does not lower is its one error: the run reports no
/// missing argument for it.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_unknown_type_argument_is_reported_once() {
    let errors = compile_errors(&program(
        "run box(T=Nope, x=3) as b\nb::held\n",
        &[("box", BOX)],
    ));
    assert!(errors.contains("unknown type annotation: Nope"), "{errors}");
    assert_eq!(errors.matches("Error:").count(), 1, "{errors}");
}
