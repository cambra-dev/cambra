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
#[case::a_value(indoc! {"
    run box(T=Int, x=3) as b
    b::held
"}, Value::Int(3))]
#[case::a_function(indoc! {"
    run box(T=Int, x=3) as b
    b::get(5)
"}, Value::Int(5))]
#[case::a_used_function(indoc! {"
    run box(T=Int, x=3) as b use get
    get(5)
"}, Value::Int(5))]
#[case::two_runs_at_two_types(
    indoc! {r#"
        run box(T=String, x="a") as s
        run box(T=Int, x=3) as i
        i::held
    "#},
    Value::Int(3)
)]
#[case::a_local_alias(
    indoc! {"
        Pos = {Int where _ > 0}
        run box(T=Pos, x=3) as b
        b::held
    "},
    Value::Int(3)
)]
#[case::a_refinement_reading_a_local_value(
    indoc! {"
        lo = 2
        run box(T={Int where _ > lo}, x=3) as b
        b::held
    "},
    Value::Int(3)
)]
#[case::an_inferred_kind(indoc! {"
    run adder(T=Int, x=4) as a
    a::y
"}, Value::Int(5))]
#[case::a_default_over_another_parameter(
    indoc! {"
        run keyed(K=Int, x=(5, 6)) as k
        k::held
    "},
    Value::Int(5)
)]
#[case::a_type_member(
    indoc! {"
        run holder(T=Int) as h
        x: h::Pair = (h::first=1, h::second=2)
        x.h::second
    "},
    Value::Int(2)
)]
#[case::a_used_type_member(
    indoc! {"
        run holder(T=Int) as h use Pair
        x: Pair = (h::first=1, h::second=2)
        x.h::second
    "},
    Value::Int(2)
)]
#[case::a_nested_run_at_a_type_over_a_parameter(
    indoc! {"
        run nest(U=Int, y=4) as n
        n::out.n::a
    "},
    Value::Int(4)
)]
#[case::a_type_member_through_a_member(
    indoc! {"
        run shop as s
        x: s::k::Pair = (s::k::first=1, s::k::second=2)
        x.s::k::first
    "},
    Value::Int(1)
)]
#[case::a_module_type_over_a_parameter(
    indoc! {"
        run box(T=Int, x=7) as b
        run typed(T=Int, m=b) as t
        t::v
    "},
    Value::Int(7)
)]
#[case::a_root_parameter_takes_its_default(indoc! {"
    param T = Int
    x: T = 3
    x
"}, Value::Int(3))]
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
                (
                    "shop",
                    indoc! {"
                        run holder(T=Int) as h
                        pub k = h
                    "},
                ),
                (
                    "typed",
                    indoc! {"
                        param T
                        param m: Module{held: T}
                        pub v: T = m::held
                    "},
                ),
            ],
        ),
        expected,
    );
}

/// An import takes its type arguments as a run does, and an argument may be a
/// type member of another import, written above it or below.
#[rstest]
#[case::a_value(indoc! {"
    import valued(T=Int)
    valued::z.valued::a
"}, Value::Int(3))]
#[case::a_refinement_of_literals(
    indoc! {"
        import valued(T={Int where _ > 0})
        valued::z.valued::a
    "},
    Value::Int(3)
)]
#[case::a_type_member(
    indoc! {"
        import holder(T=Int)
        x: holder::Pair = (holder::first=1, holder::second=2)
        x.holder::first
    "},
    Value::Int(1)
)]
#[case::a_used_type_member(
    indoc! {"
        import holder(T=Int) use Pair
        x: Pair = (holder::first=1, holder::second=2)
        x.holder::first
    "},
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
            (
                "both",
                indoc! {"
                    import valued(T=Int)
                    pub t = 1
                "},
            ),
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
    indoc! {"
        run box(x=3) as b
        1
    "},
    "the run `b` passes no argument for the parameter `T`, which has no default"
)]
#[case::an_import_missing_one(
    indoc! {"
        import holder
        1
    "},
    "this import passes no argument for the parameter `T`, which has no default"
)]
#[case::a_root_parameter_without_a_default(
    indoc! {"
        param T
        1
    "},
    "the root module's parameter `T` has no default"
)]
#[case::an_argument_outside_its_type(
    indoc! {"
        run box(T={Int where _ > 0}, x=0) as b
        b::held
    "},
    "annotated as {Int where _ > 0}, but inferred as {Int where _ == 0}"
)]
#[case::a_type_member_of_the_wrong_type(
    indoc! {r#"
        run holder(T=Int) as h
        x: h::Pair = (h::first=1, h::second="a")
        1
    "#},
    "annotated as {holder::first: Int, holder::second: Int}"
)]
#[case::an_inferred_kind_the_argument_does_not_fit(
    indoc! {r#"
        run adder(T=String, x="a") as a
        a::y
    "#},
    "No Addable instance"
)]
#[case::a_local_alias_passed_to_an_import(
    indoc! {"
        Local = Int
        import holder(T=Local)
        1
    "},
    "`Local` is a type this module declares, and an argument to an import is built from \
     built-in types and imported type members for now"
)]
#[case::a_refinement_reading_a_value_passed_to_an_import(
    indoc! {"
        lo = 1
        import holder(T={Int where _ > lo})
        1
    "},
    "this type's refinement reads `lo`, and an argument to an import is a type whose \
     refinements read no value for now"
)]
#[case::a_type_member_above_its_run(
    indoc! {"
        x: h::Pair = (h::first=1, h::second=2)
        run holder(T=Int) as h
        1
    "},
    "the run `h` is declared below this use"
)]
#[case::a_built_in_type_name(indoc! {"
    param Int = String
    1
"}, "`Int` is a built-in type")]
#[case::an_argument_outside_its_bound(
    indoc! {r#"
        run below(T=String, x="a") as b
        1
    "#},
    "annotated as Int, but inferred as String"
)]
#[case::an_imports_argument_outside_its_bound(
    indoc! {"
        import capped(T=String)
        1
    "},
    "annotated as Int, but inferred as String"
)]
#[case::a_use_beyond_the_bound(indoc! {"
    run beyond(T=Int, x=3) as b
    b::v
"}, "No Addable instance")]
#[timeout(Duration::from_secs(10))]
fn a_misused_type_parameter_is_refused(#[case] root: &str, #[case] needle: &str) {
    assert_refused(
        &program(
            root,
            &[
                ("box", BOX),
                ("holder", HOLDER),
                ("adder", ADDER),
                (
                    "below",
                    indoc! {"
                        param T <: Int
                        param x: T
                        pub v = x
                    "},
                ),
                (
                    "capped",
                    indoc! {"
                        param T <: Int
                        pub Pair = {T, T}
                    "},
                ),
                (
                    "beyond",
                    indoc! {r#"
                        param T <: {Int where _ > 0}
                        param x: T
                        pub v = x + "a"
                    "#},
                ),
            ],
        ),
        needle,
    );
}

/// A type argument outside its parameter's bound is reported at the argument.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_bound_is_checked_at_the_argument() {
    let errors = compile_errors(&program(
        indoc! {r#"
            run below(T=String, x="a") as b
            1
        "#},
        &[(
            "below",
            indoc! {"
                param T <: Int
                param x: T
                pub v = x
            "},
        )],
    ));
    assert!(errors.contains("main.cambra:1:11"), "{errors}");
}

/// A type argument that does not lower is its one error: the run reports no
/// missing argument for it.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_unknown_type_argument_is_reported_once() {
    let errors = compile_errors(&program(
        indoc! {"
            run box(T=Nope, x=3) as b
            b::held
        "},
        &[("box", BOX)],
    ));
    assert!(errors.contains("unknown type annotation: Nope"), "{errors}");
    assert_eq!(errors.matches("Error:").count(), 1, "{errors}");
}
