//! Module types, and parameters that take a module: a module passed to a run or
//! an import as an argument, or bound to a member (`docs/chl-spec.md`, "9.4
//! Parameters", "9.8 Module types").

use std::time::Duration;

use cambra::interpreter::Value;
use indoc::indoc;
use rstest_log::rstest;

use crate::helpers::*;
use crate::modules::{assert_refused, compile_errors, program, shared_runs};

/// A module of a value, two functions, one generic, and a private value.
const COUNTER: &str = indoc! {"
    pub count = 3
    pub def bump(x):
        x + 1
    pub def id(x):
        x
    hidden = 1
"};

/// A module that uses a generic member of the module it takes at two types.
const GENERIC: &str = indoc! {"
    param counter: Module{id: forall (T) T => T}
    pub v = counter::id(3) + (1 if counter::id(\"a\") == \"a\" else 0)
"};

/// A module that takes a module with a `count` and a `bump`.
const SHOP: &str = indoc! {"
    param counter: Module{count: Int, bump: Int => Int}
    pub total = counter::bump(counter::count)
"};

/// A module whose parameter's Module type is an alias another module exports.
const TALLY: &str = indoc! {"
    import api
    param counter: api::Counter
    pub total = counter::count * 2
"};

/// A module that passes the module it takes on to a run of `shop`.
const RELAY: &str = indoc! {"
    param counter: Module{count: Int, bump: Int => Int}
    run shop(counter=counter) as s
    pub out = s::total
"};

/// A module that publishes a feed and its total.
const AUDIT: &str = indoc! {"
    pub events = defer()
    pub total = sum([e for e in events])
"};

/// A module that feeds the feed of the module it takes.
const LOGGER: &str = indoc! {"
    param log: Module{events: Feed(Int)}
    for x in [1, 2, 3]:
        log::events << x
"};

/// A module that returns a run it declares, by binding it to a member.
const HOLDER: &str = indoc! {"
    run counter as c
    pub k = c
"};

/// A parameter of Module type reaches the members of the module its argument
/// names: a run, an import, its default, or a member bound to a run.
#[rstest]
#[case::a_run(indoc! {"
    run counter as c
    run shop(counter=c) as s
    s::total
"}, 4)]
#[case::an_import(indoc! {"
    import counter
    run shop(counter=counter) as s
    s::total
"}, 4)]
#[case::through_an_imported_alias(indoc! {"
    run counter as c
    run tally(counter=c) as t
    t::total
"}, 6)]
#[case::through_an_alias(
    indoc! {"
        Counter = Module{count: Int}
        import counter
        param c: Counter = counter
        c::count
    "},
    3
)]
#[case::the_roots_default(
    indoc! {"
        import counter
        param c: Module{count: Int} = counter
        c::count + 1
    "},
    4
)]
#[case::an_imports_argument(indoc! {"
    import counter
    import shop(counter=counter)
    shop::total
"}, 4)]
#[case::passed_on(indoc! {"
    run counter as c
    run relay(counter=c) as r
    r::out
"}, 4)]
#[case::a_member_bound_to_a_run(indoc! {"
    run holder as h
    h::k::count
"}, 3)]
#[case::a_member_bound_to_a_run_passed(
    indoc! {"
        run holder as h
        run shop(counter=h::k) as s
        s::total
    "},
    4
)]
#[case::a_use_name_of_a_run_member(indoc! {"
    run holder as h use k
    k::count
"}, 3)]
#[case::a_use_name_passed(indoc! {"
    run holder as h use k
    run shop(counter=k) as s
    s::total
"}, 4)]
#[case::a_use_name_of_an_imports_member(
    indoc! {"
        import counter
        import bound(counter=counter) use k as kk
        kk::count
    "},
    3
)]
#[case::a_module_entry(indoc! {"
    run holder as h
    run nested(shop=h) as n
    n::v
"}, 3)]
#[case::a_binding_of_a_parameter_returned(
    indoc! {"
        run counter as c
        run relayed(counter=c) as r
        r::k::count
    "},
    3
)]
#[case::a_generic_member(indoc! {"
    run counter as c
    run generic(counter=c) as g
    g::v
"}, 4)]
#[case::a_feed_fed_through_it(indoc! {"
    run audit as a
    run logger(log=a) as l
    a::total
"}, 6)]
#[case::a_feed_two_runs_feed(
    indoc! {"
        run audit as a
        run logger(log=a) as eu
        run logger(log=a) as us
        a::total
    "},
    12
)]
#[timeout(Duration::from_secs(10))]
fn a_module_typed_parameter_reaches_its_arguments_members(
    #[case] root: &str,
    #[case] expected: i64,
) {
    check_program_scalar(
        &program(
            root,
            &[
                ("counter", COUNTER),
                ("shop", SHOP),
                ("tally", TALLY),
                ("api", "pub Counter = Module{count: Int}\n"),
                ("relay", RELAY),
                ("holder", HOLDER),
                ("audit", AUDIT),
                ("logger", LOGGER),
                ("generic", GENERIC),
                (
                    "nested",
                    indoc! {"
                        param shop: Module{k: Module{count: Int}}
                        pub v = shop::k::count
                    "},
                ),
                (
                    "relayed",
                    indoc! {"
                        param counter: Module{count: Int}
                        pub k = counter
                    "},
                ),
                (
                    "bound",
                    indoc! {"
                        param counter: Module{count: Int}
                        pub k = counter
                    "},
                ),
            ],
        ),
        Value::Int(expected),
    );
}

#[rstest]
#[case::a_member_its_type_does_not_name(
    indoc! {"
        run counter as c
        run narrow(counter=c) as n
        1
    "},
    "the Module type of `counter` has no member `bump`"
)]
#[case::a_missing_member(
    indoc! {"
        run counter as c
        run wide(counter=c) as w
        1
    "},
    "this module does not fit the parameter's Module type: module `counter` has no member `other`"
)]
#[case::a_private_member(
    indoc! {"
        run counter as c
        run peek(counter=c) as p
        1
    "},
    "this module does not fit the parameter's Module type: `hidden` is private to module `counter`"
)]
#[case::a_member_of_another_type(
    indoc! {"
        run counter as c
        run mistyped(counter=c) as m
        m::v
    "},
    "annotated as String"
)]
#[case::a_value_for_a_module(
    indoc! {"
        run shop(counter=1) as s
        1
    "},
    "the parameter `counter` is of Module type, and its argument is not a module"
)]
#[case::a_module_for_a_value(
    indoc! {"
        run counter as c
        run valued(n=c) as v
        1
    "},
    "this argument is a module, and the parameter `n` is not annotated with a Module type"
)]
#[case::a_value_for_a_module_to_an_import(
    indoc! {"
        import shop(counter=1)
        1
    "},
    "the parameter `counter` is of Module type, and its argument is not a module: pass an import \
     name"
)]
#[case::a_module_for_a_value_to_an_import(
    indoc! {"
        import counter as c
        import valued(n=c)
        1
    "},
    "this argument is a module, and the parameter `n` is not annotated with a Module type"
)]
#[case::no_argument(
    indoc! {"
        run shop as s
        1
    "},
    "the run `s` passes no argument for the parameter `counter`"
)]
#[case::a_run_to_an_import(
    indoc! {"
        run counter as c
        import shop(counter=c)
        1
    "},
    "`c` is a run name, and a run is not an argument to an import"
)]
#[case::a_module_type_as_a_values_type(
    indoc! {"
        x: Module{count: Int} = 1
        x
    "},
    "`Module{…}` is a Module type, the type of a module, and no value has one"
)]
#[case::an_alias_of_one_as_a_values_type(
    indoc! {"
        C = Module{count: Int}
        x: C = 1
        x
    "},
    "`C` is a Module type"
)]
#[case::a_module_as_a_value(indoc! {"
    run counter as c
    c
"}, "`c` names a module")]
#[case::a_txn_entry(
    indoc! {"
        run counter as c
        run stocked(counter=c) as s
        1
    "},
    "`stock` is a `Txn` variable, which a Module type does not name yet"
)]
#[case::a_member_less_generic_than_its_entry(
    indoc! {"
        run rigid as c
        run generic(counter=c) as g
        g::v
    "},
    "annotated as forall (T) T => T, but inferred as forall (A) A => Int"
)]
#[case::a_member_its_module_entry_does_not_name(
    indoc! {"
        run holder as h
        run deep(shop=h) as d
        1
    "},
    "the Module type of `shop::k` has no member `bump`"
)]
#[case::a_missing_module_member(
    indoc! {"
        run counter as c
        run nested(shop=c) as n
        1
    "},
    "this module does not fit the parameter's Module type: module `counter` has no member `k` bound \
     to a module"
)]
#[case::a_forwarded_parameter_reaching_more(
    indoc! {"
        run counter as c
        run narrow_relay(counter=c) as r
        1
    "},
    "this module does not fit the parameter's Module type: the Module type of `counter` does not \
     name `bump`"
)]
#[case::a_binding_of_a_parameter(
    indoc! {"
        run counter as c
        run rebound(counter=c) as r
        1
    "},
    "the Module type of `x` has no member `bump`"
)]
#[case::a_returned_binding_of_a_parameter(
    indoc! {"
        run counter as c
        run relayed(counter=c) as r
        r::k::bump(1)
    "},
    "the Module type of `r::k` has no member `bump`"
)]
#[case::a_use_name_above_its_run(
    indoc! {"
        x = k::count
        run holder as h use k
        x
    "},
    "`k` is declared below this use"
)]
#[case::a_use_name_of_a_parameters_narrowed_member(
    indoc! {"
        run counter as c
        run relayed(counter=c) as r use k
        k::bump(1)
    "},
    "the Module type of `k` has no member `bump`"
)]
#[case::a_feed_of_another_type(
    indoc! {"
        run audit as a
        run loud(log=a) as l
        a::total
    "},
    "annotated as Feed(String), but inferred as Feed(Int)"
)]
#[case::a_type_member_with_a_type_for_a_kind(
    indoc! {"
        C = Module{T: Int}
        1
    "},
    "`T: …` states the kind of the type member `T`, `Type` or `SubtypesOf(T)`"
)]
#[case::a_binder_named_like_the_parameter(
    indoc! {"
        run counter as c
        run shadow(counter=c) as s
        1
    "},
    "`counter` is a parameter of Module type, so no binder in its module takes it"
)]
#[case::an_import_passed_in_error(
    indoc! {"
        import counter(nope=1)
        import shop(counter=counter)
        1
    "},
    "module `counter` has no parameter `nope`"
)]
#[case::a_parameter_named_like_an_import(
    indoc! {"
        import counter
        param counter: Module{count: Int} = counter
        1
    "},
    "`counter` is already an import name"
)]
#[case::a_label_through_a_parameter(
    indoc! {"
        run counter as c
        run labelled(counter=c) as l
        1
    "},
    "a label through a parameter of Module type is not supported yet"
)]
#[case::a_binding_used_above_it(
    indoc! {"
        run counter as c
        x = k::count
        k = c
        x
    "},
    "`k` is declared below this use"
)]
#[timeout(Duration::from_secs(10))]
fn a_misused_module_type_is_refused(#[case] root: &str, #[case] needle: &str) {
    assert_refused(
        &program(
            root,
            &[
                ("counter", COUNTER),
                ("shop", SHOP),
                (
                    "narrow",
                    indoc! {"
                        param counter: Module{count: Int}
                        pub v = counter::bump(1)
                    "},
                ),
                (
                    "wide",
                    indoc! {"
                        param counter: Module{count: Int, other: Int}
                        pub v = 1
                    "},
                ),
                (
                    "peek",
                    indoc! {"
                        param counter: Module{hidden: Int}
                        pub v = 1
                    "},
                ),
                (
                    "mistyped",
                    indoc! {"
                        param counter: Module{count: String}
                        pub v = counter::count
                    "},
                ),
                (
                    "valued",
                    indoc! {"
                        param n: Int
                        pub v = n
                    "},
                ),
                (
                    "stocked",
                    indoc! {"
                        param counter: Module{stock: Mut(Int, Txn)}
                        pub v = 1
                    "},
                ),
                (
                    "shadow",
                    indoc! {"
                        param counter: Module{count: Int}
                        def f(counter):
                            counter
                        pub v = 1
                    "},
                ),
                ("audit", AUDIT),
                ("holder", HOLDER),
                (
                    "nested",
                    indoc! {"
                        param shop: Module{k: Module{count: Int}}
                        pub v = shop::k::count
                    "},
                ),
                (
                    "deep",
                    indoc! {"
                        param shop: Module{k: Module{count: Int}}
                        pub v = shop::k::bump(1)
                    "},
                ),
                (
                    "narrow_relay",
                    indoc! {"
                        param counter: Module{count: Int}
                        run shop(counter=counter) as s
                        pub v = 1
                    "},
                ),
                (
                    "rebound",
                    indoc! {"
                        param counter: Module{count: Int}
                        x = counter
                        pub v = x::bump(1)
                    "},
                ),
                (
                    "relayed",
                    indoc! {"
                        param counter: Module{count: Int}
                        pub k = counter
                    "},
                ),
                ("generic", GENERIC),
                (
                    "rigid",
                    indoc! {"
                        pub def id(x):
                            x + 1
                    "},
                ),
                (
                    "labelled",
                    indoc! {"
                        param counter: Module{count: Int}
                        pub v = (counter::price=1).counter::price
                    "},
                ),
                (
                    "loud",
                    indoc! {r#"
                        param log: Module{events: Feed(String)}
                        log::events << "x"
                    "#},
                ),
            ],
        ),
        needle,
    );
}

/// A path written above the statement binding its first segment is reported
/// once: by the binding, when the path names a module, and otherwise by the
/// value's lowering.
#[rstest]
#[case::a_value_member(indoc! {"
    x = c::count
    run counter as c
    x
"})]
#[case::a_module(indoc! {"
    k = c
    run counter as c
    k::count
"})]
#[timeout(Duration::from_secs(10))]
fn a_path_above_its_qualifier_is_reported_once(#[case] root: &str) {
    let errors = compile_errors(&program(root, &[("counter", COUNTER)]));
    assert!(
        errors.contains("the run `c` is declared below this use"),
        "{errors}"
    );
    assert_eq!(errors.matches("Error:").count(), 1, "{errors}");
}

/// A module argument whose module has errors of its own adds no error, as a
/// reference into that module adds none: the module's own errors account for
/// the run.
#[rstest]
#[case::to_a_run(indoc! {"
    import bad
    run lib(dep=bad) as l
    l::m
"})]
#[case::to_an_import(indoc! {"
    import bad
    import lib(dep=bad)
    lib::m
"})]
#[timeout(Duration::from_secs(10))]
fn a_module_argument_with_errors_adds_no_error(#[case] root: &str) {
    let lib = indoc! {"
        param dep: Module{n: Int}
        pub m = dep::n
    "};
    let errors = compile_errors(&program(root, &[("bad", "pub n = = 1\n"), ("lib", lib)]));
    assert!(errors.contains("bad.cambra:1:9"), "{errors}");
    assert_eq!(errors.matches("Error:").count(), 1, "{errors}");
}

/// Two imports that pass one module the same import reach one shared run, and
/// its home names the argument's shared run (`docs/chl-spec.md`, "9.2
/// Imports").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_import_passing_a_module_reaches_one_shared_run_per_argument() {
    let program = program(
        indoc! {"
            import counter
            import shop(counter=counter)
            import both
            shop::total + both::t
        "},
        &[
            ("counter", COUNTER),
            ("shop", SHOP),
            (
                "both",
                indoc! {"
                    import counter
                    import shop(counter=counter)
                    pub t = shop::total
                "},
            ),
        ],
    );
    let expected = ["both", "counter", "shop(counter=counter)"];
    assert_eq!(
        shared_runs(&program),
        expected.iter().map(|s| s.to_string()).collect()
    );
}

/// A module whose type member is a refinement, and a function over it.
const POSITIVE: &str = indoc! {"
    pub Count = {Int where _ > 0}
    pub def keep(c: Count) => Count:
        c
"};

/// A module whose type member is `Int`, and a function over it.
const INTS: &str = indoc! {"
    pub Count = Int
    pub def keep(c: Count) => Count:
        c
"};

/// A module that knows its parameter's `Count` only through a bound.
const BOUNDED: &str = indoc! {"
    param n: Module{Count <: Int, keep: Count => Count}
    pub v: n::Count = n::keep(3)
"};

/// Each Module-typed parameter takes its argument's type members: `Name <: T`
/// and `Name: K` the argument's own, `Name = T` the written `T`
/// (`docs/chl-spec.md`, "9.8 Module types").
#[rstest]
#[case::a_bounded_member(indoc! {"
    run positive as p
    run bounded(n=p) as b
    b::v
"}, 3)]
#[case::a_kinded_member(indoc! {"
    run positive as p
    run kinded(n=p) as k
    k::v
"}, 3)]
#[case::a_subtypes_of_kind(indoc! {"
    run positive as p
    run subtyped(n=p) as k
    k::v
"}, 3)]
#[case::an_exact_member(indoc! {"
    run ints as i
    run exact(n=i) as e
    e::w
"}, 0)]
#[case::an_imported_argument(indoc! {"
    import positive
    import bounded(n=positive)
    bounded::v
"}, 3)]
#[case::a_parameter_passed_on(indoc! {"
    run positive as p
    run relay(n=p) as r
    r::v
"}, 3)]
#[case::the_roots_default(
    indoc! {"
        import positive
        param n: Module{Count <: Int, keep: Count => Count} = positive
        x: n::Count = n::keep(2)
        x
    "},
    2
)]
#[case::two_parameters_of_one_module_type(
    indoc! {"
        run ints as i
        run positive as p
        run pair(a=i, b=p) as q
        q::w
    "},
    0
)]
#[timeout(Duration::from_secs(10))]
fn a_module_typed_parameter_takes_its_arguments_type_members(
    #[case] root: &str,
    #[case] expected: i64,
) {
    check_program_scalar(
        &program(
            root,
            &[
                ("positive", POSITIVE),
                ("ints", INTS),
                ("bounded", BOUNDED),
                (
                    "kinded",
                    indoc! {"
                        param n: Module{Count: Type, keep: Count => Count}
                        pub v = n::keep(3)
                    "},
                ),
                (
                    "subtyped",
                    indoc! {"
                        param n: Module{Count: SubtypesOf(Int), keep: Count => Count}
                        pub v = n::keep(3)
                    "},
                ),
                (
                    "exact",
                    indoc! {"
                        param n: Module{Count = Int, keep: Count => Count}
                        pub w: n::Count = 0
                    "},
                ),
                (
                    "relay",
                    indoc! {"
                        param n: Module{Count <: Int, keep: Count => Count}
                        run bounded(n=n) as b
                        pub v = b::v
                    "},
                ),
                (
                    "pair",
                    indoc! {"
                        Num = Module{Count <: Int, keep: Count => Count}
                        param a: Num
                        param b: Num
                        pub w: a::Count = 0
                        pub v: b::Count = 1
                    "},
                ),
            ],
        ),
        Value::Int(expected),
    );
}

#[rstest]
#[case::a_value_outside_the_arguments_member(
    indoc! {"
        run positive as p
        run zero(n=p) as z
        1
    "},
    "annotated as {Int where _ > 0}, but inferred as {Int where _ == 0}"
)]
#[case::an_exact_member_the_argument_does_not_fit(
    indoc! {"
        run positive as p
        run exact(n=p) as e
        1
    "},
    "annotated as Int => Int, but inferred as {Int where _ > 0} => {Int where _ > 0}"
)]
#[case::a_missing_type_member(
    indoc! {"
        run plain as p
        run bounded(n=p) as b
        1
    "},
    "this module does not fit the parameter's Module type: module `plain` has no type member \
     `Count`"
)]
#[case::a_missing_type_member_of_an_import(
    indoc! {"
        import plain
        import bounded(n=plain)
        1
    "},
    "module `plain` has no type member `Count`"
)]
#[case::an_entry_before_its_type_member(
    indoc! {"
        C = Module{keep: Count => Count, Count <: Int}
        1
    "},
    "unknown type annotation: Count"
)]
#[case::a_value_member_written_with_a_bound(
    indoc! {"
        C = Module{count <: Int}
        1
    "},
    "`count` is a value member, written `count: T`"
)]
#[case::an_argument_below_the_run(
    indoc! {"
        import positive
        run bounded(n=m) as b
        param m: Module{Count <: Int, keep: Count => Count} = positive
        b::v
    "},
    "the argument for `n` is declared below this statement"
)]
#[timeout(Duration::from_secs(10))]
fn a_misused_type_member_is_refused(#[case] root: &str, #[case] needle: &str) {
    assert_refused(
        &program(
            root,
            &[
                ("positive", POSITIVE),
                ("bounded", BOUNDED),
                (
                    "plain",
                    indoc! {"
                        pub def keep(c: Int) => Int:
                            c
                    "},
                ),
                (
                    "zero",
                    indoc! {"
                        param n: Module{Count <: Int, keep: Count => Count}
                        pub w: n::Count = 0
                    "},
                ),
                (
                    "exact",
                    indoc! {"
                        param n: Module{Count = Int, keep: Count => Count}
                        pub w: n::Count = 0
                    "},
                ),
            ],
        ),
        needle,
    );
}
