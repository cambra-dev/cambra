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
#[case::a_run("run counter as c\nrun shop(counter=c) as s\ns::total\n", 4)]
#[case::an_import("import counter\nrun shop(counter=counter) as s\ns::total\n", 4)]
#[case::through_an_imported_alias("run counter as c\nrun tally(counter=c) as t\nt::total\n", 6)]
#[case::through_an_alias(
    "Counter = Module{count: Int}\nimport counter\nparam c: Counter = counter\nc::count\n",
    3
)]
#[case::the_roots_default(
    "import counter\nparam c: Module{count: Int} = counter\nc::count + 1\n",
    4
)]
#[case::an_imports_argument("import counter\nimport shop(counter=counter)\nshop::total\n", 4)]
#[case::passed_on("run counter as c\nrun relay(counter=c) as r\nr::out\n", 4)]
#[case::a_member_bound_to_a_run("run holder as h\nh::k::count\n", 3)]
#[case::a_member_bound_to_a_run_passed(
    "run holder as h\nrun shop(counter=h::k) as s\ns::total\n",
    4
)]
#[case::a_use_name_of_a_run_member("run holder as h use k\nk::count\n", 3)]
#[case::a_use_name_passed("run holder as h use k\nrun shop(counter=k) as s\ns::total\n", 4)]
#[case::a_use_name_of_an_imports_member(
    "import counter\nimport bound(counter=counter) use k as kk\nkk::count\n",
    3
)]
#[case::a_module_entry("run holder as h\nrun nested(shop=h) as n\nn::v\n", 3)]
#[case::a_binding_of_a_parameter_returned(
    "run counter as c\nrun relayed(counter=c) as r\nr::k::count\n",
    3
)]
#[case::a_generic_member("run counter as c\nrun generic(counter=c) as g\ng::v\n", 4)]
#[case::a_feed_fed_through_it("run audit as a\nrun logger(log=a) as l\na::total\n", 6)]
#[case::a_feed_two_runs_feed(
    "run audit as a\nrun logger(log=a) as eu\nrun logger(log=a) as us\na::total\n",
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
                    "param shop: Module{k: Module{count: Int}}\npub v = shop::k::count\n",
                ),
                (
                    "relayed",
                    "param counter: Module{count: Int}\npub k = counter\n",
                ),
                (
                    "bound",
                    "param counter: Module{count: Int}\npub k = counter\n",
                ),
            ],
        ),
        Value::Int(expected),
    );
}

#[rstest]
#[case::a_member_its_type_does_not_name(
    "run counter as c\nrun narrow(counter=c) as n\n1\n",
    "the Module type of `counter` has no member `bump`"
)]
#[case::a_missing_member(
    "run counter as c\nrun wide(counter=c) as w\n1\n",
    "this module does not fit the parameter's Module type: module `counter` has no member `other`"
)]
#[case::a_private_member(
    "run counter as c\nrun peek(counter=c) as p\n1\n",
    "this module does not fit the parameter's Module type: `hidden` is private to module `counter`"
)]
#[case::a_member_of_another_type(
    "run counter as c\nrun mistyped(counter=c) as m\nm::v\n",
    "annotated as String"
)]
#[case::a_value_for_a_module(
    "run shop(counter=1) as s\n1\n",
    "the parameter `counter` is of Module type, and its argument is not a module"
)]
#[case::a_module_for_a_value(
    "run counter as c\nrun valued(n=c) as v\n1\n",
    "this argument is a module, and the parameter `n` is not annotated with a Module type"
)]
#[case::no_argument(
    "run shop as s\n1\n",
    "the run `s` passes no argument for the parameter `counter`"
)]
#[case::a_run_to_an_import(
    "run counter as c\nimport shop(counter=c)\n1\n",
    "`c` is a run name, and a run is not an argument to an import"
)]
#[case::a_module_type_as_a_values_type(
    "x: Module{count: Int} = 1\nx\n",
    "`Module{…}` is a Module type, the type of a module, and no value has one"
)]
#[case::an_alias_of_one_as_a_values_type(
    "C = Module{count: Int}\nx: C = 1\nx\n",
    "`C` is a Module type"
)]
#[case::a_module_as_a_value("run counter as c\nc\n", "`c` names a module")]
#[case::a_txn_entry(
    "run counter as c\nrun stocked(counter=c) as s\n1\n",
    "`stock` is a `Txn` variable, which a Module type does not name yet"
)]
#[case::a_member_less_generic_than_its_entry(
    "run rigid as c\nrun generic(counter=c) as g\ng::v\n",
    "annotated as forall (T) T => T, but inferred as forall (A) A => Int"
)]
#[case::a_member_its_module_entry_does_not_name(
    "run holder as h\nrun deep(shop=h) as d\n1\n",
    "the Module type of `shop::k` has no member `bump`"
)]
#[case::a_missing_module_member(
    "run counter as c\nrun nested(shop=c) as n\n1\n",
    "this module does not fit the parameter's Module type: module `counter` has no member `k` bound \
     to a module"
)]
#[case::a_forwarded_parameter_reaching_more(
    "run counter as c\nrun narrow_relay(counter=c) as r\n1\n",
    "this module does not fit the parameter's Module type: the Module type of `counter` does not \
     name `bump`"
)]
#[case::a_binding_of_a_parameter(
    "run counter as c\nrun rebound(counter=c) as r\n1\n",
    "the Module type of `x` has no member `bump`"
)]
#[case::a_returned_binding_of_a_parameter(
    "run counter as c\nrun relayed(counter=c) as r\nr::k::bump(1)\n",
    "the Module type of `r::k` has no member `bump`"
)]
#[case::a_use_name_above_its_run(
    "x = k::count\nrun holder as h use k\nx\n",
    "`k` is declared below this use"
)]
#[case::a_use_name_of_a_parameters_narrowed_member(
    "run counter as c\nrun relayed(counter=c) as r use k\nk::bump(1)\n",
    "the Module type of `k` has no member `bump`"
)]
#[case::a_feed_of_another_type(
    "run audit as a\nrun loud(log=a) as l\na::total\n",
    "annotated as Feed(String), but inferred as Feed(Int)"
)]
#[case::a_type_member(
    "C = Module{T: Int}\n1\n",
    "a type member of a Module type is not supported yet"
)]
#[case::a_binder_named_like_the_parameter(
    "run counter as c\nrun shadow(counter=c) as s\n1\n",
    "`counter` is a parameter of Module type, so no binder in its module takes it"
)]
#[case::an_import_passed_in_error(
    "import counter(nope=1)\nimport shop(counter=counter)\n1\n",
    "module `counter` has no parameter `nope`"
)]
#[case::a_parameter_named_like_an_import(
    "import counter\nparam counter: Module{count: Int} = counter\n1\n",
    "`counter` is already an import name"
)]
#[case::a_label_through_a_parameter(
    "run counter as c\nrun labelled(counter=c) as l\n1\n",
    "a label through a parameter of Module type is not supported yet"
)]
#[case::a_binding_used_above_it(
    "run counter as c\nx = k::count\nk = c\nx\n",
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
                    "param counter: Module{count: Int}\npub v = counter::bump(1)\n",
                ),
                (
                    "wide",
                    "param counter: Module{count: Int, other: Int}\npub v = 1\n",
                ),
                ("peek", "param counter: Module{hidden: Int}\npub v = 1\n"),
                (
                    "mistyped",
                    "param counter: Module{count: String}\npub v = counter::count\n",
                ),
                ("valued", "param n: Int\npub v = n\n"),
                (
                    "stocked",
                    "param counter: Module{stock: Mut(Int, Txn)}\npub v = 1\n",
                ),
                (
                    "shadow",
                    "param counter: Module{count: Int}\ndef f(counter):\n    counter\npub v = 1\n",
                ),
                ("audit", AUDIT),
                ("holder", HOLDER),
                (
                    "nested",
                    "param shop: Module{k: Module{count: Int}}\npub v = shop::k::count\n",
                ),
                (
                    "deep",
                    "param shop: Module{k: Module{count: Int}}\npub v = shop::k::bump(1)\n",
                ),
                (
                    "narrow_relay",
                    "param counter: Module{count: Int}\nrun shop(counter=counter) as s\npub v = 1\n",
                ),
                (
                    "rebound",
                    "param counter: Module{count: Int}\nx = counter\npub v = x::bump(1)\n",
                ),
                (
                    "relayed",
                    "param counter: Module{count: Int}\npub k = counter\n",
                ),
                ("generic", GENERIC),
                ("rigid", "pub def id(x):\n    x + 1\n"),
                (
                    "labelled",
                    "param counter: Module{count: Int}\npub v = (counter::price=1).counter::price\n",
                ),
                (
                    "loud",
                    "param log: Module{events: Feed(String)}\nlog::events << \"x\"\n",
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
#[case::a_value_member("x = c::count\nrun counter as c\nx\n")]
#[case::a_module("k = c\nrun counter as c\nk::count\n")]
#[timeout(Duration::from_secs(10))]
fn a_path_above_its_qualifier_is_reported_once(#[case] root: &str) {
    let errors = compile_errors(&program(root, &[("counter", COUNTER)]));
    assert!(
        errors.contains("the run `c` is declared below this use"),
        "{errors}"
    );
    assert_eq!(errors.matches("Error:").count(), 1, "{errors}");
}

/// Two imports that pass one module the same import reach one shared run, and
/// its home names the argument's shared run (`docs/chl-spec.md`, "9.2
/// Imports").
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_import_passing_a_module_reaches_one_shared_run_per_argument() {
    let program = program(
        "import counter\nimport shop(counter=counter)\nimport both\nshop::total + both::t\n",
        &[
            ("counter", COUNTER),
            ("shop", SHOP),
            (
                "both",
                "import counter\nimport shop(counter=counter)\npub t = shop::total\n",
            ),
        ],
    );
    let expected = ["both", "counter", "shop(counter=counter)"];
    assert_eq!(
        shared_runs(&program),
        expected.iter().map(|s| s.to_string()).collect()
    );
}
