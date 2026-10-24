//! Link-time constants (`docs/chl-spec.md`, "9.19 Constants"): `const` marks a binding or a
//! value parameter whose value is fixed once the program is linked, a declaration's
//! refinements name only constants, and a type reaching a `const` parameter is one type per
//! value its runs give it ("Nominal type identity").

use std::time::Duration;

use cambra::interpreter::Value;
use indoc::indoc;
use rstest_log::rstest;

use super::helpers::*;
use super::modules::{compile_errors, program};

/// A module whose type reaches its `const` parameter through a refinement, and whose other
/// type reaches it through a method.
const SHOP: &str = indoc! {"
    const param max_rate: Int
    const limit = max_rate * 2
    pub type Capped = {Int where _ <= limit}
    pub type Tag = Int
    pub def Tag::rate(self) => Int:
        max_rate
"};

/// A module that passes its own `const` parameter on to a run of `shop`.
const MID: &str = indoc! {"
    const param r: Int
    run shop(max_rate=r + 1) as s
    pub t = s::Tag::new(1)
"};

/// A `const` binding is a constant built from literals, `const` names, operators and the
/// fields of records.
#[rstest]
#[case::arithmetic(
    indoc! {"
        const a = 3
        const b = a * 2 + 1
        b
    "},
    7
)]
#[case::comparison_and_ternary(
    indoc! {"
        const a = 3
        const b = 10 if 1 < a < 5 else 20
        b
    "},
    10
)]
#[case::record_field(
    indoc! {"
        const p = (x=2, y=3)
        const q = p.x + p.y
        q
    "},
    5
)]
#[case::root_parameter(
    indoc! {"
        const param n: Int = 4
        const m = n * n
        m
    "},
    16
)]
#[timeout(Duration::from_secs(10))]
fn a_constant_has_the_value_it_computes(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A constant reads nothing but constants: a binding without `const`, a value parameter
/// without `const`, a mutable variable and a function are each refused at the reference, and
/// a call is refused as not supported yet. A constant with no value is refused where it is
/// computed, and `const` stands only at a module's top level, on a binding or a value
/// parameter.
#[rstest]
#[case::plain_binding(
    indoc! {"
        ten = 10
        const limit = ten
        limit
    "},
    "`ten` is not a constant: it is bound without `const`"
)]
#[case::parameter(
    indoc! {"
        param n: Int = 1
        const limit = n
        limit
    "},
    "`n` is a parameter without `const`"
)]
#[case::mutable(
    indoc! {"
        total := 0
        const limit = total
        limit
    "},
    "`total` is a mutable variable"
)]
#[case::call(
    indoc! {"
        def f(x):
            x
        const limit = f(1)
        limit
    "},
    "a call in a constant is not supported yet"
)]
#[case::comprehension(
    indoc! {"
        const xs = [x for x in [1, 2]]
        xs
    "},
    "this is not a constant"
)]
#[case::no_value(
    indoc! {"
        const limit = 1 // 0
        limit
    "},
    "`1 // 0` has no value"
)]
#[case::nested(
    indoc! {"
        def f(x):
            const y = 1
            x + y
        f(1)
    "},
    "`const` stands only at a module's top level"
)]
#[case::type_parameter(
    indoc! {"
        const param T <: Int
        1
    "},
    "`T` is a type parameter, which is fixed at link time already"
)]
#[timeout(Duration::from_secs(10))]
fn a_constant_reads_only_constants(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
}

/// A declaration's refinement reads a `const` binding or another module's public `const`
/// member, qualified or through a `use` name, as the value it is, and refuses any other name.
#[rstest]
#[case::binding(
    program(
        indoc! {"
            const limit = 2 * 5
            type Capped = {Int where _ <= limit}
            Capped::new(3).extract()
        "},
        &[]
    ),
    3
)]
#[case::imported(
    program(
        indoc! {"
            import cfg
            type Small = {Int where _ <= cfg::rate}
            Small::new(3).extract()
        "},
        &[("cfg", "pub const rate = 5\n")]
    ),
    3
)]
#[case::used(
    program(
        indoc! {"
            import cfg use rate
            type Small = {Int where _ <= rate}
            Small::new(3).extract()
        "},
        &[("cfg", "pub const rate = 5\n")]
    ),
    3
)]
#[timeout(Duration::from_secs(10))]
fn a_declaration_refines_by_a_constant(
    #[case] program: cambra::ccl::load::LoadedProgram,
    #[case] expected: i64,
) {
    check_program_scalar(&program, Value::Int(expected));
}

/// A construction the constant's value refuses is refused, and so is a refinement naming an
/// imported member that is not `const`.
#[rstest]
#[case::beyond_the_constant(
    indoc! {"
        import cfg
        type Small = {Int where _ <= cfg::rate}
        Small::new(30).extract()
    "},
    "pub const rate = 5\n",
    "expected {Int | __elem <= 5}"
)]
#[case::imported_not_const(
    indoc! {"
        import cfg
        type Small = {Int where _ <= cfg::rate}
        Small::new(3).extract()
    "},
    "pub rate = 5\n",
    "`cfg::rate` is not a constant: module `cfg` has no public `const` member `rate`"
)]
#[timeout(Duration::from_secs(10))]
fn a_declaration_refuses_what_its_constant_refuses(
    #[case] root: &str,
    #[case] cfg: &str,
    #[case] needle: &str,
) {
    let errors = compile_errors(&program(root, &[("cfg", cfg)]));
    assert!(errors.contains(needle), "{errors}");
}

/// A run's `const` argument is the value a constructor's refinement checks against, whether
/// the run, an import or a constant of another module gives it.
#[rstest]
#[case::run(
    indoc! {"
        run shop(max_rate=5) as eu
        eu::Capped::new(3).extract()
    "},
    3
)]
#[case::import(
    indoc! {"
        import shop(max_rate=5)
        shop::Capped::new(3).extract()
    "},
    3
)]
#[case::imported_constant(
    indoc! {"
        import cfg
        run shop(max_rate=cfg::rate + 1) as eu
        eu::Capped::new(11).extract()
    "},
    11
)]
#[case::method(
    indoc! {"
        run shop(max_rate=5) as eu
        eu::Tag::new(1).rate()
    "},
    5
)]
#[case::used_constant(
    indoc! {"
        import cfg use rate
        run shop(max_rate=rate) as eu
        eu::Tag::new(1).rate()
    "},
    5
)]
#[timeout(Duration::from_secs(10))]
fn a_run_gives_its_constant_a_value(#[case] root: &str, #[case] expected: i64) {
    check_program_scalar(
        &program(root, &[("shop", SHOP), ("cfg", "pub const rate = 5\n")]),
        Value::Int(expected),
    );
}

/// A construction the run's value refuses is refused, and an argument for a `const`
/// parameter must be a constant.
#[rstest]
#[case::beyond_the_value(
    indoc! {"
        run shop(max_rate=5) as eu
        eu::Capped::new(30).extract()
    "},
    "expected {Int | __elem <= 10}"
)]
#[case::not_a_constant(
    indoc! {"
        x = 5
        run shop(max_rate=x) as eu
        1
    "},
    "`x` is not a constant: it is bound without `const`"
)]
#[case::call(
    indoc! {"
        def f(x):
            x
        run shop(max_rate=f(5)) as eu
        1
    "},
    "a call in a constant is not supported yet"
)]
#[timeout(Duration::from_secs(10))]
fn a_run_refuses_what_its_constant_refuses(#[case] root: &str, #[case] needle: &str) {
    let errors = compile_errors(&program(root, &[("shop", SHOP)]));
    assert!(errors.contains(needle), "{errors}");
}

/// Two runs reach one type exactly when their `const` arguments have one value, however each
/// writes it, and a run of a run compares by the value its arguments compute.
#[rstest]
#[case::one_value(
    indoc! {"
        run shop(max_rate=5) as eu
        run shop(max_rate=2 + 3) as us
        def f(c: eu::Capped) => Int:
            c.extract()
        f(us::Capped::new(3))
    "},
    &[("shop", SHOP)],
    3
)]
#[case::through_a_run(
    indoc! {"
        run mid(r=4) as m
        run shop(max_rate=5) as five
        def f(t: five::Tag) => Int:
            t.rate()
        f(m::t)
    "},
    &[("shop", SHOP), ("mid", MID)],
    5
)]
#[timeout(Duration::from_secs(10))]
fn runs_with_one_value_reach_one_type(
    #[case] root: &str,
    #[case] modules: &[(&str, &str)],
    #[case] expected: i64,
) {
    check_program_scalar(&program(root, modules), Value::Int(expected));
}

/// Runs given different values reach different types, through a refinement or through a
/// method, and a diagnostic writes each value.
#[rstest]
#[case::refinement(
    indoc! {"
        run shop(max_rate=5) as eu
        run shop(max_rate=6) as us
        def f(c: eu::Capped) => Int:
            c.extract()
        f(us::Capped::new(3))
    "},
    "expected shop::Capped[max_rate = 5], found shop::Capped[max_rate = 6]"
)]
#[case::method(
    indoc! {"
        run shop(max_rate=5) as eu
        run shop(max_rate=6) as us
        def f(t: eu::Tag) => Int:
            t.rate()
        f(us::Tag::new(1))
    "},
    "expected shop::Tag[max_rate = 5], found shop::Tag[max_rate = 6]"
)]
#[case::through_a_run(
    indoc! {"
        run mid(r=4) as m
        run shop(max_rate=6) as other
        def f(t: other::Tag) => Int:
            t.rate()
        f(m::t)
    "},
    "expected shop::Tag[max_rate = 6], found shop::Tag[max_rate = 5]"
)]
#[timeout(Duration::from_secs(10))]
fn runs_with_different_values_reach_different_types(#[case] root: &str, #[case] needle: &str) {
    let errors = compile_errors(&program(root, &[("shop", SHOP), ("mid", MID)]));
    assert!(errors.contains(needle), "{errors}");
}

/// A module whose constants divide by a `const` parameter only where it is not zero.
const CALC: &str = indoc! {"
    const param d: Int
    pub const q = 10 // d if d != 0 else 0
    pub const big = d != 0 and 10 // d > 1
"};

/// A run's value decides a condition or a boolean operation, which leaves the other operand
/// unread, as the runtime does.
#[rstest]
#[case::ternary(
    indoc! {"
        run calc(d=0) as c
        type T = {Int where _ <= c::q}
        T::new(0).extract()
    "},
    0
)]
#[case::boolean(
    indoc! {"
        run calc(d=0) as c
        const k = 1 if c::big else 0
        type T = {Int where _ <= k}
        T::new(0).extract()
    "},
    0
)]
#[timeout(Duration::from_secs(10))]
fn a_runs_value_decides_what_a_constant_reads(#[case] root: &str, #[case] expected: i64) {
    check_program_scalar(&program(root, &[("calc", CALC)]), Value::Int(expected));
}

/// The module a ternary constant's refinement is declared in.
const TIERS: &str = indoc! {"
    const param m: Int
    const lim = 10 if m > 3 else 1
    pub type T = {Int where _ <= lim}
"};

/// A declaration's refinement reads a ternary over a `const` parameter, which takes the arm
/// each run's value decides.
#[rstest]
#[case::low(
    indoc! {"
        run tiers(m=1) as low
        low::T::new(1).extract()
    "},
    1
)]
#[case::high(
    indoc! {"
        run tiers(m=5) as high
        high::T::new(7).extract()
    "},
    7
)]
#[timeout(Duration::from_secs(10))]
fn a_refinement_reads_a_ternary_constant(#[case] root: &str, #[case] expected: i64) {
    check_program_scalar(&program(root, &[("tiers", TIERS)]), Value::Int(expected));
}

#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_ternary_constant_refuses_what_its_arm_refuses() {
    let errors = compile_errors(&program(
        indoc! {"
            run tiers(m=1) as low
            low::T::new(7).extract()
        "},
        &[("tiers", TIERS)],
    ));
    assert!(errors.contains("expected {Int | __elem <= 1}"), "{errors}");
}

/// A run that gives a tuple to a `const` parameter a declaration's refinement reads is
/// refused at the run, whether the refinement reads the parameter or a constant bound to it,
/// and whether its annotation is written or `_`.
#[rstest]
#[case::annotated(indoc! {"
    const param p: {Int, Int}
    pub type T = {Int where _ <= p.0}
"})]
#[case::inferred(indoc! {"
    const param p: _
    pub type T = {Int where _ <= p.0}
"})]
#[case::through_a_constant(indoc! {"
    const param p: {Int, Int}
    const q = p
    pub type T = {Int where _ <= q.0}
"})]
#[timeout(Duration::from_secs(10))]
fn a_refinement_reading_a_tuple_constant_is_refused(#[case] pairs: &str) {
    let errors = compile_errors(&program(
        indoc! {"
            run pairs(p=(5, 6)) as a
            a::T::new(3).extract()
        "},
        &[("pairs", pairs)],
    ));
    assert!(
        errors.contains(
            "`p` is `(5, 6)` here, and a declaration's refinement reads it; a tuple, a record or \
             a list constant in a declaration's refinement is not supported yet"
        ),
        "{errors}"
    );
}

/// A constant with no value is reported once, where it is computed: a refinement, a `const`
/// parameter's default or a route's address that reads it, in its module or another,
/// reports nothing more.
#[rstest]
#[case::refinement(indoc! {"
    const limit = 1 // 0
    type T = {Int where _ <= limit}
    T::new(0).extract()
"})]
#[case::default(indoc! {"
    const limit = 1 // 0
    const param p: Int = limit
    p
"})]
#[case::route(indoc! {r#"
    const port = 1 // 0
    reqs, resps = http_serve(port, "GET", "/x")
    for r in reqs:
        resps << "x"
"#})]
#[timeout(Duration::from_secs(10))]
#[case::imported(indoc! {"
    import cfg
    type T = {Int where _ <= cfg::rate}
    T::new(0).extract()
"})]
#[case::used(indoc! {"
    import cfg use rate
    type T = {Int where _ <= rate}
    T::new(0).extract()
"})]
fn a_constant_with_no_value_is_reported_once(#[case] code: &str) {
    let errors = compile_errors(&program(code, &[("cfg", "pub const rate = 1 // 0\n")]));
    assert_eq!(errors.matches("Error:").count(), 1, "{errors}");
    assert!(errors.contains("`1 // 0` has no value"), "{errors}");
}

/// A module whose `Order` reaches `max_order` through `Amount`, the type its constructor
/// holds.
const ORDERS: &str = indoc! {"
    const param max_order: Int
    pub type Amount = {Int where _ <= max_order}
    pub type Order:
        placed(Amount)
    pub def total(o: Order) => Int:
        match o:
            case Order::placed(a):
                a.extract()
"};

/// A type that reaches a `const` parameter through another type takes each run's value for
/// that type too, both where it is built and where a pattern reads the other type back.
#[rstest]
#[case::run(indoc! {"
    run orders(max_order=100) as s
    s::total(s::Order::placed(s::Amount::new(5)))
"})]
#[case::import(indoc! {"
    import orders(max_order=100)
    orders::total(orders::Order::placed(orders::Amount::new(5)))
"})]
#[timeout(Duration::from_secs(10))]
fn a_type_reaches_a_constant_through_another_type(#[case] root: &str) {
    check_program_scalar(&program(root, &[("orders", ORDERS)]), Value::Int(5));
}
