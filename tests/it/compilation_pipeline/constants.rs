//! Link-time constants (`docs/chl-spec.md`, "9.19 Constants"): `const` marks a value parameter
//! whose value is fixed once the program is linked, a binding is a constant when its
//! definition is one, a declaration's refinements name only constants, and a type reaching a
//! `const` parameter is one type per value its imports and runs give it ("Nominal type
//! identity").

use std::time::Duration;

use cambra::ccl::context::{GlobalContext, check_program};
use cambra::interpreter::Value;
use indoc::{formatdoc, indoc};
use rstest_log::rstest;

use super::helpers::*;
use super::modules::{compile_errors, program, report_count};

/// A module whose type reaches its `const` parameter through a refinement, and whose other
/// type reaches it through a method.
const SHOP: &str = indoc! {"
    const param max_rate: Int
    limit = max_rate * 2
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

/// A binding whose definition is built from literals, constants, operators and the fields of
/// records is a constant, with the value it computes.
#[rstest]
#[case::arithmetic(
    indoc! {"
        a = 3
        b = a * 2 + 1
        b
    "},
    7
)]
#[case::comparison_and_ternary(
    indoc! {"
        a = 3
        b = 10 if 1 < a < 5 else 20
        b
    "},
    10
)]
#[case::record_field(
    indoc! {"
        p = (x=2, y=3)
        q = p.x + p.y
        q
    "},
    5
)]
#[case::root_parameter(
    indoc! {"
        const param n: Int = 4
        m = n * n
        m
    "},
    16
)]
#[timeout(Duration::from_secs(10))]
fn a_constant_has_the_value_it_computes(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A binding whose definition is not a constant is an ordinary value wherever no constant is
/// required, and nothing reports it.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_binding_no_constant_requires_is_any_value() {
    check_scalar(
        indoc! {"
            total := 0
            limit = total + 1
            limit
        "},
        Value::Int(1),
    );
}

/// A binding read where a constant is required is refused at the read when its definition
/// is not a constant, with what the definition reads beside it: a value parameter without
/// `const`, a mutable variable, a call, a comprehension, or an operation with no value.
#[rstest]
#[case::parameter(
    indoc! {"
        param n: Int = 1
        limit = n
    "},
    "`n` is a parameter without `const`"
)]
#[case::mutable(
    indoc! {"
        total := 0
        limit = total
    "},
    "`total` is a mutable variable"
)]
#[case::call(
    indoc! {"
        def f(x):
            x
        limit = f(1)
    "},
    "a call in a constant is not supported yet"
)]
#[case::comprehension("limit = [x for x in [1, 2]]\n", "this is not a constant")]
#[case::no_value("limit = 1 // 0\n", "`1 // 0` has no value")]
#[timeout(Duration::from_secs(10))]
fn a_constant_reads_only_constants(#[case] binding: &str, #[case] why: &str) {
    let code = formatdoc! {"
        {binding}
        type T = {{Int where _ <= limit}}
        T::new(0).extract()
    "};
    let errors = compile_errors(&program(&code, &[]));
    assert!(
        errors.contains("`limit` is not a constant, since its definition is not one"),
        "{errors}"
    );
    assert!(errors.contains(why), "{errors}");
}

/// `const` marks only a value parameter: not a binding, which is a constant when its
/// definition is one, and not a type parameter, which is fixed at link time already.
#[rstest]
#[case::binding(
    indoc! {"
        const limit = 1
        limit
    "},
    "`const` marks a parameter, `const param x: T`"
)]
#[case::type_parameter(
    indoc! {"
        const param T <: Int
        1
    "},
    "`T` is a type parameter, which is fixed at link time already"
)]
#[timeout(Duration::from_secs(10))]
fn const_marks_a_value_parameter(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
}

/// A declaration's refinement reads a constant binding or another module's public constant,
/// qualified or through a `use` name, as the value it is.
#[rstest]
#[case::binding(
    program(
        indoc! {"
            limit = 2 * 5
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
        &[("cfg", "pub rate = 5\n")]
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
        &[("cfg", "pub rate = 5\n")]
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
    "pub rate = 5\n",
    "expected {Int | __elem <= 5}"
)]
#[case::imported_not_a_constant(
    indoc! {"
        import cfg
        type Small = {Int where _ <= cfg::rate}
        Small::new(3).extract()
    "},
    "pub rate = len([1, 2])\n",
    "`cfg::rate` is not a constant, since its definition is not one"
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
        &program(root, &[("shop", SHOP), ("cfg", "pub rate = 5\n")]),
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
        x := 5
        run shop(max_rate=x) as eu
        1
    "},
    "`x` is a mutable variable, so it is not a constant"
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

/// Imports and runs given different values reach different types, through a refinement or
/// through a method, and a diagnostic writes each value.
#[rstest]
#[case::refinement(
    indoc! {"
        import shop(max_rate=5) as eu
        import shop(max_rate=6) as us
        def f(c: eu::Capped) => Int:
            c.extract()
        f(us::Capped::new(3))
    "},
    "expected shop(max_rate=5)::Capped, found shop(max_rate=6)::Capped"
)]
#[case::method(
    indoc! {"
        import shop(max_rate=5) as eu
        import shop(max_rate=6) as us
        def f(t: eu::Tag) => Int:
            t.rate()
        f(us::Tag::new(1))
    "},
    "expected shop(max_rate=5)::Tag, found shop(max_rate=6)::Tag"
)]
#[case::through_a_run(
    indoc! {"
        run mid(r=4) as m
        run shop(max_rate=6) as other
        def f(t: other::Tag) => Int:
            t.rate()
        f(m::t)
    "},
    "expected shop(max_rate=6)::Tag, found shop(max_rate=5)::Tag"
)]
#[timeout(Duration::from_secs(10))]
fn copies_with_different_values_reach_different_types(#[case] root: &str, #[case] needle: &str) {
    let errors = compile_errors(&program(root, &[("shop", SHOP), ("mid", MID)]));
    assert!(errors.contains(needle), "{errors}");
}

/// A method reaches a `const` parameter through a function of its module as it does by
/// naming it, so imports given different values reach different types.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_method_reaches_a_constant_through_a_function() {
    let errors = compile_errors(&program(
        indoc! {"
            import lib(k=1) as a
            import lib(k=2) as b
            x: a::Box = b::Box::new(1)
            x.extract()
        "},
        &[(
            "lib",
            indoc! {"
                const param k: Int
                def plus(x):
                    x + k
                pub type Box = Int
                pub def Box::get(self) => Int:
                    plus(1)
            "},
        )],
    ));
    assert!(
        errors.contains("annotated as lib(k=1)::Box, but inferred as lib(k=2)::Box"),
        "{errors}"
    );
}

/// A module whose constants divide by a `const` parameter only where it is not zero.
const CALC: &str = indoc! {"
    const param d: Int
    pub q = 10 // d if d != 0 else 0
    pub big = d != 0 and 10 // d > 1
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
        k = 1 if c::big else 0
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
    lim = 10 if m > 3 else 1
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
    q = p
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
    limit = 1 // 0
    type T = {Int where _ <= limit}
    T::new(0).extract()
"})]
#[case::default(indoc! {"
    limit = 1 // 0
    const param p: Int = limit
    p
"})]
#[case::route(indoc! {r#"
    port = 1 // 0
    reqs, resps = http_serve(port, "GET", "/x")
    for r in reqs:
        resps << "x"
"#})]
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
#[timeout(Duration::from_secs(10))]
fn a_constant_with_no_value_is_reported_once(#[case] code: &str) {
    let errors = compile_errors(&program(code, &[("cfg", "pub rate = 1 // 0\n")]));
    assert_eq!(report_count(&errors), 1, "{errors}");
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

/// An argument or a default that has no value at the arguments a run of its module gives it is
/// reported once, at the statement in that module, with a label at each run of the module
/// whose arguments give it none.
#[rstest]
#[case::an_argument(
    indoc! {"
        const param r: Int
        run shop(m=10 // r) as s
        pub v = s::v
    "},
    indoc! {"
        const param m: Int
        visits := 0
        pub v = m
    "},
    "`m` has no value at this run: `10 // 0` has no value"
)]
#[case::a_default(
    indoc! {"
        const param r: Int
        run shop(m=r) as s
        pub v = s::v
    "},
    indoc! {"
        const param m: Int
        const param d: Int = 10 // m
        visits := 0
        pub v = d
    "},
    "`d` has no value at this run: `10 // 0` has no value"
)]
#[timeout(Duration::from_secs(10))]
fn a_constant_with_no_value_at_a_runs_arguments_is_labelled_at_the_run(
    #[case] mid: &str,
    #[case] shop: &str,
    #[case] message: &str,
) {
    let errors = compile_errors(&program(
        indoc! {"
            run mid(r=0) as a
            run mid(r=0) as b
            run mid(r=1) as c
            a::v + b::v + c::v
        "},
        &[("mid", mid), ("shop", shop)],
    ));
    assert!(errors.contains(message), "{errors}");
    assert!(errors.contains("mid.cambra:2:1"), "{errors}");
    assert!(errors.contains("the run `a`, whose copy fails"), "{errors}");
    assert!(errors.contains("the run `b`, whose copy fails"), "{errors}");
    assert!(!errors.contains("the run `c`"), "{errors}");
    assert_eq!(report_count(&errors), 1, "{errors}");
}

/// In a module checked alone, a read of a `const` parameter is known to be the parameter, so
/// a value built from it meets a refinement that reads it.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_read_of_a_const_parameter_meets_a_refinement_that_reads_it() {
    let program = program(
        indoc! {"
            const param max_rate: Int
            pub type Capped = {Int where _ <= max_rate}
            pub def top(n: Int) => Capped:
                Capped::new(max_rate)
        "},
        &[],
    );
    check_program(&mut GlobalContext::default(), &program)
        .unwrap_or_else(|errors| panic!("{errors:?}"));
}

/// A run's `const` argument over the `const` parameters of the module checked alone is what
/// the run's predicates read, and what a read of the run's parameter is known to be, so the
/// module's own refinements over its parameters meet the run's.
#[rstest]
#[case::a_parameter("r")]
#[case::an_operation("r + 1")]
#[timeout(Duration::from_secs(10))]
fn a_runs_const_argument_over_the_modules_own_parameters_meets_its_refinements(
    #[case] argument: &str,
) {
    let shop = indoc! {"
        const param max_rate: Int
        pub type Capped = {Int where _ <= max_rate}
        pub top = Capped::new(max_rate)
        visits := 0
    "};
    let mid = formatdoc! {"
        const param r: Int
        run shop(max_rate={argument}) as a
        pub def g(n: {{Int where _ <= {argument}}}) => Int:
            a::Capped::new(n).extract()
        pub h = a::top.extract()
    "};
    check_program(
        &mut GlobalContext::default(),
        &program(&mid, &[("shop", shop)]),
    )
    .unwrap_or_else(|errors| panic!("{errors:?}"));
}

/// A constant term prints each operator as CHL writes it, including the two whose CHL spelling
/// differs from `BinOpKind::sym`: xor `^` and string concatenation `+`.
#[rstest]
#[case::xor(
    cambra::ccl::BinOpKind::BoolLogic(cambra::ccl::LogicKind::Xor),
    "(p ^ 1)"
)]
#[case::concat(cambra::ccl::BinOpKind::Concat, "(p + 1)")]
#[case::add(
    cambra::ccl::BinOpKind::Arithmetic(cambra::ccl::ArithmeticKind::Add),
    "(p + 1)"
)]
fn a_constant_term_spells_its_operator_as_chl_does(
    #[case] op: cambra::ccl::BinOpKind,
    #[case] expected: &str,
) {
    use cambra::ccl::constant::{ConstParam, ConstTerm};
    let term = ConstTerm::BinOp(
        op,
        Box::new(ConstTerm::Param(ConstParam::declared("p"))),
        Box::new(ConstTerm::Lit(cambra::ccl::Lit::Int(1))),
    );
    assert_eq!(term.to_string(), expected);
}
