//! `raise` and `try` (`docs/chl-spec.md`, "Exceptions"), compiled through exception
//! elimination (`src/ccl/design/ir.md`, "Exceptions").

use super::helpers::*;
use cambra::interpreter::Value;
use indoc::{formatdoc, indoc};
use rstest_log::rstest;

/// `raise` and `try` in straight-line code: an exception ends its path, the statements before
/// it stand, and the first exception in written order escapes.
#[rstest]
#[case::writes_before_stand(indoc! {"
    t := 0
    try:
        t := 5
        raise 1
        t := 7
    except Int:
        t := t + 100
    t
"}, Value::Int(105))]
#[case::reraise_to_an_outer_try(indoc! {r#"
    y = try:
            try:
                raise 1
            except Int as e:
                raise "again"
        except String as s:
            9
    y
"#}, Value::Int(9))]
#[case::first_operand_wins(indoc! {"
    def f(x):
        if x > 0:
            raise x
        x
    y = try:
            f(1) + f(2)
        except Int as e:
            e
    y
"}, Value::Int(1))]
#[case::and_short_circuits(indoc! {"
    def f(x):
        if x > 0:
            raise x
        True
    y = try:
            False and f(1)
        except Int as e:
            True
    y
"}, Value::Bool(false))]
#[case::raise_in_a_match_arm(indoc! {"
    def f(o):
        match o:
            case `some(v):
                v
            case `none:
                raise 0
    y = try:
            f(`none)
        except Int as e:
            e - 1
    y
"}, Value::Int(-1))]
#[case::feed_after_a_raise_skipped(indoc! {"
    ys: Feed(_)
    try:
        ys << 1
        raise 0
        ys << 2
    except Int:
        ys << 3
    sum([y for y in ys])
"}, Value::Int(4))]
#[case::a_nominal_exception(indoc! {"
    type Negative = {qty: Int}
    def checked(qty: Int) => Int:
        if qty < 0:
            raise Negative::new((qty=qty))
        qty
    def checked_or_zero(qty: Int) => Int:
        try:
            checked(qty)
        except Negative:
            0
    checked_or_zero(-3) * 10 + checked_or_zero(4)
"}, Value::Int(4))]
fn straight_line(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// An exception escaping a loop body: the loop raises the exception of its first raising
/// iteration, and the iterations after it contribute nothing.
#[rstest]
#[case::first_raising_iteration(indoc! {"
    t := 0
    r = try:
            for i in [1, 2, 3]:
                t := t + i
                if i == 2:
                    raise i
            0
        except Int as e:
            e * 100
    t * 1000 + r
"}, 3200)]
#[case::no_iteration_raises(indoc! {"
    t := 0
    r = try:
            for i in [1, 2, 3]:
                t := t + i
                if i == 9:
                    raise i
            7
        except Int as e:
            e * 100
    t * 1000 + r
"}, 6007)]
#[case::first_of_two_raises(indoc! {"
    t := 0
    r = try:
            for i in [1, 2, 3, 4]:
                if i >= 2:
                    raise i * 10
                t := t + i
            0
        except Int as e:
            e
    t * 1000 + r
"}, 1020)]
#[case::write_after_a_raise_skipped(indoc! {"
    t := 0
    r = try:
            for i in [1, 2, 3]:
                t := t + 1
                if i == 2:
                    raise i
                t := t + 100
            0
        except Int as e:
            e
    t * 10 + r
"}, 1022)]
#[case::caught_inside_the_body(indoc! {"
    t := 0
    for i in [1, 2, 3]:
        try:
            if i == 2:
                raise i
            t := t + i
        except Int as e:
            t := t + 100
    t
"}, 104)]
#[case::feeds_beside_an_accumulator(indoc! {"
    o: Feed(_)
    t := 0
    r = try:
            for i in [1, 2, 3]:
                t := t + 1
                o << i
                if i == 2:
                    raise i
                o << i * 100
            0
        except Int as e:
            e
    sum(o) * 10 + r + t * 1000
"}, 3032)]
#[case::a_loop_that_only_feeds(indoc! {"
    o: Feed(_)
    r = try:
            for i in [1, 2, 3]:
                o << i
                if i == 2:
                    raise i
            0
        except Int as e:
            e
    sum(o) * 10 + r
"}, 32)]
#[case::nested_loops(indoc! {"
    t := 0
    r = try:
            for i in [1, 2, 3]:
                for j in [10, 20]:
                    t := t + j
                    if i == 2 and j == 20:
                        raise i
            0
        except Int as e:
            e
    t * 10 + r
"}, 602)]
#[case::a_raising_source(indoc! {"
    def src(n):
        if n > 2:
            raise n
        [1, 2]
    t := 0
    r = try:
            for i in src(5):
                t := t + i
            0
        except Int as e:
            e
    t * 10 + r
"}, 5)]
#[case::over_a_map_by_key(indoc! {"
    m = map([3 -> 30, 1 -> 10, 2 -> 20])
    r = try:
            for v in m:
                if v > 15:
                    raise v
            0
        except Int as e:
            e
    r
"}, 20)]
fn loops(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A comprehension whose elements may raise raises the exception of its first raising
/// position, as a loop over its source would.
#[rstest]
#[case::one_generator(indoc! {"
    y = try:
            sum([f(x) for x in [1, 3, 2, 4]])
        except Int as e:
            e
    y
"}, 3)]
#[case::no_element_raises(indoc! {"
    y = try:
            sum([f(x) for x in [1, 2, 1]])
        except Int as e:
            e
    y
"}, 40)]
#[case::a_filter_skips_a_raising_position(indoc! {"
    y = try:
            sum([f(x) for x in [1, 3, 2, 4] if x != 3])
        except Int as e:
            e
    y
"}, 4)]
#[case::two_generators(indoc! {"
    y = try:
            sum([f(x * j) for x in [1, 3, 2] for j in [1, 10]])
        except Int as e:
            e
    y
"}, 10)]
#[case::a_raising_source(indoc! {"
    def g():
        raise 7
        [1, 2]
    y = try:
            sum([x for x in g()])
        except Int as e:
            e
    y
"}, 7)]
#[case::nested(indoc! {"
    y = try:
            sum([sum([f(x + j) for j in [0, 1]]) for x in [1, 2, 0]])
        except Int as e:
            e
    y
"}, 3)]
#[case::in_a_raising_loop(indoc! {"
    t := 0
    r = try:
            for i in [1, 2, 3]:
                t := t + sum([f(x + i) for x in [0, 1]])
            0
        except Int as e:
            e
    t * 100 + r
"}, 3003)]
#[case::caught_in_a_loop(indoc! {"
    t := 0
    for i in [0, 1, 2, 3]:
        v = try:
                sum([f(x + i) for x in [0, 1]])
            except Int as e:
                e
        t := t + v
    t
"}, 46)]
#[case::of_pairs(indoc! {"
    y = try:
            sum([p.1 for p in [x -> f(x) for x in [1, 3, 2]]])
        except Int as e:
            e
    y
"}, 3)]
// A comprehension in the element of another: each row's inner comprehension is scanned on its
// own, and the first exception in the rows' order escapes.
#[case::nested(indoc! {"
    y = try:
            sum([sum([f(v) for v in r]) for r in [[1, 2], [0, 1]]])
        except Int as e:
            e
    y
"}, 40)]
#[case::nested_raises(indoc! {"
    y = try:
            sum([sum([f(v) for v in r]) for r in [[1, 2], [4, 1]]])
        except Int as e:
            e
    y
"}, 4)]
fn comprehensions(#[case] code: &str, #[case] expected: i64) {
    let f = indoc! {"
        def f(x):
            if x > 2:
                raise x
            x * 10
    "};
    check_scalar(&format!("{f}{code}"), Value::Int(expected));
}

/// A guard that raises is evaluated only where the guards before it failed.
#[rstest]
#[case::the_first_guard(indoc! {"
    y = try:
            if p(3):
                1
            else:
                2
        except Int as e:
            e
    y
"}, 103)]
#[case::a_later_guard_reached(indoc! {"
    y = try:
            if 0 > 1:
                1
            elif p(3):
                2
            else:
                4
        except Int as e:
            e
    y
"}, 103)]
#[case::a_later_guard_not_reached(indoc! {"
    y = try:
            if 2 > 1:
                1
            elif p(3):
                2
            else:
                4
        except Int as e:
            e
    y
"}, 1)]
#[case::a_guard_that_holds(indoc! {"
    y = try:
            if p(2):
                1
            else:
                2
        except Int as e:
            e
    y
"}, 1)]
#[case::a_statement_guard(indoc! {"
    t := 0
    try:
        t := 5
        if p(3):
            t := 6
        t := 7
    except Int as e:
        t := t + e
    t
"}, 108)]
#[case::in_a_loop(indoc! {"
    t := 0
    r = try:
            for i in [1, 2, 3, 4]:
                if p(i):
                    t := t + i
            0
        except Int as e:
            e
    t * 1000 + r
"}, 2103)]
fn raising_guards(#[case] code: &str, #[case] expected: i64) {
    let p = indoc! {"
        def p(x):
            if x == 3:
                raise 100 + x
            x > 1
    "};
    check_scalar(&format!("{p}{code}"), Value::Int(expected));
}

/// `Raise(T)` in a `causes` clause: under `only`, a body raising a subtype of `T` fits.
#[rstest]
#[case::only_the_raised_type(indoc! {"
    def f(x: Int) => Int causes only Raise(Int):
        if x > 1:
            raise x
        x
    y = try:
            f(5)
        except Int as e:
            e + 100
    y
"}, 105)]
#[case::only_a_wider_type(indoc! {"
    def f(x: Int) => Int causes only Raise(Int):
        if x > 1:
            raise 2
        x
    y = try:
            f(5)
        except Int as e:
            e + 100
    y
"}, 102)]
#[case::stated_and_not_raised(indoc! {"
    def f(x: Int) => Int causes Raise(Int):
        x
    y = try:
            f(5)
        except Int as e:
            e + 100
    y
"}, 5)]
fn raise_clauses(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

#[rstest]
#[case::an_exception_escaping_the_program(
    indoc! {"
        def f(x: Int) => Int:
            if x > 1:
                raise x
            x
        f(5)
    "},
    "no exception may escape the program"
)]
#[case::a_stated_exception_escaping_the_program(
    indoc! {"
        def f(x: Int) => Int causes Raise(Int):
            x
        f(5)
    "},
    "no exception may escape the program"
)]
#[case::a_clause_catching_nothing(
    indoc! {"
        y = try:
                5
            except Int:
                0
        y
    "},
    "catches nothing its `try` block raises"
)]
#[case::a_raise_escaping_a_loop_over_positions_with_no_order(
    indoc! {"
        m = map([(a=1) -> 10, (a=2) -> 20])
        r = try:
                for v in m:
                    if v > 15:
                        raise v
                0
            except Int as e:
                e
        r
    "},
    "No Orderable instance for the positions of a loop whose iterations interact"
)]
#[case::a_raise_beyond_an_only_clause(
    indoc! {"
        def f(x: Int) => Int causes only Raise(String):
            if x > 1:
                raise x
            x
        y = try:
                f(5)
            except Int as e:
                e
        y
    "},
    "does not list"
)]
fn refused(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
}

/// A comprehension whose filter may raise: each position evaluates its filter, then its
/// element where the filter holds, and the first exception in position order escapes.
#[rstest]
#[case::the_filter_raises(indoc! {"
    y = try:
            sum([x for x in [1, 3, 2, 4] if p(x)])
        except Int as e:
            e
    y
"}, 103)]
#[case::no_filter_raises(indoc! {"
    y = try:
            sum([x for x in [1, 2, 4] if p(x)])
        except Int as e:
            e
    y
"}, 6)]
#[case::an_element_before_a_filter(indoc! {"
    y = try:
            sum([f(x) for x in [4, 3] if p(x)])
        except Int as e:
            e
    y
"}, 4)]
#[case::a_filter_before_an_element(indoc! {"
    y = try:
            sum([f(x) for x in [3, 4] if p(x)])
        except Int as e:
            e
    y
"}, 103)]
#[case::two_generators(indoc! {"
    y = try:
            sum([x * j for x in [1, 2] for j in [1, 3] if p(x * j)])
        except Int as e:
            e
    y
"}, 103)]
#[case::the_result_read_twice(indoc! {"
    y = try:
            xs = [x for x in [1, 2, 4] if p(x)]
            sum(xs) * 10 + sum([1 for v in xs])
        except Int as e:
            e
    y
"}, 62)]
#[case::caught_in_a_loop(indoc! {"
    t := 0
    for i in [0, 1, 2]:
        v = try:
                sum([x + i for x in [0, 1] if p(x + i)])
            except Int as e:
                e
        t := t + v
    t
"}, 105)]
#[case::nested(indoc! {"
    y = try:
            sum([sum([v for v in r if p(v)]) for r in [[1, 2], [4, 5]]])
        except Int as e:
            e
    y
"}, 11)]
#[case::nested_raises(indoc! {"
    y = try:
            sum([sum([v for v in r if p(v)]) for r in [[1, 2], [3, 5]]])
        except Int as e:
            e
    y
"}, 103)]
// A filtered comprehension a function returns, called twice.
#[case::returned_by_a_function(indoc! {"
    def keep(xs, k):
        [x + k for x in xs if p(x + k)]
    y = try:
            sum(keep([0, 1, 2], 0)) + sum(keep([0, 1], 3))
        except Int as e:
            e
    y
"}, 103)]
fn raising_filters(#[case] code: &str, #[case] expected: i64) {
    let defs = indoc! {"
        def f(x):
            if x > 2:
                raise x
            x * 10
        def p(x):
            if x == 3:
                raise 100 + x
            x > 1
    "};
    check_scalar(&format!("{defs}{code}"), Value::Int(expected));
}

/// An exception from a function passed as a value is raised where the function is applied. An
/// unannotated parameter causes what each use passes, so a `try` around its call catches at the
/// uses that raise and has no dead clause at the definition, whatever the uses pass.
#[rstest]
#[case::stated(
    "def apply(g: Int => Int causes Raise(Int), x: Int) => Int:",
    "apply(h, 7)",
    107
)]
#[case::unannotated("def apply(g, x):", "apply(h, 7)", 107)]
#[case::unannotated_passed_nothing_raising("def apply(g, x):", "apply(k, 7)", 7)]
#[case::unannotated_and_unused("def apply(g, x):", "7", 7)]
fn an_exception_through_a_function_parameter(
    #[case] head: &str,
    #[case] call: &str,
    #[case] expected: i64,
) {
    check_scalar(
        &formatdoc! {"
            {head}
                try:
                    g(x)
                except Int as e:
                    e + 100
            def h(x: Int) => Int:
                if x > 1:
                    raise x
                x
            def k(x):
                x
            {call}
        "},
        Value::Int(expected),
    );
}
