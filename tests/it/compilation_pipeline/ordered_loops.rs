//! A loop whose iterations interact runs in its source's position order, and its positions must
//! be orderable (`docs/chl-spec.md`, "Ordered loops").

use super::helpers::*;
use super::modules::program;
use cambra::ccl::context::{GlobalContext, check_program};
use cambra::interpreter::Value;
use indoc::indoc;
use rstest_log::rstest;

#[rstest]
#[case::a_list_by_index(indoc! {"
    s := 0
    for v in [3, 1, 2]:
        s := s * 10 + v
    s
"}, 312)]
#[case::a_map_by_key(indoc! {"
    m = map([3 -> 30, 1 -> 10, 2 -> 20])
    s := 0
    for v in m:
        s := s * 100 + v
    s
"}, 102030)]
#[case::two_generators_by_their_positions(indoc! {"
    s := 0
    for v in [x * y for x in [3, 1] for y in [1, 2]]:
        s := s * 10 + v
    s
"}, 3612)]
#[case::eleven_generators_by_position_not_by_name(indoc! {"
    last := 0
    for v in [a + b + c + d + e + f + g + h + i + j + k for a in [0] for b in [0] for c in [0] for d in [0] for e in [0] for f in [0] for g in [0] for h in [0] for i in [0] for j in [0, 100] for k in [1, 2]]:
        last := v
    last
"}, 102)]
#[case::a_polymorphic_definition_at_each_use(indoc! {"
    def lastof(c):
        last := 0
        for v in c:
            last := v
        last + 0
    lastof([1, 5, 2]) * 100 + lastof(map([2 -> 7, 1 -> 9]))
"}, 207)]
#[case::a_nominal_key_by_its_declarations_order(indoc! {"
    type Q = {zeta: Int, alpha: Int}
    instance Equatable(Q, Q)
    instance Orderable(Q, Q)
    m = map([Q::new((zeta=1, alpha=9)) -> 10, Q::new((zeta=2, alpha=0)) -> 20])
    s := 0
    for v in m:
        s := s * 100 + v
    s
"}, 1020)]
#[case::a_nominal_key_of_several_parameters(indoc! {"
    type P:
        new(zeta: Int, alpha: Int)
    instance Equatable(P, P)
    instance Orderable(P, P)
    m = map([P::new(2, 0) -> 20, P::new(1, 9) -> 10])
    s := 0
    for v in m:
        s := s * 100 + v
    s
"}, 1020)]
#[case::a_loop_that_only_feeds_needs_no_order(indoc! {"
    o: Feed(_)
    m = map([(a=1) -> 10, (a=2) -> 20])
    for v in m:
        o << v
    sum(o)
"}, 30)]
fn runs_in_position_order(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// `max`, `min` and `<` read the order an ordered loop runs in.
#[rstest]
#[case::max(indoc! {"
    q = max([Q::new((zeta=1, alpha=9)), Q::new((zeta=2, alpha=0))])
    match q:
        case Q::new(r):
            r.zeta
"}, 2)]
#[case::min(indoc! {"
    q = min([Q::new((zeta=1, alpha=9)), Q::new((zeta=2, alpha=0))])
    match q:
        case Q::new(r):
            r.zeta
"}, 1)]
#[case::less(indoc! {"
    if Q::new((zeta=1, alpha=9)) < Q::new((zeta=2, alpha=0)):
        1
    else:
        0
"}, 1)]
fn comparisons_agree(#[case] code: &str, #[case] expected: i64) {
    let q = indoc! {"
        type Q = {zeta: Int, alpha: Int}
        instance Equatable(Q, Q)
        instance Orderable(Q, Q)
    "};
    check_scalar(&format!("{q}{code}"), Value::Int(expected));
}

/// A loop that must run in order is refused over positions with no order: record keys, a map's
/// whose key type the source's type states included, and a concatenation, whose parts have none
/// between them. The refusal says what orders the loop and what its source's positions are.
#[rstest]
#[case::record_keys(indoc! {"
    m = map([(a=1) -> 10, (a=2) -> 20])
    last := 0
    for v in m:
        last := v
    last
"}, "positions of type `{a: Int}`, which have no order")]
#[case::keys_a_parameter_states(indoc! {"
    def total(m: Map({a: Int}, Int)):
        t := 0
        for v in m:
            t += v
        t + 0
    total(box(map([(a=1) -> 10])))
"}, "keys of type `{a: Int}`, which have no order")]
#[case::a_concatenation(indoc! {"
    acc := 0
    for v in [1, 2] ++ [3]:
        acc := acc * 10 + v
    acc
"}, "the positions of a concatenation, which puts neither part first")]
#[case::a_bound_concatenation(indoc! {"
    xs = [1, 2] ++ [3]
    acc := 0
    for v in xs:
        acc += v
    acc
"}, "the positions of a concatenation, which puts neither part first")]
#[case::a_concatenation_around_a_nested_loop(indoc! {"
    total := 0
    for x in [1] ++ [2]:
        for y in [10, 20]:
            total := total * 100 + x * y
    total
"}, "the positions of a concatenation, which puts neither part first")]
#[case::a_counter_beside_a_block(indoc! {"
    hits: Mut(Int, Txn) := 0
    def f(a, b):
        n := 0
        for x in a ++ b:
            with begin():
                hits := hits + x
            n += 1
        n + 0
    f([1], [2])
"}, "the positions of a concatenation, which puts neither part first")]
fn positions_without_an_order_are_refused(#[case] code: &str, #[case] positions: &str) {
    check_compile_error(
        code,
        "this loop runs in its source's position order, since its body writes",
    );
    check_compile_error(code, &format!("but this source has {positions}"));
}

/// A transactional write orders no loop: a block's writes commit in commit order, not in the
/// source's position order, so a loop whose iterations only run blocks over transactional
/// variables needs no order of its positions, whether the block writes directly or through a
/// call (`docs/chl-spec.md`, "Ordered loops").
#[rstest]
#[case::over_a_concatenation(indoc! {"
    hits: Mut(Int, Txn) := 0
    pub def f(a: List(Int), b: List(Int)):
        for x in a ++ b:
            with begin():
                hits := hits + x
        0
"})]
#[case::over_a_set_of_records(indoc! {"
    hits: Mut(Int, Txn) := 0
    pub def f(s: Set({a: Int})):
        for r in s:
            with begin():
                hits := hits + 1
        0
"})]
#[case::through_a_call(indoc! {"
    hits: Mut(Int, Txn) := 0
    def bump(x):
        hits := hits + x
        x
    pub def f(a: List(Int), b: List(Int)):
        for x in a ++ b:
            with begin():
                bump(x)
        0
"})]
fn transactional_writes_order_no_loop(#[case] code: &str) {
    check_program(&mut GlobalContext::default(), &program(code, &[]))
        .unwrap_or_else(|errors| panic!("{errors:?}"));
}

/// A loop of blocks over a concatenation runs, each iteration one transaction.
#[test]
fn a_loop_of_blocks_over_a_concatenation_runs() {
    check_scalar(
        indoc! {"
            t: Mut(Int, Txn) := 0
            for y in [10] ++ [20]:
                with begin():
                    t := t + y
            await_final(t)
        "},
        Value::Int(30),
    );
}

/// An exception escaping the body orders the loop, a block beside it or not.
#[test]
fn an_escaping_raise_orders_a_loop_of_blocks() {
    check_compile_error(
        indoc! {"
            hits: Mut(Int, Txn) := 0
            def f(a, b):
                for x in a ++ b:
                    with begin():
                        hits := hits + x
                    if x < 0:
                        raise x
                0
            r = try:
                    f([1], [2])
                except Int as e:
                    e
            r
        "},
        "since an exception may escape its body, but this source has the positions of a \
         concatenation",
    );
}
