//! A loop whose iterations interact runs in its source's position order, and its positions must
//! be orderable (`docs/chl-spec.md`, "Ordered loops").

use super::helpers::*;
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
    impl Equatable(Q, Q)
    impl Orderable(Q, Q)
    m = map([Q::new((zeta=1, alpha=9)) -> 10, Q::new((zeta=2, alpha=0)) -> 20])
    s := 0
    for v in m:
        s := s * 100 + v
    s
"}, 1020)]
#[case::a_nominal_key_of_several_parameters(indoc! {"
    type P:
        new(zeta: Int, alpha: Int)
    impl Equatable(P, P)
    impl Orderable(P, P)
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
        impl Equatable(Q, Q)
        impl Orderable(Q, Q)
    "};
    check_scalar(&format!("{q}{code}"), Value::Int(expected));
}

/// A loop that must run in order is refused over positions with no order: record keys, and a
/// concatenation, whose parts have none between them.
#[rstest]
#[case::record_keys(indoc! {"
    m = map([(a=1) -> 10, (a=2) -> 20])
    last := 0
    for v in m:
        last := v
    last
"})]
#[case::a_concatenation(indoc! {"
    acc := 0
    for v in [1, 2] ++ [3]:
        acc := acc * 10 + v
    acc
"})]
#[case::a_bound_concatenation(indoc! {"
    xs = [1, 2] ++ [3]
    acc := 0
    for v in xs:
        acc += v
    acc
"})]
#[case::a_concatenation_around_a_nested_loop(indoc! {"
    total := 0
    for x in [1] ++ [2]:
        for y in [10, 20]:
            total := total * 100 + x * y
    total
"})]
#[case::a_transaction_per_position_of_a_concatenation(indoc! {"
    t: Mut(Int, Txn) := 0
    for y in [10] ++ [20]:
        with begin():
            t := t * 100 + y
    await_final(t)
"})]
fn positions_without_an_order_are_refused(#[case] code: &str) {
    check_compile_error(
        code,
        "No Orderable instance for the positions of a loop whose iterations interact",
    );
}
