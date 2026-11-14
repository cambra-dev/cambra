//! Readings: calls whose value comes from outside the program, one per position and call path
//! (`docs/chl-spec.md`, "Inputs from outside the program").

use std::time::Duration;

use cambra::ccl::load::{InMemory, LoadedProgram, RootFile};
use cambra::interpreter::Value;
use indoc::indoc;
use rstest_log::rstest;

use super::helpers::check_program_scalar;

/// `root`, loaded against the std root, whose `std::random::next()` is the random reading.
fn with_random(root: &str) -> LoadedProgram {
    with_random_and(root, &[])
}

/// [`with_random`] with the user modules `modules`, each a path and its text.
fn with_random_and(root: &str, modules: &[(&str, &str)]) -> LoadedProgram {
    let mut files = modules
        .iter()
        .fold(InMemory::default(), |files, (path, text)| {
            files.with(path, *text)
        });
    let root = RootFile {
        path: "main.cambra".to_owned(),
        module: None,
        text: root.to_owned(),
    };
    crate::std_root::load_against_std(root, &mut files)
}

#[rstest]
#[case::two_bound_calls_at_the_top_level(indoc! {"
    import std::random
    a = random::next()
    b = random::next()
    a != b
"})]
#[case::two_calls_in_one_expression(indoc! {"
    import std::random
    random::next() != random::next()
"})]
#[case::one_binding_is_one_reading(indoc! {"
    import std::random
    a = random::next()
    a == a
"})]
#[case::each_iteration_reads_its_own(indoc! {"
    import std::random
    xs = [random::next() for n in [1, 2, 3]]
    sum([1 for x in xs for y in xs if x == y]) == 3
"})]
#[case::each_nested_iteration_reads_its_own(indoc! {"
    import std::random
    rows = [[random::next() for m in [10, 20]] for n in [1, 2]]
    tops = [max(row) for row in rows]
    sum([1 for row in rows if max(row) != min(row)]) == 2 and max(tops) != min(tops)
"})]
#[case::a_filtered_iteration_reads_its_own(indoc! {"
    import std::random
    xs = [random::next() for n in [1, 2, 3, 4] if n > 2]
    max(xs) != min(xs)
"})]
#[case::two_calls_in_one_iteration(indoc! {"
    import std::random
    sum([1 for n in [1, 2, 3] if random::next() == random::next()]) == 0
"})]
#[case::one_binding_in_an_iteration_is_one_reading(indoc! {"
    import std::random
    sum([t - t for t in [random::next() for n in [1, 2, 3]]]) == 0
"})]
#[case::equal_elements_are_two_positions(indoc! {"
    import std::random
    ys: Feed(_)
    for x in [1, 1]:
        ys << random::next()
    max(ys) != min(ys)
"})]
#[case::each_group_reads_its_own(indoc! {"
    import std::random
    xs = [random::next() for g in groupby([2, 3, 4, 5], \\x -> x // 2)]
    max(xs) != min(xs)
"})]
#[timeout(Duration::from_secs(10))]
fn a_reading_holds_one_value_per_position_and_call_path(#[case] root: &str) {
    check_program_scalar(&with_random(root), Value::Bool(true));
}

/// A reading in a comprehension's filter is a reading at each position of the loop the filter
/// refines, so the filter keeps some rows and drops others: one value for the whole loop would
/// keep all of them or none.
#[rstest]
#[case::one_generator(indoc! {"
    import std::random
    xs = [n for n in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] if random::next() > 0]
    n = sum([1 for x in xs])
    n > 0 and n < 16
"})]
#[case::two_generators(indoc! {"
    import std::random
    xs = [n for n in [1, 2, 3, 4, 5, 6, 7, 8] for m in [1, 2, 3, 4, 5, 6, 7, 8] if random::next() > 0]
    n = sum([1 for x in xs])
    n > 0 and n < 64
"})]
#[timeout(Duration::from_secs(10))]
fn a_reading_in_a_filter_reads_each_position(#[case] root: &str) {
    check_program_scalar(&with_random(root), Value::Bool(true));
}

/// A reading in a refinement under a loop depends on a position the refined type does not state,
/// so it is refused rather than read once per position of the wrong loop: a filter under another
/// loop, and a key function, which a group's membership refinement holds under the loop over the
/// groups.
#[rstest]
#[case::a_filter_under_another_loop(indoc! {"
    import std::random
    xs = [[n for n in [1, 2, 3, 4] if random::next() > 0] for m in [1, 2]]
    sum([1 for r in xs for x in r])
"})]
#[case::a_key_function(indoc! {"
    import std::random
    groups = groupby([1, 2, 3, 4], \\x -> random::next() // 4611686018427387904)
    sum([1 for g in groups])
"})]
fn a_reading_in_a_refinement_under_a_loop_is_refused(#[case] root: &str) {
    use cambra::ccl::context::{GlobalContext, compile_program};
    use cambra::interpreter::Consumer;
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let Err(errors) = compile_program(&mut GlobalContext::default(), &with_random(root), consumer)
    else {
        panic!("a reading in a refinement under a loop compiled");
    };
    let rendered = format!("{errors:?}");
    assert!(
        rendered.contains("a reading in a refinement under a loop"),
        "{rendered}",
    );
}

/// Only a std module declares a `@Builtin` function, and only one whose path the compiler
/// supplies a body for (`docs/chl-spec.md`, "9.16 The std root"), with clauses or without.
#[rstest]
#[case::with_a_clause(indoc! {"
    @Builtin
    def next() => Int requires ObserveWorld
    next()
"})]
#[case::with_no_clause(indoc! {"
    @Builtin
    def f() => Int
    1
"})]
fn a_builtin_function_outside_std_is_refused(#[case] code: &str) {
    super::helpers::check_compile_error(
        code,
        "a `@Builtin` function is declared at a std module's top level",
    );
}

#[test]
fn a_builtin_function_the_compiler_does_not_supply_is_refused() {
    let root = RootFile {
        path: "main.cambra".to_owned(),
        module: None,
        text: indoc! {"
            import std::extra
            extra::tick()
        "}
        .to_owned(),
    };
    let program = LoadedProgram::load_with_std(
        root,
        &mut InMemory::default(),
        &[(
            "std::extra",
            indoc! {"
                @Builtin
                pub def tick() => Int requires ObserveWorld
            "},
        )],
    );
    let errors = super::modules::compile_errors(&program);
    assert!(
        errors.contains("the compiler supplies no function `std::extra::tick`"),
        "{errors}"
    );
}

/// A reading requires `ObserveWorld`, which only the run supplies: a module whose top level takes
/// one is run, and one whose functions take one is imported (`docs/chl-spec.md`, "Inputs from
/// outside the program").
#[test]
fn a_module_whose_top_level_takes_a_reading_is_run() {
    let stamps = indoc! {"
        import std::random
        pub first = random::next()
    "};
    let errors = super::modules::compile_errors(&with_random_and(
        indoc! {"
            import stamps
            stamps::first
        "},
        &[("stamps", stamps)],
    ));
    assert!(
        errors.contains("its top level requires `ObserveWorld`"),
        "{errors}"
    );
}

#[test]
fn a_module_whose_functions_take_readings_is_imported() {
    let stamps = indoc! {"
        import std::random
        pub def pair():
            (random::next(), random::next())
    "};
    let program = with_random_and(
        indoc! {"
            import stamps
            p = stamps::pair()
            p.0 != p.1
        "},
        &[("stamps", stamps)],
    );
    check_program_scalar(&program, Value::Bool(true));
}

/// A reading in a loop that writes a mutable variable, or that commits a transaction, has one
/// value at each of the loop's positions.
#[rstest]
#[case::an_induction_loop(indoc! {"
    import std::random
    total := 0
    last := 0
    for n in [1, 2, 3]:
        r = random::next()
        total += r - r
        last := r
    total == 0 and last != 0
"})]
#[case::a_transaction(indoc! {"
    import std::random
    stock: Mut(Int, Txn) := 0
    for n in [1, 2, 3]:
        with begin():
            stock := random::next()
    await_final(stock) != 0
"})]
#[timeout(Duration::from_secs(10))]
fn a_reading_in_a_writer(#[case] root: &str) {
    check_program_scalar(&with_random(root), Value::Bool(true));
}

/// A pass may copy a reading, and the copies are one evaluation: mutability elimination copies a
/// written value into each statement that reads it, and every copy reads the call path's one
/// value at its position (`docs/chl-spec.md`, "Inputs from outside the program").
#[rstest]
#[case::a_write_in_a_branch_then_a_feed(indoc! {"
    import std::random
    t := 0
    ys: Feed(_)
    for x in [1, 2]:
        if t == 0:
            t := random::next()
        ys << t
    max(ys) == min(ys)
"})]
#[case::a_feed_in_the_writing_branch(indoc! {"
    import std::random
    t := 0
    ys: Feed(_)
    zs: Feed(_)
    for x in [1, 2]:
        if t == 0:
            t := random::next()
            ys << t
        zs << t
    max(ys) == max(zs)
"})]
#[case::one_reading_written_in_two_branches(indoc! {"
    import std::random
    a := 0
    b := 0
    for x in [1, 2, 3]:
        r = random::next()
        if x == 1:
            a := r
        if x == 1:
            b := r
    a == b
"})]
#[case::a_block_that_writes_then_feeds(indoc! {"
    import std::random
    t: Mut(Int, Txn) := 0
    ys: Feed(_)
    for x in [1, 2]:
        with begin():
            if t == 0:
                t := random::next()
            ys << t
    max(ys) == min(ys)
"})]
#[case::a_writing_if_at_the_top_level(indoc! {"
    import std::random
    t := 0
    u := 0
    if t == 0:
        t := random::next()
        u := t
    else:
        u := 1
    t == u
"})]
#[case::a_binding_fed_under_an_inner_loop(indoc! {"
    import std::random
    ys: Feed(_)
    for x in [1, 2]:
        r = random::next()
        for y in [1, 2]:
            ys << r
    sum([1 for a in ys for b in ys if a == b]) == 8
"})]
#[case::a_binding_written_under_an_inner_loop(indoc! {"
    import std::random
    a := 0
    b := 0
    for x in [1, 2]:
        r = random::next()
        for y in [1, 2]:
            if y == 1:
                a := r
            else:
                b := r
    a == b
"})]
#[case::a_binding_fed_in_two_branches(indoc! {"
    import std::random
    ys: Feed(_)
    zs: Feed(_)
    ws: Feed(_)
    for x in [1, 2, 3]:
        r = random::next() // 100000000000
        ws << r
        if x > 1:
            ys << r
        else:
            zs << r
    sum(ys) + sum(zs) == sum(ws)
"})]
#[case::a_binding_fed_under_a_join(indoc! {"
    import std::random
    ys: Feed(_)
    ws: Feed(_)
    for x in [1, 2, 3]:
        r = random::next() // 100000000000
        ws << r
        for y in [3, 4, 5]:
            if x + 2 == y:
                ys << r
    sum(ys) == sum(ws)
"})]
#[timeout(Duration::from_secs(10))]
fn the_copies_of_a_reading_are_one_reading(#[case] root: &str) {
    check_program_scalar(&with_random(root), Value::Bool(true));
}

/// A std module whose functions call a function value twice, as a parameter and as a binding.
const PAIRS: &str = indoc! {"
    import std::random

    def both(g):
        (g(1), g(2))

    pub def as_an_argument():
        both(\\x -> random::next())

    pub def as_a_binding():
        g = \\x -> random::next()
        (g(1), g(2))
"};

/// Each use of a function value is a call of its own, so the two calls take two readings
/// however the function reaches them (`docs/chl-spec.md`, "Inputs from outside the program").
#[rstest]
#[case::as_an_argument(indoc! {"
    import pairs
    p = pairs::as_an_argument()
    p.0 != p.1
"})]
#[case::as_a_binding(indoc! {"
    import pairs
    p = pairs::as_a_binding()
    p.0 != p.1
"})]
#[case::in_an_iteration(indoc! {"
    import pairs
    ys: Feed(_)
    for x in [1, 2]:
        p = pairs::as_an_argument()
        ys << (1 if p.0 == p.1 else 0)
    sum([y for y in ys]) == 0
"})]
#[timeout(Duration::from_secs(10))]
fn each_call_of_a_function_value_takes_its_own_reading(#[case] root: &str) {
    check_program_scalar(
        &with_random_and(root, &[("pairs", PAIRS)]),
        Value::Bool(true),
    );
}
