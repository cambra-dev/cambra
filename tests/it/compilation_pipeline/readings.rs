//! Readings: calls whose value comes from outside the program, one per position and call path
//! (`docs/chl-spec.md`, "Inputs from outside the program").

use std::time::Duration;

use cambra::ccl::load::{InMemory, LoadedProgram, RootFile};
use cambra::interpreter::Value;
use indoc::indoc;
use rstest_log::rstest;

use super::helpers::check_program_scalar;

/// A std module that reaches the random reading, as `std::time` reaches the clock.
const RANDOM: &str = indoc! {"
    pub def draw(seed):
        __random()

    pub def next() => Int:
        __random()
"};

/// `root`, loaded against the std module `std::random` holding [`RANDOM`].
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
    LoadedProgram::load_with_std(root, &mut files, &[("std::random", RANDOM)])
}

#[rstest]
#[case::two_calls_at_the_top_level(indoc! {"
    import std::random
    a = random::draw(0)
    b = random::draw(0)
    a != b
"})]
#[case::two_calls_of_no_arguments(indoc! {"
    import std::random
    random::next() != random::next()
"})]
#[case::calls_of_no_arguments_in_an_iteration(indoc! {"
    import std::random
    xs = [random::next() for n in [1, 2]]
    max(xs) != min(xs)
"})]
#[case::one_binding_is_one_reading(indoc! {"
    import std::random
    a = random::draw(0)
    a == a
"})]
#[case::each_iteration_reads_its_own(indoc! {"
    import std::random
    xs = [random::draw(n) for n in [1, 2, 3]]
    sum([1 for x in xs for y in xs if x == y]) == 3
"})]
#[case::each_nested_iteration_reads_its_own(indoc! {"
    import std::random
    rows = [[random::draw(n + m) for m in [10, 20]] for n in [1, 2]]
    tops = [max(row) for row in rows]
    sum([1 for row in rows if max(row) != min(row)]) == 2 and max(tops) != min(tops)
"})]
#[case::a_filtered_iteration_reads_its_own(indoc! {"
    import std::random
    xs = [random::draw(n) for n in [1, 2, 3, 4] if n > 2]
    max(xs) != min(xs)
"})]
#[case::two_calls_in_one_iteration(indoc! {"
    import std::random
    sum([1 for n in [1, 2, 3] if random::draw(n) == random::draw(n)]) == 0
"})]
#[case::one_binding_in_an_iteration_is_one_reading(indoc! {"
    import std::random
    sum([t - t for t in [random::draw(n) for n in [1, 2, 3]]]) == 0
"})]
#[timeout(Duration::from_secs(10))]
fn a_reading_holds_one_value_per_position_and_call_path(#[case] root: &str) {
    check_program_scalar(&with_random(root), Value::Bool(true));
}

/// Only a std module names an intrinsic (`docs/chl-spec.md`, "9.16 The std root").
#[test]
fn a_user_module_naming_an_intrinsic_is_refused() {
    super::helpers::check_compile_error(
        "__random()\n",
        "`__random` is an intrinsic, which only a std module names",
    );
}

/// A reading requires `Ext`, which only the run supplies: a module whose top level takes one is
/// run, and one whose functions take one is imported (`docs/chl-spec.md`, "Inputs from outside
/// the program").
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
    assert!(errors.contains("its top level requires `Ext`"), "{errors}");
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
        r = random::draw(n)
        total += r - r
        last := r
    total == 0 and last != 0
"})]
#[case::a_transaction(indoc! {"
    import std::random
    stock: Mut(Int, Txn) := 0
    for n in [1, 2, 3]:
        with begin():
            stock := random::draw(n)
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
            t := random::draw(x)
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
            t := random::draw(x)
            ys << t
        zs << t
    max(ys) == max(zs)
"})]
#[case::one_reading_written_in_two_branches(indoc! {"
    import std::random
    a := 0
    b := 0
    for x in [1, 2, 3]:
        r = random::draw(x)
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
                t := random::draw(x)
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
#[timeout(Duration::from_secs(10))]
fn the_copies_of_a_reading_are_one_reading(#[case] root: &str) {
    check_program_scalar(&with_random(root), Value::Bool(true));
}

/// A std module whose functions call a function value twice, as a parameter and as a binding.
const PAIRS: &str = indoc! {"
    def both(g):
        (g(1), g(2))

    pub def as_an_argument():
        both(\\x -> __random())

    pub def as_a_binding():
        g = \\x -> __random()
        (g(1), g(2))
"};

/// Each use of a function value is a call of its own, so the two calls take two readings
/// however the function reaches them (`docs/chl-spec.md`, "Inputs from outside the program").
#[rstest]
#[case::as_an_argument(indoc! {"
    import std::pairs
    p = pairs::as_an_argument()
    p.0 != p.1
"})]
#[case::as_a_binding(indoc! {"
    import std::pairs
    p = pairs::as_a_binding()
    p.0 != p.1
"})]
#[case::in_an_iteration(indoc! {"
    import std::pairs
    ys: Feed(_)
    for x in [1, 2]:
        p = pairs::as_an_argument()
        ys << (1 if p.0 == p.1 else 0)
    sum([y for y in ys]) == 0
"})]
#[timeout(Duration::from_secs(10))]
fn each_call_of_a_function_value_takes_its_own_reading(#[case] root: &str) {
    let root = RootFile {
        path: "main.cambra".to_owned(),
        module: None,
        text: root.to_owned(),
    };
    let program = LoadedProgram::load_with_std(
        root,
        &mut InMemory::default(),
        &[("std::random", RANDOM), ("std::pairs", PAIRS)],
    );
    check_program_scalar(&program, Value::Bool(true));
}
