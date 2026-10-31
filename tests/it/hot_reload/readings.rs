//! A reading belongs to its version of the program, and a mutable variable holding one keeps it
//! across a reload (`docs/chl-spec.md`, "Inputs from outside the program").
//!
//! Each program's value is a collection over the live source `source1()`, which no consumer
//! releases, so the replacement pulls again every position its predecessor delivered.

use std::{cell::RefCell, rc::Rc};

use cambra::{
    ccl::{
        Type,
        context::GlobalContext,
        load::{InMemory, LoadedProgram, RootFile},
    },
    interpreter::{BaseType, ColumnValue, Extent, Predicate, TestDataSource, Tile, Value},
    live_program::{LiveProgram, MAIN_BRANCH},
};
use indoc::indoc;

use super::serving::no_main;

/// A std module that reaches the random reading, as `std::time` reaches the clock.
const RANDOM: &str = indoc! {"
    pub def draw(seed):
        __random()

    pub def next() => Int:
        __random()
"};

/// `text`, loaded against the std module `std::random` holding [`RANDOM`].
fn program(text: &str) -> LoadedProgram {
    let root = RootFile {
        path: "main.cambra".to_owned(),
        module: None,
        text: text.to_owned(),
    };
    LoadedProgram::load_with_std(root, &mut InMemory::default(), &[("std::random", RANDOM)])
}

/// The values of a collection of integers, by key.
fn values(tile: &Tile) -> Vec<i64> {
    let Tile::DataFunction {
        domain, codomain, ..
    } = tile
    else {
        panic!("a collection, got {tile:?}");
    };
    let Tile::Scalar(ColumnValue::Ints(values)) = &**codomain else {
        panic!("integers, got {codomain:?}");
    };
    let mut keyed: Vec<(Value, i64)> = (0..domain.len())
        .map(|row| (domain.index_at(row), values[row]))
        .collect();
    keyed.sort_by(|a, b| a.0.partial_cmp(&b.0).expect("keys are ordered"));
    keyed.into_iter().map(|(_, v)| v).collect()
}

/// Run `v1` over a live `source1()` holding one integer, reload it to `v2`, deliver a second,
/// and answer the program's value before the reload and after it.
fn across_a_reload(v1: &str, v2: &str) -> (Vec<i64>, Vec<i64>) {
    let mut ctx = GlobalContext::default();
    let source = Rc::new(RefCell::new(TestDataSource::new(
        "source1",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    ctx.register_source(source.clone());
    let pull = |ctx: &mut GlobalContext, live: &mut LiveProgram| -> Tile {
        let mut tile = None;
        for _ in 0..20 {
            ctx.scheduler().check_for_notifications();
            let producer = live
                .main_producer_mut(MAIN_BRANCH)
                .expect("the program's value is pulled");
            tile = Some(producer.get(producer.tiling().universal_guard()));
        }
        tile.expect("pulled")
    };
    let mut live = LiveProgram::start(&mut ctx, &program(v1), &no_main).expect("v1 compiles");
    source
        .borrow_mut()
        .add_data(&[(Value::uint_from_row(0), Value::Int(1))]);
    source
        .borrow_mut()
        .set_yield_predicate(Predicate::at_or_below(Value::uint_from_row(0)));
    let before = values(&pull(&mut ctx, &mut live));
    live.reload(&mut ctx, MAIN_BRANCH, &program(v2), &no_main)
        .expect("v2 replaces v1");
    source
        .borrow_mut()
        .add_data(&[(Value::uint_from_row(1), Value::Int(2))]);
    source
        .borrow_mut()
        .set_yield_predicate(Predicate::at_or_below(Value::uint_from_row(1)));
    let after = values(&pull(&mut ctx, &mut live));
    (before, after)
}

/// A mutable variable holding a reading keeps it across a reload, whatever else the reload
/// changes: here the loop that writes it is edited, so its store is rebuilt and the variable takes
/// the value its predecessor held. A position delivered after the reload reads that value.
#[test]
fn a_mutable_variable_keeps_its_reading() {
    let (before, after) = across_a_reload(
        indoc! {"
            import std::random
            t := 0
            ys: Feed(_)
            for x in source1():
                if t == 0:
                    t := random::draw(x)
                ys << t + x
            [y for y in ys]
        "},
        indoc! {"
            import std::random
            t := 0
            ys: Feed(_)
            for x in source1():
                if t == 0:
                    t := random::draw(x)
                ys << t + x * 10
            [y for y in ys]
        "},
    );
    let t = before[0] - 1;
    assert_eq!(
        after.last(),
        Some(&(t + 20)),
        "before: {before:?}, after: {after:?}"
    );
}

/// A top-level mutable variable holding a reading keeps it across a reload that edits its
/// initializer: the declaration already ran, so the new initializer is not evaluated.
///
/// Wrong today: mutability elimination lowers a top-level `t := e` outside every loop to a plain
/// binding, so `t` has no store and no `VarPath`, the reload carries nothing for it, and the new
/// version takes the reading again. Carrying it is not a matter of carrying write-less variables:
/// a top-level variable's straight-line writes and its loops' writes are one history, and a reload
/// has to carry that history over the positions it has decided, statement positions included.
// Pinned on the failure rather than deferred, as `tests/it/http_server.rs` explains.
#[test]
#[should_panic(expected = "the reload took the reading again")]
fn a_top_level_mutable_variable_keeps_its_reading() {
    let (before, after) = across_a_reload(
        indoc! {"
            import std::random
            t := random::next()
            [t + x for x in source1()]
        "},
        indoc! {"
            import std::random
            t := random::next() + 1
            [t + x * 10 for x in source1()]
        "},
    );
    let t = before[0] - 1;
    assert_eq!(
        after.last(),
        Some(&(t + 20)),
        "the reload took the reading again: before: {before:?}, after: {after:?}"
    );
}

/// A transactional variable holding a reading keeps it across a reload that edits its
/// initializer: the declaration already ran, so the new initializer is not evaluated.
///
/// Wrong today: the new version reads its own initializer's reading. A variable a transaction
/// only reads is still a key of its store, so it has an identity to carry; the reload appears to
/// capture a value only for a key something has written. Not yet confirmed.
// Pinned on the failure rather than deferred, as `tests/it/http_server.rs` explains.
#[test]
#[should_panic(expected = "the reload took the reading again")]
fn a_transactional_variable_keeps_its_reading() {
    let (before, after) = across_a_reload(
        indoc! {"
            import std::random
            t: Mut(Int, Txn) := random::next()
            ys: Feed(_)
            for x in source1():
                with begin():
                    ys << t + x
            [y for y in ys]
        "},
        indoc! {"
            import std::random
            t: Mut(Int, Txn) := random::next() + 1
            ys: Feed(_)
            for x in source1():
                with begin():
                    ys << t + x * 10
            [y for y in ys]
        "},
    );
    let t = before[0] - 1;
    assert_eq!(
        after.last(),
        Some(&(t + 20)),
        "the reload took the reading again: before: {before:?}, after: {after:?}"
    );
}
