//! Dropping a program stops its sinks and frees the operator graph behind them.
//!
//! A program's outputs are the only strong owners of its sink consumers: the operator each
//! consumer subscribes to holds it weakly ([`compile_program`]). Each test holds a weak reference
//! to every sink consumer of a program it ran to completion, drops the program, and checks that
//! nothing still holds a consumer. A strong edge back to a consumer from the graph fails them.
//!
//! Each test keeps the context alive. Its last compilation's operator map
//! ([`GlobalContext::take_operator_map`]) holds the fan-outs the consumers subscribed to, so a
//! fan-out that held its consumers strongly would keep them alive past the program.

use std::cell::RefCell;
use std::rc::{Rc, Weak};

use cambra::ccl::context::{CompileResultExt, CompiledProgram, GlobalContext, compile_program};
use cambra::ccl::load::LoadedProgram;
use cambra::interpreter::sinks::SinkConsumer;
use cambra::live_program::{LiveProgram, MAIN_BRANCH};
use indoc::indoc;
use rstest::rstest;

/// How many scheduler passes a program gets to complete.
const CAP: usize = 10_000;

/// A weak reference to each of `program`'s sink consumers.
fn sink_consumers(program: &CompiledProgram) -> Vec<Weak<RefCell<SinkConsumer>>> {
    let consumers: Vec<_> = program
        .sinks()
        .filter_map(|output| output.sink_consumer.as_ref().map(Rc::downgrade))
        .collect();
    assert!(!consumers.is_empty(), "the program has a sink consumer");
    assert!(
        consumers.iter().all(|c| c.upgrade().is_some()),
        "every sink consumer is alive while its program is held"
    );
    consumers
}

/// Drive `ctx`'s scheduler until `program`'s sinks are all terminal.
fn run_to_completion(ctx: &mut GlobalContext, program: &CompiledProgram) {
    let finished = (0..CAP).any(|_| {
        ctx.scheduler().check_for_notifications();
        program.done.try_recv().is_ok()
    });
    assert!(
        finished,
        "the program finishes within {CAP} scheduler passes"
    );
}

fn assert_released(consumers: &[Weak<RefCell<SinkConsumer>>]) {
    assert!(
        consumers.iter().all(|c| c.upgrade().is_none()),
        "a sink consumer outlived its program, so something besides its output holds it strongly"
    );
}

#[rstest]
#[case::a_loop_over_a_literal(indoc! {"
    out = test_sink()
    for i in [1, 2]:
        out << 2 + 3 * 4
"})]
#[case::a_conditional(indoc! {"
    out = test_sink()
    n = 5
    out << (n // 3 if n > 3 else 0)
"})]
#[case::a_mutable_variable_written_in_a_loop(indoc! {"
    out = test_sink()
    x := 0
    for i in [1, 2, 3]:
        x := x + i
    out << x
"})]
#[case::a_filtered_comprehension_over_a_bound_collection(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    out << [x * 2 for x in xs if x > 1]
"})]
fn dropping_a_program_releases_its_sinks(#[case] code: &str) {
    let mut ctx = GlobalContext::default();
    let _sink = ctx.register_test_sink("out");
    let loaded = LoadedProgram::test(code);
    let program = compile_program(&mut ctx, &loaded, Box::new(|| {})).unwrap_or_render(&loaded);
    run_to_completion(&mut ctx, &program);
    let consumers = sink_consumers(&program);
    drop(program);
    assert_released(&consumers);
    drop(ctx);
}

/// A [`LiveProgram`] holds each branch's program, so dropping it drops them.
#[test]
fn dropping_a_live_program_releases_its_sinks() {
    let mut ctx = GlobalContext::default();
    let _sink = ctx.register_test_sink("out");
    let loaded = LoadedProgram::test(indoc! {"
        out = test_sink()
        for i in [1, 2]:
            out << i
    "});
    let live = LiveProgram::start(&mut ctx, &loaded, &|| Box::new(|| {})).unwrap_or_render(&loaded);
    let (_, program) = live.program(MAIN_BRANCH).expect("`main` runs");
    run_to_completion(&mut ctx, program);
    let consumers = sink_consumers(program);
    drop(live);
    assert_released(&consumers);
    drop(ctx);
}
