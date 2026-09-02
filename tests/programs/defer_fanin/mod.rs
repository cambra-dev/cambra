//! One `defer()` channel fed from two sites — a scalar seed and a
//! per-iteration `<<` inside a `for` loop — then collapsed with `max`.
//!
//! The two feed sites fan in to one channel during channelization; that channel
//! union is the synthesized structure the inspector shows. Isolated from
//! generators on purpose: [`super::defer_generators`] is the same fan-in reached
//! through `yield`.

use super::common::expect_scalar;

#[test]
fn defer_fanin() {
    expect_scalar(include_str!("program.cambra"), "10");
}
