//! Two `yield` generators feeding one explicit `defer()` channel from two
//! sites.
//!
//! The channel's five positions arrive in two shapes: one feed carries `sum`
//! over the first generator, and the loop over the second feeds one position
//! per iteration. Channelization fans both sites into one channel, so the
//! `max` reads across both — `max(20, 1, 4, 9, 16)`.

use super::common::expect_scalar;

#[test]
fn defer_generators() {
    expect_scalar(include_str!("program.cambra"), "20");
}
