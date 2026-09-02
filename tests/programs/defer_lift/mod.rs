//! A UDF that creates, feeds, and returns a defer channel, whose result is then
//! fed again from a `for` loop.
//!
//! Inlining the call produces `let totals = (feed-prefix; let t = Defer in t) in
//! …`, the shape `try_lift_defer` rewrites by merging the inner and outer defer
//! scopes; the lifted feed head keeps its `NodeId` (preserve, not mint) so its
//! source span survives into the post-channelize span index. The loop adds a
//! second feed site, so the two sites also fan in to one channel during
//! channelization. Both structures — `channelize.defer_lift` and
//! `channelize.cluster` — are pinned by the `defer_lift` snapshot fixture.

use super::common::expect_scalar;

#[test]
fn defer_lift() {
    expect_scalar(include_str!("program.cambra"), "10");
}
