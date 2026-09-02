//! A UDF that creates, feeds, and *returns* a defer channel.
//!
//! Inlining the call produces `let totals = (feed-prefix; let t = Defer in t) in
//! …`, the shape `try_lift_defer` rewrites by merging the inner and outer defer
//! scopes. The lifted feed head keeps its `NodeId` (preserve, not mint) so its
//! source span survives into the post-channelize span index — which the
//! `defer_lift` snapshot fixture pins.

use super::common::expect_scalar;

#[test]
fn defer_lift() {
    expect_scalar(include_str!("program.cambra"), "10");
}
