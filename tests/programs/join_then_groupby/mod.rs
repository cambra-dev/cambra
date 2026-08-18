//! A hash join and a group-by in one program — the fixture that puts both
//! planning recognizers on a single tree.
//!
//! `planning/join.rs` rewrites the two-source comprehension with its
//! `u.id == o.user_id` guard into a keyed lookup, and `planning/groupby.rs`
//! rewrites the `groupby` into its bucketize chain. The `post-lambda-elim →
//! post-planning` pane pair therefore has both rewrites to explain on one tree,
//! which is what makes this the program to point the inspector at.
//!
//! The two are summed rather than chained: grouping directly over a join's
//! product domain panics in `transform_by_map` today, so a chained form would
//! pin an engine limitation rather than the planning rewrites.
//!
//! `425` is the join — every order's user id matches, so all four amounts
//! survive (100 + 50 + 200 + 75). `14` is the group-by: `x // 2` buckets
//! `[2,3]` and `[4,5]`, summing to 5 and 9.

use super::common::expect_scalar;

#[test]
fn join_then_groupby() {
    expect_scalar(include_str!("program.cambra"), "439");
}
