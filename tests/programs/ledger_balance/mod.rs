//! A time-pinned view over a transactionally-fed collection.  `ledger` is
//! fed only inside transactions, so each element carries the commit time of
//! the transaction that fed it; `/balance` sums the deposits committed
//! strictly before its own transaction began.  This lifts `txn_kv`'s /stats
//! idiom from a request stream (whose elements naturally carry `req.time`)
//! to a *feed*, where `e.time` is contributed by the feed's
//! transaction-time domain rather than written by the feeder.
//!
//! This isolates the storefront's revenue view: without the `restrict`, the
//! aggregate is only defined when the feed closes — for a server, never.
//!
//! **Currently blocked at lexing.**  The `\` lambda in the restrict
//! predicate isn't a lexable token yet (same first blocker as `txn_kv`).
//! Behind it: the `Feed(...)` annotation, feed elements carrying
//! transaction time, `restrict`/`sum` over a feed, and structured requests.
//! This pins the lambda lex failure.

use super::common::expect_compile_error;

#[test]
fn ledger_balance_currently_blocked_at_lexing() {
    expect_compile_error(include_str!("program.cambra"), "invalid token");
}
