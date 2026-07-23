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
//! **Currently blocked at parsing.**  The `\` lambda now lexes; the next
//! unsupported construct is the `Feed(...)` annotation-only forward
//! declaration (an annotation with no initialiser).  Behind it: feed elements
//! carrying transaction time, `restrict`/`sum` over a feed, and structured
//! requests.  This pins the `Feed(...)` forward-declaration parse failure.

use super::common::expect_compile_error;

#[test]
fn ledger_balance_currently_blocked_at_parsing() {
    expect_compile_error(include_str!("program.cambra"), "Feed({amount: Int})");
}
