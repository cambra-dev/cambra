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
//! The HTTP runs load. Indexed response assignment remains unsupported;
//! transaction-time feed fields and structured requests are also sketches.

use super::common::expect_compile_error;

#[test]
fn ledger_balance_currently_blocked_at_indexed_response() {
    expect_compile_error(include_str!("program.cambra"), "`m[k]` is a keyed write");
}
