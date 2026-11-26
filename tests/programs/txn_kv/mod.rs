//! Transactional KV store over HTTP, with a `/stats` endpoint.  `/get` and
//! `/set` are handled concurrently, so the shared `store` must be
//! transactional — it's mutable over the transaction time domain
//! (`Mut(Map(...), Txn)`), and every access runs inside `with begin():`.  The
//! read-modify-write in `/set` (insert only if absent) is atomic because the
//! read and write share one transaction.
//!
//! `/stats` contrasts the two idioms: the store uses transactional *mutation*,
//! while the write count is a *declarative aggregate* over the request stream
//! (`count(set_reqs.restrict(\r -> r.time < txn::now()))`) — no mutable
//! counter, no shared state to race on.
//!
//! `requires Transaction` makes the transaction a contextual requirement,
//! which the block calling `put` supplies; a transaction commits on normal
//! block exit, and one that should not write is written with a guard.
//!
//! This merges two former standalone examples: `kv_store` (a KV store served
//! by concurrent HTTP handlers is only correct if its state is transactional)
//! and `hit_counter` (the request-stream aggregate).
//!
//! The HTTP runs load, and the program parses, including its inline `case` arms
//! (`docs/chl-spec.md`, "An arm on its `case` line"). Indexed response assignment
//! remains unsupported. Structured requests and time-pinned aggregates are sketches.

use super::common::expect_compile_error_past;

#[test]
fn txn_kv_currently_blocked_at_indexed_response() {
    expect_compile_error_past(
        include_str!("program.cambra"),
        "`m[k]` is a keyed write",
        "parse error",
    );
}
