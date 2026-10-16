//! Transactional KV store over HTTP, with a `/stats` endpoint.  `/get` and
//! `/set` are handled concurrently, so the shared `store` must be
//! transactional — it's mutable over the transaction time domain
//! (`Mut(Map(...), Txn)`), and every access runs inside `with begin():`.  The
//! read-modify-write in `/set` (insert only if absent) is atomic because the
//! read and write share one transaction.
//!
//! `/stats` contrasts the two idioms: the store uses transactional *mutation*,
//! while the write count is a *declarative aggregate* over the request stream
//! (`count(set_reqs.restrict(\r -> r.time < txn.current_time()))`) — no mutable
//! counter, no shared state to race on.
//!
//! `requires Transaction` makes the transaction a contextual parameter
//! (resolved by the typeclass/given solver, not an effect); a transaction
//! commits on normal block exit, `abort()` rolls it back.
//!
//! This merges two former standalone examples: `kv_store` (a KV store served
//! by concurrent HTTP handlers is only correct if its state is transactional)
//! and `hit_counter` (the request-stream aggregate).
//!
//! **Currently blocked at lowering.**  The whole program parses, its `case`
//! arms on their `case` lines included (`docs/chl-spec.md`, "An arm on its
//! `case` line"), so the first error is lowering refusing `import http`.  Behind
//! it: `requires Transaction` (also refused by lowering), `with begin()` /
//! `abort()`, map-index assignment, structured requests, and `restrict` /
//! `count`.  This pins the `import` refusal, and that no parse error precedes
//! it.

use super::common::expect_compile_error_past;

#[test]
fn txn_kv_currently_blocked_at_lowering() {
    expect_compile_error_past(
        include_str!("program.cambra"),
        "`import` is not supported yet",
        "parse error",
    );
}
