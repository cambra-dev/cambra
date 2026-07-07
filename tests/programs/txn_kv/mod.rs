//! Transactional KV store over HTTP, with a `/stats` endpoint.  `/get` and
//! `/set` are handled concurrently, so the shared `store` must be
//! transactional — it's mutable over the transaction time domain
//! (`Mut(Map(...), Txn)`), and every access runs inside `with begin():`.  The
//! read-modify-write in `/set` (insert only if absent) is atomic because the
//! read and write share one transaction.
//!
//! `/stats` contrasts the two idioms: the store uses transactional *mutation*,
//! while the write count is a *declarative aggregate* over the request stream
//! (`count(set_reqs.restrict(λ r → r.time < txn.current_time()))`) — no mutable
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
//! **Currently blocked at lexing.**  The lambda `λ` in the `/stats` aggregate
//! isn't a lexable token yet, so lexing fails before parsing.  Behind it: the
//! `requires` clause, `with begin()` / `abort()`, the `Mut(..., Txn)`
//! annotation, `match`, map-index assignment, structured requests, and
//! `restrict` / `count`.  This pins the `λ` lex failure.

use super::common::expect_compile_error;

#[test]
fn txn_kv_currently_blocked_at_lexing() {
    expect_compile_error(include_str!("program.cambra"), "invalid token");
}
