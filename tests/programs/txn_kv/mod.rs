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
//! **Currently blocked at parsing.**  The `\` lambda lexes and the variant tags
//! both lex and parse (`docs/chl-spec.md`, "3.15 Variant constructors"), so the
//! first unsupported construct is `import http` — modules, which have no
//! grammar.  Behind it: the `requires Transaction` contextual-parameter clause,
//! `with begin()` / `abort()`, map-index assignment, structured requests, and
//! `restrict` / `count`.  This pins the `import` parse failure.

use super::common::expect_compile_error;

#[test]
fn txn_kv_currently_blocked_at_parsing() {
    expect_compile_error(include_str!("program.cambra"), "import http");
}
