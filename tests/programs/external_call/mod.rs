//! The outbound half of the HTTP library: a call to an external service, as
//! the dual of `http.serve`.  A server endpoint is an incoming collection of
//! requests paired with a deferred outgoing collection of responses; a client
//! call is an outgoing collection of requests paired with an incoming
//! collection of results, and the two are paired by a key the program supplies.
//!
//! The key is the idempotency key, and the durability contract is stated on it:
//! for each key the runtime dispatches at most one call and records its result
//! durably before any consumer observes it.  That contract is the irreducible
//! content of durable execution — a restart between dispatch and result must
//! neither lose the charge nor repeat it — and it is why this program exists
//! separately from `checkout_saga`, which assumes it.
//!
//! Two consequences the program leans on.  A result that has not arrived is not
//! a missing value but an unfilled tile, so `results[key]` has the result type
//! rather than `Option` of it and the read waits the way every dataflow read
//! waits.  And the apparent cycle — a feed of this program causes a source of
//! this program — is well-founded by the key: the result at `k` depends only on
//! the request at `k`.  That is the causal-accessor argument of
//! `src/ccl/design/mutability.md`, "The model: histories and causal recursion",
//! with the key in place of the domain position.
//!
//! **Blocked at lowering.**  The needle pins this program's own gap: the
//! `(requests, results)` destructuring is special-cased to `http_serve`, so an
//! `http.call` binding falls through to the generic assignment path and is
//! rejected as a non-simple target.  Ahead of it in the same run, shared with
//! every north-star program: `import` is not a keyword, record terms `(f=v)`
//! do not parse, and a `<<` feed is not admitted as a non-terminal statement in
//! a loop body.

use super::common::expect_compile_error;

#[test]
fn external_call_currently_blocked_at_lowering() {
    expect_compile_error(
        include_str!("program.cambra"),
        r#"http.call("payments", "POST", "/charges")"#,
    );
}
