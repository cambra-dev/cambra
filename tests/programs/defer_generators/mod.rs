//! Two `yield` generators feeding one explicit `defer()` channel from two
//! sites.
//!
//! Currently rejected: after lambda elimination the `zip`-of-generators result
//! is typed as a compute function (`⇒`) where the letrec binder wants a data
//! collection (`⤇`), and the two kinds are incomparable. Expected `16` once the
//! kinds agree. This is the gallery's record of that limitation — no other
//! program reaches it — and the one entry in `tests/inspector_goldens.rs`'
//! `DUMP_PANICS`, since a program that does not compile has no payload to
//! validate.
//!
//! The needle names the mismatch, not the check that reports it: the
//! pass-boundary check reports "post-lambda-elim produced an invalid tree", and
//! the incomparable-kinds sentence it renders is what this test pins.

use super::common::expect_compile_error;

#[test]
fn defer_generators_currently_fails_on_incomparable_kinds() {
    expect_compile_error(
        include_str!("program.cambra"),
        "a compute function ⇒ and a data collection ⤇ met at one position",
    );
}
