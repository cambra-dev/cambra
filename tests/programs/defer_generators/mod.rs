//! Two `yield` generators feeding one explicit `defer()` channel from two
//! sites — the generator route to [`super::defer_fanin`]'s channel union.
//!
//! Currently rejected: after lambda elimination the `zip`-of-generators result
//! is typed as a compute function (`⇒`) where the letrec binder wants a data
//! collection (`⤇`), and the two kinds are incomparable. Expected `16` once the
//! kinds agree.
//!
//! The needle names the *mismatch*, not the check that reports it. Which
//! checkpoint fires first depends on the build: the always-on pass-boundary wall
//! says "post-lambda-elim produced an invalid tree", while under
//! `--features deep-typecheck` (which CI sets via `DEEP_TYPECHECK=1`) the
//! per-operation typecheck reaches it earlier and says "Failed post-transform
//! typecheck". Both render the same incomparable-kinds sentence, so pinning that
//! is what makes this test say the same thing in either configuration.

use super::common::expect_compile_error;

#[test]
fn defer_generators_currently_fails_on_incomparable_kinds() {
    expect_compile_error(
        include_str!("program.cambra"),
        "a compute function ⇒ and a data collection ⤇ met at one position",
    );
}
