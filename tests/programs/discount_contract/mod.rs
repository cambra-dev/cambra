//! Function contracts as asserts — the CHL surface form for refinement
//! types (`docs/chl-spec.md`, "6. Types (informal sketch)").  Asserts at the top of a function are preconditions (lifted to
//! refinements on the parameters); an assert on the result variable before
//! it is returned is a postcondition (lifted to a refinement on the
//! codomain); placement and reference rules beyond those two canonical
//! shapes are still being elaborated.  Call sites must prove the
//! preconditions; an
//! implementation that can't discharge the postcondition is rejected at
//! compile time.
//!
//! This is the smallest program on the storefront's dependency list: `quote`
//! and `reserve` there use exactly this mechanism.
//!
//! **Currently blocked at parsing.**  `assert` isn't a recognized statement
//! (the parser reads it as an identifier and trips on what follows).
//! Behind it: the lift itself (asserts -> CCL refinements) and call-site
//! discharge.  This pins the parse failure at the first assert.  The def
//! deliberately omits the recommended `=> Int` return annotation
//! (`docs/chl-spec.md`, "4.1 `def` — function definition") so the pin
//! stays on the contract machinery, not the annotation syntax.
//!
//! Expected output once fully unblocked: `75`.

use super::common::expect_compile_error;

#[test]
fn discount_contract_currently_blocked_at_parsing() {
    expect_compile_error(include_str!("program.cambra"), "assert price >= 0");
}
