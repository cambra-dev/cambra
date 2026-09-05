//! Fuzz the concrete subtype relation for transitivity.
//!
//! `constrain_go` implements `<:` without writing the relation down, so
//! transitivity is a property of the algorithm rather than of any one arm, and no
//! unit test states it: a single case cannot, because the property is over
//! *every* chain the relation accepts, and the chains where it fails are the ones
//! nobody thought to write down.
//!
//! This builds chains `a <: b <: c` out of near-miss partners of a generated type
//! (`type_gen::partner`), keeps the ones `constrain_subtype` accepts, and asserts
//! it accepts the direct edge too. `formal/CclFormal/SubtypingIsTransitive.lean` proves the
//! same property of the *declarative* relation; this checks the implementation,
//! which is the half a proof about a model cannot reach.
//!
//! `tests/constraint_order_fuzz.rs` fuzzes the same defect class one level up: an
//! answer that depends on the order constraints arrive in.
//!
//! Seeded and dependency-free, so a failure replays — `CAMBRA_FUZZ_SEED` picks the
//! seed and `CAMBRA_FUZZ_N` the number of chains, the same two knobs the
//! order fuzz reads.

mod type_gen;

use cambra::ccl::Type;
use cambra::ccl::infer::solver::{ConstrainCache, constrain_subtype};
use type_gen::{Fragment, Rng, env_or, gen_ty, partner};

/// Chains `a <: b <: c` that `constrain` accepts, checked against the direct
/// edge. No violation is tolerated — a hit is a finding, and fails the test with
/// the triple printed.
#[test]
fn transitivity_chain_fuzz() {
    let seed: u64 = env_or("CAMBRA_FUZZ_SEED", 0xBEEF);
    let n: usize = env_or("CAMBRA_FUZZ_N", 4000);

    let ok = |x: &Type, y: &Type| {
        let mut cache = ConstrainCache::new();
        constrain_subtype(x, y, &mut cache).is_ok()
    };
    let mut rng = Rng::new(seed);
    let mut chains = 0usize;
    let mut attempts = 0usize;
    let mut violations: Vec<(Type, Type, Type)> = Vec::new();
    while chains < n && attempts < n * 100 {
        attempts += 1;
        let b = gen_ty(&mut rng, 3, Fragment::WithSums);
        let a = partner(&mut rng, &b, Fragment::WithSums);
        let c = partner(&mut rng, &b, Fragment::WithSums);
        if !(ok(&a, &b) && ok(&b, &c)) {
            continue;
        }
        chains += 1;
        if !ok(&a, &c) {
            violations.push((a, b, c));
        }
    }

    eprintln!(
        "transitivity: {chains} chains (seed {seed}, {attempts} attempts), {} violations",
        violations.len()
    );
    // The attempt cap bounds the loop, not the coverage: a generator that stops
    // producing acceptable chains would otherwise leave this test reporting a
    // smaller number and still passing.
    assert_eq!(
        chains, n,
        "only {chains}/{n} chains built in {attempts} attempts — the generator \
         stopped producing pairs `constrain` accepts"
    );
    assert!(
        violations.is_empty(),
        "transitivity violations (first 5):\n{}",
        violations
            .iter()
            .take(5)
            .map(|(a, b, c)| format!("a={a}\nb={b}\nc={c}\n"))
            .collect::<Vec<_>>()
            .join("\n")
    );
}
