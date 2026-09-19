//! Agreement between a `Let`/`LetRec` binder's recorded type and its references'.
//!
//! `settle` runs [`check_binder_references`] at every strict wall but `post-planning`, so
//! a pass that rewrites a binder and its references out of step is rejected where it
//! happens rather than at whichever later pass first reads both. Held here: the shapes
//! that used to diverge and no longer do, and the one planning still builds.

use cambra::ccl::context::{Phase, compile_to};
use cambra::ccl::infer::check_binder_references;
use indoc::indoc;

/// Assert `code`'s tree at `phase` has no binder/reference disagreement.
fn agrees(code: &str, phase: Phase) {
    let tree = compile_to(code, phase)
        .unwrap_or_else(|errs| panic!("compiling {code:?} to {phase:?}: {errs:?}"));
    if let Err(errs) = check_binder_references(&tree) {
        panic!("{phase:?} on {code:?}: {errs:?}");
    }
}

/// A correlated filter over a cross join of two let-bound collections. `simplify`
/// collapses `id ≫ a` to `a` and stamps the chain's kind over it, so `a` — bound at
/// `[0, 1] ⤇ Int` — was read at `[0, 1] ⇒ Int`, a collection typed as a compute
/// function. The `id` is minted by planning's hash-join key rewrite, which now carries
/// the kind onto it instead of leaving the replaced projection's behind.
#[test]
fn a_correlated_filter_over_a_cross_join_keeps_its_sources_data_kind() {
    agrees(
        "a = [1,2]\nb = [10, 20]\n[x + y for x in a for y in b if x == y // 10]\n",
        Phase::Planning,
    );
}

/// The same rewrite reached through a mutable loop over the product domain — two routes
/// to one rule, so both are held.
#[test]
fn a_loop_over_a_product_domain_keeps_its_sources_data_kind() {
    agrees(
        indoc! {r#"
            xs = [1, 2, 3]
            ys = [2, 3, 4]
            n := 0
            for l in [x for x in xs for y in ys if x == y]:
                n := n + 1
            n
        "#},
        Phase::Planning,
    );
}

/// **Pinned defect.** A same-domain conditional realizes to a gated union, and the
/// `realize(…)` asserting that carries the sum it realizes — `Σ (σ : [[0, 1]]). (σ ⤇
/// Int)` — while the consumer reading the binding is typed at `[0, 1] ⤇ Int`, the one
/// candidate that sum determines. A sum sits below no plain arrow in either direction,
/// so nothing relates the two and the tree is ill-typed.
///
/// The shared `let` is all that hides it. Inline the binding — the same program, the
/// same planning output, one fewer binder — and plain `typecheck` rejects it at the
/// consuming `Apply` with those two types. This is not a rule the check is missing; it
/// is a tree planning should not build.
///
/// Two local repairs are ruled out by decisions already recorded in the code. Collapsing
/// this sum along with the other determined ones instantiates an assertion that stands
/// over a `Variant` domain, which breaks five tests. Inlining the binding regardless of
/// determinacy moves the rejection to the `Apply` rather than removing it, and
/// contradicts `a_conditional_binding_is_copied_when_its_witness_is_undetermined`. What
/// is left is where a determined `Realize` discharges its witness, a change to planning
/// rather than to this check.
#[test]
fn planning_leaves_a_determined_realize_unreadable() {
    let code = indoc! {r#"
        c: Bool = True
        xs = [y * 10 for y in box([1, 2])] if c else [z * 100 for z in box([3, 4])]
        sum([w for w in xs])
    "#};
    let tree = compile_to(code, Phase::Planning).expect("planning succeeds");
    let errs = check_binder_references(&tree)
        .expect_err("a sum-typed binder read at a plain arrow must be reported");
    let rendered = format!("{errs:?}");
    assert!(
        rendered.contains("Σ") && rendered.contains("[0, 1] ⤇ Int"),
        "expected the sum/plain-arrow disagreement, got: {rendered}"
    );
}

/// The walls below planning stay clean, including the channel a collection feed builds —
/// the shape whose binder and reference used to differ by one level.
#[test]
fn the_phases_below_planning_agree() {
    for code in [
        "out = defer()\nout << [2, 4, 6]\nout\n",
        "a = [1,2]\nb = [10, 20]\n[x + y for x in a for y in b if x == y // 10]\n",
        indoc! {r#"
            c: Bool = True
            xs = [y * 10 for y in box([1, 2])] if c else [z * 100 for z in box([3, 4])]
            sum([w for w in xs])
        "#},
    ] {
        for phase in [Phase::Channelize, Phase::LambdaElim] {
            agrees(code, phase);
        }
    }
}
