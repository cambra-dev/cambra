//! The scoped-children walk sits under `is_free`, which capture-avoiding
//! substitution consults once per mapped binder per node. That makes it one of
//! the hottest paths in the compiler, and it must stay allocation-free — which
//! is why `Binders` borrows a `LetRec` group in place instead of collecting it
//! into a `Vec` so every child can be handed one slice. Collecting would be an
//! allocation per `LetRec` node *per query*, and nothing in a freeness query's
//! signature would show it.
//!
//! `is_free_in_value` is the right probe — unlike `is_free` it threads no
//! `visited` set, so nothing but the walk itself can allocate.
//!
//! The counter is `tests/alloc_probe/mod.rs`, which measures per thread and
//! documents why that is the measurement this assertion wants.

mod alloc_probe;

use alloc_probe::allocations;
use cambra::ccl::TypedBinding;
use cambra::ccl::ccl_utils::is_free_in_value;
use cambra::ccl::{Name, TypedExpr};

#[test]
fn a_freeness_query_over_a_letrec_spine_does_not_allocate() {
    // `letrec f0 = 0; ..; fn = n in x`, nested `depth` deep so the walk visits
    // `depth` LetRec nodes in one query.
    const GROUP: usize = 4;
    const DEPTH: usize = 10;

    let mut e = TypedExpr::var("x");
    for _ in 0..DEPTH {
        let bindings: Vec<_> = (0..GROUP)
            .map(|i| {
                (
                    TypedBinding::new_unannotated(format!("f{i}")),
                    TypedExpr::var("x"),
                )
            })
            .collect();
        e = TypedExpr::letrec(bindings, e);
    }

    let probe = Name::raw("x");
    let mut found = false;
    let allocs = allocations(|| found = is_free_in_value(&probe, &e));

    assert!(found, "`x` is free in the spine");
    assert_eq!(
        allocs, 0,
        "the scoped walk allocated {allocs} times for a {DEPTH}-deep letrec spine — \
         a freeness query is consulted once per mapped binder per node during \
         substitution, so the walk must borrow its binder group rather than \
         collecting it into a Vec"
    );
}
