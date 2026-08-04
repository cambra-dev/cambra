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

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

use cambra::ccl::TypedBinding;
use cambra::ccl::ccl_utils::is_free_in_value;
use cambra::ccl::{Name, TypedExpr};

static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static COUNTING: AtomicUsize = AtomicUsize::new(0);

struct Counting;

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if COUNTING.load(Ordering::Relaxed) != 0 {
            ALLOCS.fetch_add(1, Ordering::Relaxed);
        }
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if COUNTING.load(Ordering::Relaxed) != 0 {
            ALLOCS.fetch_add(1, Ordering::Relaxed);
        }
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

#[global_allocator]
static A: Counting = Counting;

/// Allocations performed while running `body`. Single-threaded by construction —
/// this file holds one test so no other thread is inside the window.
fn allocations(body: impl FnOnce()) -> usize {
    ALLOCS.store(0, Ordering::Relaxed);
    COUNTING.store(1, Ordering::Relaxed);
    body();
    COUNTING.store(0, Ordering::Relaxed);
    ALLOCS.load(Ordering::Relaxed)
}

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
