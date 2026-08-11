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
//! # The window is per-thread, and has to be
//!
//! "Allocations during a window of wall-clock time" is not the property under
//! test; "allocations *this thread* made during the walk" is. A process-global
//! counter conflates them, and the difference is not hypothetical: libtest runs
//! each test on a spawned thread and its main thread keeps working right
//! afterwards, doing exactly four one-time allocations before it blocks —
//! `running_tests.insert` (first insert into an empty `HashMap`),
//! `timeout_queue.push_back` (first push into an empty `VecDeque`), and two
//! inside the first blocking `rx.recv_timeout`. If the spawned test thread wins
//! the race to the walk, a global counter charges all four to the walk. That is
//! a real observed failure ("the scoped walk allocated 4 times") — rare, because
//! the main thread normally finishes those four before a freshly spawned thread
//! is scheduled at all, but reachable whenever the main thread is preempted
//! right after the spawn, which is what a loaded CI runner does.
//!
//! Counting per-thread costs nothing in strength. The walk is a plain recursive
//! fold that spawns nothing, so every allocation it could make is made by the
//! thread that armed the window; the counter still sees all of them and now
//! sees only them.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

use cambra::ccl::TypedBinding;
use cambra::ccl::ccl_utils::is_free_in_value;
use cambra::ccl::{Name, TypedExpr};

thread_local! {
    /// Allocations this thread has made since it armed its window.
    static ALLOCS: Cell<usize> = const { Cell::new(0) };
    /// Is this thread's measurement window open?
    static COUNTING: Cell<bool> = const { Cell::new(false) };
}

struct Counting;

impl Counting {
    /// Charge one allocation to the current thread, if its window is open.
    ///
    /// Both thread-locals are `const`-initialized and hold a type with no
    /// destructor, so the access is a direct TLS read: no lazy initializer, no
    /// destructor registration, and so no allocation. That matters here and not
    /// just for accuracy — an allocating counter inside `GlobalAlloc` would
    /// recurse.
    fn charge() {
        if COUNTING.get() {
            ALLOCS.set(ALLOCS.get() + 1);
        }
    }
}

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        Self::charge();
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        Self::charge();
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

#[global_allocator]
static A: Counting = Counting;

/// Allocations the calling thread performs while running `body`. Other threads'
/// allocations are not counted — see the module docs for why that is the
/// measurement the assertions want.
fn allocations(body: impl FnOnce()) -> usize {
    ALLOCS.set(0);
    COUNTING.set(true);
    body();
    COUNTING.set(false);
    ALLOCS.get()
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

/// The probe has to be able to *see* an allocation, or the assertion above
/// passes for the wrong reason. A zero-allocation claim measured by a counter
/// that counts nothing is vacuous, and nothing else in this file would notice —
/// so pay one allocation on the measuring thread and check it lands.
#[test]
fn the_probe_counts_allocations_made_by_the_measuring_thread() {
    let allocs = allocations(|| {
        let v: Vec<u8> = Vec::with_capacity(64);
        std::hint::black_box(&v);
    });
    assert_eq!(
        allocs, 1,
        "one `Vec::with_capacity` is one allocation; the probe saw {allocs}"
    );
}
