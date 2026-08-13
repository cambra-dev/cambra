//! A per-thread allocation counter for integration tests, plus its own tests.
//!
//! Include it with `mod alloc_probe;` and measure with
//! [`allocations`](alloc_probe::allocations). Including the module installs a
//! `#[global_allocator]` for that test binary — which is why this is a module rather
//! than a library: an allocator is per-binary, so each test binary needs its own
//! instance of it, but they can share the code.
//!
//! # The window is per-thread, and has to be
//!
//! "Allocations during a window of wall-clock time" is not a property worth
//! asserting; "allocations *this thread* made while running `body`" is. A
//! process-global counter conflates them, and the difference is not hypothetical:
//! libtest runs each test on a spawned thread and its main thread keeps working right
//! afterwards, doing exactly four one-time allocations before it blocks —
//! `running_tests.insert` (first insert into an empty `HashMap`),
//! `timeout_queue.push_back` (first push into an empty `VecDeque`), and two inside the
//! first blocking `rx.recv_timeout`. If the spawned test thread wins the race to the
//! measured code, a global counter charges all four to it. That is a real observed
//! failure ("the scoped walk allocated 4 times") — rare, because the main thread
//! normally finishes those four before a freshly spawned thread is scheduled at all,
//! but reachable whenever the main thread is preempted right after the spawn, which is
//! what a loaded CI runner does.
//!
//! Counting per-thread costs nothing in strength for code that spawns nothing: every
//! allocation such code could make is made by the thread that armed the window, so the
//! counter still sees all of them and now sees only them.
//!
//! # The probe tests itself
//!
//! [`the_probe_counts_allocations_made_by_the_measuring_thread`] and
//! [`another_threads_allocations_are_not_charged_to_this_window`] live here rather
//! than beside any one measurement, so a binary that adopts the probe adopts the
//! evidence that it works. A zero-allocation claim measured by a counter that counts
//! nothing would pass for the wrong reason, and no assertion in the *using* file would
//! notice.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

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

/// An open measurement window on the current thread, closed when dropped.
///
/// The guard exists so that no path can leave a window open. A `body` that
/// panics — a failing assertion inside one of these tests is exactly that —
/// would otherwise leave `COUNTING` set, and every later window on the same
/// thread would then be measuring from an armed counter it did not arm.
struct Window;

impl Window {
    /// Zero this thread's counter and arm it.
    fn open() -> Self {
        ALLOCS.set(0);
        COUNTING.set(true);
        Window
    }
}

impl Drop for Window {
    fn drop(&mut self) {
        COUNTING.set(false);
    }
}

/// Allocations the calling thread performs while running `body`. Other threads'
/// allocations are not counted — see the module docs for why that is the
/// measurement the assertions want.
pub fn allocations(body: impl FnOnce()) -> usize {
    let _window = Window::open();
    body();
    ALLOCS.get()
}

/// The probe has to be able to *see* an allocation, or a zero-allocation claim
/// measured with it passes for the wrong reason — so pay one allocation on the
/// measuring thread and check it lands.
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

/// The other half of that: a window must see *only* its own thread. This is the
/// property the whole probe rests on, and the one a global counter silently
/// loses — swap the counters back for process-global ones and this reports 1002
/// rather than 0, the worker's thousand plus two the test harness happened to
/// make, while every other assertion stays green.
///
/// The window has to bracket the worker's allocating loop and nothing else.
/// Spawning heap-allocates the closure and the result slot *on the spawning
/// thread*, and joining does bookkeeping of its own, so a window drawn around
/// `thread::scope` counts those — correctly, as its own — and drowns the signal.
/// Hence the handshake: two `AtomicBool`s, which spin without allocating.
#[test]
fn another_threads_allocations_are_not_charged_to_this_window() {
    use std::sync::atomic::{AtomicBool, Ordering};

    const N: usize = 1000;

    let go = AtomicBool::new(false);
    let done = AtomicBool::new(false);

    std::thread::scope(|s| {
        s.spawn(|| {
            while !go.load(Ordering::Acquire) {
                std::hint::spin_loop();
            }
            for _ in 0..N {
                std::hint::black_box(Vec::<u8>::with_capacity(64));
            }
            done.store(true, Ordering::Release);
        });

        let allocs = allocations(|| {
            go.store(true, Ordering::Release);
            while !done.load(Ordering::Acquire) {
                std::hint::spin_loop();
            }
        });

        assert_eq!(
            allocs, 0,
            "another thread's allocations were charged to this window: {allocs}"
        );
    });
}
