//! Coverage for [`reserve_test_port`], the allocator the http tests' anti-flake
//! guarantee rests on.
//!
//! Nothing else exercises the allocator directly: the http tests consume a port
//! and would only report a regression as the same intermittent `EADDRINUSE` the
//! allocator exists to remove — a failure that is expensive to diagnose and easy
//! to write off as environmental.  These two tests turn that into a deterministic
//! red.

use std::{collections::HashSet, net::TcpListener, thread};

use cambra::interpreter::http_server::reserve_test_port;

/// The reservation must be exclusive *within* the process too: `cargo test` runs
/// a binary's tests as threads, so two concurrent calls handed the same port
/// would reproduce exactly the `EADDRINUSE` this allocator prevents.  It holds
/// because the lock is on the open file description (`flock`) rather than the
/// process (`fcntl(F_SETLK)`, under which the second lock in a process
/// *succeeds*) — a platform or std change there would silently restore the
/// flakiness, and this is what catches it.
#[test]
fn reserve_test_port_is_exclusive_across_threads() {
    let ports: Vec<u16> = thread::scope(|s| {
        let handles: Vec<_> = (0..16).map(|_| s.spawn(reserve_test_port)).collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });

    let unique: HashSet<u16> = ports.iter().copied().collect();
    assert_eq!(
        unique.len(),
        ports.len(),
        "duplicate ports handed out: {ports:?}"
    );
    assert!(
        ports.iter().all(|p| (20_000..30_000).contains(p)),
        "ports outside the reserved band: {ports:?}"
    );
}

/// A reserved port must still be bindable by the caller — the bind probe's
/// listener has to be closed, not leaked into the static that holds the locks —
/// and bindable on the same wildcard address `SharedHttpServer::new` uses.
#[test]
fn reserved_port_is_bindable_by_the_caller() {
    let port = reserve_test_port();
    TcpListener::bind(("0.0.0.0", port)).expect("reserved port must be bindable by its reserver");
}
