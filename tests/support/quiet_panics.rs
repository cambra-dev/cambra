//! Mute the panic hook for panics the calling thread expects, and only those.
//!
//! The panic hook is process-wide and the tests in a binary run concurrently, so a test
//! that swaps the hook out and restores it afterwards mutes every other test's panic
//! messages for as long as it holds it — and two tests doing that interleave their
//! save/restore pairs, which can leave a muting hook installed for the rest of the run.
//! Instead the hook is wrapped once, for good, and consults a per-thread flag: a panic
//! inside [`quietly`] on this thread is silent, every other panic prints as before.

use std::cell::Cell;
use std::sync::Once;

thread_local! {
    static QUIET: Cell<bool> = const { Cell::new(false) };
}

static INSTALL: Once = Once::new();

/// Run `body` with this thread's panics kept off stderr.
pub fn quietly<T>(body: impl FnOnce() -> T) -> T {
    INSTALL.call_once(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if !QUIET.get() {
                previous(info);
            }
        }));
    });
    // Restored on unwind too, so the thread's later panics print. A panic that escapes
    // `body` is itself silent: the hook ran inside `body`, before the unwind.
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            QUIET.set(self.0);
        }
    }
    let _restore = Restore(QUIET.replace(true));
    body()
}
