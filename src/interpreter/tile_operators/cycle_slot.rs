//! Late wiring for cyclic operator graphs.

use std::sync::Arc;
use std::sync::OnceLock;

/// Shared construction-time slot for one late-wired operator input.
///
/// Construction fills the slot after the input's owner exists. Graph inspection borrows the
/// operator, and subscriptions clone its shared handle. Clones refer to the same cell, not independent slots.
///
/// The slot carries operators, not values exchanged during evaluation. Tile communication follows
/// `src/interpreter/CLAUDE.md`, "Core invariant: data flows between operators as Tiles, nothing
/// else".
/// `./ci.sh shared_state` recognizes this construction-time cell.
pub struct CycleSlot<T: ?Sized>(
    // shared-state-ok: the single definition of the late-wiring cell. It holds an
    // operator, wired once, not values passed between operators.
    Arc<OnceLock<Arc<T>>>,
);

impl<T: ?Sized> CycleSlot<T> {
    pub fn new() -> Self {
        Self(Arc::new(OnceLock::new()))
    }

    /// Return a filler that can outlive the slot's construction scope. Each returned closure
    /// can be called once. The caller must fill the shared slot only once across all setters;
    /// replacing an occupied slot is rejected.
    pub(crate) fn setter(&self) -> impl FnOnce(Arc<T>) + use<T> {
        let slot = self.0.clone();
        move |op: Arc<T>| {
            assert!(slot.set(op).is_ok(), "a cycle slot is wired once");
        }
    }

    /// Run `f` on the wired operator, if the slot has been filled.
    ///
    /// The callback observes the same immutable input before and after subscription.
    pub(crate) fn peek(&self, f: &mut dyn FnMut(&T)) {
        if let Some(op) = self.0.get().map(Arc::as_ref) {
            f(op);
        }
    }

    /// Clone the wired operator handle.
    ///
    /// `None` means the slot has not been filled.
    /// The subscribing caller is responsible for rejecting either case when an input is required.
    pub fn get(&self) -> Option<Arc<T>> {
        self.0.get().cloned()
    }
}

impl<T: ?Sized> Default for CycleSlot<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: ?Sized> Clone for CycleSlot<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
