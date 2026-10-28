//! Late wiring for cyclic operator graphs.

use std::cell::RefCell;
use std::rc::Rc;

/// Shared construction-time slot for one late-wired operator input.
///
/// Construction fills the slot after the input's owner exists. Graph inspection borrows the
/// operator, and subscription takes it. Clones refer to the same cell, not independent slots.
///
/// The slot carries operators, not values exchanged during evaluation. Tile communication follows
/// `src/interpreter/CLAUDE.md`, "Core invariant: data flows between operators as Tiles, nothing
/// else".
/// `./ci.sh shared_state` recognizes this construction-time cell.
pub struct CycleSlot<T: ?Sized>(
    // shared-state-ok: the single definition of the late-wiring cell. It holds an
    // operator, wired once, not values passed between operators.
    Rc<RefCell<Option<Box<T>>>>,
);

impl<T: ?Sized> CycleSlot<T> {
    pub fn new() -> Self {
        Self(Rc::new(RefCell::new(None)))
    }

    /// Return a filler that can outlive the slot's construction scope. Each returned closure
    /// can be called once. The caller must fill the shared slot only once across all setters;
    /// a debug assertion rejects replacing an occupied slot.
    pub(crate) fn setter(&self) -> impl FnOnce(Box<T>) + use<T> {
        let slot = self.0.clone();
        move |op: Box<T>| {
            debug_assert!(
                slot.borrow().is_none(),
                "a cycle slot is wired once; refilling it would drop a live input"
            );
            *slot.borrow_mut() = Some(op);
        }
    }

    /// Run `f` on the wired operator, if the slot has been filled.
    ///
    /// The borrow lasts for the callback. Graph inspection calls this before subscription
    /// takes the input; after a take, the callback is not invoked unless the slot is refilled.
    pub(crate) fn peek(&self, f: &mut dyn FnMut(&T)) {
        if let Some(op) = self.0.borrow().as_deref() {
            f(op);
        }
    }

    /// Take the wired operator, leaving the slot empty.
    ///
    /// `None` means either the slot was never filled or its input was already taken.
    /// The subscribing caller is responsible for rejecting either case when an input is required.
    pub fn take(&self) -> Option<Box<T>> {
        self.0.borrow_mut().take()
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
