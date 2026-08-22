//! Late wiring for cyclic operator graphs.

use std::cell::RefCell;
use std::rc::Rc;

/// An operator input filled once construction is done, so a cycle can be built.
///
/// A cyclic graph cannot be assembled bottom-up: the store must exist before the
/// `FanOut` that wraps it, which must exist before the drive that reads it, which
/// must exist before the body — and the body is the store's own input. One edge
/// has to be wired last. `CycleSlot` is that edge.
///
/// **It holds an operator, never a value**, which is what separates it from a back
/// channel: the graph stays static and complete, and data still crosses it at `get`
/// time as a tile (see `src/interpreter/CLAUDE.md`, "Core invariant: data flows
/// between operators as Tiles, nothing else"). Reach for this rather than a
/// hand-rolled `Rc<RefCell<…>>` — it is the shape `./ci.sh shared_state` recognises
/// as legitimate, so a hand-rolled one has to justify itself instead.
pub struct CycleSlot<T: ?Sized>(
    // shared-state-ok: the single definition of the late-wiring cell. It holds an
    // operator, wired once, not values passed between operators.
    Rc<RefCell<Option<Box<T>>>>,
);

impl<T: ?Sized> CycleSlot<T> {
    pub fn new() -> Self {
        Self(Rc::new(RefCell::new(None)))
    }

    /// A one-shot filler for this slot, detached from the operator that owns it
    /// so the caller can build the rest of the cycle first. `FnOnce` because a
    /// slot is wired exactly once: a second fill would silently replace a live
    /// input.
    pub fn setter(&self) -> impl FnOnce(Box<T>) + use<T> {
        let slot = self.0.clone();
        move |op| {
            debug_assert!(
                slot.borrow().is_none(),
                "a cycle slot is wired once; refilling it would drop a live input"
            );
            *slot.borrow_mut() = Some(op);
        }
    }

    /// Take the wired operator, leaving the slot empty.
    ///
    /// `None` means the slot holds nothing *now*, which covers two construction
    /// bugs the caller should name in its own panic: the cycle was never closed
    /// (`setter` was not called), or it is being subscribed a second time (the
    /// first `take` emptied it). A slot holds an operator, and an operator is
    /// subscribed once.
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
