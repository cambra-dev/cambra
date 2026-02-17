//! CCL (Cambra Core Language) Interpreter
//!
//! This module implements the dataflow-based interpreter for CCL.
//! Execution proceeds via a producer/consumer protocol using guards and extents.

mod binop;
mod lambda;
mod literal;
mod types;
mod var;

pub use binop::*;
pub use lambda::*;
pub use literal::*;
pub use types::*;
pub use var::*;

use std::cell::RefCell;
use std::fmt::Debug;
use std::rc::Rc;

// ============================================================================
// Producer/Consumer Protocol
// ============================================================================

/// A Consumer receives notifications from a producer.
/// Notifications are either progress updates (yield guards) or data availability signals.
pub trait Consumer {
    /// Notify the consumer of progress or data availability.
    fn notify(&mut self, notification: Notification);
}

/// Blanket implementation: Rc<RefCell<C>> implements Consumer when C does.
impl<C: Consumer> Consumer for Rc<RefCell<C>> {
    fn notify(&mut self, notification: Notification) {
        self.borrow_mut().notify(notification)
    }
}

/// Blanket implementation: FnMut(Notification) implements Consumer.
/// This allows closures to be used as consumers.
impl<F> Consumer for F
where
    F: FnMut(Notification),
{
    fn notify(&mut self, notification: Notification) {
        self(notification)
    }
}

/// A Producer provides data and handles release requests.
/// The producer is created by an operator's `subscribe` method and allows
/// the consumer to retrieve data and release regions.
pub trait Producer: Debug {
    /// Returns a `GetResult` containing the columnar data and the yield guard,
    /// guaranteeing they are synchronized.
    fn get(&mut self) -> GetResult;

    /// Release interest in a region.
    /// The `obsolete_guard` specifies a sub-region of the subscription that
    /// is no longer needed. Returns an expanded obsolete guard that may be
    /// larger if the producer has additional obsolescence information (e.g.,
    /// from variables with their own obsolete guards).
    fn release(&mut self, obsolete_guard: Guard) -> Guard;
}

/// Blanket implementation: Rc<RefCell<P>> implements Producer when P does.
impl<P: Producer> Producer for Rc<RefCell<P>> {
    fn get(&mut self) -> GetResult {
        self.borrow_mut().get()
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        self.borrow_mut().release(obsolete_guard)
    }
}

/// A dataflow operator that can be subscribed to.
/// Operators implement this trait to provide a subscription interface.
/// The `subscribe` method takes an intent guard (specifying what region the
/// consumer is interested in) and a consumer, and returns a producer that
/// allows the consumer to get data and release regions.
pub trait Operator: Debug {
    /// Get the extent (type) of this operator.
    fn extent(&self) -> &Extent;

    /// Subscribe to this operator with an intent guard and consumer.
    /// Returns a producer that allows the consumer to get data and release regions.
    ///
    /// # Arguments
    /// * `intent_guard` - The region of the operator's extent that the consumer
    ///   is interested in
    /// * `consumer` - The consumer that will receive notifications when data is ready
    /// * `var_scope` - The variable scope for looking up variables, wrapped in Rc
    ///   to match the internal parent representation and allow cheap sharing
    ///   (e.g., Lambda stores the scope for child scope construction).
    ///
    /// # Returns
    /// A producer that provides access to the data and allows releasing regions
    fn subscribe(
        &mut self,
        intent_guard: Guard,
        consumer: Box<dyn Consumer>, // TODO: Should we make this a trait bound so we don't assume a Box pointer type?
        var_scope: Option<Rc<VarScope>>,
    ) -> Box<dyn Producer>;
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    /// A test consumer that stores notifications in shared state.
    /// The notifications Vec is kept by the test, allowing access to notifications
    /// even after the consumer is moved into subscribe.
    /// Uses Rc<RefCell<>> for single-threaded, lock-free shared state.
    pub struct TestConsumer {
        notifications: Rc<RefCell<Vec<Notification>>>,
    }

    impl TestConsumer {
        /// Create a new TestConsumer and return both the consumer and the shared notifications Vec.
        /// The consumer can be moved into subscribe, while the notifications Vec allows
        /// reading notifications from outside.
        pub fn new() -> (Self, Rc<RefCell<Vec<Notification>>>) {
            let notifications = Rc::new(RefCell::new(Vec::new()));
            (
                TestConsumer {
                    notifications: notifications.clone(),
                },
                notifications,
            )
        }
    }

    impl Consumer for TestConsumer {
        fn notify(&mut self, notification: Notification) {
            self.notifications.borrow_mut().push(notification);
        }
    }
}
