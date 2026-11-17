//! CCL (Cambra Core Language) Interpreter
//!
//! This module implements the tile-operator-based interpreter for CCL.
//! Execution proceeds via the tile producer/consumer protocol using guards and tilings.

mod binop;
pub mod commit_operator;
pub mod dispatcher;
pub mod http_server;
pub mod operator_conversion;
pub mod operator_graph;
mod producer_releases;
mod scalar_expr;
mod scheduler;
pub mod sinks;
mod stdio;
mod stream_buffer;
// Test-only surface: `test_sink()` exists for tests to observe a program through, so it is
// built only where a test is.
#[cfg(any(test, feature = "test-helpers"))]
mod test_sink;
mod test_source;
pub mod tile_operators;
pub mod tiling;
mod types;
mod unary_op;
pub mod value_probe;

pub use binop::*;
pub use http_server::HttpServerDataSource;
pub use scalar_expr::ScalarProgram;
pub use scheduler::*;
pub use stdio::*;
#[cfg(any(test, feature = "test-helpers"))]
pub use test_sink::*;
pub use test_source::*;
pub use tiling::*;
pub use types::*;
pub use unary_op::*;

use smol_str::{SmolStr, format_smolstr};
use std::cell::RefCell;
use std::rc::Rc;

// ============================================================================
// Consumer Protocol
// ============================================================================

/// Receives a signal that a producer's output changed; notifications carry no tile data.
///
/// A notification names the region of the producer's outermost keys that changed. A producer
/// that cannot name it sends [`Projection::Everything`]. Deferred or coalesced notifications
/// need not correspond one-to-one with changed results, and coalescing unites their regions.
/// See `src/interpreter/design-operators.md`, "The notification contract".
pub trait Consumer {
    /// Notify the consumer that the keys `arrived` changed, and that it should pull again if it
    /// reads this producer.
    fn notify(&mut self, arrived: &Projection);

    /// Hand on `region` of the producer's keys at any level, which a pipeline breaker pushed
    /// ([`dispatcher::Pushes`]): a consumer between two breakers restates it as it restates a
    /// notification and passes it on, and the next breaker's [`dispatcher::Entry`] queues it in
    /// `landing` as a work package of the breaker's pipeline. No gate holds a push back, since
    /// every region becomes a package, and a consumer that pulls ignores it, which is the default:
    /// a push wakes no one.
    ///
    /// TODO: this is a second path beside `notify` while runs still pull. Once every run goes
    /// through the dispatcher, `notify`, its gates (`GatedConsumer`) and `WakeupQueue` go, and
    /// this method takes `notify`'s place.
    fn push(&mut self, _region: &Projection, _landing: &mut dispatcher::Landing<'_>) {}

    /// Declare where a push through this consumer goes and how, in `routes`, without pushing: a
    /// consumer that passes a push on walks on to the consumers it passes it to, one that widens
    /// it walks them through [`Routes::widened`](dispatcher::Routes::widened), and the
    /// [`dispatcher::Entry`] of a placed breaker records its pipeline. It mirrors
    /// [`push`](Self::push): a consumer that ignores a push declares nothing, which is the default.
    fn route(&mut self, _routes: &mut dispatcher::Routes) {}
}

/// Blanket implementation: Rc<RefCell<C>> implements Consumer when C does.
// shared-state-ok: this is what makes a shared *notification* handle a consumer;
// a wakeup carries no value, so it is not a dataflow edge.
impl<C: Consumer> Consumer for Rc<RefCell<C>> {
    fn notify(&mut self, arrived: &Projection) {
        self.borrow_mut().notify(arrived)
    }

    fn push(&mut self, region: &Projection, landing: &mut dispatcher::Landing<'_>) {
        self.borrow_mut().push(region, landing)
    }
    fn route(&mut self, routes: &mut dispatcher::Routes) {
        self.borrow_mut().route(routes)
    }
}

/// A boxed consumer is one, so it can be shared behind an `Rc<RefCell<_>>` as a
/// [`SharedConsumer`].
impl Consumer for Box<dyn Consumer> {
    fn notify(&mut self, arrived: &Projection) {
        (**self).notify(arrived)
    }

    fn push(&mut self, region: &Projection, landing: &mut dispatcher::Landing<'_>) {
        (**self).push(region, landing)
    }
    fn route(&mut self, routes: &mut dispatcher::Routes) {
        (**self).route(routes)
    }
}

/// Blanket implementation: FnMut() implements Consumer, ignoring the region.
/// This allows closures to be used as consumers.
impl<F> Consumer for F
where
    F: FnMut(),
{
    fn notify(&mut self, _arrived: &Projection) {
        dispatcher::debug_assert_outside_a_run();
        self()
    }
}

/// Generate a tuple field name for the given index.
///
/// Returns `"_0"`, `"_1"`, etc., used throughout the interpreter to represent
/// positional tuple fields as named record fields.
pub fn tuple_field(i: usize) -> SmolStr {
    format_smolstr!("_{i}")
}
