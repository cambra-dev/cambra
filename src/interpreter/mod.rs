//! CCL (Cambra Core Language) Interpreter
//!
//! This module implements the tile-operator-based interpreter for CCL.
//! Execution proceeds via the tile producer/consumer protocol using guards and tilings.

mod binop;
pub mod commit_operator;
pub mod dispatcher;
pub mod http_server;
mod notifications;
pub mod operator_conversion;
pub mod operator_graph;
mod producer_releases;
mod scalar_expr;
pub mod sinks;
mod stdio;
mod stream_buffer;
mod subscribe_context;
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
pub use notifications::*;
pub use scalar_expr::ScalarProgram;
pub use stdio::*;
pub use subscribe_context::*;
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

/// Receives decided regions from a producer and declares their dispatcher routes.
/// Regions carry no tile data. See `src/interpreter/design-operators.md`,
/// "The notification contract".
pub trait Consumer {
    /// Invalidate cached reads outside a dispatcher run.
    /// The next explicit producer read observes `arrived` again. This callback executes no
    /// program; direct producer protocol tests and subscription setup use it.
    fn invalidate(&mut self, arrived: &Projection);

    /// Deliver a decided region of the producer's keys at any level.
    /// Intermediate consumers restate it, and a pipeline entry queues the corresponding work in
    /// `landing`. Every delivered region is a work package, so invalidation gates never coalesce it.
    fn notify(&mut self, _region: &Projection, _landing: &mut dispatcher::Landing<'_>) {}

    /// Declare the routes a notification follows without delivering one.
    /// A consumer that widens a region uses [`Routes::widened`](dispatcher::Routes::widened).
    /// A placed breaker's [`dispatcher::Entry`] records its pipeline.
    fn route(&mut self, _routes: &mut dispatcher::Routes) {}
}

/// Blanket implementation: Rc<RefCell<C>> implements Consumer when C does.
// shared-state-ok: this is what makes a shared *notification* handle a consumer;
// a wakeup carries no value, so it is not a dataflow edge.
impl<C: Consumer> Consumer for Rc<RefCell<C>> {
    fn invalidate(&mut self, arrived: &Projection) {
        self.borrow_mut().invalidate(arrived)
    }

    fn notify(&mut self, region: &Projection, landing: &mut dispatcher::Landing<'_>) {
        self.borrow_mut().notify(region, landing)
    }
    fn route(&mut self, routes: &mut dispatcher::Routes) {
        self.borrow_mut().route(routes)
    }
}

/// A boxed consumer is one, so it can be shared behind an `Rc<RefCell<_>>` as a
/// [`SharedConsumer`].
impl Consumer for Box<dyn Consumer> {
    fn invalidate(&mut self, arrived: &Projection) {
        (**self).invalidate(arrived)
    }

    fn notify(&mut self, region: &Projection, landing: &mut dispatcher::Landing<'_>) {
        (**self).notify(region, landing)
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
    fn invalidate(&mut self, _arrived: &Projection) {
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
