//! CCL (Cambra Core Language) Interpreter
//!
//! This module implements the tile-operator-based interpreter for CCL.
//! Execution proceeds via the tile producer/consumer protocol using guards and tilings.

mod binop;
pub mod commit_operator;
pub mod http_server;
pub mod operator_conversion;
pub mod operator_graph;
mod producer_releases;
mod scalar_expr;
mod scheduler;
pub mod sinks;
mod stdio;
mod stream_buffer;
mod sync;
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
#[cfg(test)]
pub(crate) use sync::SyncCell;
pub use sync::{LockNow, ReadNow};
#[cfg(any(test, feature = "test-helpers"))]
pub use test_sink::*;
pub use test_source::*;
pub use tiling::*;
pub use types::*;
pub use unary_op::*;

use smol_str::{SmolStr, format_smolstr};
use std::sync::Arc;
use std::sync::Mutex;

// ============================================================================
// Consumer Protocol
// ============================================================================

/// Receives a signal that a producer's output changed; notifications carry no tile data.
///
/// A notification names the region of the producer's outermost keys that changed. A producer
/// that cannot name it sends [`Projection::Everything`]. Deferred or coalesced notifications
/// need not correspond one-to-one with changed results, and coalescing unites their regions.
/// See `src/interpreter/design-operators.md`, "The notification contract".
pub trait Consumer: Send {
    /// Notify the consumer that the keys `arrived` changed, and that it should pull again if it
    /// reads this producer.
    fn notify(&mut self, arrived: &Projection);
}

/// Blanket implementation: Arc<Mutex<C>> implements Consumer when C does.
// shared-state-ok: this is what makes a shared *notification* handle a consumer;
// a wakeup carries no value, so it is not a dataflow edge.
impl<C: Consumer> Consumer for Arc<Mutex<C>> {
    fn notify(&mut self, arrived: &Projection) {
        self.lock_now().notify(arrived)
    }
}

/// Blanket implementation: FnMut() implements Consumer, ignoring the region.
/// This allows closures to be used as consumers.
impl<F> Consumer for F
where
    F: FnMut() + Send,
{
    fn notify(&mut self, _arrived: &Projection) {
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
