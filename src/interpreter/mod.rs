//! CCL (Cambra Core Language) Interpreter
//!
//! This module implements the tile-operator-based interpreter for CCL.
//! Execution proceeds via the tile producer/consumer protocol using guards and tilings.

mod binop;
pub mod commit_operator;
pub mod dispatcher;
pub(crate) mod durability;
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
#[cfg(test)]
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
pub use producer_releases::SourceReaderRetirement;
pub use scalar_expr::ScalarProgram;
pub use stdio::*;
pub use subscribe_context::*;
#[cfg(test)]
pub use test_sink::*;
pub use test_source::*;
pub use tiling::*;
pub use types::*;
pub use unary_op::*;

use smol_str::{SmolStr, format_smolstr};
use std::sync::{Arc, Weak};

// ============================================================================
// Consumer Protocol
// ============================================================================

/// Receives decided regions from a producer and passes each toward its dispatcher entries.
/// Regions carry no tile data. See `src/interpreter/design-operators.md`,
/// "The notification contract".
///
/// A planner reads a push's routes by walking the same `notify` with a routing landing
/// ([`dispatcher::Landing::route`]), so planning reads the paths a delivery takes off the code
/// that takes them. What `notify` does only for a delivery ([`dispatcher::Landing::is_delivery`])
/// is not walked. A delivery that reaches a reader the walk of its pipeline did not reach fails
/// the run (`src/interpreter/design-dispatcher.md`, "Running a compiled program").
pub trait Consumer: Send + Sync {
    /// Record an announced region and deliver it toward its dispatcher entries.
    ///
    /// It takes `&self`, so delivery takes no lock on the consumer: state it records sits behind
    /// its own lock or atomic, released before it notifies another consumer.
    fn notify(&self, _region: &Projection, _landing: &mut dispatcher::Landing<'_>) {}
}

/// A shared consumer is one. Each notification passes the re-entry check ([`notify_shared`]).
impl<C: Consumer + ?Sized> Consumer for Arc<C> {
    fn notify(&self, region: &Projection, landing: &mut dispatcher::Landing<'_>) {
        notify_shared(self, region, landing)
    }
}

/// A weak handle notifies its consumer while some owner keeps the consumer alive, and does
/// nothing once it is gone: a subscription that does not keep its subscriber alive
/// (`src/ccl/design/program-evolution.md`, "A subscription lasts as long as its producer").
/// A notification that reaches the consumer passes the re-entry check ([`notify_shared`]).
impl<C: Consumer + ?Sized> Consumer for Weak<C> {
    fn notify(&self, region: &Projection, landing: &mut dispatcher::Landing<'_>) {
        if let Some(consumer) = self.upgrade() {
            notify_shared(&consumer, region, landing);
        }
    }
}

/// A boxed consumer is one, so it can be shared as a [`SharedConsumer`].
impl Consumer for Box<dyn Consumer> {
    fn notify(&self, region: &Projection, landing: &mut dispatcher::Landing<'_>) {
        (**self).notify(region, landing)
    }
}

/// Blanket implementation: Fn() implements Consumer, ignoring the region.
/// This allows closures to be used as consumers.
impl<F: Fn() + Send + Sync> Consumer for F {
    fn notify(&self, _: &Projection, landing: &mut dispatcher::Landing<'_>) {
        if landing.is_delivery() {
            self()
        }
    }
}

/// Generate a tuple field name for the given index.
///
/// Returns `"_0"`, `"_1"`, etc., used throughout the interpreter to represent
/// positional tuple fields as named record fields.
pub fn tuple_field(i: usize) -> SmolStr {
    format_smolstr!("_{i}")
}
