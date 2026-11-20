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
use std::sync::Arc;

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
/// is not walked: a package it queues, or a complete region it records, fails the run unless a
/// walk took the same path (`src/interpreter/design-dispatcher.md`, "Running a compiled
/// program").
pub trait Consumer: Send + Sync {
    /// Record an announced region and deliver it toward its dispatcher entries.
    ///
    /// It takes `&self`, so delivery takes no lock on the consumer: state it records sits behind
    /// its own lock or atomic, released before it notifies another consumer.
    ///
    /// The region is a guard of the notifying producer's output in the spelling no tiling is
    /// needed for ([`Projection::region_guard`]): a guard of keys, a record guard of fields, the
    /// domain guard admitting every key for everything.
    fn notify(&self, _region: &TileGuard, _landing: &mut dispatcher::Landing<'_>) {}

    /// [`notify`](Self::notify) of the region a projection names.
    fn notify_view(&self, region: &Projection, landing: &mut dispatcher::Landing<'_>) {
        self.notify(&region.region_guard(), landing)
    }
}

/// A shared consumer is one. Each notification passes the re-entry check ([`notify_shared`]).
impl<C: Consumer + ?Sized> Consumer for Arc<C> {
    fn notify(&self, region: &TileGuard, landing: &mut dispatcher::Landing<'_>) {
        notify_shared(self, region, landing)
    }
}

/// A boxed consumer is one, so it can be shared as a [`SharedConsumer`].
impl Consumer for Box<dyn Consumer> {
    fn notify(&self, region: &TileGuard, landing: &mut dispatcher::Landing<'_>) {
        (**self).notify(region, landing)
    }
}

/// Blanket implementation: Fn() implements Consumer, ignoring the region.
/// This allows closures to be used as consumers.
impl<F: Fn() + Send + Sync> Consumer for F {
    fn notify(&self, _: &TileGuard, landing: &mut dispatcher::Landing<'_>) {
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
