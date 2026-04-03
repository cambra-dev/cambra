//! CCL (Cambra Core Language) Interpreter
//!
//! This module implements the tile-operator-based interpreter for CCL.
//! Execution proceeds via the tile producer/consumer protocol using guards and tilings.

mod binop;
pub mod ccl_compile_util;
pub mod compile_tile_operators;
pub mod operator_conversion;
mod scheduler;
mod stdio;
mod test_source;
pub mod tile_operators;
pub mod tiling;
mod types;
mod unary_op;

pub use binop::*;
pub use scheduler::*;
pub use stdio::*;
pub use test_source::*;
pub use tiling::*;
pub use types::*;
pub use unary_op::*;

use std::cell::RefCell;
use std::rc::Rc;

// ============================================================================
// Consumer Protocol
// ============================================================================

/// A Consumer receives notifications from a producer.
/// A notification always means new data is available; the consumer should call `get()`.
pub trait Consumer {
    /// Notify the consumer that new data is available.
    fn notify(&mut self);
}

/// Blanket implementation: Rc<RefCell<C>> implements Consumer when C does.
impl<C: Consumer> Consumer for Rc<RefCell<C>> {
    fn notify(&mut self) {
        self.borrow_mut().notify()
    }
}

/// Blanket implementation: FnMut() implements Consumer.
/// This allows closures to be used as consumers.
impl<F> Consumer for F
where
    F: FnMut(),
{
    fn notify(&mut self) {
        self()
    }
}

/// Generate a tuple field name for the given index.
///
/// Returns `"_0"`, `"_1"`, etc., used throughout the interpreter to represent
/// positional tuple fields as named record fields.
pub fn tuple_field(i: usize) -> String {
    format!("_{i}")
}
