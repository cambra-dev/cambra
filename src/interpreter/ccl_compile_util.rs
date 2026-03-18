//! Shared types and utilities for CCL → operator compilation.
//!
//! This module is a thin shared layer used by both
//! [`crate::interpreter::compile_ccl`] and
//! [`crate::interpreter::compile_tile_operators`] to avoid circular imports.

use crate::ccl::Type;

/// Errors that can occur during CCL → operator-graph compilation.
#[derive(Debug, Clone, PartialEq)]
pub enum CompileError {
    /// The CCL node or construct is not yet supported by this compilation pass.
    Unsupported(String),
    /// A type-level inconsistency was detected.
    TypeError(String),
}

/// Assert that `ty` is a fully-resolved concrete type, returning
/// [`CompileError::TypeError`] if not.
///
/// [`Type::Hole`] and [`Type::Infer`] are both invalid at compilation time —
/// their presence means either the lowering placeholder was never replaced by
/// inference, or inference left an unresolved variable. Either case is a
/// precondition violation: compilation requires a fully-annotated,
/// error-free expression tree.
///
/// `context` is a short human-readable description of the binding site (e.g.
/// `"Lambda parameter 'x'"`) used in the error message.
pub fn validate_type(ty: &Type, context: &str) -> Result<(), CompileError> {
    match ty {
        Type::Hole => Err(CompileError::TypeError(format!(
            "{context}: type is a lowering placeholder (Hole); \
             ccl::infer must run before compilation"
        ))),
        Type::Infer(_) => Err(CompileError::TypeError(format!(
            "{context}: type is an unresolved inference variable; \
             ccl::infer/resolve must complete before compilation"
        ))),
        _ => Ok(()),
    }
}
