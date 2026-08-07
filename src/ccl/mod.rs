//! Cambra Core Language (CCL) abstract syntax tree.
//!
//! CCL is a λ-calculus–based intermediate representation. Python source is
//! lowered into CCL, where it is type-checked and optimized, then compiled
//! to the dataflow operator graph for execution.
//!
//! See the design docs in `src/ccl/design/` for the full design rationale.

pub mod ccl_utils;
pub mod channelize;
pub mod content_hash;
pub mod context;
pub mod diff;
pub mod infer;
pub mod inline;
pub mod lambda_elim;
pub mod letrec;
pub mod lineage;
pub mod lower;
pub mod mut_elim;
pub mod names;
pub mod planning;
pub mod provenance;
pub mod scope;
pub mod simplify;
pub mod subst;
pub mod symbolic;
pub mod transact_phase;
pub mod uniquify;

// Core type definitions, split out of this crate-root module. Each submodule
// owns one cluster of the AST/type vocabulary; the re-exports below keep every
// item reachable at the historical `crate::ccl::X` path.
mod aggregate;
mod expr;
mod infer_var;
mod ops;
mod ty;

pub use names::Name;

// `pub` re-exports — every public item of each submodule reappears at
// `crate::ccl::`, the path the rest of the crate (and the interpreter, which
// re-exports `BaseType`) reaches them through.
pub use aggregate::*;
pub use expr::*;
pub use infer_var::*;
pub use ops::*;
pub use ty::*;

// `pub(crate)` items are NOT carried by the globs above (a glob re-exports only
// `pub` items), so they are re-exported explicitly here to preserve their
// `crate::ccl::X` paths:
//   - `arena_enter` / `arena_exit` are used by `infer.rs`;
//   - `fresh_infer_var_id` is used by `solver`;
//   - `eq_refinement_predicate` is used by `subst.rs`.
pub(crate) use infer_var::{arena_enter, arena_exit, fresh_infer_var_id};
pub(crate) use ty::eq_refinement_predicate;

/// Reset all IDs allocated by ccl module counters. Test-only convenience for
/// differential harnesses that re-run lowering + inference and need stable
/// IDs across the runs. Not safe to call concurrently.
#[cfg(any(test, feature = "test-helpers"))]
pub fn reset_all_id_counters() {
    reset_infer_var_counter();
    reset_kind_var_counter();
}

/// Convenience for the [`TypedExprNode::Error`] match arm in passes that run
/// only after the lowering-error check in
/// [`crate::ccl::context::compile_program`] — i.e. anywhere the placeholder
/// shouldn't be observable.
#[macro_export]
macro_rules! unexpected_error_node {
    () => {
        unreachable!("Unexpected <error>")
    };
}
