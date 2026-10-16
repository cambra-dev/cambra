//! End-to-end pipeline tests: CHL source → CCL lower → infer → compile → eval.
//!
//! All tests run through the full CCL pipeline via [`GlobalContext::compile_program`]:
//!
//! ```text
//! CHL source
//!   → ccl::lower          (CHL AST → CCL Expr)
//!   → ccl::infer          (type inference; annotates Lambda param_ty)
//!   → operator_conversion (CCL Expr → dataflow operators)
//!   → subscribe()         (operator evaluation)
//! ```
//!
//! Unlike the unit tests in each module, these tests validate the composition
//! of all passes together.
//!
//! The tests are split into themed modules. Shared fixtures (`run_pipeline`,
//! `check_tile`, `make_int_list`, …) live in [`helpers`] and are reached from each
//! themed module via `use super::helpers::*;`.

mod helpers;

mod chl_types;
mod comprehensions;
mod conditionals;
mod constants;
mod feeds_cases;
mod generators_udf_poly;
mod joins_aggregates_groupby;
mod key_collections;
mod misc;
mod module_checks;
mod module_nominal_types;
mod module_type_parameters;
mod module_types;
mod modules;
mod mutability;
mod nested_loops;
mod nominal_types;
mod probes;
mod records;
mod runs;
mod scalars_collections;
mod secondary_labels;
mod sources_incremental;
mod sums;
mod traits;
mod transactions;
mod type_aliases;
mod type_annotations;
mod type_parameters;
mod variants;

// Shared with the other suites that catch a panic, so it lives under `tests/support/`.
use crate::panic_message;
