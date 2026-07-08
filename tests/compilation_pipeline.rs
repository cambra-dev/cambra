//! End-to-end pipeline tests: Python source → CCL lower → infer → compile → eval.
//!
//! All tests run through the full CCL pipeline via [`GlobalContext::compile_program`]:
//!
//! ```text
//! Python source
//!   → ccl::lower    (Python AST → CCL Expr)
//!   → ccl::infer    (type inference; annotates Lambda param_ty)
//!   → compile_ccl   (CCL Expr → dataflow operators)
//!   → subscribe()   (operator evaluation)
//! ```
//!
//! Unlike the unit tests in each module, these tests validate the composition
//! of all passes together.
//!
//! This is a single test binary split into themed modules. Shared fixtures
//! (`run_pipeline`, `check_tile`, `make_int_list`, …) live in [`helpers`] and
//! are reached from each themed module via `use crate::helpers::*;`.

// The crate root of a test binary resolves child modules relative to the
// directory containing this file (`tests/`), not a `compilation_pipeline/`
// subdirectory named after it. `#[path]` points each module at its file under
// `tests/compilation_pipeline/` so the whole split stays in one test binary.
#[path = "compilation_pipeline/helpers.rs"]
mod helpers;

#[path = "compilation_pipeline/comprehensions.rs"]
mod comprehensions;
#[path = "compilation_pipeline/feeds_cases.rs"]
mod feeds_cases;
#[path = "compilation_pipeline/generators_udf_poly.rs"]
mod generators_udf_poly;
#[path = "compilation_pipeline/joins_aggregates_groupby.rs"]
mod joins_aggregates_groupby;
#[path = "compilation_pipeline/misc.rs"]
mod misc;
#[path = "compilation_pipeline/mutability.rs"]
mod mutability;
#[path = "compilation_pipeline/records.rs"]
mod records;
#[path = "compilation_pipeline/scalars_collections.rs"]
mod scalars_collections;
#[path = "compilation_pipeline/sources_incremental.rs"]
mod sources_incremental;
#[path = "compilation_pipeline/transactions.rs"]
mod transactions;
