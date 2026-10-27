//! Every integration test that can share a process, as one test binary.
//!
//! Every test binary statically links the whole library, so each one costs a copy of it
//! on disk and a link after any `src/` edit; the tests that can share a process share
//! this binary, each file under `tests/it/` a module of it. The tests that cannot share a
//! process are top-level `tests/*.rs` files, each its own binary and each declared as a
//! `[[test]]` in `Cargo.toml` with the reason; [`test_layout`] fails on a top-level file
//! that is not, and on a module file no `mod` line names.

// Support modules the test modules share, mounted once: a file loaded as two
// modules of one crate is two copies of it (`clippy::duplicate_mod`).
#[path = "../support/differential.rs"]
mod differential;
#[path = "../support/panic_message.rs"]
mod panic_message;
#[path = "../support/quiet_panics.rs"]
mod quiet_panics;
#[path = "../support/serving.rs"]
mod serving;
#[path = "../type_gen/mod.rs"]
mod type_gen;

mod binding_nodes;
mod chl_parser_roundtrip;
mod cli_driver_convergence;
mod compilation_pipeline;
mod constraint_order_fuzz;
mod differential_interp;
mod editor_grammars;
mod generated_pairs;
mod hot_reload;
mod http_server;
mod inference_variants;
mod inspector_goldens;
mod live_keys_readers;
mod loop_body_binding_cost;
mod predicate_sharing;
mod predicate_sharing_review;
// The gallery stays at `tests/programs/`: its `program.cambra` paths are read at run time
// and recorded in the inspector's golden fixtures. Its root is `mod.rs` rather than
// `main.rs`, which autodiscovery would build as a binary of its own.
#[path = "../programs/mod.rs"]
mod programs;
mod reserve_port;
mod subst_binders;
mod subtype_transitivity_fuzz;
mod test_layout;
mod test_sink;
mod type_check;
