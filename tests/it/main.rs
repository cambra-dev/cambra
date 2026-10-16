//! Every integration test that can share a process, as one test binary.
//!
//! Each `tests/*.rs` file used to be its own binary, and every binary statically links
//! the whole library: ~30 copies of it on disk, and ~30 links after any `src/` edit. The
//! files keep their places and become modules here. The ones that cannot share a
//! process stay separate `[[test]]` targets in `Cargo.toml`: the two that install
//! `alloc_probe`'s counting `#[global_allocator]` (an allocator is per-process), and
//! `differential_oracle`, which needs the Lean toolchain.

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

#[path = "../chl_parser_roundtrip.rs"]
mod chl_parser_roundtrip;
#[path = "../cli_driver_convergence.rs"]
mod cli_driver_convergence;
#[path = "../compilation_pipeline.rs"]
mod compilation_pipeline;
#[path = "../constraint_order_fuzz.rs"]
mod constraint_order_fuzz;
#[path = "../differential_interp.rs"]
mod differential_interp;
#[path = "../editor_grammars.rs"]
mod editor_grammars;
#[path = "../generated_pairs.rs"]
mod generated_pairs;
#[path = "../hot_reload.rs"]
mod hot_reload;
#[path = "../http_server.rs"]
mod http_server;
#[path = "../inference_variants.rs"]
mod inference_variants;
#[path = "../inspector_goldens.rs"]
mod inspector_goldens;
#[path = "../loop_body_binding_cost.rs"]
mod loop_body_binding_cost;
#[path = "../predicate_sharing.rs"]
mod predicate_sharing;
#[path = "../predicate_sharing_review.rs"]
mod predicate_sharing_review;
#[path = "../programs/main.rs"]
mod programs;
#[path = "../reserve_port.rs"]
mod reserve_port;
#[path = "../subtype_transitivity_fuzz.rs"]
mod subtype_transitivity_fuzz;
#[path = "../test_sink.rs"]
mod test_sink;
#[path = "../type_check.rs"]
mod type_check;
