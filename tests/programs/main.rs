//! Integration tests for the demo program gallery.
//!
//! Each subdirectory is one demo program: a `program.cambra` source plus a
//! `mod.rs` containing the program's `#[test]` function(s).  Shared
//! pipeline / HTTP-client glue lives in `common/`.
//!
//! To add a new program: create `tests/programs/<name>/` with a
//! `program.cambra` and a `mod.rs`, then add a `mod <name>;` line below.
//! Cargo collects every `mod.rs`'s `#[test]` items into this one integration
//! test binary (`cargo test --test programs`).
//!
//! For the human-facing gallery, see `docs/demo-programs.md`.

mod common;

mod arithmetic;
mod discount_contract;
mod fanout;
mod filter_and_aggregate;
mod for_accumulator;
mod generator_pipeline;
mod groupby_filtered_rollup;
mod groupby_rollup;
mod http_accumulator;
mod http_counter;
mod http_greeter;
mod inner_join;
mod join_then_groupby;
mod ledger_balance;
mod nonneg_inventory;
mod prefix_lines;
mod reachability;
mod refinement;
mod storefront;
mod streaming_echo;
mod txn_kv;
mod while_counter;
