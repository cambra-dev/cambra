#![warn(unused_qualifications)]

pub mod ccl;
pub mod cli;
// The parser is its own crate; re-exported so `cambra::chl_parser` and
// `crate::chl_parser` name it.
pub use chl_parser;
pub mod control_port;
pub mod inspector_model;
pub mod inspector_server;
pub mod interpreter;
pub mod live_program;
pub mod pretty_graph;
pub mod pretty_tree;
pub mod scalar_ops;
pub mod util;
pub mod view;

// The integration tests are part of this test build, not a crate linking the library
// (`tests/it/mod.rs`). They name the library as a consumer does, `cambra::`.
#[cfg(test)]
extern crate self as cambra;
#[cfg(test)]
#[path = "../tests/it/mod.rs"]
mod it;
