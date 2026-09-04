#![warn(unused_qualifications)]

pub mod ccl;
pub mod chl_parser;
pub mod embed;
// The terminal host reads stdin on a background thread; a target with no
// threads has no such host.
#[cfg(not(target_arch = "wasm32"))]
pub mod host_driver;
pub mod inspector_model;
// The inspector's transport: an HTTP server and a websocket. The payload and
// the frames it serves are `inspector_model`, which every target builds.
#[cfg(not(target_arch = "wasm32"))]
pub mod inspector_server;
pub mod interpreter;
pub mod pretty_graph;
pub mod pretty_tree;
pub mod util;
#[cfg(target_arch = "wasm32")]
pub mod wasm_api;
