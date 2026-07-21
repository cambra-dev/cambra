//! Web inspector: serves a live dashboard of the interpreter's runtime state.
//!
//! DEPRECATED. The `cambra-inspector` crate is the intended replacement, but
//! cannot fully supplant this yet: it models only the static IR passes
//! (pre-inference / post-inference / post-desugar) and has no operator/dataflow
//! graph pane and no live per-tick view. Once the operator graph is instrumented
//! (the `NodeId → OperatorId` lineage edge) and a live/tick layer lands, this
//! module — and the `InspectNode::to_json` wire it depends on — can be removed.

use std::sync::{Arc, Mutex};
use std::thread;

use log::info;

use crate::interpreter::tile_operators::TileProducer;
use crate::pretty_graph::VizOptions;

/// Web inspector that serves a live HTML dashboard on a background thread.
///
/// Pre-rendered static trees (AST and operator graph) are passed at construction
/// and moved into the HTTP server thread; only the dynamic snapshot is updated
/// per-tick.
pub struct WebInspector {
    snapshot: Arc<Mutex<String>>,
}

const DASHBOARD_HTML: &str = include_str!("resources/dashboard.html");

impl WebInspector {
    /// Create a new WebInspector and start the HTTP server on the given port.
    ///
    /// `ast_tree` and `operator_tree` are pre-rendered Unicode tree strings
    /// computed once after parsing/lowering, served as static text endpoints.
    pub fn new(port: u16, ast_tree: String, operator_tree: String) -> Self {
        let snapshot = Arc::new(Mutex::new("{}".to_string()));
        let ast_tree = Arc::new(ast_tree);
        let operator_tree = Arc::new(operator_tree);

        let snapshot_clone = snapshot.clone();
        let ast_clone = ast_tree.clone();
        let operator_clone = operator_tree.clone();

        let text_plain: tiny_http::Header =
            "Content-Type: text/plain; charset=utf-8".parse().unwrap();

        thread::spawn(move || {
            let server = tiny_http::Server::http(format!("0.0.0.0:{port}"))
                .expect("Failed to start web inspector server");
            info!("Web inspector running at http://localhost:{port}");

            for request in server.incoming_requests() {
                let response = match request.url() {
                    "/" => tiny_http::Response::from_string(DASHBOARD_HTML).with_header(
                        "Content-Type: text/html; charset=utf-8"
                            .parse::<tiny_http::Header>()
                            .unwrap(),
                    ),
                    "/api/snapshot" => {
                        let data = snapshot_clone.lock().unwrap().clone();
                        tiny_http::Response::from_string(data).with_header(
                            "Content-Type: application/json"
                                .parse::<tiny_http::Header>()
                                .unwrap(),
                        )
                    }
                    "/api/ast" => tiny_http::Response::from_string(ast_clone.as_str())
                        .with_header(text_plain.clone()),
                    "/api/operators" => tiny_http::Response::from_string(operator_clone.as_str())
                        .with_header(text_plain.clone()),
                    _ => tiny_http::Response::from_string("Not Found")
                        .with_status_code(404)
                        .with_header(text_plain.clone()),
                };
                let _ = request.respond(response);
            }
        });

        WebInspector { snapshot }
    }

    /// Update the snapshot with the current state of all producers.
    ///
    /// `collect` is called with an accumulator function; call the accumulator
    /// once per producer to include it in the snapshot.  All producers are
    /// rendered into a single JSON object `{"tick": N, "producers": [...]}`.
    pub fn update_snapshot(
        &self,
        tick: u64,
        collect: impl FnOnce(&mut dyn FnMut(&dyn TileProducer)),
    ) {
        let opts = VizOptions::default();
        let mut jsons: Vec<String> = Vec::new();
        collect(&mut |p: &dyn TileProducer| jsons.push(p.inspect(&opts).to_json()));
        let json = format!(r#"{{"tick":{},"producers":[{}]}}"#, tick, jsons.join(","),);
        *self.snapshot.lock().unwrap() = json;
    }
}
