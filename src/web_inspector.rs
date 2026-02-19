//! Web inspector: serves a live dashboard of the interpreter's runtime state.

use std::sync::{Arc, Mutex};
use std::thread;

use log::info;

use crate::interpreter::{Producer, Scheduler};

/// Web inspector that serves a live HTML dashboard on a background thread.
pub struct WebInspector {
    snapshot: Arc<Mutex<String>>,
}

const DASHBOARD_HTML: &str = include_str!("resources/dashboard.html");

impl WebInspector {
    /// Create a new WebInspector and start the HTTP server on the given port.
    pub fn new(port: u16) -> Self {
        let snapshot = Arc::new(Mutex::new("{}".to_string()));
        let snapshot_clone = snapshot.clone();

        thread::spawn(move || {
            let server = tiny_http::Server::http(format!("0.0.0.0:{}", port))
                .expect("Failed to start web inspector server");
            info!("Web inspector running at http://localhost:{}", port);

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
                    _ => tiny_http::Response::from_string("Not Found")
                        .with_status_code(404)
                        .with_header(
                            "Content-Type: text/plain"
                                .parse::<tiny_http::Header>()
                                .unwrap(),
                        ),
                };
                let _ = request.respond(response);
            }
        });

        WebInspector { snapshot }
    }

    /// Update the snapshot with the current state of the producer graph.
    /// Called from the main thread each scheduler tick.
    pub fn update_snapshot(&self, tick: u64, producer: &dyn Producer, scheduler: &Scheduler) {
        let producer_node = producer.inspect();
        let sources = scheduler.inspect_sources();
        let sources_json: Vec<String> = sources.iter().map(|n| n.to_json()).collect();
        let json = format!(
            r#"{{"tick":{},"producer":{},"sources":[{}]}}"#,
            tick,
            producer_node.to_json(),
            sources_json.join(","),
        );
        *self.snapshot.lock().unwrap() = json;
    }
}
