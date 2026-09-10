//! Three HTTP endpoints on the same port, sharing an outer `prefix` let —
//! `GET /greet` (static), `POST /echo` (passthrough), `POST /shout` (templated).
//!
//! All three requests are sent on one background thread (sequentially, each
//! blocking on its response) while the main thread drives the scheduler;
//! that's the same pattern as `tests/http_server.rs`.

use super::serving::{compile_sink, exchange, http_get, http_post, reserve_test_port};

#[test]
fn http_greeter() {
    let port = reserve_test_port();
    let source = include_str!("program.cambra").replace("{PORT}", &port.to_string());
    let mut ctx = compile_sink(&source);

    let actual = exchange(&mut ctx, move || {
        vec![
            http_get(port, "/greet"),
            http_post(port, "/echo", "world"),
            http_post(port, "/shout", "loud"),
        ]
    });
    assert_eq!(
        actual,
        vec![
            "Hello, stranger!\n",
            "You said: world\n",
            "Hello, loud!!!\n",
        ],
    );
}
