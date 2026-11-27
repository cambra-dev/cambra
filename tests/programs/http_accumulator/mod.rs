//! POST /sign appends to an induction accumulator and returns its running text.
//! One unconditional Feed write per request constructs a nominal Response. Its
//! collection retains the exact request domain required by the response connection.

use super::serving::{compile_sink, exchange, http_post, reserve_test_port};

#[test]
fn http_accumulator() {
    let port = reserve_test_port();
    let source = include_str!("program.cambra").replace("{PORT}", &port.to_string());
    let (mut ctx, _program) = compile_sink(&source);

    // Each POST adds an entry; the response is the full guestbook so far.
    let actual = exchange(&mut ctx, move || {
        vec![
            http_post(port, "/sign", "alice: hi"),
            http_post(port, "/sign", "bob: hello"),
            http_post(port, "/sign", "carol: hey"),
        ]
    });
    assert_eq!(
        actual,
        vec![
            "alice: hi\n",
            "alice: hi\nbob: hello\n",
            "alice: hi\nbob: hello\ncarol: hey\n",
        ],
    );
}
