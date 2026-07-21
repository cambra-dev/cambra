//! A guestbook HTTP service: `POST /sign` appends an entry and the response is
//! the whole guestbook so far — one endpoint that both *adds* data and
//! *displays* it. State is carried across requests by an induction accumulator
//! (`entries: Mut[_]`) whose running value the response feeds back on each
//! request, exercising a mutating for-loop with a per-request feed in *final*
//! statement position. Plain-`String` requests and responses (`http_serve`
//! yields the request body as a `String`; the reply is the accumulated text).

use std::{sync::mpsc, thread, time::Duration};

use super::common::{compile_sink, drive_until, free_port, http_post, wait_for_bind};

#[test]
fn http_accumulator() {
    let port = free_port();
    let source = include_str!("program.cambra").replace("{PORT}", &port.to_string());
    let mut ctx = compile_sink(&source);
    wait_for_bind();

    let (tx, rx) = mpsc::channel::<Vec<String>>();
    thread::spawn(move || {
        // Each POST adds an entry; the response is the full guestbook so far.
        let responses = vec![
            http_post(port, "/sign", "alice: hi"),
            http_post(port, "/sign", "bob: hello"),
            http_post(port, "/sign", "carol: hey"),
        ];
        tx.send(responses).unwrap();
    });

    let actual = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(
        actual,
        vec![
            "alice: hi\n",
            "alice: hi\nbob: hello\n",
            "alice: hi\nbob: hello\ncarol: hey\n",
        ],
    );
}
