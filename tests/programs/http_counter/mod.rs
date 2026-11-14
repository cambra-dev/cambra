//! A scalar transactional mutable variable shared *live* across endpoints: `POST /set`
//! overwrites `latest` (`Mut(String, Txn)`, last-write-wins); `GET /get` reads its
//! current value cross-endpoint. The GET reads `latest` inside a `with begin():` block that
//! only reads: a transaction of `latest`'s store, placed in the commit order when the
//! request arrives, whose reply rides its commit keyed by the request position (which is
//! how the HTTP sink dispatches). It resolves over a *live* store, where the terminal
//! `await_final` read would never converge.
//!
//! The reply carries no id: replies are keyed by the request loop's positions, so
//! plain position-based HTTP dispatch on `String` values suffices — no
//! `{id, payload}` records.

use super::serving::{compile_sink, exchange, http_get, http_post, reserve_test_port};

#[test]
fn http_counter() {
    let port = reserve_test_port();
    let source = include_str!("program.cambra").replace("{PORT}", &port.to_string());
    let mut ctx = compile_sink(&source);

    let got = exchange(&mut ctx, move || {
        // Two overwrites, then read: the live mutable variable must reflect the *latest*
        // committed value (`bob`) — not the init `(none)`, nor the first write
        // `alice`. Writes precede the read, so it isn't racing cross-endpoint
        // commit visibility.
        http_post(port, "/set", "alice");
        http_post(port, "/set", "bob");
        http_get(port, "/get")
    });
    assert_eq!(got, "bob");
}

/// A *computed* live cross-endpoint read: `GET /get` replies `latest + "!"`, where
/// `latest` is overwritten by `POST /set`. The GET block's reply tap holds the computed
/// value, and this confirms it resolves at runtime rather than hanging. (A `String`
/// reply — the http sink only serializes `Strings` — with a non-identity map, the point
/// being the map, not the value.)
#[test]
fn http_computed_live_read() {
    let port = reserve_test_port();
    let source = indoc::formatdoc!(
        r#"
            set_reqs, set_resps = http_serve("{port}", "POST", "/set")
            get_reqs, get_resps = http_serve("{port}", "GET", "/get")
            latest: Mut(String, Txn) := "(none)"
            for msg in set_reqs:
                with begin():
                    latest := msg
                set_resps << "ok\n"
            for req in get_reqs:
                with begin():
                    get_resps << latest + "!"
            "#
    );
    let mut ctx = compile_sink(&source);

    let got = exchange(&mut ctx, move || {
        // Overwrite to `bob`, then read the computed reply `bob!`.
        http_post(port, "/set", "alice");
        http_post(port, "/set", "bob");
        http_get(port, "/get")
    });
    assert_eq!(got.trim(), "bob!");
}

/// A *multi-variable* live cross-endpoint read: `GET /get` replies `a + b`,
/// reading **two** live mutable variables in one block. Snapshot consistency requires both
/// reads to come from one commit snapshot, which the GET block's transaction reads them at. A
/// `POST /set` writes both mutable variables, so `a + b` reflects the latest committed
/// values.
#[test]
fn http_multi_mut_var_live_read() {
    let port = reserve_test_port();
    let source = indoc::formatdoc!(
        r#"
            set_reqs, set_resps = http_serve("{port}", "POST", "/set")
            get_reqs, get_resps = http_serve("{port}", "GET", "/get")
            a: Mut(String, Txn) := "a0"
            b: Mut(String, Txn) := "b0"
            for msg in set_reqs:
                with begin():
                    a := msg
                    b := msg
                set_resps << "ok\n"
            for req in get_reqs:
                with begin():
                    get_resps << a + b
            "#
    );
    let mut ctx = compile_sink(&source);

    let got = exchange(&mut ctx, move || {
        http_post(port, "/set", "x");
        http_get(port, "/get")
    });
    assert_eq!(got.trim(), "xx");
}
