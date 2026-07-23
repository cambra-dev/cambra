//! A scalar transactional register shared *live* across endpoints: `POST /set`
//! overwrites `last` (`Mut[str, Txn]`, latest-write-wins); `GET /get` reads its
//! current value cross-endpoint. The GET reads `last` inside a read-only `with
//! begin():` block that feeds it out — a live as-of read (`Builtin::AsOf`)
//! latched to the GET request loop (the outer index): each GET sees the store's
//! latest committed value as of its arrival, indexed by request position (which
//! is how the HTTP sink dispatches). The as-of join resolves over a *live* store,
//! where the terminal `ExtractLast` read would never converge.
//!
//! The reply carries no id: replies ride the request loop (outer-indexed), so
//! plain position-based HTTP dispatch on `String` values suffices — no
//! `{id, payload}` records.

use std::{sync::mpsc, thread, time::Duration};

use super::common::{compile_sink, drive_until, free_port, http_get, http_post, wait_for_bind};

#[test]
fn http_counter() {
    let port = free_port();
    let source = include_str!("program.cambra").replace("{PORT}", &port.to_string());
    let mut ctx = compile_sink(&source);
    wait_for_bind();

    let (tx, rx) = mpsc::channel::<String>();
    thread::spawn(move || {
        // Two overwrites, then read: the live register must reflect the *latest*
        // committed value (`bob`) — not the init `(none)`, nor the first write
        // `alice`. Writes precede the read, so it isn't racing cross-endpoint
        // commit visibility.
        http_post(port, "/set", "alice");
        http_post(port, "/set", "bob");
        tx.send(http_get(port, "/get")).unwrap();
    });

    let got = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(got, "bob");
}

/// A *computed* live cross-endpoint read: `GET /get` replies `last + "!"`, where
/// `last` is overwritten by `POST /set`. This exercises the `as_of ≫ (λ x → x +
/// "!")` shape at runtime — the map layer over the as-of latch — confirming it
/// resolves rather than hanging: the pre-lambda-elim rewrite makes the computed
/// reply a real as-of read (a map over the latch), not a never-resolving
/// terminal render. (A `String` reply — the http sink only serializes
/// `Strings` — with a non-identity map, the point being the map, not the value.)
#[test]
fn http_computed_live_read() {
    let port = free_port();
    let source = format!(
        "set_reqs, set_resps = http_serve(\"{port}\", \"POST\", \"/set\")\n\
         get_reqs, get_resps = http_serve(\"{port}\", \"GET\", \"/get\")\n\
         last: Mut[str, Txn] := \"(none)\"\n\
         for msg in set_reqs:\n    with begin():\n        last := msg\n    set_resps << \"ok\\n\"\n\
         for req in get_reqs:\n    with begin():\n        get_resps << last + \"!\"\n"
    );
    let mut ctx = compile_sink(&source);
    wait_for_bind();

    let (tx, rx) = mpsc::channel::<String>();
    thread::spawn(move || {
        // Overwrite to `bob`, then read the computed reply `bob!`.
        http_post(port, "/set", "alice");
        http_post(port, "/set", "bob");
        tx.send(http_get(port, "/get")).unwrap();
    });

    let got = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(got.trim(), "bob!");
}

/// A *multi-register* live cross-endpoint read: `GET /get` replies `a + b`,
/// reading **two** live registers in one block. Snapshot consistency (§I-c)
/// requires both reads to come from one commit snapshot — served by a single
/// bundled `as_of((trigger, __reg))` folding the whole store at one frontier,
/// the reply projecting each register off the latched snapshot record. A `POST
/// /set` writes both registers, so `a + b` reflects the latest committed values.
#[test]
fn http_multi_register_live_read() {
    let port = free_port();
    let source = format!(
        "set_reqs, set_resps = http_serve(\"{port}\", \"POST\", \"/set\")\n\
         get_reqs, get_resps = http_serve(\"{port}\", \"GET\", \"/get\")\n\
         a: Mut[str, Txn] := \"a0\"\n\
         b: Mut[str, Txn] := \"b0\"\n\
         for msg in set_reqs:\n    with begin():\n        a := msg\n        b := msg\n    set_resps << \"ok\\n\"\n\
         for req in get_reqs:\n    with begin():\n        get_resps << a + b\n"
    );
    let mut ctx = compile_sink(&source);
    wait_for_bind();

    let (tx, rx) = mpsc::channel::<String>();
    thread::spawn(move || {
        http_post(port, "/set", "x");
        tx.send(http_get(port, "/get")).unwrap();
    });

    let got = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(got.trim(), "xx");
}
