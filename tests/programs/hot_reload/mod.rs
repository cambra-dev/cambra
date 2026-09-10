//! Hot reload: replacing a running program with a new version of its source.
//!
//! `program.cambra` is a guestbook where `POST /sign` accumulates signatures
//! into a mutable variable and `GET /peek` holds no state.
//! `reloaded.cambra` is the same program with the accumulating loop edited, so
//! reloading it rebuilds that loop's store. The store resumes from the value it
//! held rather than restarting, so the entries already signed stand as they were
//! and the new rule governs from here.
//!
//! The feature's own suite is `tests/hot_reload.rs`, which covers the guard
//! table across the induction, transactional and `stdin` domains. This entry is
//! the demonstration.

use super::serving::{exchange, http_post, no_main, reserve_test_port, start_sink};

fn source(text: &str, port: u16) -> String {
    text.replace("{PORT}", &port.to_string())
}

/// An edit to the accumulating loop itself takes effect.
///
/// The regression this pins: every mutable variable of a causal group lives in
/// one `Transact` store bound to `__hist`, and a read of one is a projection off
/// that binding. While the store was registered outside the conversion scope,
/// `__hist` was free in every such term and hashed by its bare spelling, so
/// `sign_resps` (`__hist.to_sign_resps_0`) hashed identically however the
/// recurrence was edited, and its operator was reused against a store that no
/// longer computed what it had. The edit was accepted, reported as a divergence,
/// and silently did nothing.
#[test]
fn an_edit_to_the_accumulating_loop_takes_effect() {
    let port = reserve_test_port();
    let (mut ctx, mut live) = start_sink(&source(include_str!("program.cambra"), port));

    let before = exchange(&mut ctx, move || {
        vec![
            http_post(port, "/sign", "alice"),
            http_post(port, "/sign", "bob"),
        ]
    });
    assert_eq!(
        before,
        vec![
            "alice
",
            "alice
bob
"
        ]
    );

    live.reload(
        &mut ctx,
        &source(include_str!("reloaded.cambra"), port),
        &no_main,
    )
    .expect("editing a loop body is a change between existing endpoints");

    let after = exchange(&mut ctx, move || vec![http_post(port, "/sign", "carol")]);
    assert_eq!(
        after,
        // The store is rebuilt, and resumes from the value the replaced version
        // had reached: the entries it already recorded stand as they were, and
        // the new rule governs from here.
        vec!["alice\nbob\n- carol\n"],
        "the new loop body must govern the response",
    );
}
