//! Branches: several versions of one program running in one process, per
//! `src/ccl/design/program-evolution.md`, "The branch table".
//!
//! Every case here checks the same two things from different directions. A
//! branch operation leaves every other branch as it was: its outputs, the values
//! its mutable variables hold, and the identity of each operator its entry
//! holds. And an operator lives exactly as long as some entry holds it.
//!
//! The HTTP cases run `running-log` as `production`. A branch that diverges from
//! it reads its variable on `/get2` rather than `/get`, so each branch's value
//! is observable on a route only it serves: two versions that both bind a route
//! both reply on it, and which reply the client gets is not something a test can
//! name. `/set` is bound by both, and both reply `ok`.

use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

use indoc::indoc;

use cambra::{
    ccl::{
        Type,
        context::{GlobalContext, Phase, ReuseTally},
    },
    interpreter::{
        BaseType, Extent, Predicate, TestDataSource, Value, pull_laps, tile_operators::FanOut,
    },
    live_program::{BranchError, BranchStatus, LiveProgram, ROOT},
};

use crate::harness::*;
use crate::serving::{
    exchange, http_get, http_post, no_main, raw_http_response, reserve_test_port, start_sink,
};

/// `running-log` with its writer edited and its reader moved to `/get2`: a
/// divergent edit to the stateful loop, observable on a route `production` does
/// not serve.
const DASHED_LOG: &str = indoc! {r#"
    set_reqs, set_resps = http_serve("{PORT}", "POST", "/set")
    get_reqs, get_resps = http_serve("{PORT}", "GET", "/get2")

    log: Mut(String, Txn) := ""

    for msg in set_reqs:
        with begin():
            log := log + "-" + msg
        set_resps << "ok\n"

    for req in get_reqs:
        with begin():
            get_resps << log
"#};

/// A second divergent edit, read on `/get3`.
const PLUSSED_LOG: &str = indoc! {r#"
    set_reqs, set_resps = http_serve("{PORT}", "POST", "/set")
    get_reqs, get_resps = http_serve("{PORT}", "GET", "/get3")

    log: Mut(String, Txn) := ""

    for msg in set_reqs:
        with begin():
            log := log + "+" + msg
        set_resps << "ok\n"

    for req in get_reqs:
        with begin():
            get_resps << log
"#};

/// Held while a case reserves a port and binds it, and while the subprocess case
/// spawns its child.
///
/// A child spawned between a port's reservation probe and the bind that takes
/// the port can hold the probe's socket, and the bind then fails with
/// `EADDRINUSE`. Measured on this file run in a loop: about one run in eight
/// failed that way before the spawn and the binds were serialized. The
/// `launch_under_control` cases in `cases.rs` share the hazard with every case
/// in that binary; this lock covers only this file's.
static SPAWN_OR_BIND: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn with_port(text: &str, port: u16) -> String {
    text.replace("{PORT}", &port.to_string())
}

/// The value branch `name`'s `log` holds, read off the stores its entry holds.
fn log_of(live: &LiveProgram, name: &str) -> String {
    let state = live.held_state(name).expect("the branch exists");
    let (_, value) = state
        .iter()
        .find(|(path, _)| path.to_string() == "`log`")
        .unwrap_or_else(|| panic!("{name} holds no `log`: {state:?}"));
    match value {
        Value::String(s) => s.to_string(),
        other => panic!("`log` is a string, got {other:?}"),
    }
}

/// The operators branch `name`'s entry holds, as addresses in a fixed order, so
/// two readings compare equal exactly when the entry holds the same operators.
fn identity(live: &LiveProgram, name: &str) -> Vec<*const FanOut> {
    let mut out: Vec<*const FanOut> = live
        .held_operators(name)
        .expect("the branch exists")
        .iter()
        .map(Weak::as_ptr)
        .collect();
    out.sort();
    out
}

/// `production` running `running-log`, with `/set a` and `/set b` committed.
fn running_log_with_ab() -> (u16, GlobalContext, LiveProgram) {
    let (port, mut ctx, live) = {
        let _serial = SPAWN_OR_BIND.lock().unwrap_or_else(|e| e.into_inner());
        let port = reserve_test_port();
        let (ctx, live) = start_sink(&source("running-log", port));
        (port, ctx, live)
    };
    let replies = exchange(&mut ctx, move || {
        vec![http_post(port, "/set", "a"), http_post(port, "/set", "b")]
    });
    assert_eq!(replies, vec!["ok\n", "ok\n"]);
    (port, ctx, live)
}

/// Commit `/set <msg>` and read `/get`, which only `production` serves.
fn set_and_get(ctx: &mut GlobalContext, port: u16, msg: &'static str) -> Vec<String> {
    exchange(ctx, move || {
        vec![http_post(port, "/set", msg), http_get(port, "/get")]
    })
}

/// Creating a branch builds nothing and changes nothing its origin runs.
///
/// The copy holds exactly the origin's operators, so until one of the two
/// reloads they are one graph, and the origin's variable goes on accumulating
/// as it did.
#[test]
fn creating_a_branch_leaves_its_origin_untouched() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    let before = identity(&live, ROOT);

    live.create_branch("staging", ROOT).expect("created");

    assert_eq!(
        identity(&live, ROOT),
        before,
        "the origin holds the same operators"
    );
    assert_eq!(
        identity(&live, "staging"),
        before,
        "the copy holds exactly the origin's operators and builds none"
    );
    let rows = live.branches();
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[1].name, "staging");
    assert_eq!(rows[1].origin.as_deref(), Some(ROOT));
    assert_eq!(rows[1].status, BranchStatus::Current);
    assert_eq!(
        (rows[1].operators, rows[1].shared),
        (before.len(), before.len()),
        "every operator the copy holds is its origin's"
    );

    assert_eq!(set_and_get(&mut ctx, port, "c"), vec!["ok\n", "abc"]);
    assert_eq!(log_of(&live, ROOT), "abc");
    assert_eq!(
        log_of(&live, "staging"),
        "abc",
        "the copy runs the origin's store"
    );
}

/// A branch's reload forks it from its origin and leaves the origin running
/// what it ran.
///
/// The divergent edit is to the stateful loop, so the branch's store is rebuilt
/// and seeded from the value the origin's variable holds at the reload. From
/// there the two variables go their own ways. The origin holds the same
/// operators before and after, and its route `/get` stays served though the
/// branch's version does not bind it, because routes are retired against every
/// branch's.
#[test]
fn reloading_a_branch_forks_it_and_leaves_its_origin_untouched() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    live.create_branch("staging", ROOT).expect("created");
    let before = identity(&live, ROOT);

    let report = live
        .reload_branch(&mut ctx, "staging", &with_port(DASHED_LOG, port), &no_main)
        .expect("an edit to the writer is accepted");
    assert!(
        report.reuse.kept > 0,
        "the branch keeps its origin's unchanged operators: {:?}",
        report.reuse
    );

    assert_eq!(
        identity(&live, ROOT),
        before,
        "the origin's entry is read and left as it was"
    );
    assert_eq!(log_of(&live, ROOT), "ab");
    assert_eq!(
        log_of(&live, "staging"),
        "ab",
        "the rebuilt store forks from the origin's value at the reload"
    );

    assert_eq!(set_and_get(&mut ctx, port, "c"), vec!["ok\n", "abc"]);
    let branch_view = exchange(&mut ctx, move || vec![http_get(port, "/get2")]);
    assert_eq!(
        branch_view,
        vec!["ab-c"],
        "the branch commits under its rule"
    );
    assert_eq!(log_of(&live, ROOT), "abc", "and the origin under its own");
    assert_eq!(log_of(&live, "staging"), "ab-c");
    assert_eq!(identity(&live, ROOT), before);

    let rows = live.branches();
    assert_eq!(rows[1].status, BranchStatus::Current);
    assert!(
        0 < rows[1].shared && rows[1].shared < rows[1].operators,
        "the branch shares its origin's unchanged operators and holds its own \
         rebuilt ones: {rows:?}"
    );
}

/// Reloading a branch with the source it already runs re-forks it: its previous
/// history is discarded and its variable restarts from the origin's value.
#[test]
fn reloading_a_branch_again_re_forks_it_from_its_origin() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    live.create_branch("staging", ROOT).expect("created");
    let dashed = with_port(DASHED_LOG, port);
    live.reload_branch(&mut ctx, "staging", &dashed, &no_main)
        .expect("accepted");
    let _ = set_and_get(&mut ctx, port, "c");
    assert_eq!(log_of(&live, "staging"), "ab-c");

    live.reload_branch(&mut ctx, "staging", &dashed, &no_main)
        .expect("accepted");
    assert_eq!(
        log_of(&live, "staging"),
        "abc",
        "the branch's store forks from the origin again"
    );
    let _ = set_and_get(&mut ctx, port, "d");
    assert_eq!(log_of(&live, "staging"), "abc-d");
    assert_eq!(log_of(&live, ROOT), "abcd");
}

/// An origin's reload leaves its branches stale, and a stale branch goes on
/// running what it holds.
///
/// Two branches: `copy` never reloaded, so it runs `production`'s first version
/// outright, and `staging` diverged. After `production` reloads, both are stale,
/// both keep committing under the rule they had, and `production`'s own variable
/// carries across its reload as it would with no branches at all.
#[test]
fn an_origin_reload_leaves_its_branches_stale_and_running() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    live.create_branch("copy", ROOT).expect("created");
    live.create_branch("staging", ROOT).expect("created");
    live.reload_branch(&mut ctx, "staging", &with_port(DASHED_LOG, port), &no_main)
        .expect("accepted");
    let copy_before = identity(&live, "copy");
    let staging_before = identity(&live, "staging");

    live.reload(&mut ctx, &with_port(PLUSSED_LOG, port), &no_main)
        .expect("production may reload with branches off it");

    assert_eq!(
        identity(&live, "copy"),
        copy_before,
        "a stale branch holds what it held"
    );
    assert_eq!(identity(&live, "staging"), staging_before);
    let statuses: Vec<(String, BranchStatus)> = live
        .branches()
        .into_iter()
        .map(|b| (b.name, b.status))
        .collect();
    assert_eq!(
        statuses,
        vec![
            (ROOT.to_string(), BranchStatus::Current),
            ("copy".to_string(), BranchStatus::Stale),
            ("staging".to_string(), BranchStatus::Stale),
        ]
    );

    let replies = exchange(&mut ctx, move || {
        vec![
            http_post(port, "/set", "c"),
            http_get(port, "/get2"),
            http_get(port, "/get3"),
        ]
    });
    assert_eq!(replies, vec!["ok\n", "ab-c", "ab+c"]);
    assert_eq!(log_of(&live, ROOT), "ab+c");
    assert_eq!(log_of(&live, "staging"), "ab-c");
    assert_eq!(
        log_of(&live, "copy"),
        "abc",
        "the copy runs production's first version, whose writer appends bare"
    );
}

/// Retargeting a branch changes nothing that runs: the next reload of the
/// branch diffs against, and forks from, the new origin.
#[test]
fn retargeting_a_branch_leaves_every_branch_running_as_it_was() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    live.create_branch("qa", ROOT).expect("created");
    live.create_branch("scratch", ROOT).expect("created");
    let dashed = with_port(DASHED_LOG, port);
    live.reload_branch(&mut ctx, "qa", &dashed, &no_main)
        .expect("accepted");
    let _ = set_and_get(&mut ctx, port, "c");
    let branches = [ROOT, "qa", "scratch"];
    let identities: Vec<Vec<*const FanOut>> = branches.iter().map(|b| identity(&live, b)).collect();

    live.retarget_branch("scratch", "qa").expect("retargeted");

    assert_eq!(
        branches
            .iter()
            .map(|b| identity(&live, b))
            .collect::<Vec<_>>(),
        identities,
        "a retarget builds and frees nothing"
    );
    assert_eq!(log_of(&live, ROOT), "abc");
    assert_eq!(log_of(&live, "qa"), "ab-c");
    let scratch = &live.branches()[2];
    assert_eq!(scratch.origin.as_deref(), Some("qa"));
    assert_eq!(scratch.status, BranchStatus::Stale);

    let asked = live
        .diff_branch(&ctx, "scratch", &dashed, Phase::AsOfRead)
        .expect("diffed");
    assert!(
        asked.diff.contains("no difference"),
        "a retargeted branch diffs against its new origin's version: {}",
        asked.diff
    );
    live.reload_branch(&mut ctx, "scratch", &with_port(PLUSSED_LOG, port), &no_main)
        .expect("accepted");
    assert_eq!(
        log_of(&live, "scratch"),
        "ab-c",
        "and forks from its new origin's value"
    );
    let replies = exchange(&mut ctx, move || {
        vec![
            http_post(port, "/set", "d"),
            http_get(port, "/get"),
            http_get(port, "/get2"),
            http_get(port, "/get3"),
        ]
    });
    assert_eq!(replies, vec!["ok\n", "abcd", "ab-c-d", "ab-c+d"]);
}

/// Retarget refuses what would leave a chain of origins without a root.
#[test]
fn retargeting_refuses_the_root_and_a_cycle() {
    let (_port, _ctx, mut live) = running_log_with_ab();
    live.create_branch("a", ROOT).expect("created");
    live.create_branch("b", "a").expect("created");

    assert!(matches!(
        live.retarget_branch(ROOT, "a"),
        Err(BranchError::Refused(_))
    ));
    assert!(matches!(
        live.retarget_branch("a", "a"),
        Err(BranchError::Refused(_))
    ));
    assert!(
        matches!(live.retarget_branch("a", "b"), Err(BranchError::Refused(_))),
        "`b` descends from `a`"
    );
    assert!(matches!(
        live.retarget_branch("nope", "a"),
        Err(BranchError::Unknown(_))
    ));
    assert!(matches!(
        live.retarget_branch("a", "nope"),
        Err(BranchError::Unknown(_))
    ));
    let origins: Vec<Option<String>> = live.branches().into_iter().map(|b| b.origin).collect();
    assert_eq!(
        origins,
        vec![None, Some(ROOT.to_string()), Some("a".to_string())],
        "a refused retarget changes nothing"
    );
}

/// Creation refuses a name already taken and an origin the table does not hold.
#[test]
fn creating_refuses_a_taken_name_and_an_unknown_origin() {
    let (_port, _ctx, mut live) = running_log_with_ab();
    live.create_branch("a", ROOT).expect("created");
    assert!(matches!(
        live.create_branch("a", ROOT),
        Err(BranchError::Refused(_))
    ));
    assert!(matches!(
        live.create_branch(ROOT, "a"),
        Err(BranchError::Refused(_))
    ));
    assert!(matches!(
        live.create_branch("b", "nope"),
        Err(BranchError::Unknown(_))
    ));
    assert_eq!(live.branches().len(), 2);
}

/// Deleting a branch leaves its origin running, orphans the branches created
/// from it, and retires the routes no remaining branch binds.
///
/// An orphan keeps running what it holds, and its reload and diff are refused
/// until it is retargeted onto a running branch.
#[test]
fn deleting_a_branch_leaves_its_origin_untouched_and_orphans_its_children() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    live.create_branch("qa", ROOT).expect("created");
    let dashed = with_port(DASHED_LOG, port);
    live.reload_branch(&mut ctx, "qa", &dashed, &no_main)
        .expect("accepted");
    live.create_branch("scratch", "qa").expect("created");
    let before = identity(&live, ROOT);
    let _ = set_and_get(&mut ctx, port, "c");

    assert_eq!(
        live.delete_branch(&mut ctx, "qa").expect("deleted"),
        vec!["scratch".to_string()],
        "the branch created from `qa` is orphaned"
    );
    assert_eq!(identity(&live, ROOT), before, "the origin is untouched");
    let orphan = &live.branches()[1];
    assert_eq!(
        live.render_branches().lines().nth(1),
        Some(
            format!(
                "scratch\tqa\torphaned\toperators={}\tshared={}",
                orphan.operators, orphan.shared
            )
            .as_str()
        ),
        "an orphan is listed under its deleted origin's name"
    );

    // The orphan still runs `qa`'s version, so `/get2` is still bound.
    let replies = exchange(&mut ctx, move || {
        vec![
            http_post(port, "/set", "d"),
            http_get(port, "/get"),
            http_get(port, "/get2"),
        ]
    });
    assert_eq!(replies, vec!["ok\n", "abcd", "ab-c-d"]);
    assert_eq!(log_of(&live, ROOT), "abcd");

    assert!(matches!(
        live.reload_branch(&mut ctx, "scratch", &dashed, &no_main),
        Err(BranchError::Refused(_))
    ));
    assert!(matches!(
        live.diff_branch(&ctx, "scratch", &dashed, Phase::AsOfRead),
        Err(BranchError::Refused(_))
    ));
    assert!(matches!(
        live.delete_branch(&mut ctx, ROOT),
        Err(BranchError::Refused(_))
    ));
    assert!(matches!(
        live.delete_branch(&mut ctx, "qa"),
        Err(BranchError::Unknown(_))
    ));

    // Retargeted, the orphan reloads against production again.
    live.retarget_branch("scratch", ROOT).expect("retargeted");
    live.reload_branch(&mut ctx, "scratch", &dashed, &no_main)
        .expect("a retargeted orphan reloads");
    assert_eq!(log_of(&live, "scratch"), "abcd");

    // With the last branch binding `/get2` gone, the route is retired.
    live.delete_branch(&mut ctx, "scratch").expect("deleted");
    assert_eq!(identity(&live, ROOT), before);
    let status = exchange(&mut ctx, move || {
        raw_http_response(
            port,
            &format!("GET /get2 HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nConnection: close\r\n\r\n"),
        )
    });
    assert!(
        status.starts_with("HTTP/1.1 404"),
        "a route no branch binds is retired: {status}"
    );
    assert_eq!(set_and_get(&mut ctx, port, "e"), vec!["ok\n", "abcde"]);
}

/// An operator held by several branches lives until the last of them lets go
/// of it, by reload or by deletion, and is freed then.
///
/// `production` reloads first, so the operators its first version built and its
/// second rebuilt are held only by the two stale branches. Reloading one of them
/// re-forks it from `production`'s current version, which drops them from its
/// entry; deleting the other drops the last hold.
#[test]
fn an_operator_lives_until_the_last_branch_holding_it_lets_go() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    live.create_branch("a", ROOT).expect("created");
    live.create_branch("b", ROOT).expect("created");
    let first: Vec<Weak<FanOut>> = live.held_operators(ROOT).unwrap();

    live.reload(&mut ctx, &source("running-log-writer-edit", port), &no_main)
        .expect("accepted");
    let now = identity(&live, ROOT);
    let dropped: Vec<&Weak<FanOut>> = first
        .iter()
        .filter(|w| !now.contains(&w.as_ptr()))
        .collect();
    assert!(
        !dropped.is_empty(),
        "editing the writer rebuilds the store, so production lets go of the old one"
    );
    assert!(
        dropped.iter().all(|w| w.upgrade().is_some()),
        "the two stale branches still hold what production dropped"
    );

    live.reload_branch(
        &mut ctx,
        "a",
        &source("running-log-writer-edit", port),
        &no_main,
    )
    .expect("accepted");
    assert!(
        dropped.iter().all(|w| w.upgrade().is_some()),
        "`b` still holds them after `a` reloaded away"
    );

    live.delete_branch(&mut ctx, "b").expect("deleted");
    assert!(
        dropped.iter().all(|w| w.upgrade().is_none()),
        "no entry holds them, so they are freed"
    );
    assert!(
        first
            .iter()
            .filter(|w| now.contains(&w.as_ptr()))
            .all(|w| w.upgrade().is_some()),
        "what production kept is untouched"
    );
    assert_eq!(set_and_get(&mut ctx, port, "c"), vec!["ok\n", "ab-c"]);
}

/// A branch's operators reading a source pin that source's agreement, and a
/// deleted branch's producers hand their release records back, so the agreement
/// advances.
///
/// The branch here is a copy nothing pulls, so its producer stops where the copy
/// was made. `production`'s reload reads the source through a comprehension,
/// which rebuilds its iteration, so from then on the copy alone holds the old
/// producer.
#[test]
fn a_deleted_branch_hands_its_release_records_back() {
    let mut ctx = GlobalContext::default();
    let src = Rc::new(RefCell::new(TestDataSource::new(
        "src",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    ctx.register_source(src.clone());
    let v1 = indoc! {r#"
        x := 0
        for i in src():
            x := x + i
        x
    "#};
    let v2 = indoc! {r#"
        x := 0
        for i in [j + 0 for j in src()]:
            x := x + i
        x
    "#};
    let pull = |ctx: &mut GlobalContext, live: &mut LiveProgram| {
        let producer = live
            .main_producer_mut()
            .expect("the program's value is `x`");
        pull_laps(ctx.scheduler(), &mut **producer, 6, |_| false);
    };

    let mut live = LiveProgram::start(&mut ctx, v1, &no_main).expect("v1 compiles");
    src.borrow_mut().add_data(&[
        (Value::UInt(0), Value::Int(10)),
        (Value::UInt(1), Value::Int(20)),
    ]);
    pull(&mut ctx, &mut live);
    let pinned = src.borrow().get_released_predicate();
    assert_ne!(
        pinned,
        Predicate::False,
        "the drive releases what it decided"
    );

    live.create_branch("copy", ROOT).expect("created");
    let held_by_the_copy = live.held_operators("copy").unwrap();
    live.reload(&mut ctx, v2, &no_main).expect("accepted");
    src.borrow_mut().add_data(&[
        (Value::UInt(2), Value::Int(30)),
        (Value::UInt(3), Value::Int(40)),
    ]);
    pull(&mut ctx, &mut live);
    assert_eq!(
        src.borrow().get_released_predicate(),
        pinned,
        "the copy's producer is registered and has released nothing more"
    );

    live.delete_branch(&mut ctx, "copy").expect("deleted");
    let kept = identity(&live, ROOT);
    assert!(
        held_by_the_copy
            .iter()
            .filter(|w| !kept.contains(&w.as_ptr()))
            .all(|w| w.upgrade().is_none()),
        "what only the copy held is freed"
    );
    assert_ne!(
        src.borrow().get_released_predicate(),
        pinned,
        "its producer's record went with it, so the agreement is production's alone"
    );
}

/// Every reuse tally and every reply of one root-only reload sequence, in order.
fn root_only_trace() -> Vec<String> {
    let (port, mut ctx, mut live) = {
        let _serial = SPAWN_OR_BIND.lock().unwrap_or_else(|e| e.into_inner());
        let port = reserve_test_port();
        let (ctx, live) = start_sink(&source("two-loops", port));
        (port, ctx, live)
    };
    let mut trace = Vec::new();
    let exchange_into = |ctx: &mut GlobalContext,
                         trace: &mut Vec<String>,
                         reqs: Vec<(&'static str, &'static str)>| {
        let replies = exchange(ctx, move || {
            reqs.iter()
                .map(|(path, body)| http_post(port, path, body))
                .collect::<Vec<_>>()
        });
        trace.extend(replies);
    };
    exchange_into(&mut ctx, &mut trace, vec![("/a", "x"), ("/b", "y")]);
    for (version, reqs) in [
        ("two-loops-one-edited", vec![("/a", "p"), ("/b", "q")]),
        ("two-loops", vec![("/b", "r")]),
        ("two-loops", vec![("/a", "s")]),
        ("two-loops-swapped", vec![("/a", "t"), ("/b", "u")]),
    ] {
        let ReuseTally { kept, bound } = live
            .reload(&mut ctx, &source(version, port), &no_main)
            .unwrap_or_else(|e| panic!("reload to {version} rejected: {e:?}"))
            .reuse;
        trace.push(format!("{version}: {kept}/{bound}"));
        exchange_into(&mut ctx, &mut trace, reqs);
    }
    assert_eq!(
        live.render_branches().lines().count(),
        1,
        "nothing here creates a branch"
    );
    trace
}

/// With only `production`, a reload is the single-program hot reload: the
/// tallies and replies below are what this sequence gave before the branch
/// table existed, recorded from that build.
#[test]
fn a_root_only_reload_sequence_is_unchanged_by_the_branch_table() {
    assert_eq!(
        root_only_trace(),
        vec![
            "x\n",
            "y\n",
            "two-loops-one-edited: 8/11",
            "x\np\n",
            "y\n* q\n",
            "two-loops: 8/11",
            "y\n* q\nr\n",
            "two-loops: 10/10",
            "x\np\ns\n",
            "two-loops-swapped: 6/12",
            "y\n* q\nr\nt\n",
            "x\np\ns\nu\n",
        ]
    );
}

/// The control port serves every branch verb with the status codes the doc
/// gives, and the binary's driver pulls a branch's `main` output beside
/// `production`'s.
///
/// Driven as a subprocess, because the verbs are serviced by the binary's own
/// loop. A `stdin` program's output is its `main` value, so the line written
/// after the branch reloads is answered by both versions, the branch's labelled
/// with its name.
#[test]
fn the_control_port_serves_the_branch_verbs() {
    use std::io::Write;

    const V1: &str = "[\"> \" + line for line in stdin()]\n";
    const V2: &str = "[\">> \" + line for line in stdin()]\n";

    let mut launched = {
        let _serial = SPAWN_OR_BIND.lock().unwrap_or_else(|e| e.into_inner());
        launch_under_control(V1)
    };
    let control = launched.control;
    let ask = |path: &str, body: &str| {
        let reply = raw_http_response(
            control,
            &format!(
                "POST {path} HTTP/1.1\r\nHost: 127.0.0.1:{control}\r\n\
                 Content-Length: {}\r\nConnection: close\r\n\r\n{body}",
                body.len()
            ),
        );
        let status: u16 = reply[9..12].parse().expect("a status code");
        let body = reply
            .split_once("\r\n\r\n")
            .map(|(_, b)| b.to_string())
            .unwrap_or_default();
        (status, body)
    };
    let columns = |listed: &str| -> Vec<String> {
        listed
            .lines()
            .map(|l| l.split('\t').take(3).collect::<Vec<_>>().join(" "))
            .collect()
    };

    assert_eq!(ask("/branch/staging", "").0, 200);
    assert_eq!(ask("/branch/staging", "").0, 400, "the name is taken");
    assert_eq!(ask("/branch/qa/from/nope", "").0, 404, "no such origin");
    assert_eq!(ask("/branch/qa/from/staging", "").0, 200);
    assert_eq!(ask("/branch/bad.name", "").0, 404, "not a branch name");
    assert_eq!(ask("/branch/production/delete", "").0, 400);
    assert_eq!(ask("/branch/nope/delete", "").0, 404);
    assert_eq!(ask("/branch/production/retarget/qa", "").0, 400);
    assert_eq!(ask("/branch/staging/retarget/qa", "").0, 400, "a cycle");
    assert_eq!(ask("/branch/qa/retarget/nope", "").0, 404);
    assert_eq!(ask("/reload/nope", V2).0, 404);
    assert_eq!(ask("/diff/nope", V2).0, 404);

    let (status, listed) = ask("/branches/list", "");
    assert_eq!(status, 200);
    assert_eq!(
        columns(&listed),
        vec![
            "production - current",
            "staging production current",
            "qa staging current"
        ]
    );

    let (status, diffed) = ask("/diff/staging", V1);
    assert_eq!(status, 200);
    assert!(diffed.contains("no difference"), "{diffed}");
    let (status, reloaded) = ask("/reload/staging", V2);
    assert_eq!(status, 200, "{reloaded}");
    assert!(reloaded.contains("reloaded"), "{reloaded}");
    let (_, listed) = ask("/branches/list", "");
    assert_eq!(
        columns(&listed)[2],
        "qa staging stale",
        "reloading `staging` leaves `qa` stale"
    );

    assert_eq!(ask("/branch/staging/delete", "").0, 200);
    let (_, listed) = ask("/branches/list", "");
    assert_eq!(
        columns(&listed),
        vec!["production - current", "qa staging orphaned"]
    );
    assert_eq!(
        ask("/reload/qa", V2).0,
        400,
        "an orphan's reload is refused"
    );
    assert_eq!(ask("/diff/qa", V2).0, 400, "and so is its diff");
    assert_eq!(ask("/branch/qa/retarget/production", "").0, 200);
    let (status, reloaded) = ask("/reload/qa", V2);
    assert_eq!(status, 200, "{reloaded}");

    let mut input = launched.input.take().expect("piped stdin");
    writeln!(input, "one").expect("write");
    input.flush().expect("flush");
    std::thread::sleep(std::time::Duration::from_millis(400));
    drop(input);
    std::thread::sleep(std::time::Duration::from_millis(400));
    let out = launched.collected.lock().unwrap().clone();
    assert!(out.contains("\"> one\""), "production answers: {out}");
    assert!(
        out.contains("Got value from qa") && out.contains("\">> one\""),
        "the branch's version is pulled too: {out}"
    );
}

/// `bump-over-source` with each request appending `b` rather than `a`: a
/// divergent reply on the same route, `POST /bump`.
const BUMP_WITH_B: &str = indoc! {r#"
    n := ""
    reqs, resps = http_serve("{PORT}", "POST", "/bump")
    for r in reqs:
        n := n + "b"
        resps << n + "\n"
"#};

/// [`BUMP_WITH_B`] served on `/bump2`, a route `production` does not bind.
const BUMP_WITH_B_ELSEWHERE: &str = indoc! {r#"
    n := ""
    reqs, resps = http_serve("{PORT}", "POST", "/bump2")
    for r in reqs:
        n := n + "b"
        resps << n + "\n"
"#};

/// The value branch `name`'s `n` holds.
fn n_of(live: &LiveProgram, name: &str) -> String {
    let state = live.held_state(name).expect("the branch exists");
    let (_, value) = state
        .iter()
        .find(|(path, _)| path.to_string() == "`n`")
        .unwrap_or_else(|| panic!("{name} holds no `n`: {state:?}"));
    match value {
        Value::String(s) => s.to_string(),
        other => panic!("`n` is a string, got {other:?}"),
    }
}

/// `production` running `bump-over-source` after two requests, so `n` is `"aa"`,
/// with `staging` created from it and, when `reload` names a version, reloaded
/// to it.
fn bump_with_staging(reload: Option<&str>) -> (u16, GlobalContext, LiveProgram) {
    let (port, mut ctx, mut live) = {
        let _serial = SPAWN_OR_BIND.lock().unwrap_or_else(|e| e.into_inner());
        let port = reserve_test_port();
        let (ctx, live) = start_sink(&source("bump-over-source", port));
        (port, ctx, live)
    };
    let replies = exchange(&mut ctx, move || {
        vec![http_post(port, "/bump", "1"), http_post(port, "/bump", "2")]
    });
    assert_eq!(replies, vec!["a\n", "aa\n"]);
    live.create_branch("staging", ROOT).expect("created");
    if let Some(version) = reload {
        live.reload_branch(&mut ctx, "staging", &with_port(version, port), &no_main)
            .expect("an edit to the loop body is accepted");
    }
    (port, ctx, live)
}

/// Known defect: two branches whose versions bind one route both reply on it,
/// and the client gets whichever reply is dispatched first. The doc's Scope
/// section, "Which branch's sinks send", declares this out of scope. This test
/// pins today's behavior, so a fix shows up as a deliberate change to it.
///
/// Each request gets exactly one reply, and it is one of the two branches'. The
/// winner is not asserted: it depends on the order the scheduler notifies the
/// two versions' consumers.
#[test]
fn a_shared_route_answers_with_one_of_the_two_branches_replies() {
    let (port, mut ctx, _live) = bump_with_staging(Some(BUMP_WITH_B));
    let replies = exchange(&mut ctx, move || vec![http_post(port, "/bump", "3")]);
    assert_eq!(replies.len(), 1);
    assert!(
        ["aaa\n", "aab\n"].contains(&replies[0].as_str()),
        "the reply is production's or staging's: {replies:?}"
    );
}

/// Known defect: on a route two branches bind, both branches compute and both
/// dispatch for every request, and the reply that loses is dropped without a
/// trace. The doc's Scope section, "Which branch's sinks send", declares this
/// out of scope. This test pins today's behavior, so a fix shows up as a
/// deliberate change to it.
///
/// The losing reply is dropped by `HttpServerSharedState::process`: it finds no
/// pending request at its index, which the winning reply already removed.
#[test]
fn a_shared_route_runs_both_branches_and_drops_the_losing_reply() {
    let (port, mut ctx, live) = bump_with_staging(Some(BUMP_WITH_B));
    let _ = exchange(&mut ctx, move || vec![http_post(port, "/bump", "3")]);
    assert_eq!(n_of(&live, ROOT), "aaa", "production decided the request");
    assert_eq!(n_of(&live, "staging"), "aab", "and so did staging");
}

/// A losing reply is not delivered to a later request: a reply is addressed by
/// the request's position in the route's source, and each request has its own.
///
/// This holds today despite the shared-route defect (the doc's Scope section,
/// "Which branch's sinks send"). It pins that the defect never answers one
/// request with the reply computed for another.
#[test]
fn a_shared_route_never_answers_a_request_with_an_earlier_requests_reply() {
    let (port, mut ctx, live) = bump_with_staging(Some(BUMP_WITH_B));
    for (i, answers) in [
        (3, ["aaa\n", "aab\n"]),
        (4, ["aaaa\n", "aabb\n"]),
        (5, ["aaaaa\n", "aabbb\n"]),
    ] {
        let replies = exchange(&mut ctx, move || {
            vec![http_post(port, "/bump", &i.to_string())]
        });
        assert!(
            answers.contains(&replies[0].as_str()),
            "request {i} is answered by a reply computed for it: {replies:?}"
        );
    }
    assert_eq!(n_of(&live, ROOT), "aaaaa");
    assert_eq!(n_of(&live, "staging"), "aabbb");
}

/// Control for the shared-route defect: a copy that has never reloaded runs its
/// origin's version, so the route has one sink consumer and one reply.
#[test]
fn a_copy_that_never_reloaded_replies_once_through_its_origins_sink() {
    let (port, mut ctx, live) = bump_with_staging(None);
    let replies = exchange(&mut ctx, move || {
        vec![http_post(port, "/bump", "3"), http_post(port, "/bump", "4")]
    });
    assert_eq!(replies, vec!["aaa\n", "aaaa\n"]);
    let program = |name| live.branch_program(name).map(|p| p as *const _);
    assert_eq!(
        program(ROOT),
        program("staging"),
        "the copy runs the origin's version, and so its sink consumers"
    );
    assert_eq!(n_of(&live, "staging"), "aaaa");
}

/// Control for the shared-route defect: a diverged branch on a route of its own
/// is answered by that branch alone, and the origin's route by the origin alone.
#[test]
fn a_diverged_branch_on_its_own_route_is_the_only_one_answering_it() {
    let (port, mut ctx, live) = bump_with_staging(Some(BUMP_WITH_B_ELSEWHERE));
    let replies = exchange(&mut ctx, move || {
        vec![
            http_post(port, "/bump2", "3"),
            http_post(port, "/bump", "4"),
            http_post(port, "/bump2", "5"),
        ]
    });
    assert_eq!(replies, vec!["aab\n", "aaa\n", "aabb\n"]);
    assert_eq!(n_of(&live, ROOT), "aaa");
    assert_eq!(n_of(&live, "staging"), "aabb");
}
