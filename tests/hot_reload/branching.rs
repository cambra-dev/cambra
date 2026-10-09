//! Branches: several versions of one program running in one process, per
//! `src/ccl/design/program-evolution.md`, "The branch table".
//!
//! Every case checks one of two things. A branch operation changes only the
//! entry it names: every other branch keeps its outputs, the values its mutable
//! variables hold, and the operators its entry holds. And the table's own
//! bookkeeping — version numbers, branch origin, tombstones — reads back
//! over the control port as the doc specifies.
//!
//! The HTTP cases run `running-log` as `main`. A branch that diverges from it
//! reads its variable on a route only it binds (`/get2`, `/get3`), so each
//! branch's value is observable on its own route: two versions that both reply
//! on one route both dispatch to it, and which reply a client gets is out of
//! scope (`src/ccl/design/program-evolution.md`, "Scope"). `/set` is bound by
//! every branch, and every branch replies `ok` on it.
//!
//! The control-port cases call [`service`] directly: it is the main loop's half
//! of the port, so a case exercises every verb's status and body without a
//! socket.

use std::{cell::RefCell, rc::Rc};

use indoc::indoc;

use cambra::{
    ccl::{
        Type,
        context::{GlobalContext, Phase},
    },
    control_port::{ControlReply, ControlRequest, service},
    interpreter::{BaseType, Extent, Predicate, TestDataSource, Value, pull_laps},
    live_program::{BranchError, LiveProgram, MAIN_BRANCH},
};

use crate::harness::{OneFile, launch_under_control, source};
use crate::serving::{
    exchange, http_get, http_post, no_main, raw_http, raw_http_response, reserve_test_port,
    start_sink,
};

/// `running-log` with its writer edited and its reader moved to `/get2`: a
/// divergent edit to the stateful loop, observable on a route `main` does not
/// serve.
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

/// A second divergent edit of the same shape, read on `/get2`.
const PLUSSED_LOG: &str = indoc! {r#"
    set_reqs, set_resps = http_serve("{PORT}", "POST", "/set")
    get_reqs, get_resps = http_serve("{PORT}", "GET", "/get2")

    log: Mut(String, Txn) := ""

    for msg in set_reqs:
        with begin():
            log := log + "+" + msg
        set_resps << "ok\n"

    for req in get_reqs:
        with begin():
            get_resps << log
"#};

/// `running-log` with `log` dropped, which no version holding it may become.
const LOG_DROPPED: &str = indoc! {r#"
    set_reqs, set_resps = http_serve("{PORT}", "POST", "/set")
    get_reqs, get_resps = http_serve("{PORT}", "GET", "/get2")

    for msg in set_reqs:
        set_resps << "ok\n"

    for req in get_reqs:
        get_resps << "none\n"
"#};

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

/// `main` running `running-log`, with `/set a` and `/set b` committed.
fn running_log_with_ab() -> (u16, GlobalContext, LiveProgram) {
    let port = reserve_test_port();
    let (mut ctx, live) = start_sink(&source("running-log", port));
    let replies = exchange(&mut ctx, move || {
        vec![http_post(port, "/set", "a"), http_post(port, "/set", "b")]
    });
    assert_eq!(replies, vec!["ok\n", "ok\n"]);
    (port, ctx, live)
}

fn ask(ctx: &mut GlobalContext, live: &mut LiveProgram, request: ControlRequest) -> ControlReply {
    service(&request, ctx, live, &no_main)
}

fn create(name: &str, parent: &str, code: String) -> ControlRequest {
    ControlRequest::Branch {
        name: name.into(),
        parent: parent.into(),
        code,
    }
}

fn reload(branch: &str, code: String) -> ControlRequest {
    ControlRequest::Reload {
        branch: branch.into(),
        code,
    }
}

fn list(ctx: &mut GlobalContext, live: &mut LiveProgram) -> String {
    let reply = ask(ctx, live, ControlRequest::List);
    assert_eq!(reply.status, 200, "{}", reply.body);
    reply.body
}

/// Branch-and-reload creates the branch at version `1` with origin
/// `main@1`, forks its variable from `main`'s value, and leaves `main` serving
/// what it served. The reply names both versions and carries the reload's
/// report.
#[test]
fn branch_and_reload_creates_a_branch_forked_from_its_parent() {
    let (port, mut ctx, mut live) = running_log_with_ab();

    let reply = ask(
        &mut ctx,
        &mut live,
        create("staging", MAIN_BRANCH, with_port(DASHED_LOG, port)),
    );
    assert_eq!(reply.status, 200, "{}", reply.body);
    assert!(
        reply
            .body
            .starts_with("created `staging@1` from `main@1`\nreloaded: "),
        "{}",
        reply.body
    );
    assert_eq!(log_of(&live, "staging"), "ab", "forked from main's value");

    let replies = exchange(&mut ctx, move || {
        vec![
            http_post(port, "/set", "c"),
            http_get(port, "/get"),
            http_get(port, "/get2"),
        ]
    });
    assert_eq!(replies[0], "ok\n");
    assert_eq!(replies[1], "abc", "main folds `c` by its own rule");
    assert_eq!(replies[2], "ab-c", "staging folds `c` by its edited rule");
}

/// A branch-and-reload refused by the compiler or by the state guard leaves no
/// entry: the list reads as it did before, and the name stays free.
#[test]
fn a_refused_branch_and_reload_leaves_no_entry() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    let before = list(&mut ctx, &mut live);

    let broken = ask(
        &mut ctx,
        &mut live,
        create("staging", MAIN_BRANCH, "x = ".into()),
    );
    assert_eq!(
        broken.status, 400,
        "a compile error is a 400: {}",
        broken.body
    );
    assert_eq!(list(&mut ctx, &mut live), before);

    let dropping = ask(
        &mut ctx,
        &mut live,
        create("staging", MAIN_BRANCH, with_port(LOG_DROPPED, port)),
    );
    assert_eq!(dropping.status, 400, "{}", dropping.body);
    assert!(
        dropping.body.contains("`log`"),
        "names the variable: {}",
        dropping.body
    );
    assert_eq!(list(&mut ctx, &mut live), before);
    assert!(live.held_state("staging").is_none());

    let retried = ask(
        &mut ctx,
        &mut live,
        create("staging", MAIN_BRANCH, with_port(DASHED_LOG, port)),
    );
    assert_eq!(retried.status, 200, "{}", retried.body);
    assert!(
        retried.body.starts_with("created `staging@1`"),
        "a refusal consumes no version number: {}",
        retried.body
    );
}

/// Creating a name the table holds is refused with a 400, and creating from a
/// parent it does not hold answers 404; neither adds an entry.
#[test]
fn a_duplicate_name_is_refused_and_an_unknown_parent_is_not_found() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    assert_eq!(
        ask(
            &mut ctx,
            &mut live,
            create("staging", MAIN_BRANCH, with_port(DASHED_LOG, port))
        )
        .status,
        200
    );
    let before = list(&mut ctx, &mut live);

    let duplicate = ask(
        &mut ctx,
        &mut live,
        create("staging", MAIN_BRANCH, with_port(PLUSSED_LOG, port)),
    );
    assert_eq!(duplicate.status, 400, "{}", duplicate.body);
    assert!(
        duplicate.body.contains("already exists"),
        "{}",
        duplicate.body
    );

    let orphan = ask(
        &mut ctx,
        &mut live,
        create("qa", "nowhere", with_port(DASHED_LOG, port)),
    );
    assert_eq!(orphan.status, 404, "{}", orphan.body);

    assert_eq!(list(&mut ctx, &mut live), before);
    assert_eq!(
        log_of(&live, "staging"),
        "ab",
        "the existing branch is untouched"
    );
}

/// A parent's later reload leaves its child's state and output as they were:
/// the child's entry is not the parent's, and no reload of the parent reads it.
#[test]
fn a_parents_reload_leaves_its_child_untouched() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    assert_eq!(
        ask(
            &mut ctx,
            &mut live,
            create("staging", MAIN_BRANCH, with_port(DASHED_LOG, port))
        )
        .status,
        200
    );
    let _ = exchange(&mut ctx, move || vec![http_post(port, "/set", "c")]);
    let staging_ops = live.held_operators("staging").expect("exists");

    let reply = ask(
        &mut ctx,
        &mut live,
        reload(MAIN_BRANCH, source("running-log-writer-edit", port)),
    );
    assert_eq!(reply.status, 200, "{}", reply.body);

    assert_eq!(log_of(&live, "staging"), "ab-c");
    let still: Vec<_> = live.held_operators("staging").expect("exists");
    assert_eq!(
        staging_ops.iter().map(|w| w.as_ptr()).collect::<Vec<_>>(),
        still.iter().map(|w| w.as_ptr()).collect::<Vec<_>>(),
        "the child holds exactly the operators it held"
    );
    assert!(
        staging_ops.iter().all(|w| w.upgrade().is_some()),
        "every operator the child holds is alive"
    );

    let replies = exchange(&mut ctx, move || {
        vec![
            http_post(port, "/set", "d"),
            http_get(port, "/get"),
            http_get(port, "/get2"),
        ]
    });
    assert_eq!(replies[1], "abc-d", "main folds `d` by its new rule");
    assert_eq!(replies[2], "ab-c-d", "staging folds `d` by its own rule");
}

/// A child's reload diffs against its own version and keeps its own
/// accumulated value, not its parent's.
#[test]
fn a_childs_reload_keeps_its_own_accumulated_value() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    assert_eq!(
        ask(
            &mut ctx,
            &mut live,
            create("staging", MAIN_BRANCH, with_port(DASHED_LOG, port))
        )
        .status,
        200
    );
    let _ = exchange(&mut ctx, move || vec![http_post(port, "/set", "c")]);
    assert_eq!(log_of(&live, MAIN_BRANCH), "abc");
    assert_eq!(log_of(&live, "staging"), "ab-c");

    let reply = ask(
        &mut ctx,
        &mut live,
        reload("staging", with_port(PLUSSED_LOG, port)),
    );
    assert_eq!(reply.status, 200, "{}", reply.body);
    assert_eq!(
        log_of(&live, "staging"),
        "ab-c",
        "seeded from its own value"
    );

    let replies = exchange(&mut ctx, move || {
        vec![
            http_post(port, "/set", "d"),
            http_get(port, "/get"),
            http_get(port, "/get2"),
        ]
    });
    assert_eq!(replies[1], "abcd");
    assert_eq!(replies[2], "ab-c+d", "its own history, then its new rule");
}

/// `/diff/<branch>` compares against the branch's own version, so the source a
/// branch already runs reads as no difference and its parent's source does
/// not.
#[test]
fn a_one_branch_diff_compares_against_that_branchs_version() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    assert_eq!(
        ask(
            &mut ctx,
            &mut live,
            create("staging", MAIN_BRANCH, with_port(DASHED_LOG, port))
        )
        .status,
        200
    );
    let own = ask(
        &mut ctx,
        &mut live,
        ControlRequest::Diff {
            branch: "staging".into(),
            code: with_port(DASHED_LOG, port),
            phase: Phase::AsOfRead,
        },
    );
    assert_eq!(own.status, 200);
    assert_eq!(own.body, "no difference at phase as-of-read\n");
    let parents = ask(
        &mut ctx,
        &mut live,
        ControlRequest::Diff {
            branch: "staging".into(),
            code: source("running-log", port),
            phase: Phase::AsOfRead,
        },
    );
    assert_eq!(parents.status, 200);
    assert!(parents.body.contains("divergence"), "{}", parents.body);
}

/// `/diff/<a>/<b>` reports how `b`'s current version differs from `a`'s,
/// changes nothing, and answers 404 for a name the table does not hold.
#[test]
fn a_two_branch_diff_compares_current_versions() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    assert_eq!(
        ask(
            &mut ctx,
            &mut live,
            create("staging", MAIN_BRANCH, with_port(DASHED_LOG, port))
        )
        .status,
        200
    );
    let before = list(&mut ctx, &mut live);
    let diff = |from: &str, to: &str| ControlRequest::DiffBranches {
        from: from.into(),
        to: to.into(),
        phase: Phase::AsOfRead,
    };

    let across = ask(&mut ctx, &mut live, diff(MAIN_BRANCH, "staging"));
    assert_eq!(across.status, 200, "{}", across.body);
    assert!(across.body.contains("divergence"), "{}", across.body);
    let expected = live
        .diff_text(
            &ctx,
            MAIN_BRANCH,
            &with_port(DASHED_LOG, port),
            Phase::AsOfRead,
        )
        .expect("compiles")
        .diff;
    assert_eq!(
        across.body, expected,
        "the same difference `/diff/main` reports for staging's source"
    );

    let itself = ask(&mut ctx, &mut live, diff("staging", "staging"));
    assert_eq!(itself.body, "no difference at phase as-of-read\n");

    assert_eq!(
        ask(&mut ctx, &mut live, diff(MAIN_BRANCH, "nowhere")).status,
        404
    );
    assert_eq!(list(&mut ctx, &mut live), before, "asking changes nothing");
}

/// The version numbers and branch origin read back over `/branches`
/// and `/branch/<name>/info`: each reload raises only its own branch's number,
/// and a branch origin names the parent's version at creation even after
/// the parent has moved on.
#[test]
fn list_and_info_report_versions_and_origin() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    assert_eq!(
        ask(
            &mut ctx,
            &mut live,
            reload(MAIN_BRANCH, source("running-log-writer-edit", port))
        )
        .status,
        200
    );
    assert_eq!(
        ask(
            &mut ctx,
            &mut live,
            create("staging", MAIN_BRANCH, with_port(DASHED_LOG, port))
        )
        .status,
        200
    );
    assert_eq!(
        ask(
            &mut ctx,
            &mut live,
            reload(MAIN_BRANCH, source("running-log", port))
        )
        .status,
        200
    );
    assert_eq!(
        ask(
            &mut ctx,
            &mut live,
            reload("staging", with_port(PLUSSED_LOG, port))
        )
        .status,
        200
    );

    let rows: Vec<Vec<String>> = list(&mut ctx, &mut live)
        .lines()
        .map(|l| l.split('\t').map(str::to_string).collect())
        .collect();
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0][..3], ["main", "version=3", "from=-"]);
    assert_eq!(rows[1][..3], ["staging", "version=2", "from=main@2"]);
    for row in &rows {
        assert!(
            row[3].starts_with("operators=") && row[4].starts_with("shared="),
            "{row:?}"
        );
    }

    let info = ask(
        &mut ctx,
        &mut live,
        ControlRequest::Info {
            name: "staging".into(),
        },
    );
    assert_eq!(info.status, 200);
    let mut parts = info.body.splitn(3, "\n\n");
    let head = parts.next().unwrap();
    let versions = parts.next().unwrap();
    let body = parts.next().unwrap();
    assert!(
        head.starts_with("staging\tversion=2\tfrom=main@2\t"),
        "{head}"
    );
    let numbers: Vec<&str> = versions
        .lines()
        .map(|l| l.split('\t').next().unwrap())
        .collect();
    assert_eq!(numbers, ["1", "2"], "one line per version of the entry");
    assert!(
        versions.lines().all(|l| l.contains("\tkept=")),
        "{versions}"
    );
    assert_eq!(body, with_port(PLUSSED_LOG, port), "the current source");

    let main = ask(
        &mut ctx,
        &mut live,
        ControlRequest::Info {
            name: MAIN_BRANCH.into(),
        },
    );
    assert!(
        main.body.starts_with("main\tversion=3\tfrom=-\t"),
        "{}",
        main.body
    );
    let missing = ask(
        &mut ctx,
        &mut live,
        ControlRequest::Info {
            name: "nowhere".into(),
        },
    );
    assert_eq!(missing.status, 404);
}

/// Deleting a branch leaves a tombstone: the name answers 404 until recreated,
/// and the recreated branch continues the numbering, lists none of the
/// tombstone's versions, and records its own origin.
#[test]
fn a_recreated_name_continues_its_tombstones_numbering() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    assert_eq!(
        ask(
            &mut ctx,
            &mut live,
            create("staging", MAIN_BRANCH, with_port(DASHED_LOG, port))
        )
        .status,
        200
    );
    assert_eq!(
        ask(
            &mut ctx,
            &mut live,
            reload("staging", with_port(PLUSSED_LOG, port))
        )
        .status,
        200
    );

    let deleted = ask(
        &mut ctx,
        &mut live,
        ControlRequest::Delete {
            name: "staging".into(),
        },
    );
    assert_eq!(deleted.status, 200);
    assert_eq!(deleted.body, "deleted branch `staging`\n");
    assert!(!list(&mut ctx, &mut live).contains("staging"));
    assert_eq!(
        ask(
            &mut ctx,
            &mut live,
            reload("staging", with_port(DASHED_LOG, port))
        )
        .status,
        404,
        "a tombstoned name is one the table does not hold"
    );
    assert_eq!(
        ask(
            &mut ctx,
            &mut live,
            ControlRequest::Delete {
                name: "staging".into()
            }
        )
        .status,
        404
    );

    let recreated = ask(
        &mut ctx,
        &mut live,
        create("staging", MAIN_BRANCH, with_port(DASHED_LOG, port)),
    );
    assert_eq!(recreated.status, 200, "{}", recreated.body);
    assert!(
        recreated
            .body
            .starts_with("created `staging@3` from `main@1`"),
        "{}",
        recreated.body
    );
    let info = ask(
        &mut ctx,
        &mut live,
        ControlRequest::Info {
            name: "staging".into(),
        },
    );
    let versions = info.body.split("\n\n").nth(1).unwrap();
    assert_eq!(
        versions
            .lines()
            .map(|l| l.split('\t').next().unwrap())
            .collect::<Vec<_>>(),
        ["3"],
        "the tombstone's versions are not the new entry's"
    );
    assert_eq!(log_of(&live, "staging"), "ab", "forked afresh from main");
}

/// Deleting a branch frees the operators only it held and leaves every operator
/// another entry holds alive.
#[test]
fn deleting_a_branch_frees_only_what_no_other_entry_holds() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    let created = ask(
        &mut ctx,
        &mut live,
        create("staging", MAIN_BRANCH, with_port(DASHED_LOG, port)),
    );
    assert_eq!(created.status, 200, "{}", created.body);
    let held_by_main: Vec<_> = live.held_operators(MAIN_BRANCH).expect("exists");
    let held_by_staging: Vec<_> = live.held_operators("staging").expect("exists");
    let summary = &live.branches()[1];
    assert!(
        summary.shared > 0 && summary.shared < summary.operators,
        "staging shares some of main's operators and holds some of its own: {summary}"
    );

    let deleted = ask(
        &mut ctx,
        &mut live,
        ControlRequest::Delete {
            name: "staging".into(),
        },
    );
    assert_eq!(deleted.status, 200);
    assert!(held_by_main.iter().all(|w| w.upgrade().is_some()));
    for op in &held_by_staging {
        let mains = held_by_main.iter().any(|m| m.ptr_eq(op));
        assert_eq!(
            op.upgrade().is_some(),
            mains,
            "an operator outlives the deletion exactly when main holds it"
        );
    }
    assert_eq!(live.branches()[0].shared, 0, "main now shares nothing");
    let replies = exchange(&mut ctx, move || {
        vec![http_post(port, "/set", "c"), http_get(port, "/get")]
    });
    assert_eq!(replies, vec!["ok\n", "abc"], "main keeps serving");
}

/// The last branch in the table cannot be deleted; any other can, `main`
/// included, and a branch created from a deleted one keeps running and keeps
/// its origin.
#[test]
fn the_last_branch_cannot_be_deleted() {
    let (port, mut ctx, mut live) = running_log_with_ab();
    let last = ask(
        &mut ctx,
        &mut live,
        ControlRequest::Delete {
            name: MAIN_BRANCH.into(),
        },
    );
    assert_eq!(last.status, 400, "{}", last.body);
    assert!(last.body.contains("last branch"), "{}", last.body);

    assert_eq!(
        ask(
            &mut ctx,
            &mut live,
            create("staging", MAIN_BRANCH, with_port(DASHED_LOG, port))
        )
        .status,
        200
    );
    let get_status = |port: u16| {
        let response = raw_http_response(
            port,
            &format!("GET /get HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nConnection: close\r\n\r\n"),
        );
        response.lines().next().unwrap_or_default().to_string()
    };
    assert_eq!(
        exchange(&mut ctx, move || get_status(port)),
        "HTTP/1.1 200 OK",
        "main serves `/get` while it runs"
    );
    assert_eq!(
        ask(
            &mut ctx,
            &mut live,
            ControlRequest::Delete {
                name: MAIN_BRANCH.into()
            }
        )
        .status,
        200
    );
    assert!(
        get_status(port).starts_with("HTTP/1.1 404"),
        "no remaining branch binds `/get`, so the route is retired"
    );
    assert_eq!(
        list(&mut ctx, &mut live).lines().collect::<Vec<_>>(),
        [live.branches()[0].to_string()],
    );
    assert!(list(&mut ctx, &mut live).starts_with("staging\tversion=1\tfrom=main@1\t"));

    // A verb without a branch segment names `main`, so with `main` gone it
    // answers 404 rather than falling back to another branch.
    for request in [
        ControlRequest::Reload {
            branch: MAIN_BRANCH.into(),
            code: with_port(DASHED_LOG, port),
        },
        ControlRequest::Diff {
            branch: MAIN_BRANCH.into(),
            code: with_port(DASHED_LOG, port),
            phase: Phase::AsOfRead,
        },
        create("scratch", MAIN_BRANCH, with_port(DASHED_LOG, port)),
    ] {
        let reply = ask(&mut ctx, &mut live, request);
        assert_eq!(reply.status, 404, "{}", reply.body);
    }
    assert!(live.program(MAIN_BRANCH).is_none());

    let replies = exchange(&mut ctx, move || {
        vec![http_post(port, "/set", "c"), http_get(port, "/get2")]
    });
    assert_eq!(
        replies,
        vec!["ok\n", "ab-c"],
        "the child keeps running what it holds"
    );
    assert!(matches!(
        live.delete_branch(&mut ctx, "staging"),
        Err(BranchError::Refused(_))
    ));
}

/// A fold over `src()` whose program value is `x`.
const FOLD: &str = indoc! {r#"
    x := 0
    for i in src():
        x := x + i
    x
"#};

/// [`FOLD`] reading `src()` through a comprehension, which rebuilds the loop's
/// iteration while `x` carries.
const FOLD_VIA_VIEW: &str = indoc! {r#"
    x := 0
    for i in [j + 0 for j in src()]:
        x := x + i
    x
"#};

/// The same, through another comprehension, so a reload from [`FOLD_VIA_VIEW`]
/// rebuilds the iteration again. The comprehension scales each element by `10`,
/// so the folded value says which positions the installed version decided:
/// a carried `x` plus `10` times each element it folded.
const FOLD_VIA_OTHER_VIEW: &str = indoc! {r#"
    x := 0
    for i in [j * 10 for j in src()]:
        x := x + i
    x
"#};

/// A context with a test source `src` of integers registered.
fn with_src() -> (GlobalContext, Rc<RefCell<TestDataSource>>) {
    let mut ctx = GlobalContext::default();
    let src = Rc::new(RefCell::new(TestDataSource::new(
        "src",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    ctx.register_source(src.clone());
    (ctx, src)
}

fn add(src: &Rc<RefCell<TestDataSource>>, from: usize, values: &[i64]) {
    let rows: Vec<(Value, Value)> = values
        .iter()
        .enumerate()
        .map(|(i, v)| (Value::UInt(from + i), Value::Int(*v)))
        .collect();
    let mut src = src.borrow_mut();
    src.add_data(&rows);
    // Every position up to the last added is complete, which is what lets a
    // drive release the position it last decided.
    src.set_yield_predicate(Predicate::at_or_below(Value::UInt(from + values.len() - 1)));
}

/// Deliver and pull branch `name`'s `main` output until its fold settles.
fn pull(ctx: &mut GlobalContext, live: &mut LiveProgram, name: &str) {
    let producer = live
        .main_producer_mut(name)
        .expect("the program's value is `x`");
    pull_laps(ctx.scheduler(), &mut **producer, 8, |_| false);
}

fn x_of(live: &LiveProgram, name: &str) -> i64 {
    let state = live.held_state(name).expect("the branch exists");
    match state.iter().find(|(p, _)| p.to_string() == "`x`") {
        Some((_, Value::Int(n))) => *n,
        other => panic!("{name}'s `x` is an int, got {other:?}"),
    }
}

/// How the version that rebuilds `main`'s iteration a second time is installed.
#[derive(Clone, Copy)]
enum Install {
    /// As `main`'s next version.
    Reload,
    /// As a new branch created from `main`.
    Branch,
}

/// `main` folds `src()`, with or without a second branch reading `src()`
/// through a producer of its own that is never pulled. Then a version reading
/// `src()` through another rebuilt iteration is installed by `install`, one
/// more element arrives, and the installed version is pulled.
///
/// Returns the installed version's `x`, and what every producer on `src()` had
/// released just before the install.
fn fold_after(with_lagging_branch: bool, install: Install) -> (i64, Predicate) {
    let (mut ctx, src) = with_src();
    let mut live = LiveProgram::start_text(&mut ctx, FOLD, &no_main).expect("v1 compiles");
    add(&src, 0, &[1, 2]);
    pull(&mut ctx, &mut live, MAIN_BRANCH);
    assert_eq!(x_of(&live, MAIN_BRANCH), 3);

    if with_lagging_branch {
        live.create_branch_text(&mut ctx, "lagging", MAIN_BRANCH, FOLD_VIA_VIEW, &no_main)
            .expect("rebuilding the iteration is accepted");
    }
    add(&src, 2, &[4, 8]);
    pull(&mut ctx, &mut live, MAIN_BRANCH);
    assert_eq!(x_of(&live, MAIN_BRANCH), 15);
    let agreed = src.borrow().get_released_predicate();

    let installed = match install {
        Install::Reload => {
            live.reload_text(&mut ctx, MAIN_BRANCH, FOLD_VIA_OTHER_VIEW, &no_main)
                .expect("rebuilding the iteration is accepted");
            MAIN_BRANCH
        }
        Install::Branch => {
            live.create_branch_text(
                &mut ctx,
                "child",
                MAIN_BRANCH,
                FOLD_VIA_OTHER_VIEW,
                &no_main,
            )
            .expect("rebuilding the iteration is accepted");
            "child"
        }
    };
    add(&src, 4, &[16]);
    pull(&mut ctx, &mut live, installed);
    (x_of(&live, installed), agreed)
}

/// What [`fold_after`] folds: the carried `15` (`1 + 2 + 4 + 8`) plus `16`
/// through [`FOLD_VIA_OTHER_VIEW`], per
/// [`a_rebuilt_iteration_resumes_one_past_its_predecessors_last_position`].
/// Re-deciding `8` gives `255`, and dropping `15` and re-folding the source
/// from position 0 gives `310`.
const RESUMED_AT_16: i64 = 15 + 10 * 16;

/// Assert that a lagging second branch changes nothing the install folds.
///
/// Both runs are asserted against [`RESUMED_AT_16`]: the run without the second
/// branch as the baseline, and the run beside it as equal to that baseline.
fn assert_lag_changes_nothing(install: Install) {
    let (alone, agreed_alone) = fold_after(false, install);
    let (beside, agreed_beside) = fold_after(true, install);
    assert_ne!(
        agreed_beside, agreed_alone,
        "the second branch holds the agreement below where main's producers stopped"
    );
    assert_eq!(alone, RESUMED_AT_16, "the one-branch baseline");
    assert_eq!(
        beside, alone,
        "a second, lagging branch changes what the installed version folds"
    );
}

/// A version that rebuilds a loop's iteration over a source resumes one past the
/// last position its predecessor decided, whether a reload or branch-and-reload
/// installs it.
///
/// The predecessor's drive released `src()` through position 3, the last it
/// emitted, so the rebuilt iteration's new producer starts at position 4. The
/// store seeded with the carried `15` decides only `16`, and `x` is
/// [`RESUMED_AT_16`].
#[test]
fn a_rebuilt_iteration_resumes_one_past_its_predecessors_last_position() {
    assert_eq!(fold_after(false, Install::Reload).0, RESUMED_AT_16);
    assert_eq!(fold_after(false, Install::Branch).0, RESUMED_AT_16);
}

/// [`FOLD`] with an edited loop body, so a version built from it keeps `FOLD`'s
/// iteration and rebuilds its store.
const FOLD_TIMES_ONE: &str = indoc! {r#"
    x := 0
    for i in src():
        x := x + i * 1
    x
"#};

/// A second edit of [`FOLD`]'s loop body, so a reload from [`FOLD`] keeps the
/// iteration and rebuilds the store again.
const FOLD_PLUS_ZERO: &str = indoc! {r#"
    x := 0
    for i in src():
        x := x + i + 0
    x
"#};

/// `main` folds `1, 2`. With `with_lagging_branch`, a branch created from `main`
/// with [`FOLD_TIMES_ONE`] subscribes to `main`'s kept iteration and is never
/// pulled. `main` folds `4, 8`, reloads to [`FOLD_PLUS_ZERO`], which keeps the
/// iteration and rebuilds the store, and folds `16`. Returns `main`'s `x`, or
/// the reload's refusal.
fn reload_over_a_kept_iteration(with_lagging_branch: bool) -> Result<i64, String> {
    let (mut ctx, src) = with_src();
    let mut live = LiveProgram::start_text(&mut ctx, FOLD, &no_main).expect("v1 compiles");
    add(&src, 0, &[1, 2]);
    pull(&mut ctx, &mut live, MAIN_BRANCH);
    if with_lagging_branch {
        live.create_branch_text(&mut ctx, "lagging", MAIN_BRANCH, FOLD_TIMES_ONE, &no_main)
            .expect("a body edit is accepted");
    }
    add(&src, 2, &[4, 8]);
    pull(&mut ctx, &mut live, MAIN_BRANCH);
    assert_eq!(x_of(&live, MAIN_BRANCH), 15);
    live.reload_text(&mut ctx, MAIN_BRANCH, FOLD_PLUS_ZERO, &no_main)
        .map_err(|e| format!("{e:?}"))?;
    add(&src, 4, &[16]);
    pull(&mut ctx, &mut live, MAIN_BRANCH);
    Ok(x_of(&live, MAIN_BRANCH))
}

/// A reload that keeps an iteration another branch also reads, and has read
/// less of, is refused.
///
/// Without the lagging branch the reload is accepted and `x` is `31`
/// (`1 + 2 + 4 + 8 + 16`). With it, the rebuilt store would resume one past the
/// kept iteration's `FanOut::released_position`, which is read off the
/// intersection of every live slot's release, so the lagging branch's slot
/// would hold it at the position the branch was created at and `4` and `8`
/// would fold twice. `LiveProgram::check` refuses that reload instead
/// (`OperatorMap::disagreeing_kept_iterations`).
#[test]
fn a_reload_over_an_iteration_a_lagging_branch_reads_is_refused() {
    assert_eq!(reload_over_a_kept_iteration(false), Ok(31));
    let refusal = reload_over_a_kept_iteration(true).expect_err("refused");
    assert!(refusal.contains("fold elements twice"), "{refusal}");
}

/// [`FOLD`] with an edited program value and the same loop, so a branch built
/// from it keeps `FOLD`'s store.
const FOLD_VALUE_EDITED: &str = indoc! {r#"
    x := 0
    for i in src():
        x := x + i
    x + 0
"#};

/// [`FOLD_VALUE_EDITED`] folding ten times each element, so a reload from it
/// rebuilds the store and the store's value says which rule folded what.
const FOLD_VALUE_AND_BODY_EDITED: &str = indoc! {r#"
    x := 0
    for i in src():
        x := x + i * 10
    x + 0
"#};

/// A store kept at creation is shared: pulling one branch advances the value
/// both read. The first reload that rebuilds it gives the reloaded branch its
/// own store, seeded from the shared value, and the other branch keeps the
/// original.
#[test]
fn a_store_shared_at_creation_is_unshared_by_the_reload_that_rebuilds_it() {
    let (mut ctx, src) = with_src();
    let mut live = LiveProgram::start_text(&mut ctx, FOLD, &no_main).expect("v1 compiles");
    add(&src, 0, &[1, 2]);
    pull(&mut ctx, &mut live, MAIN_BRANCH);
    live.create_branch_text(&mut ctx, "child", MAIN_BRANCH, FOLD_VALUE_EDITED, &no_main)
        .expect("an edit outside the loop is accepted");

    add(&src, 2, &[4]);
    pull(&mut ctx, &mut live, MAIN_BRANCH);
    assert_eq!(x_of(&live, MAIN_BRANCH), 7);
    assert_eq!(x_of(&live, "child"), 7, "one store, run once for both");

    live.reload_text(&mut ctx, "child", FOLD_VALUE_AND_BODY_EDITED, &no_main)
        .expect("a body edit is accepted");
    add(&src, 3, &[8]);
    pull(&mut ctx, &mut live, MAIN_BRANCH);
    pull(&mut ctx, &mut live, "child");
    assert_eq!(
        x_of(&live, MAIN_BRANCH),
        7 + 8,
        "main keeps the original store"
    );
    assert_eq!(
        x_of(&live, "child"),
        7 + 80,
        "the child's store is its own, seeded from the shared `7`"
    );
}

/// `main@1` was installed by the process's first compile, which keeps
/// nothing, so `/branch/main/info` lists it as `kept=0/<bound>`.
#[test]
fn mains_first_version_keeps_nothing() {
    let (mut ctx, _src) = with_src();
    let live = LiveProgram::start_text(&mut ctx, FOLD, &no_main).expect("v1 compiles");
    let info = live.render_info(MAIN_BRANCH).expect("main exists");
    let versions = info.split("\n\n").nth(1).expect("a versions block");
    assert!(versions.starts_with("1\tkept=0/"), "{versions}");
    assert_eq!(versions.lines().count(), 1, "{versions}");
}

/// A reload's new producer starts where the reloaded branch's own producers
/// stopped, not at the source-wide agreement a lagging branch holds down.
///
/// The lagging branch is never pulled, so the agreement stays where it was
/// created, below `4` and `8`. Starting `main`'s replacement there would fold
/// both a second time on top of the `15` that already summarizes them.
#[test]
fn a_lagging_branch_does_not_make_a_reload_fold_twice() {
    assert_lag_changes_nothing(Install::Reload);
}

/// Branch-and-reload's new producers start where the parent's producers
/// stopped, for the same reason: the new branch forks `x` at `15`, and the
/// agreement a lagging sibling holds down is below the elements that summarizes.
#[test]
fn a_lagging_branch_does_not_make_a_new_branch_fold_twice() {
    assert_lag_changes_nothing(Install::Branch);
}

/// The binary's driver pulls every branch's `main` output, prints every branch
/// but the default one as `Got value from <branch>: …`, and exits once every
/// branch's `main` output has finished.
///
/// The branch is created after the first line has been answered, so its new
/// producer starts where `main`'s stopped: it transforms the second line and
/// never the first.
#[test]
fn the_driver_pulls_every_branch_and_exits_when_all_have_finished() {
    use std::io::Write;
    use std::time::Duration;

    let mut launched = launch_under_control("[\"A\" + line for line in stdin()]\n");
    let control = launched.control;
    let mut input = launched.input.take().expect("piped stdin");
    let reader = launched.reader.take().expect("reader thread");

    writeln!(input, "L1").expect("write");
    input.flush().expect("flush");
    launched.wait_for_output(&["AL1"], Duration::from_secs(10));

    let body = "[\"B\" + line for line in stdin()]\n";
    let reply = raw_http(
        control,
        &format!(
            "POST /branch/b HTTP/1.1\r\nHost: 127.0.0.1:{control}\r\nContent-Length: {}\r\n\
             Connection: close\r\n\r\n{body}",
            body.len()
        ),
    );
    assert!(reply.starts_with("created `b@1` from `main@1`"), "{reply}");

    writeln!(input, "L2").expect("write");
    input.flush().expect("flush");
    launched.wait_for_output(&["AL2", "BL2"], Duration::from_secs(10));
    drop(input);

    launched.program.wait_for_exit(Duration::from_secs(10));
    reader.join().expect("reader thread");
    let out = launched.collected.lock().unwrap().clone();
    let from_b: String = out
        .split("Got value")
        .filter(|chunk| chunk.starts_with(" from b:"))
        .collect();
    let from_main: String = out
        .split("Got value")
        .filter(|chunk| chunk.starts_with(':'))
        .collect();
    assert!(
        from_main.contains("AL1") && from_main.contains("AL2"),
        "{out}"
    );
    assert!(
        from_b.contains("BL2"),
        "the branch's value is labelled: {out}"
    );
    assert!(
        !out.contains("BL1"),
        "the branch starts where main stopped: {out}"
    );
    assert!(!from_main.contains("BL"), "{out}");
}
