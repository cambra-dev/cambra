//! The inspector under `--control`: the payload it serves follows `main`'s
//! version, per `src/inspector_model/design.md`, "A reload of main is followed".

use std::collections::HashSet;
use std::thread;
use std::time::{Duration, Instant};

use serde_json::Value;

use crate::harness::launch_under_control_with;
use crate::serving::{http_get, raw_http, reserve_test_port};

/// The served `/api/snapshot`, parsed.
fn snapshot(port: u16) -> Value {
    serde_json::from_str(&http_get(port, "/api/snapshot")).expect("the snapshot is JSON")
}

fn version(snapshot: &Value) -> u64 {
    snapshot["meta"]["version"]
        .as_u64()
        .expect("meta.version is a number")
}

/// Every node id of the operator pane.
fn operator_ids(snapshot: &Value) -> HashSet<u64> {
    let pane = snapshot["panes"]
        .as_array()
        .expect("panes")
        .iter()
        .find(|pane| pane["kind"] == "operators")
        .expect("an operator pane");
    pane["nodes"]
        .as_array()
        .expect("nodes")
        .iter()
        .map(|node| node["nodeId"].as_u64().expect("nodeId"))
        .collect()
}

/// Send `body` to `path` on the control port, and answer the reply's body.
fn control(port: u16, path: &str, body: &str) -> String {
    raw_http(
        port,
        &format!(
            "POST {path} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nContent-Length: {}\r\n\
             Connection: close\r\n\r\n{body}",
            body.len()
        ),
    )
}

/// The snapshot once it describes `want`, or a failure after five seconds.
///
/// Polled because the control port answers inside the driver's pass and the
/// payload is replaced right after it, so a request racing the reply can still
/// be served the version before.
fn snapshot_at(port: u16, want: u64) -> Value {
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        let served = snapshot(port);
        if version(&served) == want {
            return served;
        }
        assert!(
            Instant::now() < deadline,
            "the served payload stayed at version {} after `main` reached {want}",
            version(&served)
        );
        thread::sleep(Duration::from_millis(20));
    }
}

/// A reload of `main` replaces the served payload with the new version's, and
/// creating another branch does not.
#[test]
fn the_served_payload_follows_a_reload_of_main_and_no_other_branch() {
    let inspect = reserve_test_port();
    let launched = launch_under_control_with(
        "[\"A\" + line for line in stdin()]\n",
        &[format!("--inspect={inspect}")],
    );
    let deadline = Instant::now() + Duration::from_secs(10);
    while std::net::TcpStream::connect(("127.0.0.1", inspect)).is_err() {
        assert!(Instant::now() < deadline, "the inspector never opened");
        thread::sleep(Duration::from_millis(50));
    }

    let first = snapshot(inspect);
    assert_eq!(version(&first), 1, "a run starts at `main`'s first version");

    let created = control(
        launched.control,
        "/branch/b",
        "[\"B\" + line for line in stdin()]\n",
    );
    assert!(created.starts_with("created `b@1`"), "{created}");
    thread::sleep(Duration::from_millis(200));
    let after_branch = snapshot(inspect);
    assert_eq!(
        version(&after_branch),
        1,
        "another branch leaves the payload alone"
    );
    assert_eq!(operator_ids(&after_branch), operator_ids(&first));

    let reloaded = control(
        launched.control,
        "/reload",
        "[\"C\" + line for line in stdin()]\n",
    );
    assert!(reloaded.starts_with("reloaded"), "{reloaded}");
    let second = snapshot_at(inspect, 2);
    assert!(
        !operator_ids(&second).is_subset(&operator_ids(&first)),
        "the reload rebuilt an operator, so the new payload names an id the first did not",
    );
}
