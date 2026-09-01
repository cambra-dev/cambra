//! Golden-corpus tests over the real `--dump-snapshot` CLI (RT-1).
//!
//! The fixture corpus (`scripts/fixtures.manifest`, shared with
//! `regen-fixtures.sh`) maps committed frontend fixtures to example programs.
//! These tests spawn the actual `cambra-inspector` binary **once per program,
//! per dump** — a fresh process each time. That is not an incidental choice:
//! `NodeId`s come from a process-global counter, so only a single-compile
//! process reproduces a fixture's ids. An in-process compile inside this test
//! (or any multi-program process) starts from a counter another compile already
//! advanced and can never byte-match — which is also why `regen-fixtures.sh`
//! invokes the CLI once per fixture.
//!
//! Four ratchets, coarsest backstop of the provenance test stack (semantic
//! unit tests state intent; the boundary invariants enforce error classes;
//! these catch everything-composed drift):
//! 1. every corpus dump is cross-process deterministic (two spawns,
//!    byte-identical) — the property the goldens depend on;
//! 2. every committed fixture equals a fresh dump of its program
//!    (content-level; the ci.sh `ci_fixtures` gate does the byte-level file
//!    diff through `regen-fixtures.sh`);
//! 3. every committed fixture is a structurally-valid payload, not merely one
//!    that equals a fresh dump of itself;
//! 4. the corpus programs still trigger the passes they were chosen to pin.
//!
//! Two programs — `txn_multi_read` and `mutation_loop` — are in the corpus
//! without a committed fixture. Their payloads run to five figures of lines
//! each, which is a document nobody reads and a re-bless nobody can review, so
//! what they are here for is asserted structurally over a fresh dump instead:
//! the dense channelize window, and the `Transact`/`Letrec` rewrite tags that
//! reach the wire from no other program.

use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

/// One corpus row: the fixture basename and the example-program basename.
struct CorpusEntry {
    fixture: String,
    example: String,
}

/// The `cambra/` repo root (the parent of this crate's manifest dir) — the
/// working directory `regen-fixtures.sh` runs from. Dumps spawn from here with
/// repo-root-relative program paths so `source.name` in the payload matches the
/// fixtures byte-for-byte.
fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crate dir has a parent")
        .to_path_buf()
}

/// Parse `scripts/fixtures.manifest` — the corpus's single source of truth,
/// shared with `regen-fixtures.sh`. A row is `<fixture> <example>`; `#`
/// comments and blank lines are skipped. Two words and nothing else, so the
/// shell parser and this one have no grammar to disagree about.
fn corpus() -> Vec<CorpusEntry> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("scripts/fixtures.manifest");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("reading {}: {e}", path.display()));
    let entries: Vec<CorpusEntry> = text
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(|l| {
            let mut parts = l.split_whitespace();
            let fixture = parts.next().expect("manifest line has a fixture name");
            let example = parts
                .next()
                .unwrap_or_else(|| panic!("manifest line {l:?} lacks an example name"));
            assert!(
                parts.next().is_none(),
                "manifest line {l:?} has more than a fixture and an example"
            );
            CorpusEntry {
                fixture: fixture.to_string(),
                example: example.to_string(),
            }
        })
        .collect();
    assert!(!entries.is_empty(), "the fixture corpus must be non-empty");
    entries
}

/// Run `cambra-inspector <example>.chl --dump-snapshot` as a fresh process and
/// return its raw stdout — exactly what `regen-fixtures.sh` writes to a fixture.
fn dump(example: &str) -> Vec<u8> {
    let prog = format!("cambra-inspector/examples/{example}.chl");
    let output = Command::new(env!("CARGO_BIN_EXE_cambra-inspector"))
        .current_dir(repo_root())
        .args([prog.as_str(), "--dump-snapshot"])
        .output()
        .expect("the cambra-inspector binary spawns");
    assert!(
        output.status.success(),
        "--dump-snapshot failed for {example}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
}

/// The determinism self-check the golden fixtures depend on: dumping the same
/// program from two **separate process invocations** yields byte-identical
/// output, for every corpus program.
///
/// If this fires, the committed fixtures cannot be trusted as goldens — the
/// first suspects are hash-iteration-ordered node minting (Rust's default
/// hasher is randomly seeded per process; candidates: mono's specialization
/// iteration, channelize's channel maps, `transact_phase::collect_txn_stores`)
/// or the dump process compiling more than one program.
#[test]
fn snapshot_dumps_are_cross_process_deterministic() {
    for entry in corpus() {
        assert_dumps_agree(&entry.example);
    }
    // The two programs whose payloads are too large to commit (see
    // `assert_dense_window_sanity`) are the heaviest synthesis in the corpus and
    // so the likeliest to expose hash-iteration-ordered minting — exactly what
    // this test exists to catch. They carry no fixture, so the manifest loop
    // above does not reach them.
    assert_dumps_agree("txn_multi_read");
    assert_dumps_agree("mutation_loop");
}

/// Two spawns of one program produce byte-identical dumps.
fn assert_dumps_agree(example: &str) {
    {
        let first = dump(example);
        let second = dump(example);
        if first != second {
            // Preserve both dumps for diffing before panicking.
            let dir = std::env::temp_dir();
            let a = dir.join(format!("{example}.dump1.json"));
            let b = dir.join(format!("{example}.dump2.json"));
            std::fs::write(&a, &first).expect("writing first dump");
            std::fs::write(&b, &second).expect("writing second dump");
            let diff_at = first
                .iter()
                .zip(second.iter())
                .position(|(x, y)| x != y)
                .unwrap_or_else(|| first.len().min(second.len()));
            panic!(
                "--dump-snapshot for {example} is NOT cross-process deterministic \
                 (first difference at byte {diff_at}; dumps preserved at {} and {}). \
                 Golden fixtures cannot be blessed until the nondeterminism source \
                 is fixed — see `snapshot_dumps_are_cross_process_deterministic` \
                 for the first suspects.",
                a.display(),
                b.display()
            );
        }
    }
}

/// A short single-line rendering of a JSON value for drift messages, truncated
/// so a mismatch inside a large subtree stays readable.
fn excerpt(v: &Value) -> String {
    let s = v.to_string();
    match s.char_indices().nth(120) {
        Some((i, _)) => format!("{}…", &s[..i]),
        None => s,
    }
}

/// The first differing JSON path between two values, as
/// `(path, lhs-excerpt, rhs-excerpt)` — the targeted diagnostic an
/// `assert_eq!` over two multi-hundred-KB canonical strings cannot give (it
/// dumps both bodies wholesale, burying which key actually drifted).
fn first_json_difference(lhs: &Value, rhs: &Value, path: &str) -> Option<(String, String, String)> {
    match (lhs, rhs) {
        (Value::Object(a), Value::Object(b)) => {
            let mut keys: Vec<&String> = a.keys().chain(b.keys()).collect();
            keys.sort();
            keys.dedup();
            for k in keys {
                let sub = format!("{path}.{k}");
                match (a.get(k), b.get(k)) {
                    (Some(x), Some(y)) => {
                        if let Some(d) = first_json_difference(x, y, &sub) {
                            return Some(d);
                        }
                    }
                    (Some(x), None) => return Some((sub, excerpt(x), "<absent>".into())),
                    (None, Some(y)) => return Some((sub, "<absent>".into(), excerpt(y))),
                    (None, None) => unreachable!("key came from one of the two maps"),
                }
            }
            None
        }
        (Value::Array(a), Value::Array(b)) => {
            for (i, (x, y)) in a.iter().zip(b.iter()).enumerate() {
                if let Some(d) = first_json_difference(x, y, &format!("{path}[{i}]")) {
                    return Some(d);
                }
            }
            if a.len() != b.len() {
                let i = a.len().min(b.len());
                let side = |arr: &[Value]| arr.get(i).map_or("<absent>".into(), excerpt);
                return Some((format!("{path}[{i}]"), side(a), side(b)));
            }
            None
        }
        _ => (lhs != rhs).then(|| (path.to_string(), excerpt(lhs), excerpt(rhs))),
    }
}

/// RT-1a — the golden ratchet: every committed fixture equals a fresh dump of
/// its example program. Compared at the JSON-content level (both sides parsed)
/// so the comparison is independent of the pretty-printer `regen-fixtures.sh`
/// pipes through; the ci.sh `ci_fixtures` gate covers the literal file bytes by
/// regenerating through the same script and diffing. On failure the message
/// names the first drifted JSON path and the fix path is its one command.
#[test]
fn committed_fixtures_match_fresh_dumps() {
    let fixtures_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("web/src/__fixtures__");
    for entry in corpus() {
        let fixture_path = fixtures_dir.join(format!("{}.snapshot.json", entry.fixture));
        let committed = std::fs::read_to_string(&fixture_path).unwrap_or_else(|e| {
            panic!(
                "reading committed fixture {} for corpus entry `{}`: {e}. \
                 Every manifest entry must have a committed fixture — run \
                 cambra-inspector/scripts/regen-fixtures.sh and commit the result.",
                fixture_path.display(),
                entry.example
            )
        });
        let committed: Value = serde_json::from_str(&committed)
            .unwrap_or_else(|e| panic!("{} is valid JSON: {e}", fixture_path.display()));

        let raw = dump(&entry.example);
        let fresh: Value = serde_json::from_slice(&raw)
            .unwrap_or_else(|e| panic!("dump for {} is valid JSON: {e}", entry.example));

        if committed != fresh {
            // Preserve the fresh dump for offline diffing before panicking.
            let preserved =
                std::env::temp_dir().join(format!("{}.fresh.snapshot.json", entry.fixture));
            std::fs::write(&preserved, &raw).expect("writing fresh dump");
            let (path, committed_at, fresh_at) = first_json_difference(&committed, &fresh, "$")
                .expect("values are unequal, so a structural difference exists");
            panic!(
                "fixture drift: {}.snapshot.json differs from a fresh dump of \
                 examples/{}.chl. First difference at {path}:\n  committed: {committed_at}\n  \
                 fresh:     {fresh_at}\nFresh dump preserved at {}. If the wire change is \
                 intended, re-bless via cambra-inspector/scripts/regen-fixtures.sh and \
                 commit the diff.",
                entry.fixture,
                entry.example,
                preserved.display()
            );
        }
    }
}

/// The corpus programs added for the recorder-fixes batch actually exercise
/// what they were added for, at the wire level: the UDF fan-out program's
/// `post-inference -> post-channelize` paneLinks window carries a genuine
/// non-identity (`u != d`) inline fan-out edge — not just the dense self-edges.
/// Guards against the corpus rotting into programs that no longer trigger the
/// pass they were chosen to pin.
#[test]
fn udf_fanout_corpus_program_produces_inline_fanout_edges() {
    let raw = dump("udf_fanout");
    let v: Value = serde_json::from_slice(&raw).expect("valid JSON");
    let links = v["paneLinks"].as_array().expect("paneLinks is an array");
    let window = links
        .iter()
        .find(|l| l["from"] == "post-inference" && l["to"] == "post-channelize")
        .expect("the post-inference -> post-channelize window is present");
    let edges = window["edges"].as_array().expect("edges is an array");
    assert!(
        edges.iter().any(|e| {
            let p = e.as_array().expect("edge is a pair");
            p[0].as_u64() != p[1].as_u64()
        }),
        "udf_fanout must yield a genuine (u != d) inline fan-out edge in window 2"
    );
}

/// Every `nodeId` of a pane — its shipped node table, read directly.
fn pane_node_ids(pane: &Value) -> std::collections::HashSet<u64> {
    pane["nodes"]
        .as_array()
        .expect("nodes is an array")
        .iter()
        .map(|n| n["nodeId"].as_u64().expect("nodeId is a number"))
        .collect()
}

/// Dense-window sanity over a dump's `post-inference → post-channelize` window
/// — the structural bug-catcher that stands in for a committed fixture on the
/// two programs whose payloads are too large to commit (`txn_multi_read`,
/// `mutation_loop`). Mirrors the `udf_fanout` fan-out pattern, strengthened to
/// what a pinned document would have guaranteed: (a) the window carries genuine
/// non-identity edges, (b) some upstream node fans out to ≥2 downstream nodes
/// (the substitution copies these programs were chosen to exercise), and (c)
/// every edge endpoint is a live node in its pane.
fn assert_dense_window_sanity(example: &str) {
    let raw = dump(example); // full wire — the slimmed fixture omits paneLinks
    let v: Value = serde_json::from_slice(&raw).expect("valid JSON");
    let panes = v["panes"].as_array().expect("panes is an array");
    let pane = |id: &str| {
        panes
            .iter()
            .find(|s| s["id"] == id)
            .unwrap_or_else(|| panic!("{example}: pane {id} present in the full dump"))
    };
    let up_ids = pane_node_ids(pane("post-inference"));
    let down_ids = pane_node_ids(pane("post-channelize"));

    let links = v["paneLinks"].as_array().expect("paneLinks is an array");
    let window = links
        .iter()
        .find(|l| l["from"] == "post-inference" && l["to"] == "post-channelize")
        .unwrap_or_else(|| {
            panic!("{example}: the post-inference → post-channelize window is present")
        });
    let edges = window["edges"].as_array().expect("edges is an array");

    let mut non_self = 0usize;
    let mut fanout: std::collections::HashMap<u64, usize> = std::collections::HashMap::new();
    for e in edges {
        let p = e.as_array().expect("edge is a pair");
        let u = p[0].as_u64().expect("upstream id");
        let d = p[1].as_u64().expect("downstream id");
        assert!(
            up_ids.contains(&u),
            "{example}: edge upstream {u} is a live post-inference node"
        );
        assert!(
            down_ids.contains(&d),
            "{example}: edge downstream {d} is a live post-channelize node"
        );
        if u != d {
            non_self += 1;
        }
        *fanout.entry(u).or_default() += 1;
    }
    assert!(
        non_self > 0,
        "{example}: window 2 must carry ≥1 genuine (u != d) edge"
    );
    assert!(
        fanout.values().any(|&c| c >= 2),
        "{example}: some upstream node must fan out to ≥2 downstream nodes"
    );
}

/// `txn_multi_read` (no committed fixture) exercises the dense channelize-window
/// fan-out structurally.
#[test]
fn txn_multi_read_produces_dense_channelize_window() {
    assert_dense_window_sanity("txn_multi_read");
}

/// `mutation_loop` (no committed fixture) exercises the dense channelize-window
/// fan-out structurally.
#[test]
fn mutation_loop_produces_dense_channelize_window() {
    assert_dense_window_sanity("mutation_loop");
}

/// Every `rewritten.via` a pane of `dump` carries.
fn dump_vias(example: &str) -> std::collections::HashSet<String> {
    let raw = dump(example);
    let v: Value = serde_json::from_slice(&raw).expect("valid JSON");
    let mut out = std::collections::HashSet::new();
    for pane in v["panes"].as_array().expect("panes is an array") {
        for node in pane["nodes"].as_array().expect("nodes is an array") {
            if let Some(via) = node["rewritten"]["via"].as_str() {
                out.insert(via.to_string());
            }
        }
    }
    out
}

/// The two mutability-elimination phases reach the wire, and only these two
/// programs put them there.
///
/// Both validators pin a `rewritten.via` allowlist. An allowlist rejects a
/// *new* via on its own, but says nothing when a pinned entry stops being
/// produced — so a `Transact` or `Letrec` that vanished from the wire, or was
/// renamed, would leave a dead entry in two vocabularies and fail nothing.
/// Asserting presence is what an allowlist cannot do.
#[test]
fn the_recurrence_phases_reach_the_wire() {
    let txn = dump_vias("txn_multi_read");
    assert!(
        txn.contains("Transact"),
        "txn_multi_read is the only program that tags nodes `Transact`; got {txn:?}"
    );
    let loop_vias = dump_vias("mutation_loop");
    assert!(
        loop_vias.contains("Letrec"),
        "mutation_loop is the only program that tags nodes `Letrec`; got {loop_vias:?}"
    );
}

/// RT-1b — every committed fixture is a structurally-valid payload.
///
/// The byte comparison above cannot see a *wrongly built* dump: a bad dump
/// equals a fresh copy of itself, so committed == fresh holds and the fixture
/// still reaches the frontend. This is the check that reads the document
/// instead of comparing it, and it runs here rather than in the lib's own tests
/// because these files are what the frontend actually loads.
#[test]
fn committed_fixtures_are_structurally_valid() {
    let fixtures_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("web/src/__fixtures__");
    for entry in corpus() {
        let path = fixtures_dir.join(format!("{}.snapshot.json", entry.fixture));
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("reading {}: {e}", path.display()));
        let v: Value = serde_json::from_str(&text)
            .unwrap_or_else(|e| panic!("{} is valid JSON: {e}", path.display()));
        if v["meta"]["payloadKind"] == "failed" {
            cambra_inspector::wire_check::assert_degraded_snapshot_shape(&v);
        } else {
            cambra_inspector::wire_check::assert_snapshot_shape(&v);
        }
    }
}
