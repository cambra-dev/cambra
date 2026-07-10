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
//! Three ratchets, coarsest backstop of the provenance test stack (semantic
//! unit tests state intent; the boundary invariants enforce error classes;
//! these catch everything-composed drift):
//! 1. every corpus dump is cross-process deterministic (two spawns,
//!    byte-identical) — the property the goldens depend on;
//! 2. every committed fixture equals a fresh dump of its program
//!    (content-level; the ci.sh `ci_fixtures` gate does the byte-level file
//!    diff through `regen-fixtures.sh`);
//! 3. the corpus programs still trigger the passes they were chosen to pin.

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
/// shared with `regen-fixtures.sh`. Lines are `<fixture> <example>`; `#`
/// comments and blank lines are skipped.
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
                "manifest line {l:?} has trailing fields"
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
/// return its raw stdout — exactly what `regen-fixtures.sh` pipes into a
/// fixture (before pretty-printing).
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
/// iteration, desugar's channel maps, `transact_phase::collect_txn_stores`)
/// or the dump process compiling more than one program.
#[test]
fn snapshot_dumps_are_cross_process_deterministic() {
    for entry in corpus() {
        let first = dump(&entry.example);
        let second = dump(&entry.example);
        if first != second {
            // Preserve both dumps for diffing before panicking.
            let dir = std::env::temp_dir();
            let a = dir.join(format!("{}.dump1.json", entry.example));
            let b = dir.join(format!("{}.dump2.json", entry.example));
            std::fs::write(&a, &first).expect("writing first dump");
            std::fs::write(&b, &second).expect("writing second dump");
            let diff_at = first
                .iter()
                .zip(second.iter())
                .position(|(x, y)| x != y)
                .unwrap_or_else(|| first.len().min(second.len()));
            panic!(
                "--dump-snapshot for {} is NOT cross-process deterministic \
                 (first difference at byte {diff_at}; dumps preserved at {} and {}). \
                 Golden fixtures cannot be blessed until the nondeterminism source \
                 is fixed — see the test doc comment for the first suspects.",
                entry.example,
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
/// `post-inference -> post-desugar` stageLinks window carries non-identity
/// (inline fan-out) edges. Guards against the corpus rotting into programs
/// that no longer trigger the pass they were chosen to pin.
#[test]
fn udf_fanout_corpus_program_produces_inline_fanout_edges() {
    let raw = dump("udf_fanout");
    let v: Value = serde_json::from_slice(&raw).expect("valid JSON");
    let links = v["stageLinks"].as_array().expect("stageLinks is an array");
    let window = links
        .iter()
        .find(|l| l["from"] == "post-inference" && l["to"] == "post-desugar")
        .expect("the post-inference -> post-desugar window is present");
    assert!(
        !window["edges"]
            .as_array()
            .expect("edges is an array")
            .is_empty(),
        "udf_fanout must yield non-empty inline fan-out edges in window 2"
    );
}
