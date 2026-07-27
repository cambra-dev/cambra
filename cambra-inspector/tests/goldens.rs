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

/// One corpus row: the fixture basename, the example-program basename, and the
/// optional fixture-slimming retention spec (`panes=…`, `links=none`) parsed
/// from the manifest. The retention is applied to the fresh `--dump-snapshot`
/// so a fresh dump byte-matches the (slimmed) committed fixture; the LIVE wire
/// is never slimmed (see `scripts/fixtures.manifest`).
struct CorpusEntry {
    fixture: String,
    example: String,
    /// `--panes` comma-list, or `None` for all panes.
    panes: Option<String>,
    /// `true` ⇒ pass `--elide-pane-links` (omit `paneLinks` from the fixture).
    elide_pane_links: bool,
}

impl CorpusEntry {
    /// The `--dump-snapshot` flags this row's retention spec implies (empty for
    /// a full-wire row). Shared by every fresh dump of a slimmed fixture so it
    /// stays byte-identical to the committed copy.
    fn dump_flags(&self) -> Vec<String> {
        let mut flags = Vec::new();
        if let Some(panes) = &self.panes {
            flags.push("--panes".to_string());
            flags.push(panes.clone());
        }
        if self.elide_pane_links {
            flags.push("--elide-pane-links".to_string());
        }
        flags
    }
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
/// shared with `regen-fixtures.sh`. Lines are
/// `<fixture> <example> [panes=<comma-list>|all] [links=all|none]`; `#`
/// comments and blank lines are skipped. The retention tokens are parsed with
/// the SAME grammar `regen-fixtures.sh` uses, so the two never disagree.
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
            let mut panes = None;
            let mut elide_pane_links = false;
            for tok in parts {
                match tok {
                    "panes=all" | "links=all" => {}
                    "links=none" => elide_pane_links = true,
                    _ if tok.starts_with("panes=") => {
                        panes = Some(tok["panes=".len()..].to_string());
                    }
                    _ => panic!("manifest line {l:?} has unknown retention token {tok:?}"),
                }
            }
            CorpusEntry {
                fixture: fixture.to_string(),
                example: example.to_string(),
                panes,
                elide_pane_links,
            }
        })
        .collect();
    assert!(!entries.is_empty(), "the fixture corpus must be non-empty");
    entries
}

/// Run `cambra-inspector <example>.chl --dump-snapshot [flags]` as a fresh
/// process and return its raw stdout. With `flags` = the row's retention this is
/// exactly what `regen-fixtures.sh` pipes into a fixture (before pretty-printing).
fn dump_with(example: &str, flags: &[String]) -> Vec<u8> {
    let prog = format!("cambra-inspector/examples/{example}.chl");
    let mut args = vec![prog, "--dump-snapshot".to_string()];
    args.extend(flags.iter().cloned());
    let output = Command::new(env!("CARGO_BIN_EXE_cambra-inspector"))
        .current_dir(repo_root())
        .args(&args)
        .output()
        .expect("the cambra-inspector binary spawns");
    assert!(
        output.status.success(),
        "--dump-snapshot failed for {example}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
}

/// A full-wire dump (no slimming flags) — the live payload shape. Used by the
/// structural assertions, which run against the whole `paneLinks` graph even
/// when the committed fixture elides it.
fn dump(example: &str) -> Vec<u8> {
    dump_with(example, &[])
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
        let flags = entry.dump_flags();
        let first = dump_with(&entry.example, &flags);
        let second = dump_with(&entry.example, &flags);
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

        // Apply the row's retention flags so a slimmed fixture's fresh dump
        // matches its (slimmed) committed copy byte-for-byte.
        let raw = dump_with(&entry.example, &entry.dump_flags());
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
/// `post-inference -> post-desugar` paneLinks window carries a genuine
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
        .find(|l| l["from"] == "post-inference" && l["to"] == "post-desugar")
        .expect("the post-inference -> post-desugar window is present");
    let edges = window["edges"].as_array().expect("edges is an array");
    assert!(
        edges.iter().any(|e| {
            let p = e.as_array().expect("edge is a pair");
            p[0].as_u64() != p[1].as_u64()
        }),
        "udf_fanout must yield a genuine (u != d) inline fan-out edge in window 2"
    );
}

/// Every `nodeId` in a stage's IR tree.
fn stage_node_ids(stage: &Value) -> std::collections::HashSet<u64> {
    fn walk(node: &Value, out: &mut std::collections::HashSet<u64>) {
        if let Some(id) = node["nodeId"].as_u64() {
            out.insert(id);
        }
        for c in node["children"].as_array().into_iter().flatten() {
            walk(&c["node"], out);
        }
    }
    let mut out = std::collections::HashSet::new();
    walk(&stage["ir"], &mut out);
    out
}

/// Dense-window sanity over a FULL (unpruned) dump's
/// `post-inference → post-desugar` window — the structural bug-catcher that
/// replaces the pinned edge bytes for the pane-slimmed fixtures (`txn_multi_read`,
/// `mutation_loop`, whose committed goldens elide `paneLinks`). Mirrors the
/// `udf_fanout` fan-out pattern, strengthened to the properties the pinned bytes
/// used to guarantee: (a) the window carries genuine non-identity edges, (b) some
/// upstream node fans out to ≥2 downstream nodes (the substitution copies these
/// programs were chosen to exercise), and (c) every edge endpoint is a live node
/// in its pane. Runs against the full dump precisely because the fixture no
/// longer ships the edges.
fn assert_dense_window_sanity(example: &str) {
    let raw = dump(example); // full wire — the slimmed fixture omits paneLinks
    let v: Value = serde_json::from_slice(&raw).expect("valid JSON");
    let stages = v["stages"].as_array().expect("stages is an array");
    let stage = |id: &str| {
        stages
            .iter()
            .find(|s| s["id"] == id)
            .unwrap_or_else(|| panic!("{example}: stage {id} present in the full dump"))
    };
    let up_ids = stage_node_ids(stage("post-inference"));
    let down_ids = stage_node_ids(stage("post-desugar"));

    let links = v["paneLinks"].as_array().expect("paneLinks is an array");
    let window = links
        .iter()
        .find(|l| l["from"] == "post-inference" && l["to"] == "post-desugar")
        .unwrap_or_else(|| {
            panic!("{example}: the post-inference → post-desugar window is present")
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
            "{example}: edge downstream {d} is a live post-desugar node"
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

/// `txn_multi_read` (pane-slimmed; its committed fixture omits `paneLinks`)
/// still exercises the dense desugar-window fan-out structurally.
#[test]
fn txn_multi_read_produces_dense_desugar_window() {
    assert_dense_window_sanity("txn_multi_read");
}

/// `mutation_loop` (pane-slimmed; its committed fixture omits `paneLinks`)
/// still exercises the dense desugar-window fan-out structurally.
#[test]
fn mutation_loop_produces_dense_desugar_window() {
    assert_dense_window_sanity("mutation_loop");
}
