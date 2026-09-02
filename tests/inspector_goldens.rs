//! Golden-corpus tests over the real `cambra --dump-snapshot` CLI.
//!
//! The fixture corpus (`cambra-inspector/scripts/fixtures.manifest`, shared with
//! `regen-fixtures.sh`) maps committed frontend fixtures to gallery programs
//! under `tests/programs/`. These tests spawn the actual `cambra` binary **once
//! per program, per dump** — a fresh process each time. That is not an
//! incidental choice: `NodeId`s come from a process-global counter, so only a
//! single-compile process reproduces a fixture's ids. An in-process compile
//! inside this test (or any multi-program process) starts from a counter another
//! compile already advanced and can never byte-match — which is also why
//! `regen-fixtures.sh` invokes the CLI once per fixture.
//!
//! Six ratchets, coarsest backstop of the provenance test stack (semantic unit
//! tests state intent; the boundary invariants enforce error classes; these
//! catch everything-composed drift):
//! 1. every corpus dump is cross-process deterministic (two spawns,
//!    byte-identical) — the property the goldens depend on;
//! 2. every committed fixture equals a fresh dump of its program
//!    (content-level; the ci.sh `ci_fixtures` gate does the byte-level file
//!    diff through `regen-fixtures.sh`);
//! 3. every committed fixture is a structurally-valid payload, not merely one
//!    that equals a fresh dump of itself;
//! 4. the corpus programs still trigger the passes they were chosen to pin;
//! 5. **every** program in the gallery — not just the five with fixtures —
//!    produces a payload the wire validator accepts;
//! 6. two compiles of one program in one process differ in id numbering and
//!    nothing else.
//!
//! Ratchets 5 and 6 are what keeps the corpus bounded. Pinned bytes are the
//! narrowest of the six ratchets and the only one that costs a re-bless, so a
//! program added for backend coverage belongs in ratchet 5, which reads every
//! gallery source and commits nothing.
//!
//! Three programs — `txn_multi_read`, `for_accumulator` and `inner_join` — are
//! in the corpus without a committed fixture. Their payloads run to five figures
//! of lines each, which is a document nobody reads and a re-bless nobody can
//! review, so what they are here for is asserted structurally over a fresh dump
//! instead: the dense channelize window, the `Transact`/`Letrec` rewrite tags
//! that reach the wire, and the multi-span operator node that only a join
//! produces.

use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

/// One corpus row: the fixture basename and the example-program basename.
struct CorpusEntry {
    fixture: String,
    example: String,
}

/// The `cambra/` repo root — the working directory `regen-fixtures.sh` runs
/// from. Dumps spawn from here with repo-root-relative program paths so
/// `source.name` in the payload matches the fixtures byte-for-byte.
fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).to_path_buf()
}

/// A gallery program's source path, relative to the repo root — the path a
/// fixture's `source.name` records.
fn program_path(example: &str) -> String {
    format!("tests/programs/{example}/program.cambra")
}

/// Parse `scripts/fixtures.manifest` — the corpus's single source of truth,
/// shared with `regen-fixtures.sh`. A row is `<fixture> <example>`; `#`
/// comments and blank lines are skipped. Two words and nothing else, so the
/// shell parser and this one have no grammar to disagree about.
fn corpus() -> Vec<CorpusEntry> {
    let path = repo_root().join("cambra-inspector/scripts/fixtures.manifest");
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

/// Run `cambra <program> --dump-snapshot` as a fresh process and return its raw
/// stdout — exactly what `regen-fixtures.sh` writes to a fixture.
fn dump(example: &str) -> Vec<u8> {
    let prog = program_path(example);
    let output = Command::new(env!("CARGO_BIN_EXE_cambra"))
        .current_dir(repo_root())
        .args([prog.as_str(), "--dump-snapshot"])
        .output()
        .expect("the cambra binary spawns");
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
    assert_dumps_agree("for_accumulator");
    // A hash join mints from keyed lookups, which is the likeliest remaining
    // home for hash-iteration-ordered minting and is what this test exists to
    // catch. No fixture: the payload is ~430KB, several times the largest one
    // committed (see `fixtures.manifest`).
    assert_dumps_agree("inner_join");
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

/// A fresh join dump is a structurally-valid payload.
///
/// `committed_fixtures_are_structurally_valid` runs `wire_check` over the
/// committed corpus, and no program in it produces an operator node with more
/// than one span — so the span-ordering assertion inside `assert_spans` had
/// never run on a vector it could reject. It shipped mis-ordered spans through
/// every payload the suite built, and the frontend's mirror of this validator
/// was what finally rejected one.
///
/// Ratchet 5 sweeps this program too, so the assertion is not the only one that
/// reaches it. This test is what names the shape: `inner_join` is the gallery's
/// only program whose planner attributes one operator to several source spans,
/// and a sweep that walks every program reports a validator failure without
/// saying which program was the one that mattered.
#[test]
fn a_join_dump_is_structurally_valid() {
    let bytes = dump("inner_join");
    let v: Value = serde_json::from_slice(&bytes).expect("the dump is valid JSON");
    assert_eq!(v["meta"]["payloadKind"], "program", "inner_join compiles");
    cambra::inspector_server::wire_check::assert_snapshot_shape(&v);
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
    let fixtures_dir = repo_root().join("cambra-inspector/web/src/__fixtures__");
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
                 tests/programs/{}/program.cambra. First difference at {path}:\n  committed: {committed_at}\n  \
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

/// The corpus programs still exercise what they were chosen for, at the wire
/// level: `polymorphic`'s `post-inference -> post-channelize` paneLinks window
/// carries a genuine non-identity (`u != d`) fan-out edge — not just the dense
/// self-edges. Guards against the corpus rotting into programs that no longer
/// trigger the pass they were chosen to pin.
#[test]
fn polymorphic_corpus_program_produces_fanout_edges() {
    let raw = dump("polymorphic");
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
        "polymorphic must yield a genuine (u != d) fan-out edge in window 2"
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
/// `for_accumulator`). Mirrors the `polymorphic` fan-out pattern, strengthened to
/// what a pinned document would have guaranteed: (a) the window carries genuine
/// non-identity edges, (b) some upstream node fans out to ≥2 downstream nodes
/// (the substitution copies these programs were chosen to exercise), and (c)
/// every edge endpoint is a live node in its pane.
fn assert_dense_window_sanity(example: &str) {
    let raw = dump(example);
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

/// `for_accumulator` (no committed fixture) exercises the dense
/// channelize-window fan-out structurally.
#[test]
fn for_accumulator_produces_dense_channelize_window() {
    assert_dense_window_sanity("for_accumulator");
}

/// The operator-pane edge shapes only a store produces, over a fresh dump.
///
/// A store is the one construct that closes a cycle and wires an input late, so
/// `feedback` and `deferred` edges exist nowhere else — and neither does a
/// store-keyed edge role. Every committed fixture carries `value` and `share`
/// alone. The renderer draws feedback and deferred each their own way, so
/// without this nothing checks that either reaches the wire at all.
///
/// Structural rather than a fixture, matching the two window checks above: a
/// transaction program's operator pane is 77 nodes, and pinning its bytes would
/// re-bless on every change to how a store is built.
fn assert_store_edge_shapes(example: &str) {
    let raw = dump(example);
    let v: Value = serde_json::from_slice(&raw).expect("valid JSON");
    let pane = v["panes"]
        .as_array()
        .expect("panes is an array")
        .iter()
        .find(|p| p["kind"] == "operators")
        .unwrap_or_else(|| panic!("{example}: no operator pane"));

    let mut kinds: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut deferred = 0usize;
    let mut store_keyed = 0usize;
    for node in pane["nodes"].as_array().expect("nodes is an array") {
        for edge in node["inputs"].as_array().expect("inputs is an array") {
            if let Some(kind) = edge["kind"].as_str() {
                kinds.insert(kind.to_string());
            }
            if edge["deferred"] == Value::Bool(true) {
                deferred += 1;
            }
            // A store key is rendered as its `Value`, which quotes a string —
            // the one edge role that is neither a field name nor a position.
            if let Some(role) = edge["role"].as_str()
                && role.starts_with('"')
            {
                store_keyed += 1;
            }
        }
    }

    for want in ["value", "share", "feedback"] {
        assert!(
            kinds.contains(want),
            "{example}: the operator pane carries no {want} edge; got {kinds:?}"
        );
    }
    assert!(
        deferred > 0,
        "{example}: no edge is deferred, so the `CycleSlot` wiring reached no edge"
    );
    assert!(
        store_keyed > 0,
        "{example}: no edge carries a store-keyed role"
    );
}

/// `txn_multi_read` (no committed fixture) exercises the store-only operator
/// edge shapes.
#[test]
fn txn_multi_read_produces_store_edge_shapes() {
    assert_store_edge_shapes("txn_multi_read");
}

/// `for_accumulator` (no committed fixture) exercises the store-only operator
/// edge shapes.
#[test]
fn for_accumulator_produces_store_edge_shapes() {
    assert_store_edge_shapes("for_accumulator");
}

/// **One source node per registered source, attributed to every read site.**
///
/// The shape decision the source half of the graph rests on: a source read from
/// several expressions is one node several readers point at, never a node
/// duplicated per reader — sharing is reified everywhere else in this graph and
/// the boundary is no exception.
///
/// The span count is the assertion that matters. A source node cannot be minted
/// at the first read site, because its row names every site that reads it and a
/// row's parents are fixed when its recording closes; `materialize_sources`
/// mints once the walk is done, for that reason alone. Minting at the first read
/// site instead would look correct, would keep the node count right, and would
/// silently attribute the source to one of its readers. Only the span count
/// catches it.
#[test]
fn a_source_read_twice_is_one_node_attributed_to_both_reads() {
    let raw = dump("source_shared");
    let v: Value = serde_json::from_slice(&raw).expect("valid JSON");
    let pane = v["panes"]
        .as_array()
        .expect("panes is an array")
        .iter()
        .find(|p| p["kind"] == "operators")
        .expect("source_shared has an operator pane");

    let sources: Vec<&Value> = pane["nodes"]
        .as_array()
        .expect("nodes is an array")
        .iter()
        .filter(|n| n["role"] == "source")
        .collect();
    assert_eq!(
        sources.len(),
        1,
        "source_shared reads one source, so the graph holds one source node; got {}",
        sources.len()
    );
    let source = sources[0];
    let source_id = source["nodeId"].as_u64().expect("nodeId is a number");

    let readers: Vec<&Value> = pane["nodes"]
        .as_array()
        .expect("nodes is an array")
        .iter()
        .filter(|n| {
            n["inputs"]
                .as_array()
                .is_some_and(|es| es.iter().any(|e| e["id"].as_u64() == Some(source_id)))
        })
        .collect();
    assert!(
        readers.len() >= 2,
        "source_shared reads stdin twice, so at least two operators read the source node; got {}",
        readers.len()
    );

    for reader in &readers {
        for edge in reader["inputs"].as_array().expect("inputs is an array") {
            if edge["id"].as_u64() == Some(source_id) {
                assert_eq!(
                    edge["kind"], "share",
                    "a source has no single owner, so a read of it is a share edge"
                );
            }
        }
    }

    let spans = source["spans"].as_array().expect("spans is an array");
    assert!(
        spans.len() >= readers.len(),
        "the source node carries {} span(s) for {} read site(s): it was minted against one \
         read rather than after the walk, so `also_consumes` reached none of the others",
        spans.len(),
        readers.len()
    );
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

/// The two mutability-elimination phases reach the wire.
///
/// Both validators pin a `rewritten.via` allowlist. An allowlist rejects a new
/// via on its own, but says nothing when a pinned entry stops being produced, so
/// a `Transact` or `Letrec` that vanished from the wire, or was renamed, would
/// leave a dead entry in two vocabularies and fail nothing. Asserting presence is
/// what an allowlist cannot do.
#[test]
fn the_recurrence_phases_reach_the_wire() {
    let txn = dump_vias("txn_multi_read");
    assert!(
        txn.contains("Transact"),
        "txn_multi_read is the only program that tags nodes `Transact`; got {txn:?}"
    );
    let loop_vias = dump_vias("for_accumulator");
    assert!(
        loop_vias.contains("Letrec"),
        "for_accumulator tags nodes `Letrec`; got {loop_vias:?}"
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
    let fixtures_dir = repo_root().join("cambra-inspector/web/src/__fixtures__");
    for entry in corpus() {
        let path = fixtures_dir.join(format!("{}.snapshot.json", entry.fixture));
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("reading {}: {e}", path.display()));
        let v: Value = serde_json::from_str(&text)
            .unwrap_or_else(|e| panic!("{} is valid JSON: {e}", path.display()));
        if v["meta"]["payloadKind"] == "failed" {
            cambra::inspector_server::wire_check::assert_degraded_snapshot_shape(&v);
        } else {
            cambra::inspector_server::wire_check::assert_snapshot_shape(&v);
        }
    }
}

// ---------------------------------------------------------------------------
// Ratchet 5: the whole gallery, validated
// ---------------------------------------------------------------------------

/// The gallery sources whose `--dump-snapshot` currently **panics**, so the
/// sweep below has no payload to validate.
///
/// A pinned list rather than a silent skip, in both directions: a program that
/// starts dumping must leave this list (the sweep says so), and a program that
/// stops dumping cannot join it without an edit. `defer_generators` is the
/// gallery's own `expect_compile_error` case for the same failure — a `zip` of
/// two generators typed as a compute function where the letrec binder wants a
/// data collection.
const DUMP_PANICS: &[&str] = &["defer_generators"];

/// Every `*.cambra` source under `tests/programs/`, as (program-directory name,
/// repo-root-relative path). Walks the directory rather than reading a list:
/// the gallery's membership is the directory, and a source no test names is
/// exactly the one this sweep is here to reach.
fn gallery_sources() -> Vec<(String, PathBuf)> {
    let dir = repo_root().join("tests/programs");
    let mut out = Vec::new();
    for entry in std::fs::read_dir(&dir).expect("tests/programs is readable") {
        let entry = entry.expect("a readable directory entry");
        if !entry.file_type().expect("a stat-able entry").is_dir() {
            continue;
        }
        let name = entry.file_name().to_string_lossy().into_owned();
        let mut sources: Vec<PathBuf> = std::fs::read_dir(entry.path())
            .expect("a program directory is readable")
            .map(|e| e.expect("a readable entry").path())
            .filter(|p| p.extension().is_some_and(|e| e == "cambra"))
            .collect();
        sources.sort();
        out.extend(sources.into_iter().map(|p| (name.clone(), p)));
    }
    out.sort();
    assert!(
        out.len() > 20,
        "the gallery sweep found only {} sources — the walk is wrong, not the gallery",
        out.len()
    );
    out
}

/// Dump `path` (repo-root-relative) as a fresh process, substituting the
/// `{PORT}` placeholder the HTTP programs carry so they reach the compiler as
/// the program they describe rather than as a parse error.
fn dump_source(path: &Path) -> Option<Vec<u8>> {
    let text = std::fs::read_to_string(path).expect("a gallery source is readable");
    let mut spawn_path = path.to_path_buf();
    let substituted;
    if text.contains("{PORT}") {
        substituted = std::env::temp_dir().join(format!(
            "cambra-sweep-{}",
            path.file_name().expect("a file name").to_string_lossy()
        ));
        std::fs::write(&substituted, text.replace("{PORT}", "8080")).expect("writing the source");
        spawn_path = substituted;
    }
    let output = Command::new(env!("CARGO_BIN_EXE_cambra"))
        .current_dir(repo_root())
        .args([
            spawn_path.to_str().expect("a UTF-8 path"),
            "--dump-snapshot",
        ])
        .output()
        .expect("the cambra binary spawns");
    output.status.success().then_some(output.stdout)
}

/// Ratchet 5 — every gallery program produces a payload the wire validator
/// accepts, on whichever of the two contracts its compile outcome selects.
///
/// This is the coverage the pinned fixtures cannot afford: six committed
/// documents against every program in the repository, at no re-bless cost. A
/// payload that violates the wire contract reaches the frontend unchallenged if
/// only its own bytes are compared to themselves, which is what ratchets 2 and 3
/// do for the six.
#[test]
fn every_gallery_program_produces_a_valid_payload() {
    let mut validated = 0usize;
    let mut panicked = Vec::new();
    for (name, path) in gallery_sources() {
        match dump_source(&path) {
            None => panicked.push(name),
            Some(raw) => {
                let v: Value = serde_json::from_slice(&raw)
                    .unwrap_or_else(|e| panic!("{}: dump is valid JSON: {e}", path.display()));
                match v["meta"]["payloadKind"].as_str() {
                    Some("program") => {
                        cambra::inspector_server::wire_check::assert_snapshot_shape(&v)
                    }
                    Some("failed") => {
                        cambra::inspector_server::wire_check::assert_degraded_snapshot_shape(&v)
                    }
                    other => panic!("{}: unknown payloadKind {other:?}", path.display()),
                }
                validated += 1;
            }
        }
    }
    panicked.sort();
    panicked.dedup();
    let mut expected: Vec<String> = DUMP_PANICS.iter().map(|s| (*s).to_string()).collect();
    expected.sort();
    assert_eq!(
        panicked, expected,
        "the set of gallery programs whose dump panics changed. A program that \
         now dumps must be removed from DUMP_PANICS; one that newly panics is a \
         regression, not a list entry."
    );
    assert!(
        validated >= 25,
        "only {validated} gallery payloads validated — the sweep stopped reaching the gallery"
    );
}

// ---------------------------------------------------------------------------
// Ratchet 6: ids are the only volatile field
// ---------------------------------------------------------------------------

/// Renumber every node id in `v` by first appearance in a document-order walk,
/// in place, and likewise every inference-variable number inside a rendered
/// type.
///
/// The id fields are exactly every entry of `panes[].roots`, every
/// `panes[].nodes[].nodeId`, every inbound edge id a node names — `children[].id`
/// on a tree pane, `inputs[].id` on an operator pane — and both endpoints of
/// every `paneLinks[].edges` pair; spans and the pane's own string `id` are not
/// ids and are left alone. Renumbering is global rather than per-pane because a
/// surviving node keeps one id across every pane it appears in, and that
/// identity — not the number — is what the frontend joins on.
///
/// A rendered `?N` is the second volatile number on the wire: `Display for
/// Type` spells an unresolved `Infer` as its variable id, which comes from
/// another process-global counter. So a fixture over a program whose payload
/// carries one would churn on every change to how many variables inference
/// allocates upstream. No committed fixture carries one today.
///
/// A `?N` on this wire is not itself a defect. `for_accumulator`'s post-inference
/// pane ships `Mut(Int, ?N)` because an induction accumulator's domain is
/// necessarily `Infer` until the unified phase resolves it — see the transient-
/// variant table on `Type` in `src/ccl/ty.rs`. Normalizing it here is about the
/// number, not the openness.
fn canonicalize_ids(v: &mut Value) {
    let mut next = 0u64;
    let mut seen: std::collections::HashMap<u64, u64> = std::collections::HashMap::new();
    let mut renumber = move |id: &mut Value| {
        let old = id.as_u64().expect("an id is a number");
        let new = *seen.entry(old).or_insert_with(|| {
            next += 1;
            next
        });
        *id = Value::from(new);
    };

    let mut next_var = 0u32;
    let mut seen_vars: std::collections::HashMap<String, u32> = std::collections::HashMap::new();
    let mut canonical_type = move |ty: &mut Value| {
        let Some(text) = ty.as_str() else { return };
        if !text.contains('?') {
            return;
        }
        let mut out = String::with_capacity(text.len());
        let mut rest = text;
        while let Some(at) = rest.find('?') {
            out.push_str(&rest[..at]);
            let digits: String = rest[at + 1..]
                .chars()
                .take_while(char::is_ascii_digit)
                .collect();
            if digits.is_empty() {
                out.push('?');
                rest = &rest[at + 1..];
                continue;
            }
            let n = *seen_vars.entry(digits.clone()).or_insert_with(|| {
                next_var += 1;
                next_var
            });
            out.push_str(&format!("?{n}"));
            rest = &rest[at + 1 + digits.len()..];
        }
        out.push_str(rest);
        *ty = Value::from(out);
    };

    for pane in v["panes"].as_array_mut().into_iter().flatten() {
        for root in pane["roots"].as_array_mut().into_iter().flatten() {
            renumber(root);
        }
        for node in pane["nodes"].as_array_mut().into_iter().flatten() {
            renumber(&mut node["nodeId"]);
            canonical_type(&mut node["type"]);
            // A tree pane names its inbound edges `children`, an operator pane
            // `inputs`. Both carry the id under `id`, and a node has one of the
            // two, so walking both reaches every edge without a kind test.
            for channel in ["children", "inputs"] {
                for edge in node[channel].as_array_mut().into_iter().flatten() {
                    renumber(&mut edge["id"]);
                }
            }
        }
    }
    for window in v["paneLinks"].as_array_mut().into_iter().flatten() {
        for edge in window["edges"].as_array_mut().into_iter().flatten() {
            for endpoint in edge.as_array_mut().into_iter().flatten() {
                renumber(endpoint);
            }
        }
    }
}

/// Ratchet 6 — compiling one program twice in one process yields payloads that
/// differ in id numbering and in nothing else.
///
/// This is the premise the whole golden strategy rests on: a re-bless that
/// renumbers ids carries no other information, and a re-bless that changes
/// anything else is reporting a real wire change. Two numbers are volatile, not
/// one — node ids and the `?N` of an unresolved type — and
/// [`canonicalize_ids`] normalizes both. Nothing else in the suite
/// states it — ratchet 1 compares two dumps that are each a first compile, so
/// it cannot see what a *second* compile in the same process does.
///
/// It does **not** subsume ratchet 1. Both compiles here share one process's
/// hash seeds, so a payload whose order depends on hash iteration agrees with
/// itself and only a second process disagrees.
#[test]
fn ids_are_the_only_difference_between_two_compiles() {
    use cambra::ccl::context::{GlobalContext, compile_program};
    use cambra::interpreter::Consumer;

    for example in [
        "udf_closure",
        "polymorphic",
        "defer_lift",
        "for_accumulator",
    ] {
        let source = std::fs::read_to_string(repo_root().join(program_path(example)))
            .expect("a corpus program is readable");
        let payload = |name: &str| {
            let mut ctx = GlobalContext::default();
            let consumer: Box<dyn Consumer> = Box::new(|| {});
            let compiled =
                compile_program(&mut ctx, &source, consumer).expect("a corpus program compiles");
            let mut v: Value =
                serde_json::from_str(&cambra::inspector_server::snapshot_json(&compiled, name))
                    .expect("the payload is valid JSON");
            canonicalize_ids(&mut v);
            v
        };

        let first = payload(example);
        let second = payload(example);
        if first != second {
            let (path, a, b) = first_json_difference(&first, &second, "$")
                .expect("values are unequal, so a structural difference exists");
            panic!(
                "{example}: a second compile in one process differs from the first at \
                 {path} after id canonicalization:\n  first:  {a}\n  second: {b}\n\
                 Ids are meant to be the only volatile part of the payload; \
                 anything else here is state carried between compiles."
            );
        }
    }
}
