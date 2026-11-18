//! The inspector's wire payload, over fresh `cambra --dump-snapshot` dumps of the gallery
//! programs (`tests/programs/`).
//!
//! Each dump spawns the command line as a fresh process (`crate::it::cli::command`): `NodeId`s
//! come from a process-global counter, so only a process that compiles one program numbers its
//! payload as the inspector's own process does.
//!
//! - Every gallery program produces a payload the wire validator accepts, on the contract its
//!   pinned compile outcome selects.
//! - A dump is the same bytes from two processes.
//! - Two compiles of one program in one process differ in id numbering and nothing else.
//! - The programs chosen for a wire shape still produce it: fan-out edges, the dense channelize
//!   window, a store's edge shapes, the recurrence phases' tags, a source read's iteration.
//!
//! [`write_gallery_snapshots`] writes every gallery program's dump to a directory for the
//! frontend's tests, which read real payloads rather than committed copies of them.

use std::path::{Path, PathBuf};

use serde_json::Value;

/// The repo root. Dumps spawn from here with repo-relative program paths, so a payload's
/// `source.name` is a path a reader can open.
fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).to_path_buf()
}

/// A gallery program's source path, relative to the repo root.
fn program_path(example: &str) -> String {
    format!("tests/programs/{example}/program.cambra")
}

/// Run `cambra <program> --dump-snapshot` as a fresh process and return its raw stdout.
fn dump(example: &str) -> Vec<u8> {
    let prog = program_path(example);
    let output = crate::it::cli::command()
        .current_dir(repo_root())
        .args([prog.as_str(), "--dump-snapshot"])
        .output()
        .expect("the command line spawns");
    assert!(
        output.status.success(),
        "--dump-snapshot failed for {example}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
}

/// A dump is the same bytes from two processes, for programs that cover the heaviest synthesis.
///
/// Rust's default hasher is seeded per process, so output that follows hash iteration order
/// differs between two processes, where within one it can agree with itself
/// ([`ids_are_the_only_difference_between_two_compiles`]). The first suspects are mono's
/// specialization iteration, channelize's channel maps and
/// `transact_phase::collect_txn_stores`; a hash join mints from keyed lookups besides.
#[test]
fn snapshot_dumps_are_cross_process_deterministic() {
    for example in [
        "udf_closure",
        "polymorphic",
        "list_min",
        "list_comp",
        "type_error",
        "defer_lift",
        "source_shared",
        "txn_multi_read",
        "for_accumulator",
        "source_accumulator",
        "inner_join",
    ] {
        assert_dumps_agree(example);
    }
}

/// Two spawns of one program produce byte-identical dumps.
fn assert_dumps_agree(example: &str) {
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
             See `snapshot_dumps_are_cross_process_deterministic` for the first \
             suspects.",
            a.display(),
            b.display()
        );
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

/// The programs chosen for a wire shape still exercise it: `polymorphic`'s `post-inference -> post-channelize` paneLinks window
/// carries a genuine non-identity (`u != d`) fan-out edge — not just the dense
/// self-edges. Guards against the program rotting into one that no longer triggers
/// the pass it was chosen to pin.
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

/// Dense-window sanity over a dump's `post-inference → post-channelize` window, for the
/// programs whose substitution copies make it dense (`txn_multi_read`, `for_accumulator`).
/// Mirrors the `polymorphic` fan-out pattern, strengthened: (a) the window carries genuine
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

/// `txn_multi_read` exercises the dense channelize-window fan-out.
#[test]
fn txn_multi_read_produces_dense_channelize_window() {
    assert_dense_window_sanity("txn_multi_read");
}

/// `for_accumulator` exercises the dense channelize-window fan-out.
#[test]
fn for_accumulator_produces_dense_channelize_window() {
    assert_dense_window_sanity("for_accumulator");
}

/// The operator-pane edge shapes only a store produces, over a fresh dump.
///
/// A store is the one construct that wires an input late, so a `deferred` edge
/// exists nowhere else — and neither does a store-keyed edge role, so without this nothing
/// checks that either reaches the wire at all. That the deferred edges are the cycle set is
/// `every_operator_graph_cycle_runs_through_a_deferred_edge`'s claim, over the graph rather
/// than the payload.
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
            if edge["role"]["kind"] == "storeKey" {
                store_keyed += 1;
            }
        }
    }

    for want in ["value", "share"] {
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

/// `txn_multi_read` exercises the store-only operator edge shapes.
#[test]
fn txn_multi_read_produces_store_edge_shapes() {
    assert_store_edge_shapes("txn_multi_read");
}

/// `for_accumulator` exercises the store-only operator edge shapes.
#[test]
fn for_accumulator_produces_store_edge_shapes() {
    assert_store_edge_shapes("for_accumulator");
}

/// The operator pane's nodes for a fresh dump of `example`.
fn operator_nodes(example: &str) -> Vec<Value> {
    let raw = dump(example);
    let v: Value = serde_json::from_slice(&raw).expect("valid JSON");
    let pane = v["panes"]
        .as_array()
        .expect("panes is an array")
        .iter()
        .find(|p| p["kind"] == "operators")
        .unwrap_or_else(|| panic!("{example} has an operator pane"))
        .clone();
    pane["nodes"].as_array().expect("nodes is an array").clone()
}

/// The `IterateExtent`s upstream of `id`, following every input edge.
///
/// Share edges are followed too: a fan slot reaches its fan input through
/// one, and a source read downstream of a shared iteration crosses it.
fn iterations_upstream(nodes: &[Value], id: u64) -> Vec<&Value> {
    let by_id: std::collections::HashMap<u64, &Value> = nodes
        .iter()
        .map(|n| (n["nodeId"].as_u64().expect("nodeId is a number"), n))
        .collect();
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![id];
    let mut found = Vec::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let node = by_id[&id];
        if node["label"] == "IterateExtent" {
            found.push(node);
        }
        stack.extend(
            node["inputs"]
                .as_array()
                .expect("inputs is an array")
                .iter()
                .filter_map(|e| e["subscribed"].as_u64()),
        );
    }
    found
}

/// **A data source is read from an `IterateExtent` over its domain, not from a
/// node of its own.**
///
/// The graph draws no source node, which is sound because nothing is lost: a
/// `MapResultWithSource` reads a source's values at keys of its domain, and such
/// a key comes only from iterating that domain. So every value read has, upstream
/// of it, an `IterateExtent` whose tiling names the same source and which holds
/// no input — the root the source is read from.
///
/// A source's attribution rides the reader: the program's every `stdin()` is the
/// span of the `MapResultWithSource` built for it, so a selection of the call
/// reaches an operator with no source node in between.
#[test]
fn a_source_read_descends_from_an_iteration_of_that_source() {
    for example in ["source_shared", "source_accumulator"] {
        let nodes = operator_nodes(example);
        assert!(
            nodes.iter().all(|n| n["role"] != "source"),
            "{example}: a source is not a node of the operator graph"
        );

        let readers: Vec<&Value> = nodes
            .iter()
            .filter(|n| n["label"] == "MapResultWithSource")
            .collect();
        assert!(!readers.is_empty(), "{example} reads stdin's values");
        for reader in &readers {
            let id = reader["nodeId"].as_u64().expect("nodeId is a number");
            let roots = iterations_upstream(&nodes, id);
            assert!(
                roots.iter().any(|it| {
                    it["tiling"]
                        .as_str()
                        .is_some_and(|t| t.contains("Source(stdin)"))
                        && it["inputs"].as_array().is_some_and(|es| es.is_empty())
                }),
                "{example}: MapResultWithSource {id} reads stdin, but no input-free \
                 `IterateExtent` over stdin's domain is upstream of it: {roots:?}"
            );
        }

        let raw = dump(example);
        let v: Value = serde_json::from_slice(&raw).expect("valid JSON");
        let text = v["source"]["text"]
            .as_str()
            .expect("source.text is a string");
        let reader_spans: std::collections::BTreeSet<(u64, u64)> = readers
            .iter()
            .flat_map(|r| r["spans"].as_array().expect("spans is an array"))
            .map(|s| {
                (
                    s["start"].as_u64().expect("start is a number"),
                    s["end"].as_u64().expect("end is a number"),
                )
            })
            .collect();
        for (start, call) in text.match_indices("stdin()") {
            let site = (start as u64, (start + call.len()) as u64);
            assert!(
                reader_spans.contains(&site),
                "{example}: the `stdin()` at {site:?} is the span of no MapResultWithSource; \
                 reader spans are {reader_spans:?}"
            );
        }
    }
}

/// **A store folding over a source's domain reads its final value from the store.**
///
/// `source_accumulator` loops over `stdin()` and accumulates into a mutable
/// variable, so the loop's induction extent is the source's own domain. The
/// trailing read of the accumulator is a `StoreFinalRead` over the store itself,
/// so the source is iterated once, by the chain that reads its values, and no
/// second iteration of it triggers the read.
#[test]
fn a_store_over_a_source_domain_reads_its_final_value_from_the_store() {
    let nodes = operator_nodes("source_accumulator");
    let over_stdin: Vec<&Value> = nodes
        .iter()
        .filter(|n| {
            n["label"] == "IterateExtent"
                && n["tiling"]
                    .as_str()
                    .is_some_and(|t| t.contains("Source(stdin)"))
        })
        .collect();
    assert_eq!(
        over_stdin.len(),
        1,
        "one `IterateExtent` heads the chain that reads stdin's values; got {over_stdin:?}"
    );
    assert_eq!(
        over_stdin[0]["inputs"].as_array().map(Vec::len),
        Some(0),
        "an `IterateExtent` holds no input, so it is a root: {:?}",
        over_stdin[0]
    );
    assert!(
        nodes.iter().any(|n| n["label"] == "StoreFinalRead"),
        "the accumulator's trailing read is a `StoreFinalRead`"
    );
    assert!(
        !nodes.iter().any(|n| n["label"] == "StoreDenseRead"),
        "no dense read re-iterates the source"
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

/// The labels of the rewrites that produced `example`'s nodes, over every pane.
fn dump_rewrite_labels(example: &str) -> std::collections::HashSet<String> {
    let raw = dump(example);
    let v: Value = serde_json::from_slice(&raw).expect("valid JSON");
    let mut out = std::collections::HashSet::new();
    for pane in v["panes"].as_array().expect("panes is an array") {
        for node in pane["nodes"].as_array().expect("nodes is an array") {
            if let Some(label) = node["rewritten"]["label"].as_str() {
                out.insert(label.to_string());
            }
        }
    }
    out
}

/// `defer_lift` still exercises the two channelize rewrites it is in the gallery for: the lift
/// that merges a call's defer scope into its caller's, and the fan-in of two feed sites into
/// one channel.
#[test]
fn defer_lift_reaches_the_wire_through_both_channelize_rewrites() {
    let labels = dump_rewrite_labels("defer_lift");
    for label in ["channelize.defer_lift", "channelize.cluster"] {
        assert!(
            labels.contains(label),
            "defer_lift's payload carries no node rewritten by `{label}`; got {labels:?}"
        );
    }
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

// ---------------------------------------------------------------------------
// The whole gallery, validated
// ---------------------------------------------------------------------------

/// The gallery sources whose `--dump-snapshot` **panics**, so the sweep below
/// has no payload to validate. Empty: every gallery program dumps.
///
/// A pinned list rather than a silent skip, in both directions: a program that
/// starts dumping must leave this list (the sweep says so), and a program that
/// stops dumping cannot join it without an edit. A program that does not
/// compile still dumps — the degraded contract carries source and diagnostics
/// with empty panes — so a panic here is a hole in the dump path, not a
/// rejected program.
const DUMP_PANICS: &[&str] = &[];

/// The gallery programs that do **not** compile, so the sweep below validates
/// them on the degraded contract rather than the successful one.
///
/// Pinned for the same reason `DUMP_PANICS` is, and in the same two directions.
/// The sweep reads each payload's own `payloadKind` to pick a contract, so a
/// program that silently stops compiling would slide onto the degraded contract
/// and pass — a regression the wire validators cannot see, because a degraded
/// payload is a legal document. A program that starts compiling must leave this
/// list; one that newly fails is a regression, not a list entry.
///
/// Being non-empty, it is also what bounds the walk: a sweep that stops
/// reaching the gallery reports these as missing.
const COMPILE_FAILS: &[&str] = &[
    "discount_contract",
    "fanout",
    "ledger_balance",
    "nonneg_inventory",
    "reachability",
    "refinement",
    // A program of two modules: the dump refuses a program of several files,
    // and `lines.cambra`, a module, ends in no program value.
    "source_two_runs",
    "storefront",
    "txn_kv",
    "type_error",
    "while_counter",
];

/// Every `*.cambra` source under `tests/programs/`, as (program-directory name,
/// absolute path). Walks the directory rather than reading a list:
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
    // A walk that stops reaching the directory is the failure this guards; the
    // size of the gallery is not pinned here, because a count would need an
    // edit for every program added and this sweep exists to cost nothing. What
    // bounds it is `COMPILE_FAILS` below: a non-empty list, compared exactly.
    assert!(
        !out.is_empty(),
        "the gallery sweep found no sources under {} — the walk is wrong, not the gallery",
        dir.display()
    );
    out
}

/// Dump `path` as a fresh process, spawned at its repo-relative path, substituting the
/// `{PORT}` placeholder the HTTP programs carry so they reach the compiler as
/// the program they describe rather than as a parse error.
fn dump_source(path: &Path) -> Option<Vec<u8>> {
    let text = std::fs::read_to_string(path).expect("a gallery source is readable");
    let mut spawn_path = path.strip_prefix(repo_root()).unwrap_or(path).to_path_buf();
    let substituted;
    if text.contains("{PORT}") {
        // The file keeps its name, which is the root's module path, in a
        // directory of its own.
        let parent = path
            .parent()
            .and_then(Path::file_name)
            .expect("a directory");
        let dir = std::env::temp_dir().join(format!("cambra-sweep-{}", parent.to_string_lossy()));
        std::fs::create_dir_all(&dir).expect("creating the directory");
        substituted = dir.join(path.file_name().expect("a file name"));
        std::fs::write(&substituted, text.replace("{PORT}", "8080")).expect("writing the source");
        spawn_path = substituted;
    }
    let output = crate::it::cli::command()
        .current_dir(repo_root())
        .args([
            spawn_path.to_str().expect("a UTF-8 path"),
            "--dump-snapshot",
        ])
        .output()
        .expect("the command line spawns");
    output.status.success().then_some(output.stdout)
}

/// Every gallery program produces a payload the wire validator accepts, on whichever of the
/// two contracts its compile outcome selects. The frontend's tests run its own validator over
/// the same dumps ([`write_gallery_snapshots`]).
#[test]
fn every_gallery_program_produces_a_valid_payload() {
    let mut panicked = Vec::new();
    let mut degraded = Vec::new();
    for (name, path) in gallery_sources() {
        let Some(raw) = dump_source(&path) else {
            panicked.push(name);
            continue;
        };
        // Repo-relative, so a failure names a path a reader can open.
        let at = path
            .strip_prefix(repo_root())
            .unwrap_or(&path)
            .display()
            .to_string();
        let v: Value = serde_json::from_slice(&raw)
            .unwrap_or_else(|e| panic!("{at}: dump is valid JSON: {e}"));
        match v["meta"]["payloadKind"].as_str() {
            Some("program") => {
                cambra::inspector_server::wire_check::assert_snapshot_shape_at(&v, &at)
            }
            Some("failed") => {
                degraded.push(name);
                cambra::inspector_server::wire_check::assert_degraded_snapshot_shape_at(&v, &at)
            }
            other => panic!("{at}: unknown payloadKind {other:?}"),
        }
    }
    assert_eq!(
        pinned(&mut panicked),
        listed(DUMP_PANICS),
        "the set of gallery programs whose dump panics changed. A program that \
         now dumps must be removed from DUMP_PANICS; one that newly panics is a \
         regression, not a list entry."
    );
    assert_eq!(
        pinned(&mut degraded),
        listed(COMPILE_FAILS),
        "the set of gallery programs that do not compile changed. A program that \
         now compiles must be removed from COMPILE_FAILS; one that newly fails is \
         a regression, not a list entry."
    );
}

/// Writes every gallery program's dump to the directory `CAMBRA_SNAPSHOT_DIR` names, for the
/// frontend's tests (`web/src/__fixtures__/dumps.ts`): `<program>.snapshot.json` for a
/// directory's `program.cambra`, and `<program>.<file stem>.snapshot.json` for any other
/// source. A dump already in the directory is removed first, so none outlives its program.
///
/// Ignored because it writes files: the frontend tests' setup runs it, with the profile the
/// suite was built with.
#[test]
#[ignore = "writes the frontend tests' payloads; their setup runs it"]
fn write_gallery_snapshots() {
    let dir = PathBuf::from(
        std::env::var_os("CAMBRA_SNAPSHOT_DIR")
            .expect("CAMBRA_SNAPSHOT_DIR names the directory to write the dumps to"),
    );
    std::fs::create_dir_all(&dir).expect("creating the dump directory");
    for entry in std::fs::read_dir(&dir).expect("the dump directory is readable") {
        let path = entry.expect("a readable entry").path();
        if path.to_string_lossy().ends_with(".snapshot.json") {
            std::fs::remove_file(&path).expect("removing an earlier dump");
        }
    }
    for (name, path) in gallery_sources() {
        // The sweep above pins these; the frontend has no payload of theirs to read.
        if DUMP_PANICS.contains(&name.as_str()) {
            continue;
        }
        let raw = dump_source(&path)
            .unwrap_or_else(|| panic!("--dump-snapshot failed for {}", path.display()));
        let stem = path
            .file_stem()
            .expect("a source has a file name")
            .to_string_lossy();
        let file = if stem == "program" {
            format!("{name}.snapshot.json")
        } else {
            format!("{name}.{stem}.snapshot.json")
        };
        std::fs::write(dir.join(file), raw).expect("writing a dump");
    }
}

/// The observed program names, sorted and deduped for comparison against a
/// pinned list. A program directory with several sources reports once, as the
/// pinned lists name directories.
fn pinned(names: &mut Vec<String>) -> Vec<String> {
    names.sort();
    names.dedup();
    std::mem::take(names)
}

/// A pinned list in the shape `pinned` returns.
fn listed(names: &[&str]) -> Vec<String> {
    let mut out: Vec<String> = names.iter().map(|s| (*s).to_string()).collect();
    out.sort();
    out
}

// ---------------------------------------------------------------------------
// Ids are the only volatile field
// ---------------------------------------------------------------------------

/// Renumber every node id in `v` by first appearance in a document-order walk,
/// in place, and likewise every inference-variable number inside a rendered
/// type.
///
/// The id fields are exactly `panes[].root` on a tree pane (an operator pane
/// ships no start set), every `panes[].nodes[].nodeId`,
/// every inbound edge id a node names — `children[].id` on a tree pane,
/// `inputs[].subscribed` on an operator pane — and both endpoints of every
/// `paneLinks[].edges` pair; spans and the pane's own string `id` are not ids and
/// are left alone. Renumbering is global rather than per-pane because a
/// surviving node keeps one id across every pane it appears in, and that
/// identity — not the number — is what the frontend joins on.
///
/// A rendered `?N` is the second volatile number on the wire: `Display for
/// Type` spells an unresolved `Infer` as its variable id, which comes from
/// another process-global counter.
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
        // A tree pane's walk start is one id under `root`; an operator pane ships
        // none, so the null check covers both shapes without a kind test.
        if !pane["root"].is_null() {
            renumber(&mut pane["root"]);
        }
        for node in pane["nodes"].as_array_mut().into_iter().flatten() {
            renumber(&mut node["nodeId"]);
            canonical_type(&mut node["type"]);
            // A tree pane names its inbound edges `children` and an operator
            // pane `inputs`; a child carries `id` and an operator input
            // `subscribed`. A node has one of the two, so walking both reaches
            // every edge without a kind test.
            for edge in node["children"].as_array_mut().into_iter().flatten() {
                renumber(&mut edge["id"]);
            }
            for edge in node["inputs"].as_array_mut().into_iter().flatten() {
                renumber(&mut edge["subscribed"]);
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

/// Compiling one program twice in one process yields payloads that differ in id numbering and
/// in nothing else: anything else that differs is state carried from one compile to the next.
/// Two numbers are volatile, not one — node ids and the `?N` of an unresolved type — and
/// [`canonicalize_ids`] normalizes both.
///
/// [`snapshot_dumps_are_cross_process_deterministic`] compares two dumps that are each a first
/// compile, so it cannot see what a *second* compile in one process does; and both compiles
/// here share one process's hash seeds, so a payload whose order follows hash iteration agrees
/// with itself here and only a second process disagrees.
#[test]
fn ids_are_the_only_difference_between_two_compiles() {
    use cambra::ccl::context::{GlobalContext, compile_program};
    use cambra::ccl::load::LoadedProgram;
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
                compile_program(&mut ctx, &LoadedProgram::from_text(name, &source), consumer)
                    .expect("a corpus program compiles");
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
