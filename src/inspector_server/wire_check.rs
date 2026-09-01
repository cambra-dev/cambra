//! Structural validators for the `/api/snapshot` wire shape — the Rust mirror
//! of the frontend's `validateSnapshot` (`cambra-inspector/web/src/wireValidate.ts`).
//! Asserting the wire contract in one place lets the transport, the server and
//! `tests/inspector_goldens.rs` check one contract (the cross-language twin of
//! the TS validator, since the two cannot literally share code).
//!
//! **Public, not `#[cfg(test)]`.** `tests/inspector_goldens.rs` is a separate
//! crate linking the library as a consumer does, so a `#[cfg(test)]` item is
//! invisible to it — and the committed golden corpus is the payload set that
//! most needs validating, being the one the frontend reads. Gating this behind a
//! feature instead would add a build configuration no CI pass compiles, which is
//! the failure mode `ci_clippy_lib` exists to prevent.

use serde_json::Value;

/// The pane ids, in upstream → downstream order — the exact pane list a
/// successful payload ships as `panes`.
///
/// This is a **pin, not a derivation**: the producer builds its panes from
/// the compiler's `PANES` table, so reading that table here would make the
/// validator agree with the producer by construction and check nothing. A
/// pane added upstream is meant to fail this list, and the failure is the
/// notice that the wire changed.
const PANE_IDS: [&str; 7] = [
    "pre-inference",
    "post-inference",
    "post-channelize",
    "post-as-of-read",
    "post-lambda-elim",
    "post-planning",
    "post-conversion",
];
/// The per-pane `kind` discriminants, aligned with [`PANE_IDS`]: the
/// pre-inference tree is hole-typed (`"holes"`); every tree from
/// post-inference on is fully typed (`"typed"`); the terminal pane holds the
/// dataflow operator graph (`"operators"`).
///
/// The kind is also the node-shape discriminant: `"holes"` and `"typed"`
/// panes hold IR nodes, an `"operators"` pane holds operator nodes.
const PANE_KINDS: [&str; 7] = [
    "holes",
    "typed",
    "typed",
    "typed",
    "typed",
    "typed",
    "operators",
];
/// The adjacent pane windows, in order — the exact `paneLinks` from/to
/// pairs a successful payload ships. One shorter than [`PANE_IDS`].
const PANE_WINDOWS: [(&str, &str); 6] = [
    ("pre-inference", "post-inference"),
    ("post-inference", "post-channelize"),
    ("post-channelize", "post-as-of-read"),
    ("post-as-of-read", "post-lambda-elim"),
    ("post-lambda-elim", "post-planning"),
    ("post-planning", "post-conversion"),
];
/// The observed rewrite-tag `via` vocabulary on the wire (the `Phase` names
/// that appear in a node's `rewritten.via`). Pinned so a new `via` reaching
/// the wire is a deliberate, reviewed event.
///
/// `Uniquify` is a declared phase that records nothing, so it is absent here
/// on purpose: this is what the wire carries, not what the enum spells.
const ALLOWED_VIA: &[&str] = &[
    "Lower",
    "Infer",
    "Inline",
    "Transact",
    "Letrec",
    "Channelize",
    "AsOfRead",
    "LambdaElim",
    "Planning",
    "Convert",
];
/// The rewrite-tag `nature` discriminants (the wire lowercases them).
/// Deliberately **omits** `"source"`: a direct-image (`Nature::Source`) tag
/// null-compresses to `rewritten: null` at the emission sites, so `"source"`
/// must never reach the wire — `assert_rewrite_shape` guards that boundary
/// explicitly, and this list would fail it regardless.
const ALLOWED_NATURE: &[&str] = &["expansion", "machinery"];

/// The pane `kind` whose node table holds operator nodes rather than IR
/// nodes. `kind` is the node-shape discriminant, so the validator dispatches
/// on it.
const OPERATOR_PANE_KIND: &str = "operators";
/// The operator-node `role` discriminants: an operator, or one of the two
/// program boundaries.
const ALLOWED_OPERATOR_ROLE: &[&str] = &["operator", "source", "sink"];
/// The operator-input `kind` discriminants: an exclusively owned input, one
/// several consumers reach, and one that closes a cycle.
const ALLOWED_EDGE_KIND: &[&str] = &["value", "share", "feedback"];

/// The `meta.payloadKind` discriminants: `"program"` for a compiled program,
/// `"failed"` for the degraded payload.
///
/// A pin like [`PANE_IDS`], and checked against that list too — a kind that
/// is also a pane id means one word on the wire names both a document kind
/// and a pipeline position.
const ALLOWED_PAYLOAD_KIND: &[&str] = &["program", "failed"];

/// Collect every `nodeId` of a pane's node table into `out`.
fn collect_node_ids(pane: &Value, out: &mut std::collections::HashSet<u64>) {
    for n in pane["nodes"].as_array().into_iter().flatten() {
        out.insert(n["nodeId"].as_u64().expect("nodeId is a number"));
    }
}

/// The `kind` a given pane id must carry (aligned with [`PANE_IDS`]).
///
/// Keyed by id rather than by position, so a pane list that is right in
/// content and wrong in order fails on the order rather than reading a
/// neighbour's kind.
fn kind_for(id: &str) -> &'static str {
    let i = PANE_IDS
        .iter()
        .position(|s| *s == id)
        .unwrap_or_else(|| panic!("unknown pane id {id:?}"));
    PANE_KINDS[i]
}

/// Assert `v` is a structurally-valid **successful** `/api/snapshot` payload
/// under `ctx`.
///
/// Pins the full pane contract: the retired top-level `ir`/`spanIndex`
/// absent, the panes in pipeline order with their kinds, each pane's node
/// table closed under its own inbound edges and `roots`, each pane's
/// `spanIndex` non-empty, the windowed `paneLinks` with matching from/to ids
/// and every edge endpoint a live node id in its respective pane (self-edges
/// legal), and every node's `rewritten` tag in the observed vocabulary.
/// Panics naming the offending path otherwise. Does not assert
/// program-specific content — that is each caller's job.
///
pub fn assert_snapshot_shape(v: &Value) {
    assert_common_shape(v);

    // An earlier wire retired the legacy top-level `ir`/`spanIndex` (byte-for-byte
    // duplicates of the post-inference pane). They must be *absent*, not
    // merely null — the client reads the panes, never the top level.
    assert!(v.get("ir").is_none(), "the wire has no top-level ir");
    assert!(
        v.get("spanIndex").is_none(),
        "the wire has no top-level spanIndex"
    );

    // The panes, in pipeline order, with their kinds.
    let panes = v["panes"].as_array().expect("panes is an array");
    let ids: Vec<&str> = panes
        .iter()
        .map(|s| s["id"].as_str().expect("pane id is a string"))
        .collect();
    assert_eq!(
        ids, PANE_IDS,
        "panes are the pipeline panes in upstream → downstream order"
    );
    // Each retained pane carries the kind its id mandates (subset-safe).
    for (i, pane) in panes.iter().enumerate() {
        let id = pane["id"].as_str().expect("pane id is a string");
        let kind = pane["kind"].as_str().expect("pane kind is a string");
        assert_eq!(kind, kind_for(id), "panes[{i}] ({id}) has the wrong kind");
    }
    for (i, pane) in panes.iter().enumerate() {
        let at = format!("panes[{i}]");
        assert!(pane["label"].is_string(), "{at}.label is a string");
        assert_node_table(pane, &at);
        // Every node of a compiled pane is attributed, so the pane resolves
        // some source position.
        assert!(
            pane["nodes"]
                .as_array()
                .unwrap_or_else(|| panic!("{at}.nodes is an array"))
                .iter()
                .any(|n| !n["spans"].as_array().is_none_or(|s| s.is_empty())),
            "{at} has a node carrying source spans for a successful compile"
        );
    }

    let links = v["paneLinks"]
        .as_array()
        .expect("paneLinks is present and an array");

    // The live node-id set per pane, keyed by pane id, for endpoint-liveness
    // checks on the pane links below.
    let mut ids_by_pane: std::collections::HashMap<&str, std::collections::HashSet<u64>> =
        std::collections::HashMap::new();
    for pane in panes {
        let id = pane["id"].as_str().expect("pane id is a string");
        let mut set = std::collections::HashSet::new();
        collect_node_ids(pane, &mut set);
        ids_by_pane.insert(id, set);
    }

    // Exactly the adjacent windows, in order, with matching from/to ids.
    let windows: Vec<(&str, &str)> = links
        .iter()
        .map(|l| {
            (
                l["from"].as_str().expect("paneLink.from is a string"),
                l["to"].as_str().expect("paneLink.to is a string"),
            )
        })
        .collect();
    assert_eq!(
        windows,
        PANE_WINDOWS.to_vec(),
        "paneLinks are the adjacent pane windows in pipeline order"
    );
    for (i, link) in links.iter().enumerate() {
        let at = format!("paneLinks[{i}]");
        let (from, to) = windows[i];
        let up_ids = &ids_by_pane[from];
        let down_ids = &ids_by_pane[to];
        let edges = link["edges"]
            .as_array()
            .unwrap_or_else(|| panic!("{at}.edges is an array"));
        for (j, e) in edges.iter().enumerate() {
            let pair = e
                .as_array()
                .unwrap_or_else(|| panic!("{at}.edges[{j}] is an array"));
            assert_eq!(pair.len(), 2, "{at}.edges[{j}] is an [up, down] pair");
            let u = pair[0]
                .as_u64()
                .unwrap_or_else(|| panic!("{at}.edges[{j}][0] is a number"));
            let d = pair[1]
                .as_u64()
                .unwrap_or_else(|| panic!("{at}.edges[{j}][1] is a number"));
            // Dense wire: self-edges (u == d) are legal and expected. Both
            // endpoints must be live node ids in their respective panes.
            assert!(
                up_ids.contains(&u),
                "{at}.edges[{j}] upstream {u} is a live node in `{from}`"
            );
            assert!(
                down_ids.contains(&d),
                "{at}.edges[{j}] downstream {d} is a live node in `{to}`"
            );
        }
    }
}

/// Assert `v` is a structurally-valid **degraded** payload: the
/// retired top-level `ir`/`spanIndex` absent, empty `panes`/`paneLinks`,
/// `payloadKind: "failed"`. `paneLinks` is empty but present: no payload
/// ever omits the field.
pub fn assert_degraded_snapshot_shape(v: &Value) {
    assert_common_shape(v);
    assert!(v.get("ir").is_none(), "the wire has no top-level ir");
    assert!(
        v.get("spanIndex").is_none(),
        "the wire has no top-level spanIndex"
    );
    assert!(
        v["panes"].as_array().expect("array").is_empty(),
        "degraded panes is empty"
    );
    assert!(
        v["paneLinks"].as_array().expect("array").is_empty(),
        "degraded paneLinks is empty"
    );
    assert_eq!(v["meta"]["payloadKind"], "failed");
}

/// The keys common to both the success and degraded payloads.
fn assert_common_shape(v: &Value) {
    assert!(v["source"]["name"].is_string(), "source.name is a string");
    assert!(v["source"]["text"].is_string(), "source.text is a string");
    assert!(v["definitions"].is_array(), "definitions is an array");
    assert!(v["diagnostics"].is_array(), "diagnostics is an array");
    assert!(v.get("scopes").is_none(), "the payload ships no scopes");
    let meta = &v["meta"];
    assert!(meta.get("tick").is_none(), "meta ships no tick");
    let kind = meta["payloadKind"]
        .as_str()
        .expect("meta.payloadKind is a string");
    assert!(
        ALLOWED_PAYLOAD_KIND.contains(&kind),
        "meta.payloadKind {kind:?} is outside the pinned vocabulary \
         {ALLOWED_PAYLOAD_KIND:?}"
    );
    // A payload kind names what the document is; a pane id names a position
    // in the pipeline. One word for both put a pane name in the frontend's
    // header badge.
    assert!(
        !PANE_IDS.contains(&kind),
        "meta.payloadKind {kind:?} is also a pane id"
    );
    assert_eq!(
        meta["schema"],
        crate::inspector_model::SCHEMA_VERSION,
        "meta.schema is the supported version"
    );
}

/// Assert one node's `rewritten` tag is either `null` (a lowering root, or a
/// node the pane's projection does not cover) or an object
/// `{ via, nature, label }` with `via` in [`ALLOWED_VIA`], `nature` in
/// [`ALLOWED_NATURE`], and a non-empty `label`.
fn assert_rewrite_shape(node: &Value, at: &str) {
    let r = &node["rewritten"];
    if !r.is_null() {
        let o = r
            .as_object()
            .unwrap_or_else(|| panic!("{at}: rewritten is null or an object, got {r}"));
        let via = o["via"].as_str().expect("rewritten.via is a string");
        assert!(
            ALLOWED_VIA.contains(&via),
            "{at}: rewritten.via {via:?} is outside the pinned vocabulary {ALLOWED_VIA:?}"
        );
        let nature = o["nature"].as_str().expect("rewritten.nature is a string");
        // Null-compression guard: a `Nature::Source` tag ships as
        // `rewritten: null`, never as a "source" tag. If this fires, the
        // emission-site null-compression rotted.
        assert!(
            nature != "source",
            "{at}: rewritten.nature is \"source\" — a Source tag must null-compress \
             to `rewritten: null`, not ship a Source tag"
        );
        assert!(
            ALLOWED_NATURE.contains(&nature),
            "{at}: rewritten.nature {nature:?} is not one of {ALLOWED_NATURE:?}"
        );
        let label = o["label"].as_str().expect("rewritten.label is a string");
        assert!(!label.is_empty(), "{at}: rewritten.label is non-empty");
    }
}

/// Assert a pane's node table: every root and every inbound `id` names an
/// entry of this same pane's `nodes`, no id appears twice, and every node
/// carries the node shape its pane's `kind` mandates.
///
/// The closure check is what the table buys over the nested tree it
/// replaced: an edge a consumer follows always lands on an entry it holds.
fn assert_node_table(pane: &Value, at: &str) {
    assert!(
        pane.get("ir").is_none(),
        "{at} has no `ir` tree — a pane ships `roots` + `nodes`"
    );
    // The parallel span table shipped one row per node per span, which is
    // what a node's own `spans` says.
    assert!(
        pane.get("spanIndex").is_none(),
        "{at} has no `spanIndex` — a node carries its own spans"
    );
    let kind = pane["kind"]
        .as_str()
        .unwrap_or_else(|| panic!("{at}.kind is a string"));
    let nodes = pane["nodes"]
        .as_array()
        .unwrap_or_else(|| panic!("{at}.nodes is an array"));
    let mut ids = std::collections::HashSet::new();
    for (i, n) in nodes.iter().enumerate() {
        let id = n["nodeId"]
            .as_u64()
            .unwrap_or_else(|| panic!("{at}.nodes[{i}].nodeId is a number"));
        assert!(
            ids.insert(id),
            "{at}.nodes[{i}] repeats node id {id} — the table holds each node once"
        );
    }
    // A tree has the one node nothing owns; an operator graph has several —
    // a sink per compiled output and a fan input per share point.
    let roots = pane["roots"]
        .as_array()
        .unwrap_or_else(|| panic!("{at}.roots is an array"));
    assert!(!roots.is_empty(), "{at}.roots is non-empty");
    if kind != OPERATOR_PANE_KIND {
        assert_eq!(
            roots.len(),
            1,
            "{at} is a tree pane, so {at}.roots holds exactly one id; got {roots:?}"
        );
    }
    let mut seen_roots: std::collections::HashSet<u64> = std::collections::HashSet::new();
    for (i, r) in roots.iter().enumerate() {
        let root = r
            .as_u64()
            .unwrap_or_else(|| panic!("{at}.roots[{i}] is a number"));
        assert!(
            ids.contains(&root),
            "{at}.roots[{i}] {root} names an entry of {at}.nodes"
        );
        assert!(
            seen_roots.insert(root),
            "{at}.roots repeats {root} — a node is a root once"
        );
    }
    for (i, n) in nodes.iter().enumerate() {
        let node_at = format!("{at}.nodes[{i}]");
        if kind == OPERATOR_PANE_KIND {
            assert_operator_node(n, &node_at, &ids);
        } else {
            assert_ir_node(n, &node_at, &ids);
        }
        // The rewrite tag is one channel with one meaning on both shapes.
        assert_rewrite_shape(n, &node_at);
    }
}

/// Assert one entry of an **operator** pane's node table: the scalar fields,
/// the expression-node fields' absence, and every input `id` resolving
/// within `ids`.
fn assert_operator_node(v: &Value, at: &str, ids: &std::collections::HashSet<u64>) {
    assert!(v["label"].is_string(), "{at}.label is a string");
    assert!(v["nodeId"].is_number(), "{at}.nodeId is a number");
    // An operator holds typed input edges, not a type and children. Mirrors
    // the IR shape's absence assertions.
    assert!(v.get("type").is_none(), "{at} has no type field");
    assert!(v.get("children").is_none(), "{at} has no children field");
    let role = v["role"]
        .as_str()
        .unwrap_or_else(|| panic!("{at}.role is a string"));
    assert!(
        ALLOWED_OPERATOR_ROLE.contains(&role),
        "{at}.role {role:?} is not one of {ALLOWED_OPERATOR_ROLE:?}"
    );
    // A tiling is an operator's output shape; a boundary node has no output
    // of its own to tile.
    if role == "operator" {
        assert!(
            v["tiling"].is_string(),
            "{at}.role is \"operator\", so {at}.tiling is a rendered string"
        );
    } else {
        assert!(
            v["tiling"].is_null(),
            "{at}.role is {role:?}, which has no tiling; got {}",
            v["tiling"]
        );
    }
    assert_spans(v, at);
    let inputs = v["inputs"]
        .as_array()
        .unwrap_or_else(|| panic!("{at}.inputs is an array"));
    for (i, e) in inputs.iter().enumerate() {
        assert!(e["role"].is_string(), "{at}.inputs[{i}].role is a string");
        let kind = e["kind"]
            .as_str()
            .unwrap_or_else(|| panic!("{at}.inputs[{i}].kind is a string"));
        assert!(
            ALLOWED_EDGE_KIND.contains(&kind),
            "{at}.inputs[{i}].kind {kind:?} is not one of {ALLOWED_EDGE_KIND:?}"
        );
        // That the `value` edges form a forest is asserted at the producer,
        // by `operator_graph::assert_graph_invariants`, where the whole graph
        // is in hand. Re-walking it here would restate a check the payload
        // cannot fail independently.
        assert!(
            e["deferred"].is_boolean(),
            "{at}.inputs[{i}].deferred is a boolean"
        );
        let id = e["id"]
            .as_u64()
            .unwrap_or_else(|| panic!("{at}.inputs[{i}].id is a number"));
        assert!(
            ids.contains(&id),
            "{at}.inputs[{i}].id {id} names an entry of this pane's nodes"
        );
    }
}

/// Assert a node's `spans`: every entry a `{start, end}` pair, each one once,
/// narrowest first. Same channel and same meaning on both node shapes.
fn assert_spans(v: &Value, at: &str) {
    let spans = v["spans"]
        .as_array()
        .unwrap_or_else(|| panic!("{at}.spans is an array"));
    let mut widths = Vec::with_capacity(spans.len());
    let mut seen_spans = std::collections::HashSet::new();
    for (i, sp) in spans.iter().enumerate() {
        let start = sp["start"]
            .as_u64()
            .unwrap_or_else(|| panic!("{at}.spans[{i}].start is a number"));
        let end = sp["end"]
            .as_u64()
            .unwrap_or_else(|| panic!("{at}.spans[{i}].end is a number"));
        assert!(
            seen_spans.insert((start, end)),
            "{at}.spans[{i}] repeats span {start}..{end}"
        );
        widths.push(end.saturating_sub(start));
    }
    assert!(
        widths.windows(2).all(|w| w[0] <= w[1]),
        "{at}.spans is narrowest first; got widths {widths:?}"
    );
}

/// Assert one entry of an **IR** pane's node table: the scalar fields, the
/// retired fields' absence, and `{edge, id, predicate}` children resolving
/// within `ids`.
fn assert_ir_node(v: &Value, at: &str, ids: &std::collections::HashSet<u64>) {
    assert!(v["label"].is_string(), "{at}.label is a string");
    assert!(v["nodeId"].is_number(), "{at}.nodeId is a number");
    // `annotations` and `tiling` were tile-producer fields on the renderer's
    // node that the payload never set; the wire's IR node type has neither.
    // Scoped to the IR shape: an operator node carries a real `tiling`.
    assert!(
        v.get("annotations").is_none(),
        "{at} has no annotations field"
    );
    assert!(v.get("tiling").is_none(), "{at} has no tiling field");
    // Every node has a type, so the field is a string and never null.
    assert!(v["type"].is_string(), "{at}.type is a string");
    // `typeKind` and `predicateRefs` rode beside the rendered type for a
    // consumer that never read either.
    assert!(v.get("typeKind").is_none(), "{at} has no typeKind field");
    assert!(
        v.get("predicateRefs").is_none(),
        "{at} has no predicateRefs field"
    );
    // A node carries every span its attribution records, narrowest first and
    // each one once.
    assert_spans(v, at);
    let children = v["children"]
        .as_array()
        .unwrap_or_else(|| panic!("{at}.children is an array"));
    let mut predicate_targets = std::collections::HashSet::new();
    for (i, c) in children.iter().enumerate() {
        let is_predicate = c["predicate"]
            .as_bool()
            .unwrap_or_else(|| panic!("{at}.children[{i}].predicate is a boolean"));
        let id = c["id"]
            .as_u64()
            .unwrap_or_else(|| panic!("{at}.children[{i}].id is a number"));
        assert!(
            ids.contains(&id),
            "{at}.children[{i}].id {id} names an entry of this pane's nodes"
        );
        // One edge per predicate: a node's type slots overlap, so a
        // slot-order walk reaches a shared predicate once per slot, and a
        // second edge to it asserts nothing the first does.
        if is_predicate {
            assert!(
                predicate_targets.insert(id),
                "{at}.children[{i}] repeats predicate {id}"
            );
        }
    }
}
