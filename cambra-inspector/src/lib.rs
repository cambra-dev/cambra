//! The user-facing Cambra program-inspector.
//!
//! This crate is the second member of the Cambra workspace (the first being the
//! `cambra` compiler/engine crate at the repo root). It owns the pieces the core
//! deliberately keeps out: **serde + `serde_json`** (it depends on `cambra` with
//! the `serde` feature enabled), the [`server`] module's `tiny_http` server, and
//! the embedded CodeMirror frontend. Keeping these here is what lets
//! `cargo build -p cambra` compile zero serde: serde is an optional, default-off
//! feature on `cambra`.
//!
//! # Snapshot serialization
//!
//! The read-only model and its serde-gated wire types live in
//! [`cambra::inspector_model`]; this crate is the **transport edge** that turns
//! them into JSON. [`snapshot_json`] compiles-then-serializes: given a
//! [`CompiledProgram`](cambra::ccl::context::CompiledProgram) it builds the
//! [`SnapshotPayload`](cambra::inspector_model::SnapshotPayload) (via
//! `Snapshot::build_payload`) and renders it with `serde_json`. The [`server`]'s
//! `GET /api/snapshot` route calls exactly this.

pub mod server;

use cambra::ccl::context::{CompiledProgram, GlobalContext, compile_program};
use cambra::inspector_model::{Snapshot, diagnostics_from_compile_errors};
use cambra::interpreter::Consumer;

/// Build the `/api/snapshot` payload for a compiled program and serialize it to
/// a JSON string.
///
/// This is the build-then-serialize entry [`server`] calls per
/// request. `name` becomes the payload's `source.name` (the program's display
/// name). Serialization is infallible for this payload (it is plain data — no
/// maps with non-string keys, no custom errors), so a failure is a bug; we
/// surface it via `expect` rather than leaking a `serde_json::Error` into the
/// signature the server wants.
pub fn snapshot_json(compiled: &CompiledProgram, name: &str) -> String {
    let snapshot = Snapshot::new(compiled);
    let payload = snapshot.build_payload(name);
    serde_json::to_string(&payload).expect("snapshot payload serializes")
}

/// Compile `code` and serialize the resulting diagnostics to JSON.
///
/// The web half of the dual-use diagnostics: the same `CompileError`s
/// the terminal renders via ariadne, emitted as `{ "diagnostics": [...] }`.
/// On a successful compile the array is empty (M1 has no warnings); on failure
/// each error becomes a structured
/// [`Diagnostic`](cambra::inspector_model::Diagnostic) — for inference errors
/// carrying the source span resolved at the `compile_program` boundary, so the
/// browser can underline the offending range exactly as the terminal does.
///
/// `name` is the program's display name (unused in the diagnostics payload
/// today, but kept symmetric with [`snapshot_json`]'s signature).
pub fn diagnose_json(ctx: &mut GlobalContext, code: &str, _name: &str) -> String {
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let diagnostics = match compile_program(ctx, code, consumer) {
        Ok(_) => Vec::new(),
        Err(errors) => diagnostics_from_compile_errors(&errors),
    };
    serde_json::to_string(&serde_json::json!({ "diagnostics": diagnostics }))
        .expect("diagnostics payload serializes")
}

/// Shared test helpers: structural validators for the `/api/snapshot` wire
/// shape — the Rust mirror of the frontend's `validateSnapshot`
/// (`web/src/wireValidate.ts`). Asserting the schema-3 contract in one place
/// lets both the lib and `server` test modules reuse it (the cross-language
/// twin of the TS validator, since the two cannot literally share code).
#[cfg(test)]
pub(crate) mod test_support {
    use serde_json::Value;

    /// The three pipeline stage ids, in upstream → downstream order — the exact
    /// stage list a schema-3 successful payload ships.
    const STAGE_IDS: [&str; 3] = ["pre-inference", "post-inference", "post-desugar"];
    /// The per-stage `kind` discriminants, aligned with [`STAGE_IDS`]: the
    /// pre-inference tree is hole-typed (`"holes"`); the post-inference and
    /// post-desugar trees are both fully typed (`"typed"`).
    const STAGE_KINDS: [&str; 3] = ["holes", "typed", "typed"];
    /// The adjacent stage windows, in order — the exact `paneLinks` from/to
    /// pairs a schema-3 successful payload ships.
    const STAGE_WINDOWS: [(&str, &str); 2] = [
        ("pre-inference", "post-inference"),
        ("post-inference", "post-desugar"),
    ];
    /// The observed rewrite-tag `via` vocabulary on the wire (the `Pass` names
    /// that appear in a node's `rewritten.via`). Pinned so a new `via` reaching
    /// the wire is a deliberate, reviewed event.
    const ALLOWED_VIA: &[&str] = &["Lower", "Mono", "Inline", "Transact", "Letrec", "Desugar"];
    /// The rewrite-tag `nature` discriminants (schema 3 lowercases them).
    /// Deliberately **omits** `"source"`: a direct-image (`Nature::Source`) tag
    /// null-compresses to `rewritten: null` at the emission sites, so `"source"`
    /// must never reach the wire — `assert_rewrite_shape` guards that boundary
    /// explicitly, and this list would fail it regardless.
    const ALLOWED_NATURE: &[&str] = &["expansion", "machinery"];

    /// Collect every `nodeId` in a stage's IR tree into `out`.
    fn collect_node_ids(node: &Value, out: &mut std::collections::HashSet<u64>) {
        if let Some(id) = node["nodeId"].as_u64() {
            out.insert(id);
        }
        for c in node["children"].as_array().into_iter().flatten() {
            collect_node_ids(&c["node"], out);
        }
    }

    /// Assert `v` is a structurally-valid **successful** `/api/snapshot` payload
    /// (schema 3). Pins the full stage contract: schema 3, the retired top-level
    /// `ir`/`spanIndex` absent, the three pipeline stages in order with their
    /// kinds, each stage's `spanIndex` non-empty, the two windowed `paneLinks`
    /// with matching from/to ids and every edge endpoint a live node id in its
    /// respective pane (self-edges legal), and every node's `rewritten` tag in
    /// the observed vocabulary. Panics naming the offending path otherwise. Does
    /// not assert program-specific content — that is each caller's job.
    pub(crate) fn assert_snapshot_shape(v: &Value) {
        assert_common_shape(v);

        // Schema 2 retired the legacy top-level `ir`/`spanIndex` (byte-for-byte
        // duplicates of the post-inference stage). They must be *absent*, not
        // merely null — the client reads the stages, never the top level.
        assert!(v.get("ir").is_none(), "schema 3 has no top-level ir");
        assert!(
            v.get("spanIndex").is_none(),
            "schema 3 has no top-level spanIndex"
        );

        // The three pipeline stages, in pipeline order, with their kinds.
        let stages = v["stages"].as_array().expect("stages is an array");
        let ids: Vec<&str> = stages
            .iter()
            .map(|s| s["id"].as_str().expect("stage id is a string"))
            .collect();
        assert_eq!(
            ids, STAGE_IDS,
            "stages are the three pipeline stages in upstream → downstream order"
        );
        let kinds: Vec<&str> = stages
            .iter()
            .map(|s| s["kind"].as_str().expect("stage kind is a string"))
            .collect();
        assert_eq!(
            kinds, STAGE_KINDS,
            "stage kinds are holes (pre-inference) then typed (the two typed trees)"
        );
        for (i, st) in stages.iter().enumerate() {
            let at = format!("stages[{i}]");
            assert!(st["label"].is_string(), "{at}.label is a string");
            assert_inspect_node(&st["ir"], &format!("{at}.ir"));
            assert_span_index(&st["spanIndex"], &format!("{at}.spanIndex"));
            assert!(
                !st["spanIndex"]
                    .as_array()
                    .unwrap_or_else(|| panic!("{at}.spanIndex is an array"))
                    .is_empty(),
                "{at}.spanIndex is non-empty for a successful compile"
            );
            // Every rewrite tag a stage's tree carries uses the pinned
            // via/nature vocabulary.
            assert_rewrite_shape(&st["ir"], &at);
        }

        // The live node-id set per stage, keyed by stage id, for endpoint-liveness
        // checks on the pane links below.
        let mut ids_by_stage: std::collections::HashMap<&str, std::collections::HashSet<u64>> =
            std::collections::HashMap::new();
        for st in stages {
            let id = st["id"].as_str().expect("stage id is a string");
            let mut set = std::collections::HashSet::new();
            collect_node_ids(&st["ir"], &mut set);
            ids_by_stage.insert(id, set);
        }

        // Exactly the two adjacent windows, in order, with matching from/to ids.
        let links = v["paneLinks"].as_array().expect("paneLinks is an array");
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
            STAGE_WINDOWS.to_vec(),
            "paneLinks are the two adjacent stage windows in pipeline order"
        );
        for (i, link) in links.iter().enumerate() {
            let at = format!("paneLinks[{i}]");
            let (from, to) = windows[i];
            let up_ids = &ids_by_stage[from];
            let down_ids = &ids_by_stage[to];
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

    /// Assert `v` is a structurally-valid **degraded** payload (schema 3): the
    /// retired top-level `ir`/`spanIndex` absent, empty `stages`/`paneLinks`,
    /// `snapshotKind: "failed"`.
    pub(crate) fn assert_degraded_snapshot_shape(v: &Value) {
        assert_common_shape(v);
        assert!(v.get("ir").is_none(), "schema 3 has no top-level ir");
        assert!(
            v.get("spanIndex").is_none(),
            "schema 3 has no top-level spanIndex"
        );
        assert!(
            v["stages"].as_array().expect("array").is_empty(),
            "degraded stages is empty"
        );
        assert!(
            v["paneLinks"].as_array().expect("array").is_empty(),
            "degraded paneLinks is empty"
        );
        assert_eq!(v["meta"]["snapshotKind"], "failed");
    }

    /// The keys common to both the success and degraded payloads.
    fn assert_common_shape(v: &Value) {
        assert!(v["source"]["name"].is_string(), "source.name is a string");
        assert!(v["source"]["text"].is_string(), "source.text is a string");
        assert!(v["definitions"].is_array(), "definitions is an array");
        assert!(v["scopes"].is_array(), "scopes is an array");
        assert!(v["diagnostics"].is_array(), "diagnostics is an array");
        let meta = &v["meta"];
        assert!(
            meta["tick"].is_null() || meta["tick"].is_number(),
            "meta.tick is null or a number"
        );
        assert!(
            meta["snapshotKind"].is_string(),
            "meta.snapshotKind is a string"
        );
        assert_eq!(
            meta["schema"],
            cambra::inspector_model::SCHEMA_VERSION,
            "meta.schema is the supported version"
        );
    }

    /// Recursively assert every node's `rewritten` tag (schema 3) is either
    /// `null` (a directly-lowered source node) or an object
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
            // Null-compression guard (lineage-redesign §2.14): a direct image
            // (`Nature::Source`) ships as `rewritten: null`, never as a "source"
            // tag. If this fires, the emission-site null-compression rotted.
            assert!(
                nature != "source",
                "{at}: rewritten.nature is \"source\" — a direct image must null-compress \
                 to `rewritten: null`, not ship a Source tag"
            );
            assert!(
                ALLOWED_NATURE.contains(&nature),
                "{at}: rewritten.nature {nature:?} is not one of {ALLOWED_NATURE:?}"
            );
            let label = o["label"].as_str().expect("rewritten.label is a string");
            assert!(!label.is_empty(), "{at}: rewritten.label is non-empty");
        }
        for c in node["children"].as_array().into_iter().flatten() {
            assert_rewrite_shape(&c["node"], at);
        }
    }

    fn assert_span_index(v: &Value, at: &str) {
        let entries = v.as_array().unwrap_or_else(|| panic!("{at} is an array"));
        for (i, e) in entries.iter().enumerate() {
            assert!(
                e["span"]["start"].is_number() && e["span"]["end"].is_number(),
                "{at}[{i}].span is {{start, end}}"
            );
            assert!(e["nodeId"].is_number(), "{at}[{i}].nodeId is a number");
        }
    }

    /// Recursively assert the `InspectNode` wire shape, including the
    /// first-class `type` field (`string | null`) and `{edge, node}` children.
    fn assert_inspect_node(v: &Value, at: &str) {
        assert!(v["label"].is_string(), "{at}.label is a string");
        assert!(v["annotations"].is_array(), "{at}.annotations is an array");
        assert!(v["nodeId"].is_number(), "{at}.nodeId is a number");
        assert!(
            v["type"].is_string() || v["type"].is_null(),
            "{at}.type is a string or null"
        );
        let children = v["children"]
            .as_array()
            .unwrap_or_else(|| panic!("{at}.children is an array"));
        for (i, c) in children.iter().enumerate() {
            assert!(c["edge"].is_string(), "{at}.children[{i}].edge is a string");
            assert_inspect_node(&c["node"], &format!("{at}.children[{i}].node"));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::test_support::assert_snapshot_shape;
    use super::*;
    use cambra::ccl::context::{GlobalContext, compile_program};
    use cambra::interpreter::Consumer;
    use serde_json::Value;

    const PROG: &str = "\
g = 10
def f(p, q):
  p + q + g
f(1, 2)
";

    /// Compile `code` and parse its `/api/snapshot` JSON back to a `Value`.
    fn snapshot_value(code: &str, name: &str) -> Value {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, code, consumer).expect("program compiles");
        serde_json::from_str(&snapshot_json(&compiled, name)).expect("payload is valid JSON")
    }

    /// The structural wire-shape contract (schema 3) — the Rust twin of the
    /// frontend's `validateSnapshot`. Program-specific facts are asserted by the
    /// focused tests below.
    #[test]
    fn snapshot_json_is_structurally_valid() {
        assert_snapshot_shape(&snapshot_value(PROG, "prog.chl"));
    }

    /// meta seams + source round-trip + empty M1 diagnostics.
    #[test]
    fn snapshot_meta_source_and_diagnostics() {
        let v = snapshot_value(PROG, "prog.chl");
        assert!(v["meta"]["tick"].is_null(), "meta.tick is null in M1");
        assert_eq!(v["meta"]["snapshotKind"], "post-inference");
        assert_eq!(v["meta"]["schema"], 3);
        assert_eq!(v["source"]["name"], "prog.chl");
        assert_eq!(
            v["source"]["text"], PROG,
            "source.text is the retained program text"
        );
        assert!(
            v["diagnostics"].as_array().expect("array").is_empty(),
            "diagnostics is [] in M1"
        );
    }

    /// The body use of `g` resolves to its definition span.
    #[test]
    fn snapshot_definitions_resolve_g_use_to_def() {
        let v = snapshot_value(PROG, "prog.chl");
        let definitions = v["definitions"]
            .as_array()
            .expect("definitions is an array");
        let g_use_start = PROG.match_indices('g').nth(1).expect("a 2nd g").0;
        let g_def = definitions
            .iter()
            .find(|d| {
                d["name"] == "g" && d["useSpan"]["start"].as_u64() == Some(g_use_start as u64)
            })
            .expect("the body use of g resolves to a definition");
        assert!(
            g_def["defSpan"]["start"].is_number(),
            "definition carries a defSpan {{start,end}}"
        );
    }

    /// `g`'s scope binding carries its type as a Display string containing Int.
    #[test]
    fn snapshot_scopes_carry_binding_types() {
        let v = snapshot_value(PROG, "prog.chl");
        let scopes = v["scopes"].as_array().expect("scopes is an array");
        let g_typed = scopes
            .iter()
            .flat_map(|s| s["bindings"].as_array().unwrap())
            .find(|b| b["name"] == "g" && b["type"].as_str().is_some_and(|t| t.contains("Int")));
        assert!(
            g_typed.is_some(),
            "g's type renders as a string containing Int; scopes = {scopes:#?}"
        );
    }

    /// Three stages, ordered upstream → downstream, each with a populated index.
    #[test]
    fn snapshot_stages_ordered_upstream_to_downstream() {
        let v = snapshot_value(PROG, "prog.chl");
        let stages = v["stages"].as_array().expect("stages is an array");
        assert_eq!(stages.len(), 3, "three pipeline stages");
        assert_eq!(stages[0]["id"], "pre-inference");
        assert_eq!(stages[1]["id"], "post-inference");
        assert_eq!(stages[2]["id"], "post-desugar");
        for (i, stage) in stages.iter().enumerate() {
            assert!(
                !stage["spanIndex"]
                    .as_array()
                    .unwrap_or_else(|| panic!("stages[{i}].spanIndex is an array"))
                    .is_empty(),
                "stages[{i}].spanIndex is non-empty"
            );
        }
    }

    /// A stage's IR root carries the type in the first-class `type` field — no
    /// longer smuggled into a positional `annotations[0]` entry. Reads the
    /// post-inference stage tree (schema 2 retired the top-level `ir`; schema 3
    /// keeps it retired).
    #[test]
    fn snapshot_ir_root_carries_type_field() {
        let v = snapshot_value(PROG, "prog.chl");
        let stages = v["stages"].as_array().expect("stages is an array");
        let ir = &stages
            .iter()
            .find(|s| s["id"] == "post-inference")
            .expect("the post-inference stage is present")["ir"];
        assert!(ir["nodeId"].is_number(), "ir root carries a numeric nodeId");
        assert!(
            ir["type"].is_string(),
            "ir root carries the type in the dedicated field; got {}",
            ir["type"]
        );
        assert!(
            ir["annotations"].as_array().expect("array").is_empty(),
            "the type is no longer smuggled into annotations"
        );
    }

    /// A known source span resolves to an IR node — proves the index the payload
    /// is built from actually maps a span to a node.
    #[test]
    fn snapshot_span_resolves_to_node() {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, PROG, consumer).expect("program compiles");
        let snapshot = Snapshot::new(&compiled);
        let g_def_start = PROG.find('g').expect("g present");
        let resolved = snapshot.resolve(cambra::chl_parser::ast::Span::new(
            g_def_start,
            g_def_start + 1,
        ));
        assert!(
            resolved.node_id.is_some(),
            "the `g` def span resolves to an IR node"
        );
    }

    /// For a let-polymorphic program (`dup` used at two types), `paneLinks[0].edges`
    /// carries a genuine `u != d` fan-out edge — the monomorphization fan-out
    /// produces non-identity cross-stage edges alongside the dense self-edges.
    #[test]
    fn pane_links_edges_non_empty_for_polymorphic_program() {
        let code = "\
dup = \\x -> (x, x)
a = dup(1)
b = dup(2 == 2)
a
";
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, code, consumer).expect("program compiles");

        let json = snapshot_json(&compiled, "poly.chl");
        let v: Value = serde_json::from_str(&json).expect("payload is valid JSON");

        let pane_links = v["paneLinks"].as_array().expect("paneLinks is an array");
        assert!(!pane_links.is_empty(), "paneLinks is non-empty");

        let link = &pane_links[0];
        assert_eq!(link["from"], "pre-inference");
        assert_eq!(link["to"], "post-inference");

        let edges = link["edges"].as_array().expect("edges is an array");
        assert!(
            edges.iter().any(|e| {
                let p = e.as_array().expect("edge is a pair");
                p[0].as_u64() != p[1].as_u64()
            }),
            "a let-polymorphic def used at two types must yield a genuine (u != d) fan-out edge"
        );
    }

    /// RT-3b — for a scalar UDF called at two sites (inline fan-out), the wire
    /// payload's `post-inference → post-desugar` paneLinks entry has non-empty
    /// edges, each `[upstream, downstream]` pair joining a live node in the
    /// post-inference stage tree to a live node in the post-desugar stage tree.
    ///
    /// This is the wire-level proof that the retained inline remap is actually
    /// consumed: without the pair→pass stage-links association reading it, the
    /// `CompiledProgram`-retained remap would never reach the payload (the
    /// second window would ship identity-only, i.e. empty edges).
    #[test]
    fn stage_links_inline_fanout_edges_non_empty_for_udf_program() {
        let code = "\
add1 = \\x -> x + 1
a = add1(10)
b = add1(20)
a + b
";
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, code, consumer).expect("program compiles");

        let json = snapshot_json(&compiled, "udf.chl");
        let v: Value = serde_json::from_str(&json).expect("payload is valid JSON");

        // Collect the live node ids of a stage's shipped IR tree.
        let stages = v["stages"].as_array().expect("stages is an array");
        fn walk_ids(node: &Value, ids: &mut std::collections::HashSet<u64>) {
            ids.insert(node["nodeId"].as_u64().expect("nodeId is a number"));
            for c in node["children"].as_array().expect("children is an array") {
                walk_ids(&c["node"], ids);
            }
        }
        let stage_ids = |id: &str| {
            let stage = stages
                .iter()
                .find(|s| s["id"] == id)
                .unwrap_or_else(|| panic!("stage {id} is present"));
            let mut ids = std::collections::HashSet::new();
            walk_ids(&stage["ir"], &mut ids);
            ids
        };
        let up_ids = stage_ids("post-inference");
        let down_ids = stage_ids("post-desugar");

        let pane_links = v["paneLinks"].as_array().expect("paneLinks is an array");
        let link = pane_links
            .iter()
            .find(|l| l["from"] == "post-inference" && l["to"] == "post-desugar")
            .expect("the post-inference → post-desugar link entry is present");
        let edges = link["edges"].as_array().expect("edges is an array");
        assert!(
            !edges.is_empty(),
            "a two-site UDF fan-out must yield non-empty post-inference → post-desugar edges"
        );
        for (i, e) in edges.iter().enumerate() {
            let pair = e.as_array().expect("edge is an [up, down] pair");
            let u = pair[0].as_u64().expect("upstream id is a number");
            let d = pair[1].as_u64().expect("downstream id is a number");
            assert!(
                up_ids.contains(&u),
                "edges[{i}] upstream id {u} is a node in the post-inference stage"
            );
            assert!(
                down_ids.contains(&d),
                "edges[{i}] downstream id {d} is a node in the post-desugar stage"
            );
        }
    }

    /// Web dual-use: a program with a type error yields a non-empty
    /// `diagnostics` array, each entry structured `{severity, stage, message,
    /// span:{start,end}, labels}`. The infer diagnostic carries the span
    /// resolved at the `compile_program` boundary — the same span the terminal
    /// underlines — proving one `resolve`, two consumers.
    #[test]
    fn diagnose_json_emits_structured_infer_diagnostic() {
        let code = "1 and 2\n";
        let mut ctx = GlobalContext::default();
        let json = diagnose_json(&mut ctx, code, "prog.chl");
        let v: Value = serde_json::from_str(&json).expect("diagnostics JSON is valid");

        let diags = v["diagnostics"]
            .as_array()
            .expect("diagnostics is an array");
        assert!(!diags.is_empty(), "a type error produces diagnostics");

        let infer = diags
            .iter()
            .find(|d| d["stage"] == "infer")
            .expect("an infer-stage diagnostic is present");
        assert_eq!(infer["severity"], "error");
        assert!(
            infer["message"].as_str().is_some_and(|m| !m.is_empty()),
            "the diagnostic carries a non-empty message"
        );

        // span resolves to the offending source range (the `1 and 2` expression).
        let start = infer["span"]["start"].as_u64().expect("span.start");
        let end = infer["span"]["end"].as_u64().expect("span.end");
        assert!(start < end, "span is a non-empty range, got {start}..{end}");
        let pointed = &code[start as usize..end as usize];
        assert!(
            pointed.contains("and"),
            "span {start}..{end} covers the offending expression, points at {pointed:?}"
        );

        // labels mirror the primary span.
        let labels = infer["labels"].as_array().expect("labels is an array");
        assert_eq!(labels.len(), 1, "one label at the offending span");
        assert_eq!(labels[0]["span"]["start"].as_u64(), Some(start));
        assert_eq!(labels[0]["span"]["end"].as_u64(), Some(end));
    }

    /// A successful compile yields an empty `diagnostics` array (M1 has no
    /// warnings) — the standalone diagnostics endpoint's success shape.
    #[test]
    fn diagnose_json_empty_on_success() {
        let code = "1 + 2\n";
        let mut ctx = GlobalContext::default();
        let json = diagnose_json(&mut ctx, code, "prog.chl");
        let v: Value = serde_json::from_str(&json).expect("diagnostics JSON is valid");
        assert!(
            v["diagnostics"].as_array().expect("array").is_empty(),
            "a clean compile has no diagnostics"
        );
    }
}
