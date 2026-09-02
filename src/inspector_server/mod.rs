//! The inspector's transport edge: the read-only model rendered as JSON, and
//! the HTTP server that hands it to the frontend.
//!
//! The model itself is [`inspector_model`](crate::inspector_model), which owns
//! the payload shape and the indices it is built from and answers no positional
//! query. This module turns that payload into bytes — nothing here decides what
//! the payload says.
//!
//! # Snapshot serialization
//!
//! [`snapshot_json`] compiles-then-serializes: given a
//! [`CompiledProgram`](crate::ccl::context::CompiledProgram) it builds the
//! [`InspectorPayload`](crate::inspector_model::InspectorPayload) (via
//! `InspectedProgram::build_payload`) and renders it with `serde_json`. The
//! server's `GET /api/snapshot` route calls exactly this.
//!
//! Every path emits the whole payload. The wire has one shape, and
//! [`snapshot_json_pretty`] differs from [`snapshot_json`] in whitespace alone.
//!
//! # The frontend is a sibling directory, not a crate
//!
//! `cambra-inspector/web/` is the TypeScript frontend and its build; the bundle
//! it produces is embedded by [`serve`]. It is a JS project rather than a
//! workspace member because the Rust half of the inspector is this module.

mod serve;
pub mod wire_check;

pub use serve::{serve, snapshot_body_pretty};

use crate::ccl::context::CompiledProgram;
use crate::inspector_model::InspectedProgram;

/// Build the `/api/snapshot` payload for a compiled program and serialize it to
/// a JSON string.
///
/// This is the build-then-serialize entry [`serve`] calls per
/// request. `name` becomes the payload's `source.name` (the program's display
/// name). Serialization is infallible for this payload (it is plain data — no
/// maps with non-string keys, no custom errors), so a failure is a bug; we
/// surface it via `expect` rather than leaking a `serde_json::Error` into the
/// signature the server wants.
pub fn snapshot_json(compiled: &CompiledProgram, name: &str) -> String {
    let inspected = InspectedProgram::new(compiled);
    let payload = inspected.build_payload(name);
    serde_json::to_string(&payload).expect("snapshot payload serializes")
}

/// Pretty-printed [`snapshot_json`] — the byte format of the committed golden
/// fixtures (`cambra-inspector/web/src/__fixtures__/`).
///
/// The binary owns these bytes deliberately: the fixtures are byte-compared by
/// `ci.sh`'s `ci_fixtures` gate, so their formatter must be pinned by
/// Cargo.lock, not an external tool. Piping through `python3 -m json.tool` made
/// the corpus a function of the local Python version, and of `FORCE_COLOR` —
/// either silently rewrites every fixture and the gate reads it as drift.
pub fn snapshot_json_pretty(compiled: &CompiledProgram, name: &str) -> String {
    let inspected = InspectedProgram::new(compiled);
    let payload = inspected.build_payload(name);
    serde_json::to_string_pretty(&payload).expect("snapshot payload serializes")
}

#[cfg(test)]
mod tests {
    use super::wire_check::assert_snapshot_shape;
    use super::*;
    use crate::ccl::context::{GlobalContext, compile_program};

    use crate::interpreter::Consumer;
    use indoc::indoc;
    use serde_json::Value;

    const PROG: &str = indoc! {r#"
        g = 10
        def f(p, q):
          p + q + g
        f(1, 2)
    "#};

    /// Compile `code` and parse its `/api/snapshot` JSON back to a `Value`.
    fn snapshot_value(code: &str, name: &str) -> Value {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, code, consumer).expect("program compiles");
        serde_json::from_str(&snapshot_json(&compiled, name)).expect("payload is valid JSON")
    }

    /// The structural wire-shape contract — the Rust twin of the
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
        assert_eq!(v["meta"]["payloadKind"], "program");
        // A literal, not `SCHEMA_VERSION`: `assert_common_shape` already pins the
        // payload against the constant, so reading the constant here would assert
        // it equals itself. The literal is what fails when the constant moves.
        assert_eq!(v["meta"]["schema"], 1);
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

    /// The panes, ordered upstream → downstream, each with a populated node
    /// table.
    #[test]
    fn snapshot_panes_ordered_upstream_to_downstream() {
        let v = snapshot_value(PROG, "prog.chl");
        let panes = v["panes"].as_array().expect("panes is an array");
        assert_eq!(panes.len(), 6, "six pipeline panes");
        assert_eq!(panes[0]["id"], "pre-inference");
        assert_eq!(panes[1]["id"], "post-inference");
        assert_eq!(panes[2]["id"], "post-channelize");
        for (i, pane) in panes.iter().enumerate() {
            assert!(
                !pane["nodes"]
                    .as_array()
                    .unwrap_or_else(|| panic!("panes[{i}].nodes is an array"))
                    .is_empty(),
                "panes[{i}].nodes is non-empty"
            );
        }
    }

    /// A pane's `root` names an entry of its node table, and that entry carries
    /// the type in the first-class `type` field.
    #[test]
    fn snapshot_root_node_carries_type_field() {
        let v = snapshot_value(PROG, "prog.chl");
        let panes = v["panes"].as_array().expect("panes is an array");
        let pane = panes
            .iter()
            .find(|s| s["id"] == "post-inference")
            .expect("the post-inference pane is present");
        let root = pane["root"].as_u64().expect("root is a number");
        let node = pane["nodes"]
            .as_array()
            .expect("nodes is an array")
            .iter()
            .find(|n| n["nodeId"].as_u64() == Some(root))
            .expect("root names an entry of the pane's node table");
        assert!(
            node["type"].is_string(),
            "the root node carries the type in the dedicated field; got {}",
            node["type"]
        );
    }

    /// A known source position is covered by a shipped node's own `spans` — the
    /// containment lookup the consumer runs is answerable from the node table
    /// alone.
    #[test]
    fn a_source_position_is_covered_by_a_node_carrying_it() {
        let v = snapshot_value(PROG, "prog.chl");
        let pane = v["panes"]
            .as_array()
            .expect("panes is an array")
            .iter()
            .find(|s| s["id"] == "post-inference")
            .expect("the post-inference pane is present");
        let table: std::collections::HashSet<u64> = pane["nodes"]
            .as_array()
            .expect("nodes is an array")
            .iter()
            .map(|n| n["nodeId"].as_u64().expect("nodeId is a number"))
            .collect();
        let g_def_start = PROG.find('g').expect("g present") as u64;
        let covering: Vec<u64> = pane["nodes"]
            .as_array()
            .expect("nodes is an array")
            .iter()
            .filter(|n| {
                n["spans"]
                    .as_array()
                    .expect("spans is an array")
                    .iter()
                    .any(|sp| {
                        let start = sp["start"].as_u64().expect("span.start");
                        let end = sp["end"].as_u64().expect("span.end");
                        start <= g_def_start && g_def_start < end
                    })
            })
            .map(|n| n["nodeId"].as_u64().expect("nodeId is a number"))
            .collect();
        assert!(
            !covering.is_empty(),
            "the `g` def position is covered by a node's spans"
        );
        for id in covering {
            assert!(
                table.contains(&id),
                "the covering node {id} is an entry of the pane's table"
            );
        }
    }

    /// For a let-polymorphic program (`dup` used at two types), `paneLinks[0].edges`
    /// carries a genuine `u != d` fan-out edge — the monomorphization fan-out
    /// produces non-identity cross-pane edges alongside the dense self-edges.
    #[test]
    fn pane_links_edges_non_empty_for_polymorphic_program() {
        let code = indoc! {r#"
            dup = \x -> (x, x)
            a = dup(1)
            b = dup(2 == 2)
            a
        "#};
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
    /// payload's `post-inference → post-channelize` paneLinks entry has non-empty
    /// edges, each `[upstream, downstream]` pair joining a live node in the
    /// post-inference pane's table to a live node in the post-channelize pane's.
    ///
    /// This is the wire-level proof that the retained inline remap is actually
    /// consumed: without the pair→pass pane-links association reading it, the
    /// `CompiledProgram`-retained remap would never reach the payload (the
    /// second window would ship identity-only, i.e. empty edges).
    #[test]
    fn pane_links_inline_fanout_edges_non_empty_for_udf_program() {
        let code = indoc! {r#"
            add1 = \x -> x + 1
            a = add1(10)
            b = add1(20)
            a + b
        "#};
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, code, consumer).expect("program compiles");

        let json = snapshot_json(&compiled, "udf.chl");
        let v: Value = serde_json::from_str(&json).expect("payload is valid JSON");

        // The live node ids of a pane are its shipped node table, read directly.
        let panes = v["panes"].as_array().expect("panes is an array");
        let pane_ids = |id: &str| -> std::collections::HashSet<u64> {
            let pane = panes
                .iter()
                .find(|s| s["id"] == id)
                .unwrap_or_else(|| panic!("pane {id} is present"));
            pane["nodes"]
                .as_array()
                .expect("nodes is an array")
                .iter()
                .map(|n| n["nodeId"].as_u64().expect("nodeId is a number"))
                .collect()
        };
        let up_ids = pane_ids("post-inference");
        let down_ids = pane_ids("post-channelize");

        let pane_links = v["paneLinks"].as_array().expect("paneLinks is an array");
        let link = pane_links
            .iter()
            .find(|l| l["from"] == "post-inference" && l["to"] == "post-channelize")
            .expect("the post-inference → post-channelize link entry is present");
        let edges = link["edges"].as_array().expect("edges is an array");
        assert!(
            !edges.is_empty(),
            "a two-site UDF fan-out must yield non-empty post-inference → post-channelize edges"
        );
        for (i, e) in edges.iter().enumerate() {
            let pair = e.as_array().expect("edge is an [up, down] pair");
            let u = pair[0].as_u64().expect("upstream id is a number");
            let d = pair[1].as_u64().expect("downstream id is a number");
            assert!(
                up_ids.contains(&u),
                "edges[{i}] upstream id {u} is a node in the post-inference pane"
            );
            assert!(
                down_ids.contains(&d),
                "edges[{i}] downstream id {d} is a node in the post-channelize pane"
            );
        }
    }
}
