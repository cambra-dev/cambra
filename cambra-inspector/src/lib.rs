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
//! [`InspectorPayload`](cambra::inspector_model::InspectorPayload) (via
//! `InspectedProgram::build_payload`) and renders it with `serde_json`. The [`server`]'s
//! `GET /api/snapshot` route calls exactly this.

pub mod server;

use cambra::ccl::context::{CompiledProgram, GlobalContext, compile_program};
use cambra::inspector_model::{
    InspectedProgram, InspectorPayload, diagnostics_from_compile_errors,
};
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
    let inspected = InspectedProgram::new(compiled);
    let payload = inspected.build_payload(name);
    serde_json::to_string(&payload).expect("snapshot payload serializes")
}

/// Pretty-printed [`snapshot_json`] — the byte format of the committed golden
/// fixtures (`web/src/__fixtures__/`).
///
/// The binary owns these bytes deliberately: the fixtures are byte-compared by
/// `ci.sh`'s `ci_fixtures` gate, so their formatter must be pinned by
/// Cargo.lock, not an external tool. Piping through `python3 -m json.tool` made
/// the corpus a function of the local Python version, and of `FORCE_COLOR` —
/// either silently rewrites every fixture and the gate reads it as drift.
/// Serializes the typed payload directly wherever it can. The slimmed path
/// cannot, and [`render_pretty`] carries what makes its `serde_json::Value`
/// round-trip byte-identical anyway.
///
/// `retention` slims the committed fixture on the big/volatile corpus programs
/// (a pane subset and/or elided `paneLinks`, per
/// `cambra-inspector/scripts/fixtures.manifest`). The live server never calls
/// this with anything but [`FixtureRetention::FULL`] — the pruning is a fixture
/// concern, applied *after* building the full payload so the build path stays
/// single.
pub fn snapshot_json_pretty(
    compiled: &CompiledProgram,
    name: &str,
    retention: &FixtureRetention,
) -> String {
    let inspected = InspectedProgram::new(compiled);
    let payload = inspected.build_payload(name);
    render_pretty(&payload, retention)
}

/// Fixture-only payload slimming: which panes a golden dump retains and whether
/// it ships `paneLinks`.
///
/// This exists **solely** for the `--dump-snapshot` fixture path (driven by
/// `cambra-inspector/scripts/fixtures.manifest`). The live server and a
/// flagless `--dump-snapshot` always emit the full wire ([`FixtureRetention::FULL`]).
/// Slimming trims what the byte-exact golden corpus pins on the big, volatile
/// programs — `paneLinks` is ~4 lines per edge and grows super-linearly across
/// the collapsed channelize window — without touching the live contract.
///
/// It lives in this crate rather than in `cambra::inspector_model` because it is
/// a property of the *corpus*, not of the read model: this crate owns the
/// fixtures (`src/inspector_model/design.md`, "The schema version"), and the
/// payload type must not grow an `Option` field so a test corpus can be smaller.
#[derive(Clone, Debug)]
pub struct FixtureRetention {
    /// Pane ids to retain (in the payload's existing pipeline order), or `None`
    /// to keep every pane.
    pub panes: Option<Vec<String>>,
    /// Whether to ship `paneLinks`. `false` omits the field entirely — never an
    /// empty array, which would claim the live wire carries no edges.
    pub links: bool,
}

impl FixtureRetention {
    /// The full wire: every pane, links shipped. The live default.
    pub const FULL: FixtureRetention = FixtureRetention {
        panes: None,
        links: true,
    };

    /// Is this the full wire (no pruning)? The fast path that lets
    /// [`render_pretty`] serialize the typed payload directly.
    pub fn is_full(&self) -> bool {
        self.panes.is_none() && self.links
    }
}

impl Default for FixtureRetention {
    fn default() -> Self {
        FixtureRetention::FULL
    }
}

/// Pretty-print a payload, pruned per `retention`.
///
/// The full-wire case serializes the typed payload directly, which is what the
/// live path and every unslimmed fixture take. Pruning needs a field *omitted*
/// rather than emptied, which `Serialize` on a fixed struct cannot express, so
/// the slimmed case goes through `serde_json::Value`. That is byte-safe only
/// because this crate enables `serde_json/preserve_order`: a `Value` is an
/// insertion-ordered map, so a round-trip re-emits the struct's field order
/// rather than sorting it. `both_render_paths_agree_on_a_full_payload` pins that
/// the two paths produce identical bytes.
fn render_pretty(payload: &InspectorPayload, retention: &FixtureRetention) -> String {
    if retention.is_full() {
        return serde_json::to_string_pretty(payload).expect("snapshot payload serializes");
    }
    let mut value = serde_json::to_value(payload).expect("snapshot payload serializes");
    prune_for_fixture(&mut value, retention);
    serde_json::to_string_pretty(&value).expect("pruned snapshot payload serializes")
}

/// Slim a serialized payload for the committed golden corpus.
///
/// * `panes = Some(keep)` retains only the listed panes (preserving the
///   payload's pipeline order) and drops any `paneLinks` window naming a dropped
///   pane, so the slimmed payload still validates.
/// * `links = false` omits `paneLinks` entirely.
fn prune_for_fixture(value: &mut serde_json::Value, retention: &FixtureRetention) {
    let Some(obj) = value.as_object_mut() else {
        return;
    };
    if let Some(keep) = &retention.panes {
        let named = |v: Option<&serde_json::Value>| {
            v.and_then(serde_json::Value::as_str)
                .is_some_and(|id| keep.iter().any(|k| k == id))
        };
        if let Some(panes) = obj
            .get_mut("panes")
            .and_then(serde_json::Value::as_array_mut)
        {
            panes.retain(|p| named(p.get("id")));
        }
        if let Some(links) = obj
            .get_mut("paneLinks")
            .and_then(serde_json::Value::as_array_mut)
        {
            links.retain(|l| named(l.get("from")) && named(l.get("to")));
        }
    }
    if !retention.links {
        obj.remove("paneLinks");
    }
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
/// (`web/src/wireValidate.ts`). Asserting the wire contract in one place
/// lets both the lib and `server` test modules reuse it (the cross-language
/// twin of the TS validator, since the two cannot literally share code).
///
/// The validator is parameterized by a [`FixtureContext`]: the **live** contract
/// (all three panes, `paneLinks` present) is the default; the **fixture** context
/// additionally accepts a slimmed golden dump (a non-empty ordered pane subset,
/// and an absent `paneLinks` meaning "elided for fixture slimming"). Slimming
/// only ever relaxes the fixture path — the live wire contract is unchanged.
#[cfg(test)]
pub(crate) mod test_support {
    use serde_json::Value;

    /// Which contract a payload is validated against. The live wire always ships
    /// the full pipeline; a committed fixture dump may be slimmed.
    #[derive(Clone, Copy, PartialEq, Debug)]
    pub(crate) enum FixtureContext {
        /// A live/served payload: every pane, `paneLinks` present.
        Live,
        /// A committed golden fixture: `panes` may be an ordered subset and
        /// `paneLinks` may be absent (elided for slimming).
        Fixture,
    }

    /// The pane ids, in upstream → downstream order — the exact pane list a live
    /// successful payload ships as `panes` (a slimmed fixture retains an ordered
    /// subset).
    ///
    /// This is a **pin, not a derivation**: the producer builds its panes from
    /// the compiler's `PANES` table, so reading that table here would make the
    /// validator agree with the producer by construction and check nothing. A
    /// pane added upstream is meant to fail this list, and the failure is the
    /// notice that the wire changed.
    const PANE_IDS: [&str; 6] = [
        "pre-inference",
        "post-inference",
        "post-channelize",
        "post-as-of-read",
        "post-lambda-elim",
        "post-planning",
    ];
    /// The per-pane `kind` discriminants, aligned with [`PANE_IDS`]: the
    /// pre-inference tree is hole-typed (`"holes"`); every tree from
    /// post-inference on is fully typed (`"typed"`).
    const PANE_KINDS: [&str; 6] = ["holes", "typed", "typed", "typed", "typed", "typed"];
    /// The adjacent pane windows, in order — the exact `paneLinks` from/to
    /// pairs a live successful payload ships (a slimmed fixture may retain an
    /// ordered subset, or omit `paneLinks` entirely). One shorter than
    /// [`PANE_IDS`].
    const PANE_WINDOWS: [(&str, &str); 5] = [
        ("pre-inference", "post-inference"),
        ("post-inference", "post-channelize"),
        ("post-channelize", "post-as-of-read"),
        ("post-as-of-read", "post-lambda-elim"),
        ("post-lambda-elim", "post-planning"),
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
    ];
    /// The rewrite-tag `nature` discriminants (the wire lowercases them).
    /// Deliberately **omits** `"source"`: a direct-image (`Nature::Source`) tag
    /// null-compresses to `rewritten: null` at the emission sites, so `"source"`
    /// must never reach the wire — `assert_rewrite_shape` guards that boundary
    /// explicitly, and this list would fail it regardless.
    const ALLOWED_NATURE: &[&str] = &["expansion", "machinery"];

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
    /// A slimmed fixture holds a pane subset, so the kinds cannot be compared
    /// positionally against [`PANE_KINDS`]; each retained pane is checked against
    /// the kind its own id mandates instead.
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
    /// table closed under its own child edges and `root`, each pane's
    /// `spanIndex` non-empty, the windowed `paneLinks` with matching from/to ids
    /// and every edge endpoint a live node id in its respective pane (self-edges
    /// legal), and every node's `rewritten` tag in the observed vocabulary.
    /// Panics naming the offending path otherwise. Does not assert
    /// program-specific content — that is each caller's job.
    ///
    /// [`FixtureContext::Live`] pins the full pipeline (every pane, `paneLinks`
    /// present); [`FixtureContext::Fixture`] additionally accepts a slimmed
    /// golden dump (a non-empty ordered pane subset, and an absent `paneLinks`
    /// meaning "elided for slimming").
    pub(crate) fn assert_snapshot_shape(v: &Value, ctx: FixtureContext) {
        assert_common_shape(v);

        // An earlier wire retired the legacy top-level `ir`/`spanIndex` (byte-for-byte
        // duplicates of the post-inference pane). They must be *absent*, not
        // merely null — the client reads the panes, never the top level.
        assert!(v.get("ir").is_none(), "the wire has no top-level ir");
        assert!(
            v.get("spanIndex").is_none(),
            "the wire has no top-level spanIndex"
        );

        // The panes, in pipeline order, with their kinds. Live: exactly the
        // declared list. Fixture: a non-empty, in-pipeline-order subset (fixture
        // slimming may drop panes).
        let panes = v["panes"].as_array().expect("panes is an array");
        let ids: Vec<&str> = panes
            .iter()
            .map(|s| s["id"].as_str().expect("pane id is a string"))
            .collect();
        match ctx {
            FixtureContext::Live => assert_eq!(
                ids, PANE_IDS,
                "panes are the pipeline panes in upstream → downstream order"
            ),
            FixtureContext::Fixture => {
                assert!(!ids.is_empty(), "a slimmed fixture retains ≥1 pane");
                assert!(
                    is_ordered_subsequence(&ids, &PANE_IDS),
                    "slimmed panes {ids:?} are a non-empty subset of {PANE_IDS:?} in order"
                );
            }
        }
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

        // paneLinks. Live: always present. Fixture: may be *absent* (elided for
        // slimming) — but if present, still validated.
        let links = match v.get("paneLinks") {
            None => {
                assert_eq!(
                    ctx,
                    FixtureContext::Fixture,
                    "paneLinks is absent — only a slimmed fixture may elide it"
                );
                return;
            }
            Some(l) => l.as_array().expect("paneLinks is an array"),
        };

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
        match ctx {
            FixtureContext::Live => assert_eq!(
                windows,
                PANE_WINDOWS.to_vec(),
                "paneLinks are the adjacent pane windows in pipeline order"
            ),
            FixtureContext::Fixture => assert!(
                is_ordered_subsequence(&windows, &PANE_WINDOWS),
                "slimmed paneLinks {windows:?} are a subset of {PANE_WINDOWS:?} in order"
            ),
        }
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

    /// Is `sub` a subsequence of `full` (same relative order, gaps allowed)?
    /// Used to accept a slimmed fixture's pane / window subset.
    fn is_ordered_subsequence<T: PartialEq>(sub: &[T], full: &[T]) -> bool {
        let mut it = full.iter();
        sub.iter().all(|x| it.any(|y| y == x))
    }

    /// Assert `v` is a structurally-valid **degraded** payload: the
    /// retired top-level `ir`/`spanIndex` absent, empty `panes`/`paneLinks`,
    /// `payloadKind: "failed"`. A degraded payload always ships an (empty but
    /// present) `paneLinks` array — only a slimmed *success* fixture ever omits
    /// the field.
    pub(crate) fn assert_degraded_snapshot_shape(v: &Value) {
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
            cambra::inspector_model::SCHEMA_VERSION,
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

    /// Assert a pane's node table: `root` and every child `id` name an entry of
    /// this same pane's `nodes`, no id appears twice, and every node carries the
    /// wire's node shape.
    ///
    /// The closure check is what the table buys over the nested tree it
    /// replaced: an edge a consumer follows always lands on an entry it holds.
    fn assert_node_table(pane: &Value, at: &str) {
        assert!(
            pane.get("ir").is_none(),
            "{at} has no `ir` tree — a pane ships `root` + `nodes`"
        );
        // The parallel span table shipped one row per node per span, which is
        // what a node's own `spans` says.
        assert!(
            pane.get("spanIndex").is_none(),
            "{at} has no `spanIndex` — a node carries its own spans"
        );
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
        let root = pane["root"]
            .as_u64()
            .unwrap_or_else(|| panic!("{at}.root is a number"));
        assert!(
            ids.contains(&root),
            "{at}.root {root} names an entry of {at}.nodes"
        );
        for (i, n) in nodes.iter().enumerate() {
            assert_ir_node(n, &format!("{at}.nodes[{i}]"), &ids);
            assert_rewrite_shape(n, &format!("{at}.nodes[{i}]"));
        }
    }

    /// Assert one entry of a pane's node table: the scalar fields, the retired
    /// fields' absence, and `{edge, id, predicate}` children resolving within
    /// `ids`.
    fn assert_ir_node(v: &Value, at: &str, ids: &std::collections::HashSet<u64>) {
        assert!(v["label"].is_string(), "{at}.label is a string");
        assert!(v["nodeId"].is_number(), "{at}.nodeId is a number");
        // `annotations` and `tiling` were tile-producer fields on the renderer's
        // node that the payload never set; the wire's own node type has neither.
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
}

#[cfg(test)]
mod tests {
    use super::test_support::{FixtureContext, assert_snapshot_shape};
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

    /// The structural wire-shape contract — the Rust twin of the
    /// frontend's `validateSnapshot`. Program-specific facts are asserted by the
    /// focused tests below.
    #[test]
    fn snapshot_json_is_structurally_valid() {
        assert_snapshot_shape(&snapshot_value(PROG, "prog.chl"), FixtureContext::Live);
    }

    /// A slimmed fixture dump — a pane subset with `paneLinks` elided — omits
    /// `paneLinks`, keeps every retained pane's own node table and `spanIndex`,
    /// and validates under the fixture context (the live contract rejects the
    /// subset). Exercises both `prune_for_fixture` and the validator relaxation.
    #[test]
    fn slimmed_fixture_payload_validates_in_fixture_context() {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, PROG, consumer).expect("program compiles");
        let retention = FixtureRetention {
            panes: Some(vec![
                "post-inference".to_string(),
                "post-channelize".to_string(),
            ]),
            links: false,
        };
        let json = snapshot_json_pretty(&compiled, "prog.chl", &retention);
        let v: Value = serde_json::from_str(&json).expect("payload is valid JSON");
        let panes = v["panes"].as_array().expect("panes array");
        assert_eq!(
            panes.iter().map(|p| &p["id"]).collect::<Vec<_>>(),
            vec!["post-inference", "post-channelize"],
            "the pane subset retained exactly the two named panes, in pipeline order"
        );
        assert!(v.get("paneLinks").is_none(), "elided paneLinks is absent");
        // Slimming drops panes and links; it never touches what a retained pane
        // says about itself.
        assert!(
            panes[0]["nodes"]
                .as_array()
                .expect("nodes array")
                .iter()
                .any(|n| !n["spans"].as_array().expect("spans array").is_empty()),
            "a retained pane keeps its nodes' own spans"
        );
        assert_snapshot_shape(&v, FixtureContext::Fixture);
    }

    /// A pane subset that keeps `paneLinks` drops the windows naming a dropped
    /// pane, rather than shipping an edge into a pane the fixture no longer
    /// holds.
    #[test]
    fn a_pane_subset_drops_the_windows_naming_a_dropped_pane() {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, PROG, consumer).expect("program compiles");
        let retention = FixtureRetention {
            panes: Some(vec![
                "post-inference".to_string(),
                "post-channelize".to_string(),
            ]),
            links: true,
        };
        let json = snapshot_json_pretty(&compiled, "prog.chl", &retention);
        let v: Value = serde_json::from_str(&json).expect("payload is valid JSON");
        assert_eq!(
            v["paneLinks"]
                .as_array()
                .expect("paneLinks array")
                .iter()
                .map(|l| (l["from"].as_str().unwrap(), l["to"].as_str().unwrap()))
                .collect::<Vec<_>>(),
            vec![("post-inference", "post-channelize")],
            "only the window whose both endpoints survive is retained"
        );
        assert_snapshot_shape(&v, FixtureContext::Fixture);
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

    /// The two `render_pretty` paths agree byte-for-byte on a full payload.
    ///
    /// The slimmed path round-trips through `serde_json::Value`, which is only
    /// byte-safe because this crate enables `serde_json/preserve_order`. Without
    /// that feature a `Value` sorts its keys and every slimmed fixture would
    /// differ from an unslimmed one in field order alone. Pinning the agreement
    /// here is what makes the feature load-bearing rather than incidental.
    #[test]
    fn both_render_paths_agree_on_a_full_payload() {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, PROG, consumer).expect("program compiles");
        let payload =
            cambra::inspector_model::InspectedProgram::new(&compiled).build_payload("prog.chl");
        // `panes: Some(every id)` is not the full wire by `is_full`, so it takes
        // the Value path while pruning nothing.
        let every_pane = FixtureRetention {
            panes: Some(
                payload
                    .panes
                    .iter()
                    .map(|p| p.id.to_string())
                    .collect::<Vec<_>>(),
            ),
            links: true,
        };
        assert!(
            !every_pane.is_full(),
            "the Value path is the one under test"
        );
        assert_eq!(
            render_pretty(&payload, &FixtureRetention::FULL),
            render_pretty(&payload, &every_pane),
            "the direct and Value render paths disagree — serde_json/preserve_order \
             is missing or a field order changed"
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

    /// Web dual-use: a program with a type error yields a non-empty
    /// `diagnostics` array, each entry structured `{severity, stage, message,
    /// span:{start,end}}`. The infer diagnostic carries the span
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
            .expect("an infer diagnostic is present");
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

        // The span is the whole of what a consumer underlines: a diagnostic is
        // built from one error, so a label list could only repeat it.
        assert!(
            infer.get("labels").is_none(),
            "a diagnostic ships no labels array"
        );
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
