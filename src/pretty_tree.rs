//! Generic tree-rendering IR and renderer.
//!
//! Provides [`InspectNode`], a lightweight tree description type, and functions
//! to render it to a string using Unicode box-drawing connectors:
//!
//! ```text
//! BinOp(+)
//! ├── left: Literal(1)
//! └── right: Literal(2)
//! ```
//!
//! This module has no dependencies on interpreter or domain types — it is
//! purely a tree renderer used by [`crate::pretty_graph`].

// Box-drawing connector strings, used by render_node.
const CONNECTOR_LAST: &str = "└── ";
const CONNECTOR_MID: &str = "├── ";
const INDENT_LAST: &str = "    ";
const INDENT_MID: &str = "│   ";

/// Structured description of a tree node for rendering.
///
/// Derives Debug and Clone so that the visualization IR itself can be
/// inspected and snapshotted — a debugging tool should itself be debuggable.
#[derive(Debug, Clone)]
pub struct InspectNode {
    /// Node label, e.g. "Lambda(x)", "BinOp(+)"
    pub label: String,
    /// Generic display annotations shown after the label, e.g. ": Int → Int"
    pub annotations: Vec<String>,
    /// The tiling / output shape of this node, e.g. "[f32; 100]".
    /// Stored separately from `annotations` so renderers can display it
    /// with dedicated styling (e.g. as a subtitle in the web inspector).
    pub tiling: Option<String>,
    /// Formatted yield guard; always displayed when present.
    pub yield_guard: Option<String>,
    /// Formatted obsolete/release guard; shown in verbose mode.
    pub obsolete_guard: Option<String>,
    /// Formatted intent guard; shown in verbose mode.
    pub intent_guard: Option<String>,
    /// Children with optional edge labels, e.g. ("left", child_desc)
    pub children: Vec<(String, InspectNode)>,

    // --- Inspector source-linking fields (added for `expand`, I2) ---
    //
    // These extend the tree node additively so the inspector's `expand` query
    // can cross-link a tree row to source + types + provenance, while the CLI
    // Unicode renderer and the existing `to_json` shape stay unaffected (all
    // `None`/absent for the non-inspector callers in `pretty_graph` etc.).
    //
    // Stored as primitives — `u64` node id, `(start, end)` byte span — to keep
    // `pretty_tree` free of any `ccl`/domain-type dependency (the module's
    // standing invariant: it is a pure tree renderer). The inspector query layer
    // converts its `NodeId`/`Span`/`Type` into these.
    /// The IR node's stable id (its `NodeId` as a wire number), if this row
    /// corresponds to an IR node.
    pub node_id: Option<u64>,
    /// The node's primary source span `(start, end)` (byte offsets), if known.
    pub span: Option<(usize, usize)>,
    /// The node's provenance kind label (e.g. `"Source"`, `"Derived(Mono)"`), if
    /// known.
    pub provenance: Option<String>,
    /// The node's type as a Display string (e.g. `"Int"`, `"(Int ⇒ Int)"`, or a
    /// hole `"_"`/`"?N"` pre-inference), if this row corresponds to a typed IR
    /// node. A dedicated field rather than a positional `annotations[0]` entry:
    /// the type is a first-class wire field (`"type"`), not smuggled into the
    /// free-form annotation list, so a consumer reads `node.type` directly. The
    /// string is CCL's canonical type rendering (`Display for Type`), so any
    /// change there changes this verbatim — see `crate::ccl::Type`.
    pub ty: Option<String>,
}

impl InspectNode {
    /// Create a new node with no annotations or children.
    pub fn new(label: impl Into<String>) -> Self {
        InspectNode {
            label: label.into(),
            annotations: Vec::new(),
            tiling: None,
            yield_guard: None,
            obsolete_guard: None,
            intent_guard: None,
            children: Vec::new(),
            node_id: None,
            span: None,
            provenance: None,
            ty: None,
        }
    }

    /// Create a leaf node (no children).
    pub fn leaf(label: impl Into<String>) -> Self {
        Self::new(label)
    }

    /// Add an annotation (shown after label on same line).
    pub fn annotate(mut self, annotation: impl Into<String>) -> Self {
        self.annotations.push(annotation.into());
        self
    }

    /// Set the tiling / output shape (shown as a subtitle in graphical renderers).
    pub fn with_tiling(mut self, tiling: impl Into<String>) -> Self {
        self.tiling = Some(tiling.into());
        self
    }

    /// Set the yield guard (always shown when present).
    pub fn with_yield_guard(mut self, guard: impl Into<String>) -> Self {
        self.yield_guard = Some(guard.into());
        self
    }

    /// Set the obsolete/release guard (shown in verbose mode).
    pub fn with_obsolete_guard(mut self, guard: impl Into<String>) -> Self {
        self.obsolete_guard = Some(guard.into());
        self
    }

    /// Set the intent guard (shown in verbose mode).
    pub fn with_intent_guard(mut self, guard: impl Into<String>) -> Self {
        self.intent_guard = Some(guard.into());
        self
    }

    /// Add a child with an edge label (empty string for no label).
    pub fn child(mut self, edge: impl Into<String>, child: InspectNode) -> Self {
        self.children.push((edge.into(), child));
        self
    }

    /// Set the inspector node id (wire number). Additive — see the field docs.
    pub fn with_node_id(mut self, id: u64) -> Self {
        self.node_id = Some(id);
        self
    }

    /// Set the inspector source span `(start, end)`. Additive.
    pub fn with_node_span(mut self, span: (usize, usize)) -> Self {
        self.span = Some(span);
        self
    }

    /// Set the node's type (a CCL `Display` string). Additive — see the field docs.
    pub fn with_type(mut self, ty: impl Into<String>) -> Self {
        self.ty = Some(ty.into());
        self
    }

    /// Set the inspector provenance-kind label. Additive.
    pub fn with_provenance(mut self, kind: impl Into<String>) -> Self {
        self.provenance = Some(kind.into());
        self
    }

    /// Serialize this node tree to a JSON string without serde.
    ///
    /// Field names mirror the Rust struct fields. `None` guard fields are
    /// omitted. Children serialize as `{"edge":"...","node":{...}}` pairs,
    /// preserving edge labels.
    pub fn to_json(&self) -> String {
        let ann_strs: Vec<String> = self
            .annotations
            .iter()
            .map(|a| format!("\"{}\"", escape_json(a)))
            .collect();
        let children_strs: Vec<String> = self
            .children
            .iter()
            .map(|(edge, child)| {
                format!(
                    "{{\"edge\":\"{}\",\"node\":{}}}",
                    escape_json(edge),
                    child.to_json()
                )
            })
            .collect();

        let mut json = format!("{{\"label\":\"{}\"", escape_json(&self.label));
        json.push_str(&format!(",\"annotations\":[{}]", ann_strs.join(",")));
        // Inspector source-linking fields (I2): emitted only when present, so
        // non-inspector callers' JSON is unchanged.
        if let Some(id) = self.node_id {
            json.push_str(&format!(",\"node_id\":{id}"));
        }
        if let Some((start, end)) = self.span {
            json.push_str(&format!(",\"span\":{{\"start\":{start},\"end\":{end}}}"));
        }
        if let Some(ref p) = self.provenance {
            json.push_str(&format!(",\"provenance\":\"{}\"", escape_json(p)));
        }
        if let Some(ref t) = self.ty {
            json.push_str(&format!(",\"type\":\"{}\"", escape_json(t)));
        }
        if let Some(ref t) = self.tiling {
            json.push_str(&format!(",\"tiling\":\"{}\"", escape_json(t)));
        }
        if let Some(ref g) = self.yield_guard {
            json.push_str(&format!(",\"yield_guard\":\"{}\"", escape_json(g)));
        }
        if let Some(ref g) = self.obsolete_guard {
            json.push_str(&format!(",\"obsolete_guard\":\"{}\"", escape_json(g)));
        }
        if let Some(ref g) = self.intent_guard {
            json.push_str(&format!(",\"intent_guard\":\"{}\"", escape_json(g)));
        }
        json.push_str(&format!(",\"children\":[{}]}}", children_strs.join(",")));
        json
    }
}

// Wire shape (inspector, feature `serde`): the `expand`-node / `ir`-root shape
// the `/api/snapshot` schema specifies. Field names are camelCase (`nodeId`),
// `None` optional fields are skipped, and children serialize as
// `{ "edge": "...", "node": { ... } }` pairs — matching the hand-rolled
// [`InspectNode::to_json`] above, which the serde-free CLI path still uses.
// Hand-written (not derived) because the `children: Vec<(String, InspectNode)>`
// pairs need the `{edge,node}` reshaping and the field key is `nodeId`, not
// `node_id`.
#[cfg(feature = "serde")]
impl serde::Serialize for InspectNode {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;

        /// A `{ "edge", "node" }` child pair, serialized to mirror `to_json`.
        struct Child<'a>(&'a str, &'a InspectNode);
        impl serde::Serialize for Child<'_> {
            fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                let mut s = serializer.serialize_struct("Child", 2)?;
                s.serialize_field("edge", self.0)?;
                s.serialize_field("node", self.1)?;
                s.end()
            }
        }

        /// `{ "start", "end" }`, matching the `Span` wire shape.
        #[derive(serde::Serialize)]
        struct WireSpan {
            start: usize,
            end: usize,
        }

        let children: Vec<Child<'_>> = self
            .children
            .iter()
            .map(|(edge, node)| Child(edge, node))
            .collect();
        let span = self.span.map(|(start, end)| WireSpan { start, end });

        let mut s = serializer.serialize_struct("InspectNode", 9)?;
        s.serialize_field("label", &self.label)?;
        s.serialize_field("annotations", &self.annotations)?;
        s.serialize_field("nodeId", &self.node_id)?;
        s.serialize_field("span", &span)?;
        s.serialize_field("provenance", &self.provenance)?;
        s.serialize_field("type", &self.ty)?;
        s.serialize_field("tiling", &self.tiling)?;
        s.serialize_field("children", &children)?;
        s.end()
    }
}

/// Escape special characters for embedding in a JSON string.
fn escape_json(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

impl std::fmt::Display for InspectNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", render(self))
    }
}

// ---------------------------------------------------------------------------
// Tree renderer
// ---------------------------------------------------------------------------

/// Render an [`InspectNode`] tree to a string with box-drawing connectors.
///
/// Uses no depth limit; see [`render_with_max_depth`] for bounded rendering.
pub fn render(node: &InspectNode) -> String {
    render_with_max_depth(node, None)
}

/// Render an [`InspectNode`] tree with an optional depth limit.
///
/// Nodes beyond `max_depth` levels are replaced with a truncation indicator
/// showing the count of elided descendants.
pub fn render_with_max_depth(node: &InspectNode, max_depth: Option<usize>) -> String {
    let mut out = String::new();
    render_node(&mut out, node, "", 0, max_depth);
    out
}

fn count_descendants(node: &InspectNode) -> usize {
    let mut count = 0;
    for (_, child) in &node.children {
        count += 1 + count_descendants(child);
    }
    count
}

fn render_node(
    out: &mut String,
    node: &InspectNode,
    prefix: &str,
    depth: usize,
    max_depth: Option<usize>,
) {
    // Write label + annotations + tiling on one line.
    out.push_str(&node.label);
    for ann in &node.annotations {
        out.push(' ');
        out.push_str(ann);
    }
    if let Some(ref t) = node.tiling {
        out.push(' ');
        out.push_str(t);
    }
    // Append structured guard fields after annotations.
    if let Some(ref g) = node.yield_guard {
        out.push_str(&format!(" [yield: {g}]"));
    }
    if let Some(ref g) = node.obsolete_guard {
        out.push_str(&format!(" [obsolete: {g}]"));
    }
    if let Some(ref g) = node.intent_guard {
        out.push_str(&format!(" [intent: {g}]"));
    }

    // Check depth limit before rendering children.
    if let Some(max) = max_depth
        && depth >= max
        && !node.children.is_empty()
    {
        let n = count_descendants(node);
        out.push_str(&format!(" ... ({n} more nodes)"));
        out.push('\n');
        return;
    }

    out.push('\n');

    // Write children with tree connectors.
    for (i, (edge, child)) in node.children.iter().enumerate() {
        let is_last = i + 1 == node.children.len();
        let (connector, child_ext) = if is_last {
            (CONNECTOR_LAST, INDENT_LAST)
        } else {
            (CONNECTOR_MID, INDENT_MID)
        };
        let child_prefix = format!("{prefix}{child_ext}");

        out.push_str(prefix);
        out.push_str(connector);
        if !edge.is_empty() {
            out.push_str(edge);
            out.push_str(": ");
        }
        render_node(out, child, &child_prefix, depth + 1, max_depth);
    }
}
