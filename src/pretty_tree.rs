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
//! purely a tree renderer used by both [`crate::pretty_graph`] and
//! [`crate::pretty_ast`].

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
    /// Formatted yield guard; always displayed when present.
    pub yield_guard: Option<String>,
    /// Formatted obsolete/release guard; shown in verbose mode.
    pub obsolete_guard: Option<String>,
    /// Formatted intent guard; shown in verbose mode.
    pub intent_guard: Option<String>,
    /// Children with optional edge labels, e.g. ("left", child_desc)
    pub children: Vec<(String, InspectNode)>,
}

impl InspectNode {
    /// Create a new node with no annotations or children.
    pub fn new(label: impl Into<String>) -> Self {
        InspectNode {
            label: label.into(),
            annotations: Vec::new(),
            yield_guard: None,
            obsolete_guard: None,
            intent_guard: None,
            children: Vec::new(),
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
    // Write label + annotations on one line.
    out.push_str(&node.label);
    for ann in &node.annotations {
        out.push(' ');
        out.push_str(ann);
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
    if let Some(max) = max_depth {
        if depth >= max && !node.children.is_empty() {
            let n = count_descendants(node);
            out.push_str(&format!(" ... ({n} more nodes)"));
            out.push('\n');
            return;
        }
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
