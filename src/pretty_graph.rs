//! Compact pretty-printer for CCL operator and dataflow graphs.
//!
//! Provides two views of a program:
//! - **Operator AST**: The static operator tree (how `subscribe()` traverses operators)
//! - **Dataflow**: The runtime producer tree (how `get()` traverses producers)
//!
//! ```text
//! BinOp(+) : Int
//! ├── left: Literal(1) : Int
//! └── right: VarRef(x) : Int
//! ```

use crate::interpreter::{
    tile_operators::{TileOperator, TileProducer},
    ArithmeticKind, BaseType, BinOpKind, CompareKind, Extent, LogicKind,
};
pub use crate::pretty_tree::{render, render_with_max_depth, InspectNode};

/// Mode labels for variable subscription display.
pub const MODE_ITERATION: &str = "iteration";
pub const MODE_ARGUMENT: &str = "argument";

// ---------------------------------------------------------------------------
// Options
// ---------------------------------------------------------------------------

/// Options controlling visualization verbosity.
///
/// Derives Debug and Clone so that callers can inspect options during
/// troubleshooting and clone-then-modify for per-subtree overrides —
/// a debugging tool should itself be debuggable.
#[derive(Debug, Clone)]
pub struct VizOptions {
    /// Include non-yield guard values (release, predicate, intent — can be verbose).
    /// Yield guards are always shown since they are the primary progress signal.
    pub show_guards: bool,
    /// Include extent/type annotations
    pub show_extents: bool,
    /// Maximum tree depth to render. Nodes beyond this depth are replaced
    /// with a truncation indicator. `None` means unlimited.
    pub max_depth: Option<usize>,
}

impl Default for VizOptions {
    fn default() -> Self {
        VizOptions {
            show_guards: false,
            show_extents: true,
            max_depth: Some(15),
        }
    }
}

impl VizOptions {
    /// All details hidden (minimal output).
    pub fn minimal() -> Self {
        VizOptions {
            show_guards: false,
            show_extents: false,
            max_depth: Some(15),
        }
    }

    /// All details shown (maximum verbosity).
    pub fn verbose() -> Self {
        VizOptions {
            show_guards: true,
            show_extents: true,
            max_depth: None,
        }
    }
}

// ---------------------------------------------------------------------------
// Compact formatting helpers
// ---------------------------------------------------------------------------

/// Format an Extent compactly for display.
pub fn fmt_extent(extent: &Extent) -> String {
    match extent {
        Extent::Base(base) => match base {
            BaseType::Int => "Int".to_string(),
            BaseType::UInt => "UInt".to_string(),
            BaseType::String => "String".to_string(),
            BaseType::Bool => "Bool".to_string(),
            BaseType::Unit => "Unit".to_string(),
        },
        Extent::Function { domain, codomain } => {
            let d = fmt_extent(domain);
            let c = fmt_extent(codomain);
            if matches!(domain.as_ref(), Extent::Function { .. }) {
                format!("({d}) → {c}")
            } else {
                format!("{d} → {c}")
            }
        }
        Extent::Record(fields) => {
            let mut parts: Vec<String> = fields
                .iter()
                .map(|(name, ext)| format!("{}: {}", name, fmt_extent(ext)))
                .collect();
            parts.sort();
            format!("{{{}}}", parts.join(", "))
        }
        Extent::UIntRange { start, end } => format!("[{start}..{end})"),
        Extent::DataSourceDomain(_) => "DataSource".to_string(),
        Extent::Union(variants) => {
            let parts: Vec<String> = variants.iter().map(fmt_extent).collect();
            parts.join(" | ")
        }
        Extent::Restricted { base, .. } => format!("Restricted({})", fmt_extent(base)),
    }
}

/// Format a BinOpKind as its operator symbol.
pub fn fmt_binop(op: &BinOpKind) -> &'static str {
    match op {
        BinOpKind::Arithmetic(ArithmeticKind::Add) => "+",
        BinOpKind::Arithmetic(ArithmeticKind::Sub) => "-",
        BinOpKind::Arithmetic(ArithmeticKind::Mul) => "*",
        BinOpKind::Arithmetic(ArithmeticKind::FloorDiv) => "//",
        BinOpKind::BoolLogic(LogicKind::And) => "and",
        BinOpKind::BoolLogic(LogicKind::Nand) => "nand",
        BinOpKind::BoolLogic(LogicKind::Or) => "or",
        BinOpKind::BoolLogic(LogicKind::Nor) => "nor",
        BinOpKind::BoolLogic(LogicKind::Xor) => "xor",
        BinOpKind::BoolLogic(LogicKind::Xnor) => "xnor",
        BinOpKind::Compare(CompareKind::Equals) => "==",
        BinOpKind::Compare(CompareKind::NotEquals) => "≠",
        BinOpKind::Compare(CompareKind::Less) => "<",
        BinOpKind::Compare(CompareKind::LessOrEq) => "≤",
        BinOpKind::Compare(CompareKind::Greater) => ">",
        BinOpKind::Compare(CompareKind::GreaterOrEq) => "≥",
        BinOpKind::Concat => "++",
    }
}

// ---------------------------------------------------------------------------
// Convenience API
// ---------------------------------------------------------------------------

/// Pretty-print an operator tree with default options.
pub fn pretty_tile_operator(op: &dyn TileOperator) -> String {
    pretty_tile_operator_with(op, &VizOptions::default())
}

/// Pretty-print an operator tree with custom options.
pub fn pretty_tile_operator_with(op: &dyn TileOperator, opts: &VizOptions) -> String {
    render_with_max_depth(&op.inspect(opts), opts.max_depth)
}

/// Pretty-print a tile producer tree with default options.
pub fn pretty_tile_producer(producer: &dyn TileProducer) -> String {
    pretty_tile_producer_with(producer, &VizOptions::default())
}

/// Pretty-print a tile producer tree with custom options.
pub fn pretty_tile_producer_with(producer: &dyn TileProducer, opts: &VizOptions) -> String {
    render_with_max_depth(&producer.inspect(opts), opts.max_depth)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::*;

    #[test]
    fn render_leaf() {
        let node = InspectNode::leaf("Hello");
        assert_eq!(render(&node), "Hello\n");
    }

    #[test]
    fn render_with_annotations() {
        let node = InspectNode::leaf("Literal(42)").annotate(": Int");
        assert_eq!(render(&node), "Literal(42) : Int\n");
    }

    #[test]
    fn render_with_children() {
        let node = InspectNode::new("BinOp(+)")
            .child("left", InspectNode::leaf("Literal(1)"))
            .child("right", InspectNode::leaf("Literal(2)"));
        assert_eq!(
            render(&node),
            "\
BinOp(+)
├── left: Literal(1)
└── right: Literal(2)
"
        );
    }

    #[test]
    fn render_nested() {
        let node = InspectNode::new("BinOp(+)")
            .child("left", InspectNode::leaf("Literal(1)"))
            .child(
                "right",
                InspectNode::new("BinOp(*)")
                    .child("left", InspectNode::leaf("Literal(2)"))
                    .child("right", InspectNode::leaf("Literal(3)")),
            );
        assert_eq!(
            render(&node),
            "\
BinOp(+)
├── left: Literal(1)
└── right: BinOp(*)
    ├── left: Literal(2)
    └── right: Literal(3)
"
        );
    }

    #[test]
    fn render_no_edge_labels() {
        let node = InspectNode::new("Parent")
            .child("", InspectNode::leaf("Child1"))
            .child("", InspectNode::leaf("Child2"));
        assert_eq!(
            render(&node),
            "\
Parent
├── Child1
└── Child2
"
        );
    }

    // -- Extent formatting --

    #[test]
    fn fmt_extent_base() {
        assert_eq!(fmt_extent(&Extent::Base(BaseType::Int)), "Int");
        assert_eq!(fmt_extent(&Extent::Base(BaseType::String)), "String");
    }

    #[test]
    fn fmt_extent_function() {
        let ext = Extent::function(Extent::Base(BaseType::Int), Extent::Base(BaseType::Int));
        assert_eq!(fmt_extent(&ext), "Int \u{2192} Int");
    }

    #[test]
    fn fmt_extent_nested_function() {
        // (Int → Int) → Int
        let inner = Extent::function(Extent::Base(BaseType::Int), Extent::Base(BaseType::Int));
        let ext = Extent::function(inner, Extent::Base(BaseType::Int));
        assert_eq!(fmt_extent(&ext), "(Int \u{2192} Int) \u{2192} Int");
    }

    // -- Depth limiting --

    #[test]
    fn render_depth_limit_truncates() {
        let deep = InspectNode::new("Level0").child(
            "a",
            InspectNode::new("Level1").child("b", InspectNode::leaf("Level2")),
        );
        // max_depth=1: Level0 renders, Level1 renders but its children are truncated
        let output = render_with_max_depth(&deep, Some(1));
        assert_eq!(
            output,
            "\
Level0
└── a: Level1 ... (1 more nodes)
"
        );
    }

    #[test]
    fn render_depth_limit_zero_truncates_root_children() {
        let node = InspectNode::new("Root")
            .child("a", InspectNode::leaf("Child1"))
            .child("b", InspectNode::leaf("Child2"));
        let output = render_with_max_depth(&node, Some(0));
        assert_eq!(output, "Root ... (2 more nodes)\n");
    }

    #[test]
    fn render_depth_limit_none_is_unlimited() {
        let deep = InspectNode::new("A")
            .child("", InspectNode::new("B").child("", InspectNode::leaf("C")));
        let limited = render_with_max_depth(&deep, None);
        let unlimited = render(&deep);
        assert_eq!(limited, unlimited);
    }

    // -- Display impl --

    #[test]
    fn display_impl() {
        let node = InspectNode::leaf("Hello");
        assert_eq!(format!("{node}"), "Hello\n");
    }
}
