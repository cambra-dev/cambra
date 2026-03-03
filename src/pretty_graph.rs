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
    ArithmeticKind, BaseType, BinOpKind, CompareKind, Extent, LogicKind, Operator, Producer,
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
pub fn pretty_operator(op: &dyn Operator) -> String {
    pretty_operator_with(op, &VizOptions::default())
}

/// Pretty-print an operator tree with custom options.
pub fn pretty_operator_with(op: &dyn Operator, opts: &VizOptions) -> String {
    render_with_max_depth(&op.inspect(opts), opts.max_depth)
}

/// Pretty-print a dataflow (producer) tree with default options.
pub fn pretty_dataflow(producer: &dyn Producer) -> String {
    pretty_dataflow_with(producer, &VizOptions::default())
}

/// Pretty-print a dataflow (producer) tree with custom options.
pub fn pretty_dataflow_with(producer: &dyn Producer, opts: &VizOptions) -> String {
    render_with_max_depth(&producer.inspect(opts), opts.max_depth)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::test_helpers::TestConsumer;
    use crate::interpreter::*;
    use std::cell::RefCell;
    use std::rc::Rc;

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

    // -- Guard formatting --

    #[test]
    fn fmt_guard_universal() {
        assert_eq!(fmt_guard(&Guard::Universal), "*");
    }

    #[test]
    fn fmt_guard_empty() {
        assert_eq!(fmt_guard(&Guard::Empty), "\u{2205}");
    }

    #[test]
    fn fmt_guard_equality() {
        let g = Guard::Equality {
            variable: "x".to_string(),
            value: Value::Int(42),
        };
        assert_eq!(fmt_guard(&g), "x=42");
    }

    #[test]
    fn fmt_guard_and() {
        let g = Guard::And(vec![Guard::Universal, Guard::Empty]);
        assert_eq!(fmt_guard(&g), "(* \u{2227} \u{2205})");
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

    // -- Operator inspect --

    #[test]
    fn literal_operator() {
        let lit = Literal::new(Value::Int(42));
        let output = pretty_operator(&lit);
        assert_eq!(output, "Literal(42) : Int\n");
    }

    #[test]
    fn literal_operator_no_extent() {
        let lit = Literal::new(Value::Int(42));
        let output = pretty_operator_with(&lit, &VizOptions::minimal());
        assert_eq!(output, "Literal(42)\n");
    }

    #[test]
    fn literal_string_operator() {
        let lit = Literal::new(Value::String("hello".to_string()));
        let output = pretty_operator(&lit);
        assert_eq!(output, "Literal(\"hello\") : String\n");
    }

    #[test]
    fn varref_operator() {
        let vr = VarRef::new("x", Extent::Base(BaseType::Int));
        let output = pretty_operator(&vr);
        assert_eq!(output, "VarRef(x) : Int\n");
    }

    #[test]
    fn binop_operator() {
        let left = Box::new(Literal::new(Value::Int(1)));
        let right = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let binop = BinOp::new(left, BinOpKind::Arithmetic(ArithmeticKind::Add), right);
        let output = pretty_operator(&binop);
        assert_eq!(
            output,
            "\
BinOp(+) : Int
├── left: Literal(1) : Int
└── right: VarRef(x) : Int
"
        );
    }

    #[test]
    fn lambda_operator() {
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let lambda = Lambda::new(variable, body);
        let output = pretty_operator(&lambda);
        assert_eq!(
            output,
            "\
Lambda(x) : Int \u{2192} Int
├── var: Var(x) : Int
└── body: VarRef(x) : Int
"
        );
    }

    #[test]
    fn lambda_with_binop_body() {
        // λ x . x + 1
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(BinOp::new(
            Box::new(VarRef::new("x", Extent::Base(BaseType::Int))),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Box::new(Literal::new(Value::Int(1))),
        ));
        let lambda = Lambda::new(variable, body);
        let output = pretty_operator(&lambda);
        assert_eq!(
            output,
            "\
Lambda(x) : Int \u{2192} Int
├── var: Var(x) : Int
└── body: BinOp(+) : Int
    ├── left: VarRef(x) : Int
    └── right: Literal(1) : Int
"
        );
    }

    // -- Dataflow inspect --

    #[test]
    fn literal_dataflow() {
        let mut lit = Literal::new(Value::Int(42));
        let (consumer, _) = TestConsumer::new();
        let producer = lit.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );
        let output = pretty_dataflow(producer.as_ref());
        assert_eq!(output, "LiteralProducer(42)\n");
    }

    #[test]
    fn binop_dataflow() {
        let left = Box::new(Literal::new(Value::Int(2)));
        let right = Box::new(Literal::new(Value::Int(3)));
        let mut binop = BinOp::new(left, BinOpKind::Arithmetic(ArithmeticKind::Add), right);

        let (consumer, _) = TestConsumer::new();
        let producer = binop.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );
        let output = pretty_dataflow(producer.as_ref());
        assert_eq!(
            output,
            "\
BinOpProducer(+)
├── left: LiteralProducer(2)
└── right: LiteralProducer(3)
"
        );
    }

    #[test]
    fn lambda_dataflow() {
        // λ x . x + 1, applied with binding 42
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(BinOp::new(
            Box::new(VarRef::new("x", Extent::Base(BaseType::Int))),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Box::new(Literal::new(Value::Int(1))),
        ));
        let lambda = Lambda::new(variable, body);
        let binding = Literal::new(Value::Int(42));
        let mut apply = Apply::new(Box::new(lambda), Box::new(binding));

        let (consumer, _) = TestConsumer::new();
        let producer = apply.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );
        let output = pretty_dataflow(producer.as_ref());
        assert_eq!(
            output,
            "\
ApplyProducer
└── lambda: LambdaProducer(x)
    ├── var: VarProducer(x) [argument, ready] [yield: ∅]
    │   └── source: LiteralProducer(42)
    └── body: BinOpProducer(+)
        ├── left: VarRefProducer(x)
        │   └── → VarProducer(x) [argument, ready, 2 consumers]
        └── right: LiteralProducer(1)
"
        );
    }

    #[test]
    fn binop_dataflow_with_guards() {
        let left = Box::new(Literal::new(Value::Int(2)));
        let right = Box::new(Literal::new(Value::Int(3)));
        let mut binop = BinOp::new(left, BinOpKind::Arithmetic(ArithmeticKind::Add), right);

        let (consumer, _) = TestConsumer::new();
        let producer = binop.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );
        let output = pretty_dataflow_with(producer.as_ref(), &VizOptions::verbose());
        assert_eq!(
            output,
            "\
BinOpProducer(+)
├── left: LiteralProducer(2)
└── right: LiteralProducer(3)
"
        );
    }

    #[test]
    fn default_fallback_operator() {
        // A type implementing Operator without overriding inspect() should use the default
        #[derive(Debug)]
        struct UnknownOp {
            extent: Extent,
        }
        impl Operator for UnknownOp {
            fn extent(&self) -> &Extent {
                &self.extent
            }
            fn subscribe(
                &mut self,
                _: Guard,
                _: Box<dyn Consumer>,
                _: Option<Rc<VarScope>>,
                _: &mut Scheduler,
            ) -> Box<dyn Producer> {
                unimplemented!()
            }
        }

        let op = UnknownOp {
            extent: Extent::Base(BaseType::Int),
        };
        let output = pretty_operator(&op);
        assert_eq!(output, "UnknownOp(?)\n");
    }

    #[test]
    fn locked_producer() {
        let var = Var::new("x", Extent::Base(BaseType::Int));
        let subscription = var.create_subscription(VarSource::Uninitialized);

        // Hold a mutable borrow so try_borrow() fails
        let _borrow = subscription.borrow_mut();

        // inspect() through the Rc<RefCell<>> blanket impl should return <locked>
        let desc = subscription.inspect(&VizOptions::default());
        assert_eq!(render(&desc), "<locked>\n");
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

    // -- ListLiteral inspect --

    #[test]
    fn list_literal_operator() {
        let list = ListLiteral::new(vec![Value::Int(10), Value::Int(20), Value::Int(30)]);
        let output = pretty_operator(&list);
        assert_eq!(output, "ListLiteral(3 × Int) : [0..3) → Int\n");
    }

    #[test]
    fn list_literal_dataflow() {
        let list = ListLiteral::new(vec![Value::Int(10), Value::Int(20), Value::Int(30)]);
        let binding = Literal::new(Value::UInt(1));
        let mut apply = Apply::new(Box::new(list), Box::new(binding));
        let (consumer, _) = TestConsumer::new();
        let producer = apply.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );
        let output = pretty_dataflow(producer.as_ref());
        assert_eq!(
            output,
            "\
ApplyProducer
└── lambda: ListLiteralProducer(3 elements)
    └── index: LiteralProducer(1)
"
        );
    }

    // -- Apply inspect --

    #[test]
    fn apply_operator() {
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let lambda = Lambda::new(variable, body);
        let argument = Literal::new(Value::Int(42));
        let apply = Apply::new(Box::new(lambda), Box::new(argument));
        let output = pretty_operator(&apply);
        assert_eq!(
            output,
            "\
Apply : Int
├── lambda: Lambda(x) : Int → Int
│   ├── var: Var(x) : Int
│   └── body: VarRef(x) : Int
└── argument: Literal(42) : Int
"
        );
    }

    #[test]
    fn apply_dataflow() {
        // (λx. x)(42) = 42
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let lambda = Lambda::new(variable, body);
        let argument = Literal::new(Value::Int(42));
        let mut apply = Apply::new(Box::new(lambda), Box::new(argument));

        let (consumer, _) = TestConsumer::new();
        let producer = apply.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );
        let output = pretty_dataflow(producer.as_ref());
        assert_eq!(
            output,
            "\
ApplyProducer
└── lambda: LambdaProducer(x)
    ├── var: VarProducer(x) [argument, ready] [yield: ∅]
    │   └── source: LiteralProducer(42)
    └── body: VarRefProducer(x)
        └── → VarProducer(x) [argument, ready, 2 consumers]
"
        );
    }

    #[test]
    fn apply_nested_dataflow() {
        // (λx. (λy. x + y)(2))(1)
        // Two nested applies demonstrating cross-scope variable references
        // and consumer sharing.

        // Inner: (λy. x + y)
        let inner_var = Var::new("y", Extent::Base(BaseType::Int));
        let inner_body = Box::new(BinOp::new(
            Box::new(VarRef::new("x", Extent::Base(BaseType::Int))),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Box::new(VarRef::new("y", Extent::Base(BaseType::Int))),
        ));
        let inner_lambda = Lambda::new(inner_var, inner_body);

        // Inner apply: (λy. x + y)(2)
        let inner_apply = Apply::new(
            Box::new(inner_lambda),
            Box::new(Literal::new(Value::Int(2))),
        );

        // Outer: (λx. inner_apply)(1)
        let outer_var = Var::new("x", Extent::Base(BaseType::Int));
        let outer_lambda = Lambda::new(outer_var, Box::new(inner_apply));
        let mut outer_apply = Apply::new(
            Box::new(outer_lambda),
            Box::new(Literal::new(Value::Int(1))),
        );

        let (consumer, _) = TestConsumer::new();
        let producer = outer_apply.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );
        let output = pretty_dataflow(producer.as_ref());
        // Key features of this output:
        // - Nested applies/lambdas: two layers of function application
        // - Cross-scope variable references: VarRefProducer(x) in the inner body
        //   points to the outer VarProducer(x)
        // - Consumer sharing: both VarProducers show "2 consumers" (one VarRefProducer
        //   + one Lambda variable_consumer each)
        // - The limitation: we see "2 consumers" but not *who* they are
        assert_eq!(
            output,
            "\
ApplyProducer
└── lambda: LambdaProducer(x)
    ├── var: VarProducer(x) [argument, ready] [yield: ∅]
    │   └── source: LiteralProducer(1)
    └── body: ApplyProducer
        └── lambda: LambdaProducer(y)
            ├── var: VarProducer(y) [argument, ready] [yield: ∅]
            │   └── source: LiteralProducer(2)
            └── body: BinOpProducer(+)
                ├── left: VarRefProducer(x)
                │   └── → VarProducer(x) [argument, ready, 2 consumers]
                └── right: VarRefProducer(y)
                    └── → VarProducer(y) [argument, ready, 2 consumers]
"
        );
    }

    // -- StdinReader inspect --

    #[test]
    fn stdin_reader_operator() {
        let reader = StdinReader::new(Rc::new(RefCell::new(StdinDataSource::new())));
        let output = pretty_operator(&reader);
        assert_eq!(output, "StdinReader : DataSource → String\n");
    }

    #[test]
    fn stdin_dataflow() {
        // Safe because inspect() doesn't read stdin — only get() and
        // check_for_new_data() do.
        let reader = StdinReader::new(Rc::new(RefCell::new(StdinDataSource::new())));
        let binding = Literal::new(Value::UInt(0));
        let mut apply = Apply::new(Box::new(reader), Box::new(binding));
        let (consumer, _) = TestConsumer::new();
        let producer = apply.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );
        let output = pretty_dataflow(producer.as_ref());
        assert_eq!(
            output,
            "\
ApplyProducer
└── lambda: StdinProducer(stdin)
    └── index: LiteralProducer(0)
"
        );
    }
}
