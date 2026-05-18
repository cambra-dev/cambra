//! Pretty-printer for CCL expressions.
//!
//! Renders a [`crate::ccl::Expr`] as a labelled tree using [`InspectNode`] and
//! [`render`], producing output like:
//!
//! ```text
//! BinOp(+)
//! ├── left: Lit(1)
//! └── right: Lit(2)
//! ```
//!
//! The formatting is intentionally kept human-readable and stable so that tests
//! can pin expected tree strings directly.

use crate::ccl::{Branch, Expr, Lit, ProjKey, RefinementKind, Type, TypedExprNode, UnaryOpKind};
use crate::pretty_tree::{InspectNode, render};

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Render a CCL expression as a pretty-printed tree string.
pub fn pretty(expr: &Expr) -> String {
    render(&expr_to_node(expr))
}

// ---------------------------------------------------------------------------
// Internal builders
// ---------------------------------------------------------------------------

fn expr_to_node(expr: &Expr) -> InspectNode {
    match &expr.node {
        TypedExprNode::Lit(lit) => InspectNode::leaf(lit_label(lit)),

        TypedExprNode::Var(name) => InspectNode::leaf(format!("Var({name})")),

        TypedExprNode::Builtin(b) => InspectNode::leaf(format!("Builtin({})", b.name())),

        TypedExprNode::Apply { function, argument } => InspectNode::new("Apply")
            .child("func", expr_to_node(function))
            .child("arg", expr_to_node(argument)),

        TypedExprNode::BinOp { left, op, right } => {
            InspectNode::new(format!("BinOp({})", op.sym()))
                .child("left", expr_to_node(left))
                .child("right", expr_to_node(right))
        }

        TypedExprNode::UnaryOp(op, operand) => {
            InspectNode::new(format!("UnaryOp({})", unaryop_symbol(op)))
                .child("expr", expr_to_node(operand))
        }

        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => {
            let mut node = InspectNode::new(format!("Lambda({})", param.name));
            if !matches!(param.ty, Type::Hole | Type::Infer(_)) {
                node = node.annotate(format!(": {}", param.ty));
            }
            if let Some(r) = refinement {
                node = match &r.kind {
                    RefinementKind::Predicate(def) => {
                        node.child("refinement", expr_to_node(&def.borrow()))
                    }
                };
            }
            node.child("body", expr_to_node(body))
        }

        TypedExprNode::Aggregate { input, kind } => {
            InspectNode::new(format!("Aggregate({kind:?})")).child("input", expr_to_node(input))
        }

        TypedExprNode::Let {
            binding,
            bound_expr: value,
            body,
        } => {
            let mut node = InspectNode::new(format!("Let({})", binding.name));
            if !matches!(binding.ty, Type::Hole | Type::Infer(_)) {
                node = node.annotate(format!(": {}", binding.ty));
            }
            node.child("value", expr_to_node(value))
                .child("body", expr_to_node(body))
        }

        TypedExprNode::List(elts) => {
            let mut node = InspectNode::new("List");
            for (i, e) in elts.iter().enumerate() {
                node = node.child(i.to_string(), expr_to_node(e));
            }
            node
        }

        TypedExprNode::Tuple(elts) => {
            let mut node = InspectNode::new("Tuple");
            for (i, e) in elts.iter().enumerate() {
                node = node.child(i.to_string(), expr_to_node(e));
            }
            node
        }

        TypedExprNode::Record(fields) => {
            let mut node = InspectNode::new("Record");
            for (field, e) in fields {
                node = node.child(field.as_str(), expr_to_node(e));
            }
            node
        }

        TypedExprNode::Case { branches } => {
            let mut node = InspectNode::new("Case");
            for (i, Branch { guard, body }) in branches.iter().enumerate() {
                node = node.child(format!("guard_{i}"), expr_to_node(guard));
                node = node.child(format!("arm_{i}"), expr_to_node(body));
            }
            node
        }

        TypedExprNode::Loop {
            init_args,
            source,
            loop_body,
            ..
        } => {
            let mut node = InspectNode::new("Loop".to_string());
            for (i, init) in init_args.iter().enumerate() {
                node = node.child(format!("init_{i}"), expr_to_node(init));
            }
            node.child("source", expr_to_node(source))
                .child("loop_body", expr_to_node(loop_body))
        }

        TypedExprNode::Source(name) => InspectNode::leaf(format!("Source({name})")),

        TypedExprNode::Compose(elts) => {
            let mut node = InspectNode::new("Compose");
            for (i, e) in elts.iter().enumerate() {
                node = node.child(i.to_string(), expr_to_node(e));
            }
            node
        }

        TypedExprNode::Proj(key) => InspectNode::leaf(match key {
            ProjKey::Index(n) => format!(".{n}"),
            ProjKey::Field(s) => format!(".{s}"),
        }),

        TypedExprNode::ExprStmt { expr, body } => InspectNode::new("ExprStmt")
            .child("expr", expr_to_node(expr))
            .child("body", expr_to_node(body)),

        TypedExprNode::Feed { name, value } => {
            InspectNode::new(format!("Bind({name})")).child("value", expr_to_node(value))
        }

        TypedExprNode::Define { name, value } => {
            InspectNode::new(format!("Define({name})")).child("value", expr_to_node(value))
        }

        TypedExprNode::Defer => InspectNode::leaf("Defer"),
    }
}

// ---------------------------------------------------------------------------
// Label helpers
// ---------------------------------------------------------------------------

fn lit_label(lit: &Lit) -> String {
    match lit {
        Lit::Int(n) => format!("Lit({n})"),
        Lit::String(s) => format!("Lit(\"{}\")", s.escape_default()),
        Lit::Bool(b) => format!("Lit({b})"),
        Lit::Unit => "Lit(unit)".to_string(),
    }
}

fn unaryop_symbol(op: &UnaryOpKind) -> &'static str {
    match op {
        UnaryOpKind::Neg => "-",
        UnaryOpKind::Not => "not",
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::pretty;
    use crate::ccl::BaseType;
    use crate::ccl::{
        AggregateKind, ArithmeticKind, BinOpKind, Branch, Expr, Lit, ProjKey, Type, TypedBinding,
        TypedExpr, TypedExprNode, UnaryOpKind,
    };
    use rstest::rstest;

    #[rstest]
    // Literals
    #[case(Expr::lit(Lit::Int(42)), "Lit(42)\n")]
    #[case(Expr::lit(Lit::String("hi".to_string())), "Lit(\"hi\")\n")]
    #[case(Expr::lit(Lit::Bool(true)), "Lit(true)\n")]
    #[case(Expr::lit(Lit::Unit), "Lit(unit)\n")]
    // Variable
    #[case(Expr::var("x"), "Var(x)\n")]
    // Proj
    #[case(TypedExpr::new(TypedExprNode::Proj(ProjKey::Index(0))), ".0\n")]
    #[case(TypedExpr::new(TypedExprNode::Proj(ProjKey::Field("name".to_string()))), ".name\n")]
    // BinOp
    #[case(
        Expr::binop(
            Expr::lit(Lit::Int(1)),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Expr::lit(Lit::Int(2))
        ),
        "\
BinOp(+)
├── left: Lit(1)
└── right: Lit(2)
"
    )]
    // UnaryOp
    #[case(
        Expr::unary(UnaryOpKind::Neg, Expr::var("x")),
        "\
UnaryOp(-)
└── expr: Var(x)
"
    )]
    #[case(
        Expr::unary(UnaryOpKind::Not, Expr::var("b")),
        "\
UnaryOp(not)
└── expr: Var(b)
"
    )]
    // Apply
    #[case(
        Expr::apply(Expr::var("x"), Expr::var("f")),
        "\
Apply
├── func: Var(f)
└── arg: Var(x)
"
    )]
    // Lambda (unannotated and annotated)
    #[case(
        Expr::lambda("x", Type::infer(), Expr::var("x")),
        "\
Lambda(x)
└── body: Var(x)
"
    )]
    #[case(
        Expr::lambda("x", Type::Base(BaseType::Int), Expr::var("x")),
        "\
Lambda(x) : Int
└── body: Var(x)
"
    )]
    // Let (unannotated — bound_expr.ty Unknown → no annotation)
    #[case(
        Expr::let_bind("x", Expr::lit(Lit::Int(1)), Expr::var("x")),
        "\
Let(x)
├── value: Lit(1)
└── body: Var(x)
"
    )]
    // Let (annotated — set bound_expr.ty to Bool so annotation is printed)
    #[case(
        Expr::let_bind("x", Expr::lit(Lit::Bool(true)).with_ty(Type::Base(BaseType::Bool)), Expr::var("x")),
        "\
Let(x) : Bool
├── value: Lit(true)
└── body: Var(x)
"
    )]
    // List (empty and non-empty)
    #[case(Expr::list(vec![]), "List\n")]
    #[case(
        Expr::list(vec![Expr::lit(Lit::Int(1)), Expr::lit(Lit::Int(2))]),
        "\
List
├── 0: Lit(1)
└── 1: Lit(2)
"
    )]
    // Tuple
    #[case(
        Expr::tuple(vec![Expr::lit(Lit::Int(1)), Expr::lit(Lit::Int(2))]),
        "\
Tuple
├── 0: Lit(1)
└── 1: Lit(2)
"
    )]
    // Record
    #[case(
        TypedExpr::new(TypedExprNode::Record(vec![("a".to_string(), Expr::lit(Lit::Int(1)))])),
        "\
Record
└── a: Lit(1)
"
    )]
    // Case with a single guard + arm
    #[case(
        TypedExpr::new(TypedExprNode::Case {
            branches: vec![Branch { guard: Expr::lit(Lit::Bool(true)), body: Expr::lit(Lit::Int(0)) }],
        }),
        "\
Case
├── guard_0: Lit(true)
└── arm_0: Lit(0)
"
    )]
    // Loop: pretty-printed children include init_args, source, and loop_body
    #[case(
        TypedExpr::new(TypedExprNode::Loop {
            params: vec![TypedBinding::new_unannotated("i")],
            init_args: vec![Expr::lit(Lit::Int(0))],
            source: Box::new(Expr::var("xs")),
            loop_body: Box::new(Expr::var("i")),
            body_taps: Vec::new(),
        }),
        "\
Loop
├── init_0: Lit(0)
├── source: Var(xs)
└── loop_body: Var(i)
"
    )]
    // Aggregate
    #[case(
        Expr::aggregate(Expr::var("xs"), AggregateKind::Sum),
        "\
Aggregate(Sum)
└── input: Var(xs)
"
    )]
    // Lambda with predicate refinement
    #[case(
        Expr::lambda_with_refinement(
            "x",
            Type::Base(BaseType::Int),
            Expr::var("x"),
            Expr::lit(Lit::Bool(true)),
            "test pred",
        ),
        "\
Lambda(x) : Int
├── refinement: Lit(true)
└── body: Var(x)
"
    )]
    fn test_pretty_expr(#[case] expr: Expr, #[case] expected: &str) {
        assert_eq!(pretty(&expr), expected);
    }

    /// Verifies the `│   ` continuation-prefix threading in `pretty_tree`.
    ///
    /// The prefix only appears when a *non-last* child itself has children.
    /// None of the per-variant cases above trigger this; only a tree where a
    /// non-last child has grandchildren (e.g. `Let` whose `value` is an `Apply`)
    /// exercises the code path.
    #[test]
    fn test_pretty_continuation_prefix() {
        let expr = Expr::let_bind(
            "x",
            Expr::apply(Expr::lit(Lit::Int(1)), Expr::var("f")),
            Expr::binop(
                Expr::var("x"),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                Expr::lit(Lit::Int(2)),
            ),
        );
        let expected = "\
Let(x)
├── value: Apply
│   ├── func: Var(f)
│   └── arg: Lit(1)
└── body: BinOp(+)
    ├── left: Var(x)
    └── right: Lit(2)
";
        assert_eq!(pretty(&expr), expected);
    }
}
