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

use crate::ccl::{Expr, Lit, RefinementKind, UnaryOpKind};
use crate::pretty_tree::{render, InspectNode};

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
    match expr {
        Expr::Lit(lit) => InspectNode::leaf(lit_label(lit)),

        Expr::Var(name) => InspectNode::leaf(format!("Var({name})")),

        Expr::Apply { function, argument } => InspectNode::new("Apply")
            .child("func", expr_to_node(function))
            .child("arg", expr_to_node(argument)),

        Expr::BinOp { left, op, right } => InspectNode::new(format!("BinOp({})", op.sym()))
            .child("left", expr_to_node(left))
            .child("right", expr_to_node(right)),

        Expr::UnaryOp(op, operand) => InspectNode::new(format!("UnaryOp({})", unaryop_symbol(op)))
            .child("expr", expr_to_node(operand)),

        Expr::Lambda {
            param,
            param_ty,
            body,
            refinement,
        } => {
            let mut node = InspectNode::new(format!("Lambda({param})"));
            if let Some(ty) = param_ty {
                node = node.annotate(format!(": {ty}"));
            }
            if let Some(r) = refinement {
                node = match &r.kind {
                    RefinementKind::Predicate(def) => {
                        node.child("refinement", expr_to_node(&def.borrow()))
                    }
                    RefinementKind::HashJoin(spec) => node.child(
                        "refinement",
                        InspectNode::leaf(format!(
                            "HashJoin({} == {})",
                            spec.build_var_name, spec.probe_var_name
                        )),
                    ),
                };
            }
            node.child("body", expr_to_node(body))
        }

        Expr::Let {
            name,
            bound_ty: ty,
            bound_expr: value,
            body,
            ..
        } => {
            let mut node = InspectNode::new(format!("Let({name})"));
            if let Some(t) = ty {
                node = node.annotate(format!(": {t}"));
            }
            node.child("value", expr_to_node(value))
                .child("body", expr_to_node(body))
        }

        Expr::List(elts) => {
            let mut node = InspectNode::new("List");
            for (i, e) in elts.iter().enumerate() {
                node = node.child(i.to_string(), expr_to_node(e));
            }
            node
        }

        Expr::Tuple(elts) => {
            let mut node = InspectNode::new("Tuple");
            for (i, e) in elts.iter().enumerate() {
                node = node.child(i.to_string(), expr_to_node(e));
            }
            node
        }

        Expr::TupleIndex(tuple, idx) => {
            InspectNode::new(format!("TupleIndex({idx})")).child("tuple", expr_to_node(tuple))
        }

        Expr::Record(fields) => {
            let mut node = InspectNode::new("Record");
            for (field, e) in fields {
                node = node.child(field.as_str(), expr_to_node(e));
            }
            node
        }

        Expr::Case {
            scrutinee,
            branches,
        } => {
            let mut node = InspectNode::new("Case").child("scrutinee", expr_to_node(scrutinee));
            for (i, (_pat, arm)) in branches.iter().enumerate() {
                node = node.child(format!("branch_{i}"), expr_to_node(arm));
            }
            node
        }

        Expr::Join {
            name,
            loop_body,
            outer_body,
            ..
        } => InspectNode::new(format!("Join({name})"))
            .child("loop_body", expr_to_node(loop_body))
            .child("outer_body", expr_to_node(outer_body)),

        Expr::TypeAnnotation(expr, ty) => InspectNode::new("TypeAnnotation")
            .annotate(format!(": {ty}"))
            .child("expr", expr_to_node(expr)),

        Expr::Jump { target, args } => {
            let mut node = InspectNode::new(format!("Jump({target})"));
            for (i, arg) in args.iter().enumerate() {
                node = node.child(format!("arg_{i}"), expr_to_node(arg));
            }
            node
        }
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
    use crate::ccl::{ArithmeticKind, BinOpKind, Expr, Lit, Pattern, Type, UnaryOpKind};
    use crate::interpreter::BaseType;
    use rstest::rstest;

    #[rstest]
    // Literals
    #[case(Expr::Lit(Lit::Int(42)), "Lit(42)\n")]
    #[case(Expr::Lit(Lit::String("hi".to_string())), "Lit(\"hi\")\n")]
    #[case(Expr::Lit(Lit::Bool(true)), "Lit(true)\n")]
    #[case(Expr::Lit(Lit::Unit), "Lit(unit)\n")]
    // Variable
    #[case(Expr::Var("x".to_string()), "Var(x)\n")]
    // BinOp
    #[case(
        Expr::BinOp {
            left: Box::new(Expr::Lit(Lit::Int(1))),
            op: BinOpKind::Arithmetic(ArithmeticKind::Add),
            right: Box::new(Expr::Lit(Lit::Int(2))),
        },
        "\
BinOp(+)
├── left: Lit(1)
└── right: Lit(2)
"
    )]
    // UnaryOp
    #[case(
        Expr::UnaryOp(UnaryOpKind::Neg, Box::new(Expr::Var("x".to_string()))),
        "\
UnaryOp(-)
└── expr: Var(x)
"
    )]
    #[case(
        Expr::UnaryOp(UnaryOpKind::Not, Box::new(Expr::Var("b".to_string()))),
        "\
UnaryOp(not)
└── expr: Var(b)
"
    )]
    // Apply
    #[case(
        Expr::apply(Expr::Var("x".to_string()), Expr::Var("f".to_string())),
        "\
Apply
├── func: Var(f)
└── arg: Var(x)
"
    )]
    // Lambda (unannotated and annotated)
    #[case(
        Expr::lambda("x", None, Expr::Var("x".to_string())),
        "\
Lambda(x)
└── body: Var(x)
"
    )]
    #[case(
        Expr::lambda("x", Some(Type::Base(BaseType::Int)), Expr::Var("x".to_string())),
        "\
Lambda(x) : Int
└── body: Var(x)
"
    )]
    // Let (unannotated and annotated)
    #[case(
        Expr::Let {
            name: "x".to_string(),
            bound_ty: None,
            bound_expr: Box::new(Expr::Lit(Lit::Int(1))),
            body: Box::new(Expr::Var("x".to_string())),
        },
        "\
Let(x)
├── value: Lit(1)
└── body: Var(x)
"
    )]
    #[case(
        Expr::Let {
            name: "x".to_string(),
            bound_ty: Some(Type::Base(BaseType::Bool)),
            bound_expr: Box::new(Expr::Lit(Lit::Bool(true))),
            body: Box::new(Expr::Var("x".to_string())),
        },
        "\
Let(x) : Bool
├── value: Lit(true)
└── body: Var(x)
"
    )]
    // List (empty and non-empty)
    #[case(Expr::List(vec![]), "List\n")]
    #[case(
        Expr::List(vec![Expr::Lit(Lit::Int(1)), Expr::Lit(Lit::Int(2))]),
        "\
List
├── 0: Lit(1)
└── 1: Lit(2)
"
    )]
    // Tuple
    #[case(
        Expr::Tuple(vec![Expr::Lit(Lit::Int(1)), Expr::Lit(Lit::Int(2))]),
        "\
Tuple
├── 0: Lit(1)
└── 1: Lit(2)
"
    )]
    // Record
    #[case(
        Expr::Record(vec![("a".to_string(), Expr::Lit(Lit::Int(1)))]),
        "\
Record
└── a: Lit(1)
"
    )]
    // Case with wildcard branch
    #[case(
        Expr::Case {
            scrutinee: Box::new(Expr::Var("x".to_string())),
            branches: vec![(Pattern::Wildcard, Expr::Lit(Lit::Int(0)))],
        },
        "\
Case
├── scrutinee: Var(x)
└── branch_0: Lit(0)
"
    )]
    // Join + Jump: loop_body (non-last) has a child → triggers │   continuation prefix
    #[case(
        Expr::Join {
            name: "k".to_string(),
            params: vec![("i".to_string(), None)],
            loop_body: Box::new(Expr::Jump {
                target: "k".to_string(),
                args: vec![Expr::Var("i".to_string())],
            }),
            outer_body: Box::new(Expr::Jump {
                target: "k".to_string(),
                args: vec![Expr::Lit(Lit::Int(0))],
            }),
        },
        "\
Join(k)
├── loop_body: Jump(k)
│   └── arg_0: Var(i)
└── outer_body: Jump(k)
    └── arg_0: Lit(0)
"
    )]
    // Jump with two args
    #[case(
        Expr::Jump {
            target: "k".to_string(),
            args: vec![Expr::Lit(Lit::Int(1)), Expr::Lit(Lit::Int(2))],
        },
        "\
Jump(k)
├── arg_0: Lit(1)
└── arg_1: Lit(2)
"
    )]
    // Lambda with predicate refinement
    #[case(
        Expr::lambda_with_refinement(
            "x",
            Some(Type::Base(BaseType::Int)),
            Expr::Var("x".to_string()),
            Expr::Lit(Lit::Bool(true)),
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

    #[test]
    fn test_pretty_lambda_hash_join_refinement() {
        use crate::ccl::{HashJoinSpec, Lit};
        use std::rc::Rc;
        let spec = HashJoinSpec {
            build_gen_position: 0,
            probe_gen_position: 1,
            build_var_name: "x".to_string(),
            probe_var_name: "y".to_string(),
            build_key: Rc::new(Expr::Var("x".to_string())),
            probe_key: Rc::new(Expr::Var("y".to_string())),
            build_source: Rc::new(Expr::Lit(Lit::Int(0))),
            probe_source: Rc::new(Expr::Lit(Lit::Int(0))),
        };
        let expr = Expr::lambda_with_hash_join(
            "p",
            Some(Type::Base(BaseType::Int)),
            Expr::Lit(Lit::Unit),
            spec,
            "x == y",
        );
        let expected = "\
Lambda(p) : Int
├── refinement: HashJoin(x == y)
└── body: Lit(unit)
";
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
        let expr = Expr::Let {
            name: "x".to_string(),
            bound_ty: None,
            bound_expr: Box::new(Expr::apply(
                Expr::Lit(Lit::Int(1)),
                Expr::Var("f".to_string()),
            )),
            body: Box::new(Expr::BinOp {
                left: Box::new(Expr::Var("x".to_string())),
                op: BinOpKind::Arithmetic(ArithmeticKind::Add),
                right: Box::new(Expr::Lit(Lit::Int(2))),
            }),
        };
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
