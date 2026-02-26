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

use crate::ccl::{ArithmeticKind, BinOpKind, CompareKind, Expr, Lit, LogicKind, UnaryOpKind};
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

        Expr::BinOp { left, op, right } => InspectNode::new(format!("BinOp({})", binop_symbol(op)))
            .child("left", expr_to_node(left))
            .child("right", expr_to_node(right)),

        Expr::UnaryOp(op, operand) => InspectNode::new(format!("UnaryOp({})", unaryop_symbol(op)))
            .child("expr", expr_to_node(operand)),

        Expr::Lambda {
            param,
            param_ty,
            body,
        } => {
            let mut node = InspectNode::new(format!("Lambda({param})"));
            if let Some(ty) = param_ty {
                node = node.annotate(format!(": {}", type_str(ty)));
            }
            node.child("body", expr_to_node(body))
        }

        Expr::Let {
            name,
            ty,
            value,
            body,
            ..
        } => {
            let mut node = InspectNode::new(format!("Let({name})"));
            if let Some(t) = ty {
                node = node.annotate(format!(": {}", type_str(t)));
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
            .annotate(format!(": {}", type_str(ty)))
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

fn binop_symbol(op: &BinOpKind) -> &'static str {
    match op {
        BinOpKind::Arithmetic(ArithmeticKind::Add) => "+",
        BinOpKind::Arithmetic(ArithmeticKind::Sub) => "-",
        BinOpKind::Arithmetic(ArithmeticKind::Mul) => "*",
        BinOpKind::Arithmetic(ArithmeticKind::FloorDiv) => "//",
        BinOpKind::Concat => "++",
        BinOpKind::Compare(CompareKind::Less) => "<",
        BinOpKind::Compare(CompareKind::LessOrEq) => "<=",
        BinOpKind::Compare(CompareKind::Greater) => ">",
        BinOpKind::Compare(CompareKind::GreaterOrEq) => ">=",
        BinOpKind::Compare(CompareKind::Equals) => "==",
        BinOpKind::Compare(CompareKind::NotEquals) => "!=",
        BinOpKind::BoolLogic(LogicKind::And) => "and",
        BinOpKind::BoolLogic(LogicKind::Or) => "or",
        BinOpKind::BoolLogic(LogicKind::Nand) => "nand",
        BinOpKind::BoolLogic(LogicKind::Nor) => "nor",
        BinOpKind::BoolLogic(LogicKind::Xor) => "xor",
        BinOpKind::BoolLogic(LogicKind::Xnor) => "xnor",
    }
}

fn unaryop_symbol(op: &UnaryOpKind) -> &'static str {
    match op {
        UnaryOpKind::Neg => "-",
        UnaryOpKind::Not => "not",
    }
}

fn type_str(ty: &crate::ccl::Type) -> String {
    use crate::ccl::Type;
    use crate::interpreter::BaseType;
    match ty {
        Type::Base(b) => match b {
            BaseType::Int => "Int".to_string(),
            BaseType::UInt => "UInt".to_string(),
            BaseType::String => "String".to_string(),
            BaseType::Bool => "Bool".to_string(),
            BaseType::Unit => "Unit".to_string(),
        },
        Type::Fun(a, b) => format!("{} → {}", type_str(a), type_str(b)),
        Type::Tuple(ts) => {
            let parts: Vec<_> = ts.iter().map(type_str).collect();
            format!("({})", parts.join(", "))
        }
        Type::Record(fields) => {
            let parts: Vec<_> = fields
                .iter()
                .map(|(n, t)| format!("{n}: {}", type_str(t)))
                .collect();
            format!("{{{}}}", parts.join(", "))
        }
        Type::Union(ts) => {
            let parts: Vec<_> = ts.iter().map(type_str).collect();
            parts.join(" | ")
        }
        Type::Unknown => "?".to_string(),
    }
}
