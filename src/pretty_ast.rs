//! Compact pretty-printer for rustpython_parser AST nodes.
//!
//! The `Debug` output for AST nodes is extremely verbose due to `Location`,
//! `end_location`, and `custom` fields. This module provides a tree-style
//! display that shows only the structurally significant parts.
//!
//! ```text
//! Module
//! └── FunctionDef(foo)
//!     ├── Assign
//!     │   ├── Name(x)
//!     │   └── Constant(3)
//!     └── Return
//!         └── BinOp(+)
//!             ├── Name(x)
//!             └── Name(x)
//! ```

use std::fmt;

use rustpython_parser::ast::{self, Constant, ExprKind, StmtKind};

use crate::pretty_tree::{render, InspectNode};

// ---------------------------------------------------------------------------
// Generic wrapper & trait
// ---------------------------------------------------------------------------

/// Wrapper that implements [`fmt::Display`] for any type implementing [`ToInspectNode`].
pub struct Pretty<'a, T>(pub &'a T);

/// Trait for AST nodes that can describe themselves as an [`InspectNode`] tree.
pub trait ToInspectNode {
    fn to_inspect_node(&self) -> InspectNode;
}

impl<'a, T: ToInspectNode> fmt::Display for Pretty<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", render(&self.0.to_inspect_node()))
    }
}

impl ToInspectNode for ast::Mod {
    fn to_inspect_node(&self) -> InspectNode {
        mod_to_node(self)
    }
}

impl ToInspectNode for ast::Stmt {
    fn to_inspect_node(&self) -> InspectNode {
        stmt_to_node(self)
    }
}

impl ToInspectNode for StmtKind {
    fn to_inspect_node(&self) -> InspectNode {
        stmtkind_to_node(self)
    }
}

impl ToInspectNode for ast::Expr {
    fn to_inspect_node(&self) -> InspectNode {
        expr_to_node(self)
    }
}

// ---------------------------------------------------------------------------
// Convenience function
// ---------------------------------------------------------------------------

/// Return a compact tree-formatted string for any AST node.
pub fn pretty<T: ToInspectNode>(node: &T) -> String {
    render(&node.to_inspect_node())
}

// ---------------------------------------------------------------------------
// Internal builders
// ---------------------------------------------------------------------------

fn mod_to_node(m: &ast::Mod) -> InspectNode {
    match m {
        ast::Mod::Module { body, .. } => {
            let mut desc = InspectNode::new("Module");
            for s in body {
                desc = desc.child("", stmt_to_node(s));
            }
            desc
        }
        ast::Mod::Interactive { body } => {
            let mut desc = InspectNode::new("Interactive");
            for s in body {
                desc = desc.child("", stmt_to_node(s));
            }
            desc
        }
        ast::Mod::Expression { body } => {
            InspectNode::new("Expression").child("", expr_to_node(body))
        }
        ast::Mod::FunctionType { .. } => InspectNode::leaf("FunctionType(?)"),
    }
}

fn stmt_to_node(s: &ast::Stmt) -> InspectNode {
    stmtkind_to_node(&s.node)
}

fn stmtkind_to_node(node: &StmtKind) -> InspectNode {
    match node {
        StmtKind::FunctionDef {
            name, args, body, ..
        }
        | StmtKind::AsyncFunctionDef {
            name, args, body, ..
        } => {
            let prefix_str = if matches!(node, StmtKind::AsyncFunctionDef { .. }) {
                "AsyncFunctionDef"
            } else {
                "FunctionDef"
            };
            let mut label = format!("{prefix_str}({name}");
            for arg in args.posonlyargs.iter().chain(args.args.iter()) {
                label.push_str(&format!(", {}", arg.node.arg));
            }
            label.push(')');
            let mut desc = InspectNode::new(label);
            for s in body {
                desc = desc.child("", stmt_to_node(s));
            }
            desc
        }
        StmtKind::Return { value } => {
            let mut desc = InspectNode::new("Return");
            if let Some(val) = value {
                desc = desc.child("", expr_to_node(val));
            }
            desc
        }
        StmtKind::Assign { targets, value, .. } => {
            let mut desc = InspectNode::new("Assign");
            for t in targets {
                desc = desc.child("", expr_to_node(t));
            }
            desc.child("", expr_to_node(value))
        }
        StmtKind::AugAssign { target, op, value } => {
            InspectNode::new(format!("AugAssign({}=)", operator_symbol(op)))
                .child("", expr_to_node(target))
                .child("", expr_to_node(value))
        }
        StmtKind::For {
            target,
            iter,
            body,
            orelse,
            ..
        } => {
            let mut desc = InspectNode::new("For")
                .child("", expr_to_node(target))
                .child("", expr_to_node(iter));
            for s in body {
                desc = desc.child("", stmt_to_node(s));
            }
            for s in orelse {
                desc = desc.child("", stmt_to_node(s));
            }
            desc
        }
        StmtKind::If { test, body, orelse } => {
            let mut desc = InspectNode::new("If").child("", expr_to_node(test));
            for s in body {
                desc = desc.child("", stmt_to_node(s));
            }
            for s in orelse {
                desc = desc.child("", stmt_to_node(s));
            }
            desc
        }
        StmtKind::Expr { value } => InspectNode::new("ExprStmt").child("", expr_to_node(value)),
        StmtKind::Pass => InspectNode::leaf("Pass"),
        StmtKind::Break => InspectNode::leaf("Break"),
        StmtKind::Continue => InspectNode::leaf("Continue"),
        other => {
            let dbg = format!("{other:?}");
            let variant = dbg.split(['{', '(']).next().unwrap_or("?").trim();
            InspectNode::leaf(format!("{variant}(?)"))
        }
    }
}

fn expr_to_node(e: &ast::Expr) -> InspectNode {
    match &e.node {
        ExprKind::Constant { value, .. } => {
            InspectNode::leaf(format!("Constant({})", constant_str(value)))
        }
        ExprKind::Name { id, .. } => InspectNode::leaf(format!("Name({id})")),
        ExprKind::BinOp { left, op, right } => {
            InspectNode::new(format!("BinOp({})", operator_symbol(op)))
                .child("", expr_to_node(left))
                .child("", expr_to_node(right))
        }
        ExprKind::UnaryOp { op, operand } => {
            InspectNode::new(format!("UnaryOp({})", unaryop_symbol(op)))
                .child("", expr_to_node(operand))
        }
        ExprKind::BoolOp { op, values } => {
            let sym = match op {
                ast::Boolop::And => "and",
                ast::Boolop::Or => "or",
            };
            let mut desc = InspectNode::new(format!("BoolOp({sym})"));
            for v in values {
                desc = desc.child("", expr_to_node(v));
            }
            desc
        }
        ExprKind::Compare {
            left,
            ops,
            comparators,
        } => {
            let ops_str: Vec<&str> = ops.iter().map(cmpop_symbol).collect();
            let mut desc = InspectNode::new(format!("Compare({})", ops_str.join(", ")))
                .child("", expr_to_node(left));
            for c in comparators {
                desc = desc.child("", expr_to_node(c));
            }
            desc
        }
        ExprKind::Call {
            func,
            args,
            keywords,
        } => {
            let mut desc = InspectNode::new("Call").child("", expr_to_node(func));
            for a in args {
                desc = desc.child("", expr_to_node(a));
            }
            for kw in keywords {
                desc = desc.child("", expr_to_node(&kw.node.value));
            }
            desc
        }
        ExprKind::List { elts, .. } => {
            let mut desc = InspectNode::new(format!("List[{}]", elts.len()));
            for e in elts {
                desc = desc.child("", expr_to_node(e));
            }
            desc
        }
        ExprKind::Tuple { elts, .. } => {
            let mut desc = InspectNode::new(format!("Tuple[{}]", elts.len()));
            for e in elts {
                desc = desc.child("", expr_to_node(e));
            }
            desc
        }
        ExprKind::Subscript { value, slice, .. } => InspectNode::new("Subscript")
            .child("", expr_to_node(value))
            .child("", expr_to_node(slice)),
        ExprKind::Attribute { value, attr, .. } => {
            InspectNode::new(format!("Attribute(.{attr})")).child("", expr_to_node(value))
        }
        ExprKind::ListComp { elt, generators } => {
            let mut desc = InspectNode::new("ListComp").child("", expr_to_node(elt));
            for comp in generators {
                let mut for_node = InspectNode::new("for")
                    .child("", expr_to_node(&comp.target))
                    .child("", expr_to_node(&comp.iter));
                for cond in &comp.ifs {
                    for_node = for_node.child("", expr_to_node(cond));
                }
                desc = desc.child("", for_node);
            }
            desc
        }
        ExprKind::IfExp { test, body, orelse } => InspectNode::new("IfExp")
            .child("", expr_to_node(test))
            .child("", expr_to_node(body))
            .child("", expr_to_node(orelse)),
        ExprKind::Lambda { args, body } => {
            let all_args: Vec<&str> = args
                .posonlyargs
                .iter()
                .chain(args.args.iter())
                .map(|a| a.node.arg.as_str())
                .collect();
            InspectNode::new(format!("Lambda({})", all_args.join(", ")))
                .child("", expr_to_node(body))
        }
        ExprKind::NamedExpr { target, value } => InspectNode::new("NamedExpr")
            .child("", expr_to_node(target))
            .child("", expr_to_node(value)),
        ExprKind::JoinedStr { values } => {
            let mut desc = InspectNode::new("JoinedStr");
            for v in values {
                desc = desc.child("", expr_to_node(v));
            }
            desc
        }
        ExprKind::FormattedValue { value, .. } => {
            InspectNode::new("FormattedValue").child("", expr_to_node(value))
        }
        ExprKind::Starred { value, .. } => {
            InspectNode::new("Starred").child("", expr_to_node(value))
        }
        other => {
            let dbg = format!("{other:?}");
            let variant = dbg.split(['{', '(']).next().unwrap_or("?").trim();
            InspectNode::leaf(format!("{variant}(?)"))
        }
    }
}

// ---------------------------------------------------------------------------
// Operator / constant helpers
// ---------------------------------------------------------------------------

fn operator_symbol(op: &ast::Operator) -> &'static str {
    match op {
        ast::Operator::Add => "+",
        ast::Operator::Sub => "-",
        ast::Operator::Mult => "*",
        ast::Operator::MatMult => "@",
        ast::Operator::Div => "/",
        ast::Operator::Mod => "%",
        ast::Operator::Pow => "**",
        ast::Operator::LShift => "<<",
        ast::Operator::RShift => ">>",
        ast::Operator::BitOr => "|",
        ast::Operator::BitXor => "^",
        ast::Operator::BitAnd => "&",
        ast::Operator::FloorDiv => "//",
    }
}

fn unaryop_symbol(op: &ast::Unaryop) -> &'static str {
    match op {
        ast::Unaryop::Invert => "~",
        ast::Unaryop::Not => "not",
        ast::Unaryop::UAdd => "+",
        ast::Unaryop::USub => "-",
    }
}

fn cmpop_symbol(op: &ast::Cmpop) -> &'static str {
    match op {
        ast::Cmpop::Eq => "==",
        ast::Cmpop::NotEq => "!=",
        ast::Cmpop::Lt => "<",
        ast::Cmpop::LtE => "<=",
        ast::Cmpop::Gt => ">",
        ast::Cmpop::GtE => ">=",
        ast::Cmpop::Is => "is",
        ast::Cmpop::IsNot => "is not",
        ast::Cmpop::In => "in",
        ast::Cmpop::NotIn => "not in",
    }
}

fn constant_str(c: &Constant) -> String {
    match c {
        Constant::None => "None".to_string(),
        Constant::Bool(b) => (if *b { "True" } else { "False" }).to_string(),
        Constant::Str(s) => format!("\"{}\"", s.escape_default()),
        Constant::Bytes(b) => format!("b\"{}\"", String::from_utf8_lossy(b)),
        Constant::Int(i) => format!("{i}"),
        Constant::Float(v) => format!("{v}"),
        Constant::Complex { real, imag } => format!("{real}+{imag}j"),
        Constant::Tuple(elts) => {
            let mut s = "(".to_string();
            for (i, e) in elts.iter().enumerate() {
                if i > 0 {
                    s.push_str(", ");
                }
                s.push_str(&constant_str(e));
            }
            s.push(')');
            s
        }
        Constant::Ellipsis => "...".to_string(),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use rustpython_parser::parser;
    use test_log::test;

    fn parse_expr(code: &str) -> ast::Expr {
        let result = parser::parse(code, parser::Mode::Expression, "<test>").unwrap();
        match result {
            ast::Mod::Expression { body } => *body,
            other => panic!("expected Expression, got {other:?}"),
        }
    }

    fn parse_module(code: &str) -> ast::Mod {
        parser::parse(code, parser::Mode::Module, "<test>").unwrap()
    }

    #[test]
    fn constant_int() {
        let e = parse_expr("42");
        assert_eq!(pretty(&e), "Constant(42)\n");
    }

    #[test]
    fn constant_string() {
        let e = parse_expr("\"hello\"");
        assert_eq!(pretty(&e), "Constant(\"hello\")\n");
    }

    #[test]
    fn name() {
        let e = parse_expr("x");
        assert_eq!(pretty(&e), "Name(x)\n");
    }

    #[test]
    fn simple_binop() {
        let e = parse_expr("1 + 2");
        let output = pretty(&e);
        assert_eq!(
            output,
            "\
BinOp(+)
├── Constant(1)
└── Constant(2)
"
        );
    }

    #[test]
    fn nested_binop() {
        let e = parse_expr("1 + (2 * (3 - 4))");
        let output = pretty(&e);
        assert_eq!(
            output,
            "\
BinOp(+)
├── Constant(1)
└── BinOp(*)
    ├── Constant(2)
    └── BinOp(-)
        ├── Constant(3)
        └── Constant(4)
"
        );
    }

    #[test]
    fn list_expr() {
        let e = parse_expr("[1, 2, 3]");
        let output = pretty(&e);
        assert_eq!(
            output,
            "\
List[3]
├── Constant(1)
├── Constant(2)
└── Constant(3)
"
        );
    }

    #[test]
    fn assign_stmt() {
        let m = parse_module("x = 3");
        let output = pretty(&m);
        assert_eq!(
            output,
            "\
Module
└── Assign
    ├── Name(x)
    └── Constant(3)
"
        );
    }

    #[test]
    fn unary_op() {
        let e = parse_expr("-x");
        let output = pretty(&e);
        assert_eq!(
            output,
            "\
UnaryOp(-)
└── Name(x)
"
        );
    }

    #[test]
    fn bool_op() {
        let e = parse_expr("a and b and c");
        let output = pretty(&e);
        assert_eq!(
            output,
            "\
BoolOp(and)
├── Name(a)
├── Name(b)
└── Name(c)
"
        );
    }

    #[test]
    fn compare() {
        let e = parse_expr("x < 10");
        let output = pretty(&e);
        assert_eq!(
            output,
            "\
Compare(<)
├── Name(x)
└── Constant(10)
"
        );
    }

    #[test]
    fn subscript_expr() {
        let e = parse_expr("a[0]");
        let output = pretty(&e);
        assert_eq!(
            output,
            "\
Subscript
├── Name(a)
└── Constant(0)
"
        );
    }

    #[test]
    fn if_exp() {
        let e = parse_expr("x if cond else y");
        let output = pretty(&e);
        assert_eq!(
            output,
            "\
IfExp
├── Name(cond)
├── Name(x)
└── Name(y)
"
        );
    }

    #[test]
    fn lambda_expr() {
        let e = parse_expr("lambda x, y: x + y");
        let output = pretty(&e);
        assert_eq!(
            output,
            "\
Lambda(x, y)
└── BinOp(+)
    ├── Name(x)
    └── Name(y)
"
        );
    }

    #[test]
    fn list_comp() {
        let e = parse_expr("[x * 2 for x in items]");
        let output = pretty(&e);
        assert_eq!(
            output,
            "\
ListComp
├── BinOp(*)
│   ├── Name(x)
│   └── Constant(2)
└── for
    ├── Name(x)
    └── Name(items)
"
        );
    }

    #[test]
    fn list_comp_with_list_iter() {
        let e = parse_expr("[1 + i for i in [1, 2, 3, 4]]");
        let output = pretty(&e);
        assert_eq!(
            output,
            "\
ListComp
├── BinOp(+)
│   ├── Constant(1)
│   └── Name(i)
└── for
    ├── Name(i)
    └── List[4]
        ├── Constant(1)
        ├── Constant(2)
        ├── Constant(3)
        └── Constant(4)
"
        );
    }

    #[test]
    fn list_comp_with_filter() {
        let e = parse_expr("[x for x in items if x > 0]");
        let output = pretty(&e);
        assert_eq!(
            output,
            "\
ListComp
├── Name(x)
└── for
    ├── Name(x)
    ├── Name(items)
    └── Compare(>)
        ├── Name(x)
        └── Constant(0)
"
        );
    }

    #[test]
    fn fallback_stmt() {
        let m = parse_module("import os\n");
        let output = pretty(&m);
        assert!(output.contains("Import(?)"), "got: {output}");
    }

    #[test]
    fn augassign() {
        let m = parse_module("x += 1\n");
        let output = pretty(&m);
        assert_eq!(
            output,
            "\
Module
└── AugAssign(+=)
    ├── Name(x)
    └── Constant(1)
"
        );
    }

    #[test]
    fn for_stmt() {
        let m = parse_module("for x in items:\n    pass\n");
        let output = pretty(&m);
        assert_eq!(
            output,
            "\
Module
└── For
    ├── Name(x)
    ├── Name(items)
    └── Pass
"
        );
    }

    #[test]
    fn module_if_stmt() {
        let m = parse_module("if x:\n    pass\n");
        let output = pretty(&m);
        assert_eq!(
            output,
            "\
Module
└── If
    ├── Name(x)
    └── Pass
"
        );
    }

    #[test]
    fn tuple_expr() {
        let e = parse_expr("(1, 2)");
        let output = pretty(&e);
        assert_eq!(
            output,
            "\
Tuple[2]
├── Constant(1)
└── Constant(2)
"
        );
    }

    #[test]
    fn function_def_application() {
        let code = "\
def foo(z):
    x = 3
    y = x * 2
    return x * x + y * 3 * z

foo(2)
";
        let m = parse_module(code);
        let output = pretty(&m);
        assert_eq!(
            output,
            "\
Module
├── FunctionDef(foo, z)
│   ├── Assign
│   │   ├── Name(x)
│   │   └── Constant(3)
│   ├── Assign
│   │   ├── Name(y)
│   │   └── BinOp(*)
│   │       ├── Name(x)
│   │       └── Constant(2)
│   └── Return
│       └── BinOp(+)
│           ├── BinOp(*)
│           │   ├── Name(x)
│           │   └── Name(x)
│           └── BinOp(*)
│               ├── BinOp(*)
│               │   ├── Name(y)
│               │   └── Constant(3)
│               └── Name(z)
└── ExprStmt
    └── Call
        ├── Name(foo)
        └── Constant(2)
"
        );
    }

    #[test]
    fn module_with_named_expr() {
        let e = parse_module(
            r#"
d = {'key': 2}
if (value := d.get('key')):
    print(f'Found: {value}')
"#,
        );
        let output = pretty(&e);
        assert_eq!(
            output,
            "\
Module
├── Assign
│   ├── Name(d)
│   └── Dict(?)
└── If
    ├── NamedExpr
    │   ├── Name(value)
    │   └── Call
    │       ├── Attribute(.get)
    │       │   └── Name(d)
    │       └── Constant(\"key\")
    └── ExprStmt
        └── Call
            ├── Name(print)
            └── JoinedStr
                ├── Constant(\"Found: \")
                └── FormattedValue
                    └── Name(value)
"
        );
    }
}
