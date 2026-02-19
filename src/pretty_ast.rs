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

// ---------------------------------------------------------------------------
// Generic wrapper & trait
// ---------------------------------------------------------------------------
pub struct Pretty<'a, T>(pub &'a T);

// Trait used by AST nodes to describe their formatting.
pub trait AstFormatter {
    fn format(&self, f: &mut fmt::Formatter<'_>, indent: &str) -> fmt::Result;
}

// Implement Display for our generic wrapper
impl<'a, T: AstFormatter> fmt::Display for Pretty<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.format(f, "")
    }
}
// Implement the trait for each specific AST type
impl AstFormatter for ast::Mod {
    fn format(&self, f: &mut fmt::Formatter<'_>, indent: &str) -> fmt::Result {
        fmt_mod(f, self, indent)
    }
}

impl AstFormatter for ast::Stmt {
    fn format(&self, f: &mut fmt::Formatter<'_>, indent: &str) -> fmt::Result {
        fmt_stmtkind(f, &self.node, indent)
    }
}

impl AstFormatter for StmtKind {
    fn format(&self, f: &mut fmt::Formatter<'_>, indent: &str) -> fmt::Result {
        fmt_stmtkind(f, self, indent)
    }
}

impl AstFormatter for ast::Expr {
    fn format(&self, f: &mut fmt::Formatter<'_>, indent: &str) -> fmt::Result {
        fmt_expr(f, self, indent)
    }
}

// ---------------------------------------------------------------------------
// Convenience functions
// ---------------------------------------------------------------------------
// Generic pretty function
pub fn pretty<T: AstFormatter>(node: &T) -> String {
    Pretty(node).to_string()
}

// ---------------------------------------------------------------------------
// Internal formatting
//
// Convention: fmt_stmt / fmt_expr write the node label (without any leading
// prefix) followed by a newline, then recurse into children using the
// `prefix` argument for indentation.  The `prefix` is the column of vertical
// bars that continues from the parent — it is prepended only to *children*,
// not to the node's own label line (which is already positioned by the
// caller's connector).
// ---------------------------------------------------------------------------

fn fmt_mod(f: &mut fmt::Formatter<'_>, m: &ast::Mod, prefix: &str) -> fmt::Result {
    match m {
        ast::Mod::Module { body, .. } => {
            writeln!(f, "Module")?;
            fmt_children_stmt(f, body, prefix)
        }
        ast::Mod::Interactive { body } => {
            writeln!(f, "Interactive")?;
            fmt_children_stmt(f, body, prefix)
        }
        ast::Mod::Expression { body } => {
            writeln!(f, "Expression")?;
            fmt_child_expr(f, body, prefix, true)
        }
        ast::Mod::FunctionType { .. } => {
            writeln!(f, "FunctionType(?)")
        }
    }
}

fn fmt_stmt(f: &mut fmt::Formatter<'_>, s: &ast::Stmt, prefix: &str) -> fmt::Result {
    fmt_stmtkind(f, &s.node, prefix)
}

/// Format a statement node.  Writes the label (no prefix) then children
/// indented under `prefix`.
fn fmt_stmtkind(f: &mut fmt::Formatter<'_>, node: &StmtKind, prefix: &str) -> fmt::Result {
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
            write!(f, "{prefix_str}({name}")?;
            for arg in args.posonlyargs.iter().chain(args.args.iter()) {
                write!(f, ", {}", arg.node.arg)?;
            }
            writeln!(f, ")")?;
            fmt_children_stmt(f, body, prefix)
        }
        StmtKind::Return { value } => {
            writeln!(f, "Return")?;
            if let Some(val) = value {
                fmt_child_expr(f, val, prefix, true)?;
            }
            Ok(())
        }
        StmtKind::Assign { targets, value, .. } => {
            writeln!(f, "Assign")?;
            for t in targets {
                // Print the middle values (is_last = false)
                fmt_child_expr(f, t, prefix, false)?;
            }
            fmt_child_expr(f, value, prefix, true)
        }
        StmtKind::AugAssign { target, op, value } => {
            writeln!(f, "AugAssign({}=)", operator_symbol(op))?;
            fmt_child_expr(f, target, prefix, false)?;
            fmt_child_expr(f, value, prefix, true)
        }
        StmtKind::For {
            target,
            iter,
            body,
            orelse,
            ..
        } => {
            writeln!(f, "For")?;
            fmt_child_expr(f, target, prefix, false)?;
            let has_else = !orelse.is_empty();
            let test_is_last = body.is_empty() && !has_else;
            fmt_child_expr(f, iter, prefix, test_is_last)?;
            if has_else {
                fmt_children_mixed(f, body, &[], prefix, false)?;
                fmt_children_mixed(f, orelse, &[], prefix, true)?;
            } else {
                fmt_children_stmt(f, body, prefix)?;
            }
            Ok(())
        }
        StmtKind::If { test, body, orelse } => {
            writeln!(f, "If")?;
            let has_else = !orelse.is_empty();
            let test_is_last = body.is_empty() && !has_else;
            fmt_child_expr(f, test, prefix, test_is_last)?;
            if has_else {
                fmt_children_mixed(f, body, &[], prefix, false)?;
                fmt_children_mixed(f, orelse, &[], prefix, true)?;
            } else {
                fmt_children_stmt(f, body, prefix)?;
            }
            Ok(())
        }
        StmtKind::Expr { value } => {
            writeln!(f, "ExprStmt")?;
            fmt_child_expr(f, value, prefix, true)
        }
        StmtKind::Pass => writeln!(f, "Pass"),
        StmtKind::Break => writeln!(f, "Break"),
        StmtKind::Continue => writeln!(f, "Continue"),
        other => {
            let dbg = format!("{other:?}");
            let variant = dbg.split(['{', '(']).next().unwrap_or("?").trim();
            writeln!(f, "{variant}(?)")
        }
    }
}

/// Format an expression node.  Writes the label (no prefix) then children
/// indented under `prefix`.
fn fmt_expr(f: &mut fmt::Formatter<'_>, e: &ast::Expr, prefix: &str) -> fmt::Result {
    match &e.node {
        ExprKind::Constant { value, .. } => {
            write!(f, "Constant(")?;
            fmt_constant(f, value)?;
            writeln!(f, ")")
        }
        ExprKind::Name { id, .. } => writeln!(f, "Name({id})"),
        ExprKind::BinOp { left, op, right } => {
            writeln!(f, "BinOp({})", operator_symbol(op))?;
            fmt_child_expr(f, left, prefix, false)?;
            fmt_child_expr(f, right, prefix, true)
        }
        ExprKind::UnaryOp { op, operand } => {
            writeln!(f, "UnaryOp({})", unaryop_symbol(op))?;
            fmt_child_expr(f, operand, prefix, true)
        }
        ExprKind::BoolOp { op, values } => {
            let sym = match op {
                ast::Boolop::And => "and",
                ast::Boolop::Or => "or",
            };
            writeln!(f, "BoolOp({sym})")?;
            fmt_children_expr(f, values, prefix)
        }
        ExprKind::Compare {
            left,
            ops,
            comparators,
        } => {
            let ops_str: Vec<&str> = ops.iter().map(cmpop_symbol).collect();
            writeln!(f, "Compare({})", ops_str.join(", "))?;
            fmt_child_expr(f, left, prefix, comparators.is_empty())?;
            fmt_children_expr(f, comparators, prefix)
        }
        ExprKind::Call {
            func,
            args,
            keywords,
        } => {
            writeln!(f, "Call")?;

            // Unify all items into an iterator of &ast::Expr
            let mut all_children = std::iter::once(func.as_ref())
                .chain(args.iter())
                .chain(keywords.iter().map(|kw| &kw.node.value))
                .peekable();

            while let Some(child) = all_children.next() {
                let is_last = all_children.peek().is_none();
                fmt_child_expr(f, child, prefix, is_last)?;
            }
            Ok(())
        }

        ExprKind::List { elts, .. } => {
            writeln!(f, "List[{}]", elts.len())?;
            fmt_children_expr(f, elts, prefix)
        }
        ExprKind::Tuple { elts, .. } => {
            writeln!(f, "Tuple[{}]", elts.len())?;
            fmt_children_expr(f, elts, prefix)
        }
        ExprKind::Subscript { value, slice, .. } => {
            writeln!(f, "Subscript")?;
            fmt_child_expr(f, value, prefix, false)?;
            fmt_child_expr(f, slice, prefix, true)
        }
        ExprKind::Attribute { value, attr, .. } => {
            writeln!(f, "Attribute(.{attr})")?;
            fmt_child_expr(f, value, prefix, true)
        }
        ExprKind::ListComp { elt, generators } => {
            writeln!(f, "ListComp")?;
            fmt_child_expr(f, elt, prefix, generators.is_empty())?;
            for (i, comp) in generators.iter().enumerate() {
                let is_last = i + 1 == generators.len();
                let (connector, child_ext) = if is_last {
                    ("└── ", "    ")
                } else {
                    ("├── ", "│   ")
                };
                let gen_prefix = format!("{prefix}{child_ext}");
                writeln!(f, "{prefix}{connector}for")?;
                let has_ifs = !comp.ifs.is_empty();
                fmt_child_expr(f, &comp.target, &gen_prefix, false)?;
                fmt_child_expr(f, &comp.iter, &gen_prefix, !has_ifs)?;
                for (j, cond) in comp.ifs.iter().enumerate() {
                    fmt_child_expr(f, cond, &gen_prefix, j + 1 == comp.ifs.len())?;
                }
            }
            Ok(())
        }
        ExprKind::IfExp { test, body, orelse } => {
            writeln!(f, "IfExp")?;
            fmt_child_expr(f, test, prefix, false)?;
            fmt_child_expr(f, body, prefix, false)?;
            fmt_child_expr(f, orelse, prefix, true)
        }
        ExprKind::Lambda { args, body } => {
            let all_args: Vec<&str> = args
                .posonlyargs
                .iter()
                .chain(args.args.iter())
                .map(|a| a.node.arg.as_str())
                .collect();
            writeln!(f, "Lambda({})", all_args.join(", "))?;
            fmt_child_expr(f, body, prefix, true)
        }
        ExprKind::NamedExpr { target, value } => {
            writeln!(f, "NamedExpr")?;
            fmt_child_expr(f, target, prefix, false)?;
            fmt_child_expr(f, value, prefix, true)
        }
        ExprKind::JoinedStr { values } => {
            writeln!(f, "JoinedStr")?;
            fmt_children_expr(f, values, prefix)
        }
        ExprKind::FormattedValue { value, .. } => {
            writeln!(f, "FormattedValue")?;
            fmt_child_expr(f, value, prefix, true)
        }
        ExprKind::Starred { value, .. } => {
            writeln!(f, "Starred")?;
            fmt_child_expr(f, value, prefix, true)
        }
        other => {
            let dbg = format!("{other:?}");
            let variant = dbg.split(['{', '(']).next().unwrap_or("?").trim();
            writeln!(f, "{variant}(?)")
        }
    }
}

// ---------------------------------------------------------------------------
// Tree connector helpers
// ---------------------------------------------------------------------------

/// Write one expression child with the appropriate tree connector.
/// `parent_prefix` is the indentation column inherited from the parent.
fn fmt_child_expr(
    f: &mut fmt::Formatter<'_>,
    expr: &ast::Expr,
    parent_prefix: &str,
    is_last: bool,
) -> fmt::Result {
    let (connector, child_ext) = if is_last {
        ("└── ", "    ")
    } else {
        ("├── ", "│   ")
    };
    let child_prefix = format!("{parent_prefix}{child_ext}");
    write!(f, "{parent_prefix}{connector}")?;
    fmt_expr(f, expr, &child_prefix)
}

/// Write one statement child with the appropriate tree connector.
fn fmt_child_stmt(
    f: &mut fmt::Formatter<'_>,
    stmt: &ast::Stmt,
    parent_prefix: &str,
    is_last: bool,
) -> fmt::Result {
    let (connector, child_ext) = if is_last {
        ("└── ", "    ")
    } else {
        ("├── ", "│   ")
    };
    let child_prefix = format!("{parent_prefix}{child_ext}");
    write!(f, "{parent_prefix}{connector}")?;
    fmt_stmt(f, stmt, &child_prefix)
}

fn fmt_children_expr(
    f: &mut fmt::Formatter<'_>,
    exprs: &[ast::Expr],
    parent_prefix: &str,
) -> fmt::Result {
    for (i, e) in exprs.iter().enumerate() {
        fmt_child_expr(f, e, parent_prefix, i + 1 == exprs.len())?;
    }
    Ok(())
}

fn fmt_children_stmt(
    f: &mut fmt::Formatter<'_>,
    stmts: &[ast::Stmt],
    parent_prefix: &str,
) -> fmt::Result {
    for (i, s) in stmts.iter().enumerate() {
        fmt_child_stmt(f, s, parent_prefix, i + 1 == stmts.len())?;
    }
    Ok(())
}

/// Write stmts then exprs as children of the current node.
fn fmt_children_mixed(
    f: &mut fmt::Formatter<'_>,
    stmts: &[ast::Stmt],
    exprs: &[ast::Expr],
    parent_prefix: &str,
    is_last_group: bool,
) -> fmt::Result {
    let total = stmts.len() + exprs.len();
    for (i, s) in stmts.iter().enumerate() {
        let is_last = is_last_group && i + 1 == total;
        fmt_child_stmt(f, s, parent_prefix, is_last)?;
    }
    for (i, e) in exprs.iter().enumerate() {
        let is_last = is_last_group && stmts.len() + i + 1 == total;
        fmt_child_expr(f, e, parent_prefix, is_last)?;
    }
    Ok(())
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

fn fmt_constant(f: &mut fmt::Formatter<'_>, c: &Constant) -> fmt::Result {
    match c {
        Constant::None => write!(f, "None"),
        Constant::Bool(b) => write!(f, "{}", if *b { "True" } else { "False" }),
        Constant::Str(s) => write!(f, "\"{}\"", s.escape_default()),
        Constant::Bytes(b) => write!(f, "b\"{}\"", String::from_utf8_lossy(b)),
        Constant::Int(i) => write!(f, "{i}"),
        Constant::Float(v) => write!(f, "{v}"),
        Constant::Complex { real, imag } => write!(f, "{real}+{imag}j"),
        Constant::Tuple(elts) => {
            write!(f, "(")?;
            for (i, e) in elts.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                fmt_constant(f, e)?;
            }
            write!(f, ")")
        }
        Constant::Ellipsis => write!(f, "..."),
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
